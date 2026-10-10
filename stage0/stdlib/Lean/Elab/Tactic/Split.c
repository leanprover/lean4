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
uint8_t l_Lean_Name_isStr(lean_object*);
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
lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(lean_object* v_k_1_, uint8_t v_defValue_2_, lean_object* v___y_3_){
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
LEAN_EXPORT void l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
uint8_t v_defValue_2_ = stack[1].m_num;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_1_, v_defValue_2_, v___y_3_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg___boxed(lean_object* v_k_25_, lean_object* v_defValue_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
uint8_t v_defValue_boxed_29_; lean_object* v_res_30_; 
v_defValue_boxed_29_ = lean_unbox(v_defValue_26_);
v_res_30_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_25_, v_defValue_boxed_29_, v___y_27_);
lean_dec_ref(v___y_27_);
lean_dec(v_k_25_);
return v_res_30_;
}
}
lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(lean_object* v_k_31_, uint8_t v_defValue_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_31_, v_defValue_32_, v___y_35_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_31_ = stack[0].m_obj;
uint8_t v_defValue_32_ = stack[1].m_num;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(v_k_31_, v_defValue_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___boxed(lean_object* v_k_40_, lean_object* v_defValue_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v_defValue_boxed_47_; lean_object* v_res_48_; 
v_defValue_boxed_47_ = lean_unbox(v_defValue_41_);
v_res_48_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(v_k_40_, v_defValue_boxed_47_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v_k_40_);
return v_res_48_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0));
v___x_51_ = l_Lean_stringToMessageData(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1);
v___x_53_ = l_Lean_MessageData_hint_x27(v___x_52_);
return v___x_53_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(lean_object* v___x_54_, uint8_t v___x_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_75_; 
v___x_61_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v___x_54_, v___x_55_, v___y_58_);
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_75_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_75_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_75_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
uint8_t v___x_66_; 
v___x_66_ = lean_unbox(v_a_62_);
lean_dec(v_a_62_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
else
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l_Lean_MessageData_nil;
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_71_);
v___x_73_ = v___x_64_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_54_ = stack[0].m_obj;
uint8_t v___x_55_ = stack[1].m_num;
lean_object* v___y_56_ = stack[2].m_obj;
lean_object* v___y_57_ = stack[3].m_obj;
lean_object* v___y_58_ = stack[4].m_obj;
lean_object* v___y_59_ = stack[5].m_obj;
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(v___x_54_, v___x_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed(lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
uint8_t v___x_709__boxed_84_; lean_object* v_res_85_; 
v___x_709__boxed_84_ = lean_unbox(v___x_78_);
v_res_85_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(v___x_77_, v___x_709__boxed_84_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___x_77_);
return v_res_85_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6(void){
_start:
{
lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5));
v___f_100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4));
v___x_101_ = l_Lean_MessageData_ofLazyM(v___f_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6);
return v___x_102_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_env_110_; uint8_t v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v_toCold_114_; lean_object* v_mctx_115_; lean_object* v_lctx_116_; lean_object* v_options_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_env_110_);
lean_dec(v___x_109_);
v___x_111_ = 0;
v_env_112_ = l_Lean_Environment_setRecordingDeps(v_env_110_, v___x_111_);
v___x_113_ = lean_st_ref_get(v___y_105_);
v_toCold_114_ = lean_ctor_get(v___y_106_, 0);
v_mctx_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_mctx_115_);
lean_dec(v___x_113_);
v_lctx_116_ = lean_ctor_get(v___y_104_, 2);
v_options_117_ = lean_ctor_get(v_toCold_114_, 2);
lean_inc_ref(v_options_117_);
lean_inc_ref(v_lctx_116_);
v___x_118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_118_, 0, v_env_112_);
lean_ctor_set(v___x_118_, 1, v_mctx_115_);
lean_ctor_set(v___x_118_, 2, v_lctx_116_);
lean_ctor_set(v___x_118_, 3, v_options_117_);
v___x_119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_msgData_103_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_103_ = stack[0].m_obj;
lean_object* v___y_104_ = stack[1].m_obj;
lean_object* v___y_105_ = stack[2].m_obj;
lean_object* v___y_106_ = stack[3].m_obj;
lean_object* v___y_107_ = stack[4].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_ref_135_; lean_object* v___x_136_; lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
v_ref_135_ = lean_ctor_get(v___y_132_, 2);
v___x_136_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_145_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
lean_inc(v_ref_135_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_ref_135_);
lean_ctor_set(v___x_141_, 1, v_a_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 1);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_129_ = stack[0].m_obj;
lean_object* v___y_130_ = stack[1].m_obj;
lean_object* v___y_131_ = stack[2].m_obj;
lean_object* v___y_132_ = stack[3].m_obj;
lean_object* v___y_133_ = stack[4].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg___boxed(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(lean_object* v_ref_154_, lean_object* v_msg_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_toCold_165_; lean_object* v_currRecDepth_166_; lean_object* v_ref_167_; uint16_t v_optionFlags_168_; uint8_t v_suppressElabErrors_169_; uint8_t v_isRecordingDeps_170_; lean_object* v_ref_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_toCold_165_ = lean_ctor_get(v___y_162_, 0);
v_currRecDepth_166_ = lean_ctor_get(v___y_162_, 1);
v_ref_167_ = lean_ctor_get(v___y_162_, 2);
v_optionFlags_168_ = lean_ctor_get_uint16(v___y_162_, sizeof(void*)*3);
v_suppressElabErrors_169_ = lean_ctor_get_uint8(v___y_162_, sizeof(void*)*3 + 2);
v_isRecordingDeps_170_ = lean_ctor_get_uint8(v___y_162_, sizeof(void*)*3 + 3);
v_ref_171_ = l_Lean_replaceRef(v_ref_154_, v_ref_167_);
lean_inc(v_currRecDepth_166_);
lean_inc_ref(v_toCold_165_);
v___x_172_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_172_, 0, v_toCold_165_);
lean_ctor_set(v___x_172_, 1, v_currRecDepth_166_);
lean_ctor_set(v___x_172_, 2, v_ref_171_);
lean_ctor_set_uint16(v___x_172_, sizeof(void*)*3, v_optionFlags_168_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*3 + 2, v_suppressElabErrors_169_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*3 + 3, v_isRecordingDeps_170_);
v___x_173_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_155_, v___y_160_, v___y_161_, v___x_172_, v___y_163_);
lean_dec_ref_known(v___x_172_, 3);
return v___x_173_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_154_ = stack[0].m_obj;
lean_object* v_msg_155_ = stack[1].m_obj;
lean_object* v___y_156_ = stack[2].m_obj;
lean_object* v___y_157_ = stack[3].m_obj;
lean_object* v___y_158_ = stack[4].m_obj;
lean_object* v___y_159_ = stack[5].m_obj;
lean_object* v___y_160_ = stack[6].m_obj;
lean_object* v___y_161_ = stack[7].m_obj;
lean_object* v___y_162_ = stack[8].m_obj;
lean_object* v___y_163_ = stack[9].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_154_, v_msg_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(lean_object* v_ref_175_, lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_175_, v_msg_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v_ref_175_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Array_mkArray0___redArg();
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(uint8_t v___x_224_, lean_object* v_t_225_, lean_object* v_error_226_, lean_object* v_loc_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
if (v___x_224_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_225_, v_error_226_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
else
{
lean_object* v_lctx_238_; lean_object* v_name_239_; uint8_t v___x_293_; 
v_lctx_238_ = lean_ctor_get(v___y_232_, 2);
v_name_239_ = l_Lean_Syntax_getId(v_t_225_);
v___x_293_ = l_Lean_Name_isStr(v_name_239_);
if (v___x_293_ == 0)
{
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v_name_239_);
v___x_294_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_225_, v_error_226_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_294_;
}
else
{
goto v___jp_240_;
}
}
else
{
if (lean_obj_tag(v_loc_227_) == 0)
{
goto v___jp_240_;
}
else
{
lean_object* v___x_295_; 
lean_dec(v_name_239_);
v___x_295_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_225_, v_error_226_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_295_;
}
}
v___jp_240_:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_238_, v_name_239_);
if (lean_obj_tag(v___x_241_) == 1)
{
lean_object* v_val_242_; lean_object* v_ref_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_val_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_241_, 1);
v_ref_243_ = lean_ctor_get(v___y_234_, 2);
v___x_244_ = l_Lean_LocalDecl_toExpr(v_val_242_);
v___x_245_ = 0;
v___x_246_ = l_Lean_SourceInfo_fromRef(v_ref_243_, v___x_245_);
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1));
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1));
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc_n(v___x_246_, 7);
v___x_250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_246_);
lean_ctor_set(v___x_250_, 1, v___x_248_);
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7));
v___x_252_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8);
v___x_253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_246_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
v___x_254_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
v___x_255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11));
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_246_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13));
v___x_258_ = l_Lean_mkIdent(v_name_239_);
v___x_259_ = l_Lean_Syntax_node1(v___x_246_, v___x_251_, v___x_258_);
v___x_260_ = l_Lean_Syntax_node1(v___x_246_, v___x_257_, v___x_259_);
v___x_261_ = l_Lean_Syntax_node2(v___x_246_, v___x_254_, v___x_256_, v___x_260_);
v___x_262_ = l_Lean_Syntax_node1(v___x_246_, v___x_251_, v___x_261_);
v___x_263_ = l_Lean_Syntax_node3(v___x_246_, v___x_249_, v___x_250_, v___x_253_, v___x_262_);
v___x_264_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15);
v___x_265_ = l_Lean_MessageData_ofExpr(v___x_244_);
lean_inc_ref(v___x_265_);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_265_);
v___x_270_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_247_);
lean_ctor_set(v___x_272_, 1, v___x_263_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v___x_273_);
lean_ctor_set(v___x_274_, 3, v___x_273_);
lean_ctor_set(v___x_274_, 4, v___x_273_);
lean_ctor_set(v___x_274_, 5, v___x_273_);
v___x_275_ = 0;
v___x_276_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_273_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*3, v___x_275_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_mk_empty_array_with_capacity(v___x_277_);
v___x_279_ = lean_array_push(v___x_278_, v___x_276_);
v___x_280_ = l_Lean_MessageData_hint(v___x_271_, v___x_279_, v___x_273_, v___x_273_, v___x_245_, v___y_234_, v___y_235_);
lean_dec_ref(v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v_error_226_);
lean_ctor_set(v___x_282_, 1, v_a_281_);
v___x_283_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_225_, v___x_282_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_283_;
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_error_226_);
v_a_284_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_280_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_280_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v___x_241_);
lean_dec(v_name_239_);
v___x_292_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_225_, v_error_226_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_224_ = stack[0].m_num;
lean_object* v_t_225_ = stack[1].m_obj;
lean_object* v_error_226_ = stack[2].m_obj;
lean_object* v_loc_227_ = stack[3].m_obj;
lean_object* v___y_228_ = stack[4].m_obj;
lean_object* v___y_229_ = stack[5].m_obj;
lean_object* v___y_230_ = stack[6].m_obj;
lean_object* v___y_231_ = stack[7].m_obj;
lean_object* v___y_232_ = stack[8].m_obj;
lean_object* v___y_233_ = stack[9].m_obj;
lean_object* v___y_234_ = stack[10].m_obj;
lean_object* v___y_235_ = stack[11].m_obj;
lean_object* v_res_296_;
v_res_296_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_224_, v_t_225_, v_error_226_, v_loc_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed(lean_object* v___x_297_, lean_object* v_t_298_, lean_object* v_error_299_, lean_object* v_loc_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v___x_6226__boxed_310_; lean_object* v_res_311_; 
v___x_6226__boxed_310_ = lean_unbox(v___x_297_);
v_res_311_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_6226__boxed_310_, v_t_298_, v_error_299_, v_loc_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v_loc_300_);
lean_dec(v_t_298_);
return v_res_311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v_error_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0));
v_error_314_ = l_Lean_stringToMessageData(v___x_313_);
return v_error_314_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(lean_object* v_t_315_, lean_object* v_loc_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_error_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___y_329_; lean_object* v___x_330_; 
v_error_326_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1);
v___x_327_ = l_Lean_Syntax_isIdent(v_t_315_);
v___x_328_ = lean_box(v___x_327_);
v___y_329_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed), 13, 4);
lean_closure_set(v___y_329_, 0, v___x_328_);
lean_closure_set(v___y_329_, 1, v_t_315_);
lean_closure_set(v___y_329_, 2, v_error_326_);
lean_closure_set(v___y_329_, 3, v_loc_316_);
v___x_330_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_329_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_330_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_315_ = stack[0].m_obj;
lean_object* v_loc_316_ = stack[1].m_obj;
lean_object* v_a_317_ = stack[2].m_obj;
lean_object* v_a_318_ = stack[3].m_obj;
lean_object* v_a_319_ = stack[4].m_obj;
lean_object* v_a_320_ = stack[5].m_obj;
lean_object* v_a_321_ = stack[6].m_obj;
lean_object* v_a_322_ = stack[7].m_obj;
lean_object* v_a_323_ = stack[8].m_obj;
lean_object* v_a_324_ = stack[9].m_obj;
lean_object* v_res_331_;
v_res_331_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_315_, v_loc_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___boxed(lean_object* v_t_332_, lean_object* v_loc_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_332_, v_loc_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_343_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(lean_object* v_00_u03b1_344_, lean_object* v_ref_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_345_, v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_345_ = stack[1].m_obj;
lean_object* v_msg_346_ = stack[2].m_obj;
lean_object* v___y_347_ = stack[3].m_obj;
lean_object* v___y_348_ = stack[4].m_obj;
lean_object* v___y_349_ = stack[5].m_obj;
lean_object* v___y_350_ = stack[6].m_obj;
lean_object* v___y_351_ = stack[7].m_obj;
lean_object* v___y_352_ = stack[8].m_obj;
lean_object* v___y_353_ = stack[9].m_obj;
lean_object* v___y_354_ = stack[10].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(lean_box(0), v_ref_345_, v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(lean_object* v_00_u03b1_358_, lean_object* v_ref_359_, lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(v_00_u03b1_358_, v_ref_359_, v_msg_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v_ref_359_);
return v_res_370_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(lean_object* v_00_u03b1_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_372_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_372_ = stack[1].m_obj;
lean_object* v___y_373_ = stack[2].m_obj;
lean_object* v___y_374_ = stack[3].m_obj;
lean_object* v___y_375_ = stack[4].m_obj;
lean_object* v___y_376_ = stack[5].m_obj;
lean_object* v___y_377_ = stack[6].m_obj;
lean_object* v___y_378_ = stack[7].m_obj;
lean_object* v___y_379_ = stack[8].m_obj;
lean_object* v___y_380_ = stack[9].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(lean_box(0), v_msg_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(lean_object* v_00_u03b1_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(v_00_u03b1_384_, v_msg_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_395_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
if (lean_obj_tag(v_a_399_) == 0)
{
lean_object* v___x_401_; 
v___x_401_ = l_List_reverse___redArg(v_a_400_);
return v___x_401_;
}
else
{
lean_object* v_head_402_; lean_object* v_tail_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_415_; 
v_head_402_ = lean_ctor_get(v_a_399_, 0);
v_tail_403_ = lean_ctor_get(v_a_399_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_a_399_);
if (v_isSharedCheck_415_ == 0)
{
v___x_405_ = v_a_399_;
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_tail_403_);
lean_inc(v_head_402_);
lean_dec(v_a_399_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_415_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_407_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_408_ = l_Lean_MessageData_ofSyntax(v_head_402_);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_407_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_a_400_);
lean_ctor_set(v___x_405_, 0, v___x_410_);
v___x_412_ = v___x_405_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_a_400_);
v___x_412_ = v_reuseFailAlloc_414_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v_a_399_ = v_tail_403_;
v_a_400_ = v___x_412_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_ref_422_; lean_object* v___x_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_432_; 
v_ref_422_ = lean_ctor_get(v___y_419_, 2);
v___x_423_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_432_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_inc(v_ref_422_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_ref_422_);
lean_ctor_set(v___x_428_, 1, v_a_424_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_416_ = stack[0].m_obj;
lean_object* v___y_417_ = stack[1].m_obj;
lean_object* v___y_418_ = stack[2].m_obj;
lean_object* v___y_419_ = stack[3].m_obj;
lean_object* v___y_420_ = stack[4].m_obj;
lean_object* v_res_433_;
v_res_433_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg___boxed(lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(lean_object* v_ref_441_, lean_object* v_msg_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_toCold_448_; lean_object* v_currRecDepth_449_; lean_object* v_ref_450_; uint16_t v_optionFlags_451_; uint8_t v_suppressElabErrors_452_; uint8_t v_isRecordingDeps_453_; lean_object* v_ref_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_toCold_448_ = lean_ctor_get(v___y_445_, 0);
v_currRecDepth_449_ = lean_ctor_get(v___y_445_, 1);
v_ref_450_ = lean_ctor_get(v___y_445_, 2);
v_optionFlags_451_ = lean_ctor_get_uint16(v___y_445_, sizeof(void*)*3);
v_suppressElabErrors_452_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*3 + 2);
v_isRecordingDeps_453_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*3 + 3);
v_ref_454_ = l_Lean_replaceRef(v_ref_441_, v_ref_450_);
lean_inc(v_currRecDepth_449_);
lean_inc_ref(v_toCold_448_);
v___x_455_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_455_, 0, v_toCold_448_);
lean_ctor_set(v___x_455_, 1, v_currRecDepth_449_);
lean_ctor_set(v___x_455_, 2, v_ref_454_);
lean_ctor_set_uint16(v___x_455_, sizeof(void*)*3, v_optionFlags_451_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*3 + 2, v_suppressElabErrors_452_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*3 + 3, v_isRecordingDeps_453_);
v___x_456_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_442_, v___y_443_, v___y_444_, v___x_455_, v___y_446_);
lean_dec_ref_known(v___x_455_, 3);
return v___x_456_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_441_ = stack[0].m_obj;
lean_object* v_msg_442_ = stack[1].m_obj;
lean_object* v___y_443_ = stack[2].m_obj;
lean_object* v___y_444_ = stack[3].m_obj;
lean_object* v___y_445_ = stack[4].m_obj;
lean_object* v___y_446_ = stack[5].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_441_, v_msg_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(lean_object* v_ref_458_, lean_object* v_msg_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_458_, v_msg_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v_ref_458_);
return v_res_465_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5);
v___x_476_ = l_Lean_MessageData_hint_x27(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(lean_object* v_stx_485_, uint8_t v_simplifyTarget_486_, lean_object* v_hyps_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_512_; 
if (v_simplifyTarget_486_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11));
v___y_512_ = v___x_518_;
goto v___jp_511_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12));
v___y_512_ = v___x_519_;
goto v___jp_511_;
}
v___jp_493_:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_hypsStr_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_496_ = lean_array_to_list(v_hyps_487_);
v___x_497_ = lean_box(0);
v___x_498_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(v___x_496_, v___x_497_);
v___x_499_ = l_Lean_MessageData_andList(v___x_498_);
lean_inc_ref(v___y_495_);
v_hypsStr_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hypsStr_500_, 0, v___y_495_);
lean_ctor_set(v_hypsStr_500_, 1, v___x_499_);
v___x_501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1);
lean_inc_ref(v___y_494_);
v___x_502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_502_, 0, v___y_494_);
v___x_503_ = l_Lean_MessageData_ofFormat(v___x_502_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_hypsStr_500_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_501_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_stx_485_, v___x_509_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
return v___x_510_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_array_get_size(v_hyps_487_);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8);
v___y_494_ = v___y_512_;
v___y_495_ = v___x_516_;
goto v___jp_493_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10);
v___y_494_ = v___y_512_;
v___y_495_ = v___x_517_;
goto v___jp_493_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_485_ = stack[0].m_obj;
uint8_t v_simplifyTarget_486_ = stack[1].m_num;
lean_object* v_hyps_487_ = stack[2].m_obj;
lean_object* v_a_488_ = stack[3].m_obj;
lean_object* v_a_489_ = stack[4].m_obj;
lean_object* v_a_490_ = stack[5].m_obj;
lean_object* v_a_491_ = stack[6].m_obj;
lean_object* v_res_520_;
v_res_520_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_485_, v_simplifyTarget_486_, v_hyps_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___boxed(lean_object* v_stx_521_, lean_object* v_simplifyTarget_522_, lean_object* v_hyps_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
uint8_t v_simplifyTarget_boxed_529_; lean_object* v_res_530_; 
v_simplifyTarget_boxed_529_ = lean_unbox(v_simplifyTarget_522_);
v_res_530_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_521_, v_simplifyTarget_boxed_529_, v_hyps_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_stx_521_);
return v_res_530_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(lean_object* v_stx_531_, uint8_t v_simplifyTarget_532_, lean_object* v_hyps_533_, lean_object* v_00_u03b1_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_531_, v_simplifyTarget_532_, v_hyps_533_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_540_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_531_ = stack[0].m_obj;
uint8_t v_simplifyTarget_532_ = stack[1].m_num;
lean_object* v_hyps_533_ = stack[2].m_obj;
lean_object* v_a_535_ = stack[4].m_obj;
lean_object* v_a_536_ = stack[5].m_obj;
lean_object* v_a_537_ = stack[6].m_obj;
lean_object* v_a_538_ = stack[7].m_obj;
lean_object* v_res_541_;
v_res_541_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(v_stx_531_, v_simplifyTarget_532_, v_hyps_533_, lean_box(0), v_a_535_, v_a_536_, v_a_537_, v_a_538_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(lean_object* v_stx_542_, lean_object* v_simplifyTarget_543_, lean_object* v_hyps_544_, lean_object* v_00_u03b1_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
uint8_t v_simplifyTarget_boxed_551_; lean_object* v_res_552_; 
v_simplifyTarget_boxed_551_ = lean_unbox(v_simplifyTarget_543_);
v_res_552_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(v_stx_542_, v_simplifyTarget_boxed_551_, v_hyps_544_, v_00_u03b1_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_stx_542_);
return v_res_552_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(lean_object* v_00_u03b1_553_, lean_object* v_ref_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_554_, v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_561_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_554_ = stack[1].m_obj;
lean_object* v_msg_555_ = stack[2].m_obj;
lean_object* v___y_556_ = stack[3].m_obj;
lean_object* v___y_557_ = stack[4].m_obj;
lean_object* v___y_558_ = stack[5].m_obj;
lean_object* v___y_559_ = stack[6].m_obj;
lean_object* v_res_562_;
v_res_562_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(lean_box(0), v_ref_554_, v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(lean_object* v_00_u03b1_563_, lean_object* v_ref_564_, lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(v_00_u03b1_563_, v_ref_564_, v_msg_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v_ref_564_);
return v_res_571_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(lean_object* v_00_u03b1_572_, lean_object* v_msg_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
return v___x_579_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_573_ = stack[1].m_obj;
lean_object* v___y_574_ = stack[2].m_obj;
lean_object* v___y_575_ = stack[3].m_obj;
lean_object* v___y_576_ = stack[4].m_obj;
lean_object* v___y_577_ = stack[5].m_obj;
lean_object* v_res_580_;
v_res_580_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(lean_box(0), v_msg_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
stack->m_obj
 = v_res_580_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(v_00_u03b1_581_, v_msg_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_588_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0));
v___x_591_ = l_Lean_stringToMessageData(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2));
v___x_594_ = l_Lean_stringToMessageData(v___x_593_);
return v___x_594_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(lean_object* v_type_604_, lean_object* v___x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_val_612_; uint8_t v_a_621_; lean_object* v___x_631_; 
v___x_631_ = l_Lean_Expr_getAppFn(v___x_605_);
if (lean_obj_tag(v___x_631_) == 4)
{
lean_object* v_declName_632_; lean_object* v___x_633_; lean_object* v_env_634_; uint8_t v___x_635_; 
v_declName_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_n(v_declName_632_, 2);
lean_dec_ref_known(v___x_631_, 2);
v___x_633_ = lean_st_ref_get(v___y_609_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref_n(v_env_634_, 2);
lean_dec(v___x_633_);
v___x_635_ = l_Lean_isStructure(v_env_634_, v_declName_632_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_env_634_);
lean_dec(v_declName_632_);
v_a_621_ = v___x_635_;
goto v___jp_620_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = l_Lean_getStructureFields(v_env_634_, v_declName_632_);
v___x_638_ = lean_array_get_size(v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = lean_nat_dec_lt(v___x_636_, v___x_638_);
v_a_621_ = v___x_639_;
goto v___jp_620_;
}
}
else
{
uint8_t v___x_640_; 
lean_dec_ref(v___x_631_);
v___x_640_ = 0;
v_a_621_ = v___x_640_;
goto v___jp_620_;
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_613_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1);
lean_inc_ref(v_val_612_);
v___x_614_ = l_Lean_stringToMessageData(v_val_612_);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_MessageData_hint_x27(v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
v___jp_620_:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5));
v___x_623_ = l_Lean_Expr_isAppOf(v_type_604_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7));
v___x_625_ = l_Lean_Expr_isAppOf(v_type_604_, v___x_624_);
if (v___x_625_ == 0)
{
if (v_a_621_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = l_Lean_MessageData_nil;
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8));
v_val_612_ = v___x_628_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_629_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9));
v_val_612_ = v___x_629_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_630_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10));
v_val_612_ = v___x_630_;
goto v___jp_611_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_604_ = stack[0].m_obj;
lean_object* v___x_605_ = stack[1].m_obj;
lean_object* v___y_606_ = stack[2].m_obj;
lean_object* v___y_607_ = stack[3].m_obj;
lean_object* v___y_608_ = stack[4].m_obj;
lean_object* v___y_609_ = stack[5].m_obj;
lean_object* v_res_641_;
v_res_641_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(v_type_604_, v___x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed(lean_object* v_type_642_, lean_object* v___x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(v_type_642_, v___x_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___x_643_);
lean_dec_ref(v_type_642_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(lean_object* v_type_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = l_Lean_Expr_getAppFn(v_type_650_);
v___f_652_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_652_, 0, v_type_650_);
lean_closure_set(v___f_652_, 1, v___x_651_);
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5));
v___x_654_ = l_Lean_MessageData_ofLazyM(v___f_652_, v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(lean_object* v_mvarId_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; 
lean_inc(v_mvarId_660_);
v___x_666_ = l_Lean_MVarId_getType(v_mvarId_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_667_);
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_670_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_668_);
v___x_672_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
v___x_675_ = l_Lean_Meta_throwTacticEx___redArg(v___x_669_, v_mvarId_660_, v___x_674_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_675_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_mvarId_660_);
v_a_676_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_666_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_660_ = stack[0].m_obj;
lean_object* v_a_661_ = stack[1].m_obj;
lean_object* v_a_662_ = stack[2].m_obj;
lean_object* v_a_663_ = stack[3].m_obj;
lean_object* v_a_664_ = stack[4].m_obj;
lean_object* v_res_684_;
v_res_684_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_mvarId_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___boxed(lean_object* v_mvarId_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_mvarId_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(lean_object* v_fvarId_698_, lean_object* v_mvarId_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; 
lean_inc(v_fvarId_698_);
v___x_705_ = l_Lean_FVarId_getType___redArg(v_fvarId_698_, v_a_700_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_n(v_a_706_, 2);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_708_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1);
v___x_709_ = lean_unsigned_to_nat(30u);
v___x_710_ = l_Lean_inlineExpr(v_a_706_, v___x_709_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_Expr_fvar___override(v_fvarId_698_);
v___x_715_ = l_Lean_MessageData_ofExpr(v___x_714_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_713_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_706_);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = l_Lean_Meta_throwTacticEx___redArg(v___x_707_, v_mvarId_699_, v___x_723_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_724_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_mvarId_699_);
lean_dec(v_fvarId_698_);
v_a_725_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_705_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_705_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_698_ = stack[0].m_obj;
lean_object* v_mvarId_699_ = stack[1].m_obj;
lean_object* v_a_700_ = stack[2].m_obj;
lean_object* v_a_701_ = stack[3].m_obj;
lean_object* v_a_702_ = stack[4].m_obj;
lean_object* v_a_703_ = stack[5].m_obj;
lean_object* v_res_733_;
v_res_733_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_fvarId_698_, v_mvarId_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___boxed(lean_object* v_fvarId_734_, lean_object* v_mvarId_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_fvarId_734_, v_mvarId_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
if (lean_obj_tag(v_a_742_) == 0)
{
lean_object* v___x_744_; 
v___x_744_ = l_List_reverse___redArg(v_a_743_);
return v___x_744_;
}
else
{
lean_object* v_head_745_; lean_object* v_tail_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_759_; 
v_head_745_ = lean_ctor_get(v_a_742_, 0);
v_tail_746_ = lean_ctor_get(v_a_742_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_759_ == 0)
{
v___x_748_ = v_a_742_;
v_isShared_749_ = v_isSharedCheck_759_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_tail_746_);
lean_inc(v_head_745_);
lean_dec(v_a_742_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_759_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_750_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_751_ = l_Lean_Expr_fvar___override(v_head_745_);
v___x_752_ = l_Lean_MessageData_ofExpr(v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_750_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_a_743_);
lean_ctor_set(v___x_748_, 0, v___x_754_);
v___x_756_ = v___x_748_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_a_743_);
v___x_756_ = v_reuseFailAlloc_758_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v_a_742_ = v_tail_746_;
v_a_743_ = v___x_756_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1));
v___x_764_ = l_Lean_MessageData_ofFormat(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3(void){
_start:
{
lean_object* v___x_765_; lean_object* v_note_766_; 
v___x_765_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2);
v_note_766_ = l_Lean_MessageData_note(v___x_765_);
return v_note_766_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6(void){
_start:
{
lean_object* v_note_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_note_770_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_771_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_note_770_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_774_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10));
v___x_782_ = l_Lean_MessageData_ofFormat(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(lean_object* v_fvarIds_786_, lean_object* v_mvarId_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_note_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_note_793_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_fvarIds_786_);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_fvarIds_786_);
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_798_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8);
v___x_799_ = l_Lean_Meta_throwTacticEx___redArg(v___x_797_, v_mvarId_787_, v___x_798_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v_fvarMsgs_802_; lean_object* v___x_803_; lean_object* v_fvarMsgs_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_800_ = lean_array_to_list(v_fvarIds_786_);
v___x_801_ = lean_box(0);
v_fvarMsgs_802_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(v___x_800_, v___x_801_);
v___x_803_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11);
v_fvarMsgs_804_ = l_Lean_MessageData_joinSep(v_fvarMsgs_802_, v___x_803_);
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_806_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_fvarMsgs_804_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_note_793_);
v___x_809_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = l_Lean_Meta_throwTacticEx___redArg(v___x_805_, v_mvarId_787_, v___x_811_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_812_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_786_ = stack[0].m_obj;
lean_object* v_mvarId_787_ = stack[1].m_obj;
lean_object* v_a_788_ = stack[2].m_obj;
lean_object* v_a_789_ = stack[3].m_obj;
lean_object* v_a_790_ = stack[4].m_obj;
lean_object* v_a_791_ = stack[5].m_obj;
lean_object* v_res_813_;
v_res_813_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_786_, v_mvarId_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___boxed(lean_object* v_fvarIds_814_, lean_object* v_mvarId_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_814_, v_mvarId_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
return v_res_821_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(lean_object* v_00_u03b1_822_, lean_object* v_fvarIds_823_, lean_object* v_mvarId_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_823_, v_mvarId_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_830_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_823_ = stack[1].m_obj;
lean_object* v_mvarId_824_ = stack[2].m_obj;
lean_object* v_a_825_ = stack[3].m_obj;
lean_object* v_a_826_ = stack[4].m_obj;
lean_object* v_a_827_ = stack[5].m_obj;
lean_object* v_a_828_ = stack[6].m_obj;
lean_object* v_res_831_;
v_res_831_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(lean_box(0), v_fvarIds_823_, v_mvarId_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(lean_object* v_00_u03b1_832_, lean_object* v_fvarIds_833_, lean_object* v_mvarId_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(v_00_u03b1_832_, v_fvarIds_833_, v_mvarId_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(lean_object* v_a_844_, lean_object* v_as_845_, size_t v_sz_846_, size_t v_i_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_847_, v_sz_846_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
lean_dec(v_a_844_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_b_848_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_859_; 
lean_dec_ref(v_b_848_);
v___x_856_ = lean_box(0);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_a_858_ = lean_array_uget_borrowed(v_as_845_, v_i_847_);
lean_inc(v_a_858_);
lean_inc(v_a_844_);
v___x_859_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_844_, v_a_858_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_871_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
if (lean_obj_tag(v_a_860_) == 1)
{
lean_object* v___x_864_; lean_object* v___x_866_; 
lean_dec(v_a_844_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_a_860_);
lean_ctor_set(v___x_864_, 1, v___x_856_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
else
{
size_t v___x_868_; size_t v___x_869_; 
lean_del_object(v___x_862_);
lean_dec(v_a_860_);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_847_, v___x_868_);
v_i_847_ = v___x_869_;
v_b_848_ = v___x_857_;
goto _start;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_844_);
v_a_872_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_859_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_859_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_844_ = stack[0].m_obj;
lean_object* v_as_845_ = stack[1].m_obj;
size_t v_sz_846_ = stack[2].m_num;
size_t v_i_847_ = stack[3].m_num;
lean_object* v_b_848_ = stack[4].m_obj;
lean_object* v___y_849_ = stack[5].m_obj;
lean_object* v___y_850_ = stack[6].m_obj;
lean_object* v___y_851_ = stack[7].m_obj;
lean_object* v___y_852_ = stack[8].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_844_, v_as_845_, v_sz_846_, v_i_847_, v_b_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___boxed(lean_object* v_a_881_, lean_object* v_as_882_, lean_object* v_sz_883_, lean_object* v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
size_t v_sz_boxed_891_; size_t v_i_boxed_892_; lean_object* v_res_893_; 
v_sz_boxed_891_ = lean_unbox_usize(v_sz_883_);
lean_dec(v_sz_883_);
v_i_boxed_892_ = lean_unbox_usize(v_i_884_);
lean_dec(v_i_884_);
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_881_, v_as_882_, v_sz_boxed_891_, v_i_boxed_892_, v_b_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v_as_882_);
return v_res_893_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0(lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_a_904_; lean_object* v___x_915_; 
v___x_915_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_895_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_n(v_a_916_, 2);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = l_Lean_MVarId_getNondepPropHyps(v_a_916_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; size_t v_sz_920_; size_t v___x_921_; lean_object* v___x_922_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_sz_920_ = lean_array_size(v_a_918_);
v___x_921_ = ((size_t)0ULL);
lean_inc(v_a_916_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_916_, v_a_918_, v_sz_920_, v___x_921_, v___x_919_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v_fst_924_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v_fst_924_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_fst_924_);
lean_dec(v_a_923_);
if (lean_obj_tag(v_fst_924_) == 0)
{
uint8_t v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v___x_925_ = 1;
v___x_926_ = 0;
lean_inc(v_a_916_);
v___x_927_ = l_Lean_Meta_splitTarget_x3f(v_a_916_, v___x_925_, v___x_926_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
if (lean_obj_tag(v_a_928_) == 1)
{
lean_object* v_val_929_; 
lean_dec(v_a_918_);
lean_dec(v_a_916_);
v_val_929_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v_a_928_, 1);
v_a_904_ = v_val_929_;
goto v___jp_903_;
}
else
{
lean_object* v___x_930_; 
lean_dec(v_a_928_);
v___x_930_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_a_918_, v_a_916_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v_a_904_ = v_a_931_;
goto v___jp_903_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_932_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_930_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_918_);
lean_dec(v_a_916_);
v_a_940_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_927_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_927_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_val_948_; 
lean_dec(v_a_918_);
lean_dec(v_a_916_);
v_val_948_ = lean_ctor_get(v_fst_924_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v_fst_924_, 1);
v_a_904_ = v_val_948_;
goto v___jp_903_;
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_918_);
lean_dec(v_a_916_);
v_a_949_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_922_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_922_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_a_916_);
v_a_957_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_917_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_917_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_915_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_915_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_box(0);
v___x_906_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_904_, v___y_895_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___x_906_, 0);
lean_dec(v_unused_914_);
v___x_908_ = v___x_906_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_dec(v___x_906_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_905_);
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_905_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
return v___x_906_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSplit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_894_ = stack[0].m_obj;
lean_object* v___y_895_ = stack[1].m_obj;
lean_object* v___y_896_ = stack[2].m_obj;
lean_object* v___y_897_ = stack[3].m_obj;
lean_object* v___y_898_ = stack[4].m_obj;
lean_object* v___y_899_ = stack[5].m_obj;
lean_object* v___y_900_ = stack[6].m_obj;
lean_object* v___y_901_ = stack[7].m_obj;
lean_object* v_res_973_;
v_res_973_ = l_Lean_Elab_Tactic_evalSplit___lam__0(v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0___boxed(lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Elab_Tactic_evalSplit___lam__0(v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_983_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1(uint8_t v_type_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_a_995_; lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_986_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc_n(v_a_1007_, 2);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_Meta_splitTarget_x3f(v_a_1007_, v_type_984_, v___x_1008_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
if (lean_obj_tag(v_a_1010_) == 1)
{
lean_object* v_val_1011_; 
lean_dec(v_a_1007_);
v_val_1011_ = lean_ctor_get(v_a_1010_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v_a_1010_, 1);
v_a_995_ = v_val_1011_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1012_; 
lean_dec(v_a_1010_);
v___x_1012_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_a_1007_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v_a_995_ = v_a_1013_;
goto v___jp_994_;
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1012_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_1007_);
v_a_1022_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1009_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1009_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1006_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1006_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(0);
v___x_997_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_995_, v___y_986_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v___x_997_, 0);
lean_dec(v_unused_1005_);
v___x_999_ = v___x_997_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_dec(v___x_997_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_996_);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_996_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
return v___x_997_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSplit___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_type_984_ = stack[0].m_num;
lean_object* v___y_985_ = stack[1].m_obj;
lean_object* v___y_986_ = stack[2].m_obj;
lean_object* v___y_987_ = stack[3].m_obj;
lean_object* v___y_988_ = stack[4].m_obj;
lean_object* v___y_989_ = stack[5].m_obj;
lean_object* v___y_990_ = stack[6].m_obj;
lean_object* v___y_991_ = stack[7].m_obj;
lean_object* v___y_992_ = stack[8].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_Lean_Elab_Tactic_evalSplit___lam__1(v_type_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1___boxed(lean_object* v_type_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v_type_3813__boxed_1049_; lean_object* v_res_1050_; 
v_type_3813__boxed_1049_ = lean_unbox(v_type_1039_);
v_res_1050_ = l_Lean_Elab_Tactic_evalSplit___lam__1(v_type_3813__boxed_1049_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1050_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2(lean_object* v_a_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_a_1062_; lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1053_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_n(v_a_1074_, 2);
lean_dec_ref_known(v___x_1073_, 1);
lean_inc(v_a_1051_);
v___x_1075_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_1074_, v_a_1051_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
if (lean_obj_tag(v_a_1076_) == 1)
{
lean_object* v_val_1077_; 
lean_dec(v_a_1074_);
lean_dec(v_a_1051_);
v_val_1077_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_val_1077_);
lean_dec_ref_known(v_a_1076_, 1);
v_a_1062_ = v_val_1077_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1078_; 
lean_dec(v_a_1076_);
v___x_1078_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_a_1051_, v_a_1074_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_a_1062_ = v_a_1079_;
goto v___jp_1061_;
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_1074_);
lean_dec(v_a_1051_);
v_a_1088_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1075_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1075_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_a_1051_);
v_a_1096_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1073_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1073_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
v___jp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_1062_, v___y_1053_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1064_, 0);
lean_dec(v_unused_1072_);
v___x_1066_ = v___x_1064_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v___x_1064_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1063_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSplit___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1051_ = stack[0].m_obj;
lean_object* v___y_1052_ = stack[1].m_obj;
lean_object* v___y_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v___y_1057_ = stack[6].m_obj;
lean_object* v___y_1058_ = stack[7].m_obj;
lean_object* v___y_1059_ = stack[8].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_Elab_Tactic_evalSplit___lam__2(v_a_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2___boxed(lean_object* v_a_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Elab_Tactic_evalSplit___lam__2(v_a_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1115_;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object* v_stx_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___f_1127_; lean_object* v___x_1128_; lean_object* v___y_1130_; lean_object* v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; uint8_t v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1171_; uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___f_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSplit___closed__0));
v___x_1128_ = lean_box(0);
v___x_1206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc(v_stx_1117_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v_stx_1117_, v___x_1206_);
if (v___x_1207_ == 0)
{
v___y_1187_ = v_a_1118_;
v___y_1188_ = v_a_1119_;
v___y_1189_ = v_a_1120_;
v___y_1190_ = v_a_1121_;
v___y_1191_ = v_a_1122_;
v___y_1192_ = v_a_1123_;
v___y_1193_ = v_a_1124_;
v___y_1194_ = v_a_1125_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1208_);
lean_inc(v___x_1209_);
v___x_1210_ = l_Lean_Syntax_matchesNull(v___x_1209_, v___x_1208_);
if (v___x_1210_ == 0)
{
lean_dec(v___x_1209_);
v___y_1187_ = v_a_1118_;
v___y_1188_ = v_a_1119_;
v___y_1189_ = v_a_1120_;
v___y_1190_ = v_a_1121_;
v___y_1191_ = v_a_1122_;
v___y_1192_ = v_a_1123_;
v___y_1193_ = v_a_1124_;
v___y_1194_ = v_a_1125_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1211_; lean_object* v_t_1212_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v_t_1212_ = l_Lean_Syntax_getArg(v___x_1209_, v___x_1211_);
lean_dec(v___x_1209_);
v___x_1224_ = lean_unsigned_to_nat(2u);
v___x_1225_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1224_);
v___x_1226_ = l_Lean_Syntax_isNone(v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; 
lean_inc(v___x_1225_);
v___x_1227_ = l_Lean_Syntax_matchesNull(v___x_1225_, v___x_1208_);
if (v___x_1227_ == 0)
{
lean_dec(v___x_1225_);
lean_dec(v_t_1212_);
v___y_1187_ = v_a_1118_;
v___y_1188_ = v_a_1119_;
v___y_1189_ = v_a_1120_;
v___y_1190_ = v_a_1121_;
v___y_1191_ = v_a_1122_;
v___y_1192_ = v_a_1123_;
v___y_1193_ = v_a_1124_;
v___y_1194_ = v_a_1125_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1228_ = l_Lean_Syntax_getArg(v___x_1225_, v___x_1211_);
lean_dec(v___x_1225_);
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
lean_inc(v___x_1228_);
v___x_1230_ = l_Lean_Syntax_isOfKind(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v___x_1228_);
lean_dec(v_t_1212_);
v___y_1187_ = v_a_1118_;
v___y_1188_ = v_a_1119_;
v___y_1189_ = v_a_1120_;
v___y_1190_ = v_a_1121_;
v___y_1191_ = v_a_1122_;
v___y_1192_ = v_a_1123_;
v___y_1193_ = v_a_1124_;
v___y_1194_ = v_a_1125_;
goto v___jp_1186_;
}
else
{
lean_object* v_loc_1231_; lean_object* v___x_1232_; 
v_loc_1231_ = l_Lean_Syntax_getArg(v___x_1228_, v___x_1208_);
lean_dec(v___x_1228_);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_loc_1231_);
v___y_1214_ = v_a_1122_;
v___y_1215_ = v_a_1119_;
v___y_1216_ = v_a_1120_;
v___y_1217_ = v_a_1123_;
v___y_1218_ = v_a_1118_;
v___y_1219_ = v_a_1124_;
v___y_1220_ = v_a_1121_;
v___y_1221_ = v_a_1125_;
v___y_1222_ = v___x_1232_;
goto v___jp_1213_;
}
}
}
else
{
lean_object* v___x_1233_; 
lean_dec(v___x_1225_);
v___x_1233_ = lean_box(0);
v___y_1214_ = v_a_1122_;
v___y_1215_ = v_a_1119_;
v___y_1216_ = v_a_1120_;
v___y_1217_ = v_a_1123_;
v___y_1218_ = v_a_1118_;
v___y_1219_ = v_a_1124_;
v___y_1220_ = v_a_1121_;
v___y_1221_ = v_a_1125_;
v___y_1222_ = v___x_1233_;
goto v___jp_1213_;
}
v___jp_1213_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_1212_, v___y_1222_, v___y_1218_, v___y_1215_, v___y_1216_, v___y_1220_, v___y_1214_, v___y_1217_, v___y_1219_, v___y_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_dec_ref_known(v___x_1223_, 1);
v___y_1187_ = v___y_1218_;
v___y_1188_ = v___y_1215_;
v___y_1189_ = v___y_1216_;
v___y_1190_ = v___y_1220_;
v___y_1191_ = v___y_1214_;
v___y_1192_ = v___y_1217_;
v___y_1193_ = v___y_1219_;
v___y_1194_ = v___y_1221_;
goto v___jp_1186_;
}
else
{
lean_dec(v_stx_1117_);
return v___x_1223_;
}
}
}
}
v___jp_1129_:
{
if (v___y_1132_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v___y_1130_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_array_get(v___x_1128_, v___y_1131_, v___x_1141_);
lean_dec_ref(v___y_1131_);
v___x_1143_ = l_Lean_Elab_Tactic_getFVarId(v___x_1142_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___f_1145_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1145_, 0, v_a_1144_);
v___x_1146_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1145_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1146_;
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1143_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1143_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v___y_1131_);
v___x_1155_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1130_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1155_;
}
}
v___jp_1156_:
{
lean_object* v___x_1169_; 
lean_dec_ref(v___y_1157_);
v___x_1169_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v___y_1166_, v___y_1165_, v___y_1162_, v___y_1164_, v___y_1161_, v___y_1167_, v___y_1158_);
lean_dec(v___y_1166_);
return v___x_1169_;
}
v___jp_1170_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_array_get_size(v___y_1171_);
v___x_1185_ = lean_nat_dec_lt(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_dec(v___y_1180_);
v___y_1130_ = v___y_1173_;
v___y_1131_ = v___y_1171_;
v___y_1132_ = v___y_1172_;
v___y_1133_ = v___y_1182_;
v___y_1134_ = v___y_1175_;
v___y_1135_ = v___y_1179_;
v___y_1136_ = v___y_1177_;
v___y_1137_ = v___y_1178_;
v___y_1138_ = v___y_1176_;
v___y_1139_ = v___y_1181_;
v___y_1140_ = v___y_1174_;
goto v___jp_1129_;
}
else
{
v___y_1157_ = v___y_1173_;
v___y_1158_ = v___y_1174_;
v___y_1159_ = v___y_1175_;
v___y_1160_ = v___y_1177_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1171_;
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1178_;
v___y_1165_ = v___y_1172_;
v___y_1166_ = v___y_1180_;
v___y_1167_ = v___y_1181_;
v___y_1168_ = v___y_1182_;
goto v___jp_1156_;
}
}
v___jp_1186_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v_loc_1197_; 
v___x_1195_ = lean_unsigned_to_nat(2u);
v___x_1196_ = l_Lean_Syntax_getArg(v_stx_1117_, v___x_1195_);
lean_dec(v_stx_1117_);
v_loc_1197_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1196_);
if (lean_obj_tag(v_loc_1197_) == 0)
{
lean_object* v___x_1198_; 
lean_dec(v___x_1196_);
v___x_1198_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1127_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1198_;
}
else
{
lean_object* v_hypotheses_1199_; uint8_t v_type_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_hypotheses_1199_ = lean_ctor_get(v_loc_1197_, 0);
lean_inc_ref(v_hypotheses_1199_);
v_type_1200_ = lean_ctor_get_uint8(v_loc_1197_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_1197_, 1);
v___x_1201_ = lean_box(v_type_1200_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1202_, 0, v___x_1201_);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_hypotheses_1199_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
v___y_1171_ = v_hypotheses_1199_;
v___y_1172_ = v_type_1200_;
v___y_1173_ = v___f_1202_;
v___y_1174_ = v___y_1194_;
v___y_1175_ = v___y_1188_;
v___y_1176_ = v___y_1192_;
v___y_1177_ = v___y_1190_;
v___y_1178_ = v___y_1191_;
v___y_1179_ = v___y_1189_;
v___y_1180_ = v___x_1196_;
v___y_1181_ = v___y_1193_;
v___y_1182_ = v___y_1187_;
goto v___jp_1170_;
}
else
{
if (v_type_1200_ == 0)
{
v___y_1171_ = v_hypotheses_1199_;
v___y_1172_ = v_type_1200_;
v___y_1173_ = v___f_1202_;
v___y_1174_ = v___y_1194_;
v___y_1175_ = v___y_1188_;
v___y_1176_ = v___y_1192_;
v___y_1177_ = v___y_1190_;
v___y_1178_ = v___y_1191_;
v___y_1179_ = v___y_1189_;
v___y_1180_ = v___x_1196_;
v___y_1181_ = v___y_1193_;
v___y_1182_ = v___y_1187_;
goto v___jp_1170_;
}
else
{
v___y_1157_ = v___f_1202_;
v___y_1158_ = v___y_1194_;
v___y_1159_ = v___y_1188_;
v___y_1160_ = v___y_1190_;
v___y_1161_ = v___y_1192_;
v___y_1162_ = v_hypotheses_1199_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1191_;
v___y_1165_ = v_type_1200_;
v___y_1166_ = v___x_1196_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1187_;
goto v___jp_1156_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalSplit_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1117_ = stack[0].m_obj;
lean_object* v_a_1118_ = stack[1].m_obj;
lean_object* v_a_1119_ = stack[2].m_obj;
lean_object* v_a_1120_ = stack[3].m_obj;
lean_object* v_a_1121_ = stack[4].m_obj;
lean_object* v_a_1122_ = stack[5].m_obj;
lean_object* v_a_1123_ = stack[6].m_obj;
lean_object* v_a_1124_ = stack[7].m_obj;
lean_object* v_a_1125_ = stack[8].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_Elab_Tactic_evalSplit(v_stx_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object* v_stx_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_Tactic_evalSplit(v_stx_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1245_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1(){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1254_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1257_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___boxed), 10, 0);
v___x_1258_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1254_, v___x_1255_, v___x_1256_, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1259_;
v_res_1259_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___boxed(lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
return v_res_1261_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3(){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6));
v___x_1290_ = l_Lean_addBuiltinDeclarationRanges(v___x_1288_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1291_;
v_res_1291_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
stack->m_obj
 = v_res_1291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
return v_res_1293_;
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
