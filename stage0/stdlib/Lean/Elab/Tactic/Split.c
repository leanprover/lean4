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
lean_object* v___x_106_; lean_object* v_env_107_; lean_object* v___x_108_; lean_object* v_toCold_109_; lean_object* v_mctx_110_; lean_object* v_lctx_111_; lean_object* v_options_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = lean_st_ref_get(v___y_102_);
v_toCold_109_ = lean_ctor_get(v___y_103_, 0);
v_mctx_110_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_mctx_110_);
lean_dec(v___x_108_);
v_lctx_111_ = lean_ctor_get(v___y_101_, 2);
v_options_112_ = lean_ctor_get(v_toCold_109_, 2);
lean_inc_ref(v_options_112_);
lean_inc_ref(v_lctx_111_);
v___x_113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_113_, 0, v_env_107_);
lean_ctor_set(v___x_113_, 1, v_mctx_110_);
lean_ctor_set(v___x_113_, 2, v_lctx_111_);
lean_ctor_set(v___x_113_, 3, v_options_112_);
v___x_114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_msgData_100_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 2);
v___x_130_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
lean_inc(v_ref_129_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_ref_129_);
lean_ctor_set(v___x_135_, 1, v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 1);
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg___boxed(lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(lean_object* v_ref_147_, lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_toCold_158_; lean_object* v_currRecDepth_159_; lean_object* v_ref_160_; uint16_t v_optionFlags_161_; uint8_t v_suppressElabErrors_162_; uint8_t v_isRecordingDeps_163_; lean_object* v_ref_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_toCold_158_ = lean_ctor_get(v___y_155_, 0);
v_currRecDepth_159_ = lean_ctor_get(v___y_155_, 1);
v_ref_160_ = lean_ctor_get(v___y_155_, 2);
v_optionFlags_161_ = lean_ctor_get_uint16(v___y_155_, sizeof(void*)*3);
v_suppressElabErrors_162_ = lean_ctor_get_uint8(v___y_155_, sizeof(void*)*3 + 2);
v_isRecordingDeps_163_ = lean_ctor_get_uint8(v___y_155_, sizeof(void*)*3 + 3);
v_ref_164_ = l_Lean_replaceRef(v_ref_147_, v_ref_160_);
lean_inc(v_currRecDepth_159_);
lean_inc_ref(v_toCold_158_);
v___x_165_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_165_, 0, v_toCold_158_);
lean_ctor_set(v___x_165_, 1, v_currRecDepth_159_);
lean_ctor_set(v___x_165_, 2, v_ref_164_);
lean_ctor_set_uint16(v___x_165_, sizeof(void*)*3, v_optionFlags_161_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*3 + 2, v_suppressElabErrors_162_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*3 + 3, v_isRecordingDeps_163_);
v___x_166_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_148_, v___y_153_, v___y_154_, v___x_165_, v___y_156_);
lean_dec_ref_known(v___x_165_, 3);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(lean_object* v_ref_167_, lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_167_, v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v_ref_167_);
return v_res_178_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Array_mkArray0___redArg();
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(uint8_t v___x_216_, lean_object* v_t_217_, lean_object* v_error_218_, lean_object* v_loc_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
if (v___x_216_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_217_, v_error_218_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_229_;
}
else
{
lean_object* v_lctx_230_; lean_object* v_name_231_; uint8_t v___x_285_; 
v_lctx_230_ = lean_ctor_get(v___y_224_, 2);
v_name_231_ = l_Lean_Syntax_getId(v_t_217_);
v___x_285_ = l_Lean_Name_isStr(v_name_231_);
if (v___x_285_ == 0)
{
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v_name_231_);
v___x_286_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_217_, v_error_218_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_286_;
}
else
{
goto v___jp_232_;
}
}
else
{
if (lean_obj_tag(v_loc_219_) == 0)
{
goto v___jp_232_;
}
else
{
lean_object* v___x_287_; 
lean_dec(v_name_231_);
v___x_287_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_217_, v_error_218_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_287_;
}
}
v___jp_232_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_230_, v_name_231_);
if (lean_obj_tag(v___x_233_) == 1)
{
lean_object* v_val_234_; lean_object* v_ref_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_val_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_233_, 1);
v_ref_235_ = lean_ctor_get(v___y_226_, 2);
v___x_236_ = l_Lean_LocalDecl_toExpr(v_val_234_);
v___x_237_ = 0;
v___x_238_ = l_Lean_SourceInfo_fromRef(v_ref_235_, v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1));
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1));
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc_n(v___x_238_, 7);
v___x_242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_238_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
v___x_243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7));
v___x_244_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8);
v___x_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_238_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11));
v___x_248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_238_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13));
v___x_250_ = l_Lean_mkIdent(v_name_231_);
v___x_251_ = l_Lean_Syntax_node1(v___x_238_, v___x_243_, v___x_250_);
v___x_252_ = l_Lean_Syntax_node1(v___x_238_, v___x_249_, v___x_251_);
v___x_253_ = l_Lean_Syntax_node2(v___x_238_, v___x_246_, v___x_248_, v___x_252_);
v___x_254_ = l_Lean_Syntax_node1(v___x_238_, v___x_243_, v___x_253_);
v___x_255_ = l_Lean_Syntax_node3(v___x_238_, v___x_241_, v___x_242_, v___x_245_, v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15);
v___x_257_ = l_Lean_MessageData_ofExpr(v___x_236_);
lean_inc_ref(v___x_257_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_257_);
v___x_262_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_239_);
lean_ctor_set(v___x_264_, 1, v___x_255_);
v___x_265_ = lean_box(0);
v___x_266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
lean_ctor_set(v___x_266_, 4, v___x_265_);
lean_ctor_set(v___x_266_, 5, v___x_265_);
v___x_267_ = 0;
v___x_268_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_265_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*3, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_mk_empty_array_with_capacity(v___x_269_);
v___x_271_ = lean_array_push(v___x_270_, v___x_268_);
v___x_272_ = l_Lean_MessageData_hint(v___x_263_, v___x_271_, v___x_265_, v___x_265_, v___x_237_, v___y_226_, v___y_227_);
lean_dec_ref(v___x_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v_error_218_);
lean_ctor_set(v___x_274_, 1, v_a_273_);
v___x_275_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_217_, v___x_274_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_275_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_error_218_);
v_a_276_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_272_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v___x_284_; 
lean_dec(v___x_233_);
lean_dec(v_name_231_);
v___x_284_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_217_, v_error_218_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed(lean_object* v___x_288_, lean_object* v_t_289_, lean_object* v_error_290_, lean_object* v_loc_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_6162__boxed_301_; lean_object* v_res_302_; 
v___x_6162__boxed_301_ = lean_unbox(v___x_288_);
v_res_302_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_6162__boxed_301_, v_t_289_, v_error_290_, v_loc_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v_loc_291_);
lean_dec(v_t_289_);
return v_res_302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1(void){
_start:
{
lean_object* v___x_304_; lean_object* v_error_305_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0));
v_error_305_ = l_Lean_stringToMessageData(v___x_304_);
return v_error_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(lean_object* v_t_306_, lean_object* v_loc_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_error_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___y_320_; lean_object* v___x_321_; 
v_error_317_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1);
v___x_318_ = l_Lean_Syntax_isIdent(v_t_306_);
v___x_319_ = lean_box(v___x_318_);
v___y_320_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed), 13, 4);
lean_closure_set(v___y_320_, 0, v___x_319_);
lean_closure_set(v___y_320_, 1, v_t_306_);
lean_closure_set(v___y_320_, 2, v_error_317_);
lean_closure_set(v___y_320_, 3, v_loc_307_);
v___x_321_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_320_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___boxed(lean_object* v_t_322_, lean_object* v_loc_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_322_, v_loc_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(lean_object* v_00_u03b1_334_, lean_object* v_ref_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_335_, v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(lean_object* v_00_u03b1_347_, lean_object* v_ref_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(v_00_u03b1_347_, v_ref_348_, v_msg_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v_ref_348_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(lean_object* v_00_u03b1_360_, lean_object* v_msg_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_361_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(lean_object* v_00_u03b1_372_, lean_object* v_msg_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(v_00_u03b1_372_, v_msg_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_383_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v___x_389_; 
v___x_389_ = l_List_reverse___redArg(v_a_388_);
return v___x_389_;
}
else
{
lean_object* v_head_390_; lean_object* v_tail_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_403_; 
v_head_390_ = lean_ctor_get(v_a_387_, 0);
v_tail_391_ = lean_ctor_get(v_a_387_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_403_ == 0)
{
v___x_393_ = v_a_387_;
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_tail_391_);
lean_inc(v_head_390_);
lean_dec(v_a_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_395_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_396_ = l_Lean_MessageData_ofSyntax(v_head_390_);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_395_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_a_388_);
lean_ctor_set(v___x_393_, 0, v___x_398_);
v___x_400_ = v___x_393_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_a_388_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
v_a_387_ = v_tail_391_;
v_a_388_ = v___x_400_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_ref_410_; lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_ref_410_ = lean_ctor_get(v___y_407_, 2);
v___x_411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_ref_410_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_410_);
lean_ctor_set(v___x_416_, 1, v_a_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg___boxed(lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(lean_object* v_ref_428_, lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_toCold_435_; lean_object* v_currRecDepth_436_; lean_object* v_ref_437_; uint16_t v_optionFlags_438_; uint8_t v_suppressElabErrors_439_; uint8_t v_isRecordingDeps_440_; lean_object* v_ref_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_toCold_435_ = lean_ctor_get(v___y_432_, 0);
v_currRecDepth_436_ = lean_ctor_get(v___y_432_, 1);
v_ref_437_ = lean_ctor_get(v___y_432_, 2);
v_optionFlags_438_ = lean_ctor_get_uint16(v___y_432_, sizeof(void*)*3);
v_suppressElabErrors_439_ = lean_ctor_get_uint8(v___y_432_, sizeof(void*)*3 + 2);
v_isRecordingDeps_440_ = lean_ctor_get_uint8(v___y_432_, sizeof(void*)*3 + 3);
v_ref_441_ = l_Lean_replaceRef(v_ref_428_, v_ref_437_);
lean_inc(v_currRecDepth_436_);
lean_inc_ref(v_toCold_435_);
v___x_442_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_442_, 0, v_toCold_435_);
lean_ctor_set(v___x_442_, 1, v_currRecDepth_436_);
lean_ctor_set(v___x_442_, 2, v_ref_441_);
lean_ctor_set_uint16(v___x_442_, sizeof(void*)*3, v_optionFlags_438_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*3 + 2, v_suppressElabErrors_439_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*3 + 3, v_isRecordingDeps_440_);
v___x_443_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_429_, v___y_430_, v___y_431_, v___x_442_, v___y_433_);
lean_dec_ref_known(v___x_442_, 3);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(lean_object* v_ref_444_, lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_444_, v_msg_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v_ref_444_);
return v_res_451_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5);
v___x_462_ = l_Lean_MessageData_hint_x27(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(lean_object* v_stx_471_, uint8_t v_simplifyTarget_472_, lean_object* v_hyps_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_498_; 
if (v_simplifyTarget_472_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11));
v___y_498_ = v___x_504_;
goto v___jp_497_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12));
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
v___jp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_hypsStr_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_482_ = lean_array_to_list(v_hyps_473_);
v___x_483_ = lean_box(0);
v___x_484_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(v___x_482_, v___x_483_);
v___x_485_ = l_Lean_MessageData_andList(v___x_484_);
lean_inc_ref(v___y_481_);
v_hypsStr_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hypsStr_486_, 0, v___y_481_);
lean_ctor_set(v_hypsStr_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1);
lean_inc_ref(v___y_480_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___y_480_);
v___x_489_ = l_Lean_MessageData_ofFormat(v___x_488_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_hypsStr_486_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_487_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_stx_471_, v___x_495_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_496_;
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_array_get_size(v_hyps_473_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8);
v___y_480_ = v___y_498_;
v___y_481_ = v___x_502_;
goto v___jp_479_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10);
v___y_480_ = v___y_498_;
v___y_481_ = v___x_503_;
goto v___jp_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___boxed(lean_object* v_stx_506_, lean_object* v_simplifyTarget_507_, lean_object* v_hyps_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
uint8_t v_simplifyTarget_boxed_514_; lean_object* v_res_515_; 
v_simplifyTarget_boxed_514_ = lean_unbox(v_simplifyTarget_507_);
v_res_515_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_506_, v_simplifyTarget_boxed_514_, v_hyps_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_stx_506_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(lean_object* v_stx_516_, uint8_t v_simplifyTarget_517_, lean_object* v_hyps_518_, lean_object* v_00_u03b1_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_516_, v_simplifyTarget_517_, v_hyps_518_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(lean_object* v_stx_526_, lean_object* v_simplifyTarget_527_, lean_object* v_hyps_528_, lean_object* v_00_u03b1_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
uint8_t v_simplifyTarget_boxed_535_; lean_object* v_res_536_; 
v_simplifyTarget_boxed_535_ = lean_unbox(v_simplifyTarget_527_);
v_res_536_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(v_stx_526_, v_simplifyTarget_boxed_535_, v_hyps_528_, v_00_u03b1_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_stx_526_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(lean_object* v_00_u03b1_537_, lean_object* v_ref_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_538_, v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(lean_object* v_00_u03b1_546_, lean_object* v_ref_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(v_00_u03b1_546_, v_ref_547_, v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v_ref_547_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(lean_object* v_00_u03b1_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_563_, lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(v_00_u03b1_563_, v_msg_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_570_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(lean_object* v_type_586_, lean_object* v___x_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_val_594_; uint8_t v_a_603_; lean_object* v___x_613_; 
v___x_613_ = l_Lean_Expr_getAppFn(v___x_587_);
if (lean_obj_tag(v___x_613_) == 4)
{
lean_object* v_declName_614_; lean_object* v___x_615_; lean_object* v_env_616_; uint8_t v___x_617_; 
v_declName_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_n(v_declName_614_, 2);
lean_dec_ref_known(v___x_613_, 2);
v___x_615_ = lean_st_ref_get(v___y_591_);
v_env_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc_ref_n(v_env_616_, 2);
lean_dec(v___x_615_);
v___x_617_ = l_Lean_isStructure(v_env_616_, v_declName_614_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_env_616_);
lean_dec(v_declName_614_);
v_a_603_ = v___x_617_;
goto v___jp_602_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Lean_getStructureFields(v_env_616_, v_declName_614_);
v___x_620_ = lean_array_get_size(v___x_619_);
lean_dec_ref(v___x_619_);
v___x_621_ = lean_nat_dec_lt(v___x_618_, v___x_620_);
v_a_603_ = v___x_621_;
goto v___jp_602_;
}
}
else
{
uint8_t v___x_622_; 
lean_dec_ref(v___x_613_);
v___x_622_ = 0;
v_a_603_ = v___x_622_;
goto v___jp_602_;
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1);
lean_inc_ref(v_val_594_);
v___x_596_ = l_Lean_stringToMessageData(v_val_594_);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = l_Lean_MessageData_hint_x27(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
v___jp_602_:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5));
v___x_605_ = l_Lean_Expr_isAppOf(v_type_586_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7));
v___x_607_ = l_Lean_Expr_isAppOf(v_type_586_, v___x_606_);
if (v___x_607_ == 0)
{
if (v_a_603_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = l_Lean_MessageData_nil;
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8));
v_val_594_ = v___x_610_;
goto v___jp_593_;
}
}
else
{
lean_object* v___x_611_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9));
v_val_594_ = v___x_611_;
goto v___jp_593_;
}
}
else
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10));
v_val_594_ = v___x_612_;
goto v___jp_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed(lean_object* v_type_623_, lean_object* v___x_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(v_type_623_, v___x_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v___x_624_);
lean_dec_ref(v_type_623_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(lean_object* v_type_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_632_ = l_Lean_Expr_getAppFn(v_type_631_);
v___f_633_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_633_, 0, v_type_631_);
lean_closure_set(v___f_633_, 1, v___x_632_);
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5));
v___x_635_ = l_Lean_MessageData_ofLazyM(v___f_633_, v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(lean_object* v_mvarId_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; 
lean_inc(v_mvarId_641_);
v___x_647_ = l_Lean_MVarId_getType(v_mvarId_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_648_);
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_649_);
v___x_653_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = l_Lean_Meta_throwTacticEx___redArg(v___x_650_, v_mvarId_641_, v___x_655_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_656_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_mvarId_641_);
v_a_657_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_647_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_647_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___boxed(lean_object* v_mvarId_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_mvarId_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
return v_res_671_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(lean_object* v_fvarId_678_, lean_object* v_mvarId_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v___x_685_; 
lean_inc(v_fvarId_678_);
v___x_685_ = l_Lean_FVarId_getType___redArg(v_fvarId_678_, v_a_680_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_n(v_a_686_, 2);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_688_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1);
v___x_689_ = lean_unsigned_to_nat(30u);
v___x_690_ = l_Lean_inlineExpr(v_a_686_, v___x_689_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_688_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_Expr_fvar___override(v_fvarId_678_);
v___x_695_ = l_Lean_MessageData_ofExpr(v___x_694_);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_693_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_686_);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = l_Lean_Meta_throwTacticEx___redArg(v___x_687_, v_mvarId_679_, v___x_703_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
return v___x_704_;
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_mvarId_679_);
lean_dec(v_fvarId_678_);
v_a_705_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_685_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_685_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___boxed(lean_object* v_fvarId_713_, lean_object* v_mvarId_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_fvarId_713_, v_mvarId_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
if (lean_obj_tag(v_a_721_) == 0)
{
lean_object* v___x_723_; 
v___x_723_ = l_List_reverse___redArg(v_a_722_);
return v___x_723_;
}
else
{
lean_object* v_head_724_; lean_object* v_tail_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_738_; 
v_head_724_ = lean_ctor_get(v_a_721_, 0);
v_tail_725_ = lean_ctor_get(v_a_721_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_721_);
if (v_isSharedCheck_738_ == 0)
{
v___x_727_ = v_a_721_;
v_isShared_728_ = v_isSharedCheck_738_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_tail_725_);
lean_inc(v_head_724_);
lean_dec(v_a_721_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_738_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_729_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_730_ = l_Lean_Expr_fvar___override(v_head_724_);
v___x_731_ = l_Lean_MessageData_ofExpr(v___x_730_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_729_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_a_722_);
lean_ctor_set(v___x_727_, 0, v___x_733_);
v___x_735_ = v___x_727_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_722_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v_a_721_ = v_tail_725_;
v_a_722_ = v___x_735_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1));
v___x_743_ = l_Lean_MessageData_ofFormat(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v_note_745_; 
v___x_744_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2);
v_note_745_ = l_Lean_MessageData_note(v___x_744_);
return v_note_745_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6(void){
_start:
{
lean_object* v_note_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_note_749_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_750_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v_note_749_);
return v___x_751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_753_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10));
v___x_761_ = l_Lean_MessageData_ofFormat(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(lean_object* v_fvarIds_765_, lean_object* v_mvarId_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_note_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_note_772_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_fvarIds_765_);
v___x_775_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_fvarIds_765_);
v___x_776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8);
v___x_778_ = l_Lean_Meta_throwTacticEx___redArg(v___x_776_, v_mvarId_766_, v___x_777_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_fvarMsgs_781_; lean_object* v___x_782_; lean_object* v_fvarMsgs_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_779_ = lean_array_to_list(v_fvarIds_765_);
v___x_780_ = lean_box(0);
v_fvarMsgs_781_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(v___x_779_, v___x_780_);
v___x_782_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11);
v_fvarMsgs_783_ = l_Lean_MessageData_joinSep(v_fvarMsgs_781_, v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_fvarMsgs_783_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v_note_772_);
v___x_788_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = l_Lean_Meta_throwTacticEx___redArg(v___x_784_, v_mvarId_766_, v___x_790_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___boxed(lean_object* v_fvarIds_792_, lean_object* v_mvarId_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_792_, v_mvarId_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(lean_object* v_00_u03b1_800_, lean_object* v_fvarIds_801_, lean_object* v_mvarId_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_801_, v_mvarId_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(lean_object* v_00_u03b1_809_, lean_object* v_fvarIds_810_, lean_object* v_mvarId_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(v_00_u03b1_809_, v_fvarIds_810_, v_mvarId_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(lean_object* v_a_821_, lean_object* v_as_822_, size_t v_sz_823_, size_t v_i_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_824_, v_sz_823_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_a_821_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_b_825_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_a_835_; lean_object* v___x_836_; 
lean_dec_ref(v_b_825_);
v___x_833_ = lean_box(0);
v___x_834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_a_835_ = lean_array_uget_borrowed(v_as_822_, v_i_824_);
lean_inc(v_a_835_);
lean_inc(v_a_821_);
v___x_836_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_821_, v_a_835_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_848_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_848_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
if (lean_obj_tag(v_a_837_) == 1)
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec(v_a_821_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_a_837_);
lean_ctor_set(v___x_841_, 1, v___x_833_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
size_t v___x_845_; size_t v___x_846_; 
lean_del_object(v___x_839_);
lean_dec(v_a_837_);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_824_, v___x_845_);
v_i_824_ = v___x_846_;
v_b_825_ = v___x_834_;
goto _start;
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_a_821_);
v_a_849_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_836_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_836_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___boxed(lean_object* v_a_857_, lean_object* v_as_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_868_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_857_, v_as_858_, v_sz_boxed_867_, v_i_boxed_868_, v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_as_858_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0(lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_a_880_; lean_object* v___x_891_; 
v___x_891_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_871_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_n(v_a_892_, 2);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = l_Lean_MVarId_getNondepPropHyps(v_a_892_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; size_t v_sz_896_; size_t v___x_897_; lean_object* v___x_898_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v___x_895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_sz_896_ = lean_array_size(v_a_894_);
v___x_897_ = ((size_t)0ULL);
lean_inc(v_a_892_);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_892_, v_a_894_, v_sz_896_, v___x_897_, v___x_895_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v_fst_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v_fst_900_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_fst_900_);
lean_dec(v_a_899_);
if (lean_obj_tag(v_fst_900_) == 0)
{
uint8_t v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; 
v___x_901_ = 1;
v___x_902_ = 0;
lean_inc(v_a_892_);
v___x_903_ = l_Lean_Meta_splitTarget_x3f(v_a_892_, v___x_901_, v___x_902_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
if (lean_obj_tag(v_a_904_) == 1)
{
lean_object* v_val_905_; 
lean_dec(v_a_894_);
lean_dec(v_a_892_);
v_val_905_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v_a_904_, 1);
v_a_880_ = v_val_905_;
goto v___jp_879_;
}
else
{
lean_object* v___x_906_; 
lean_dec(v_a_904_);
v___x_906_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_a_894_, v_a_892_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v_a_880_ = v_a_907_;
goto v___jp_879_;
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_906_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_906_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_894_);
lean_dec(v_a_892_);
v_a_916_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_903_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_903_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_val_924_; 
lean_dec(v_a_894_);
lean_dec(v_a_892_);
v_val_924_ = lean_ctor_get(v_fst_900_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_fst_900_, 1);
v_a_880_ = v_val_924_;
goto v___jp_879_;
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_a_894_);
lean_dec(v_a_892_);
v_a_925_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_898_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_898_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_892_);
v_a_933_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_893_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_893_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_891_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_891_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
v___jp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(0);
v___x_882_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_880_, v___y_871_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_890_);
v___x_884_ = v___x_882_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_dec(v___x_882_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_881_);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_881_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0___boxed(lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Elab_Tactic_evalSplit___lam__0(v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1(uint8_t v_type_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_a_970_; lean_object* v___x_981_; 
v___x_981_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_961_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; uint8_t v___x_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_n(v_a_982_, 2);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = 0;
v___x_984_ = l_Lean_Meta_splitTarget_x3f(v_a_982_, v_type_959_, v___x_983_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
if (lean_obj_tag(v_a_985_) == 1)
{
lean_object* v_val_986_; 
lean_dec(v_a_982_);
v_val_986_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v_a_985_, 1);
v_a_970_ = v_val_986_;
goto v___jp_969_;
}
else
{
lean_object* v___x_987_; 
lean_dec(v_a_985_);
v___x_987_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_a_982_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v_a_970_ = v_a_988_;
goto v___jp_969_;
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_987_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_987_);
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
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_a_982_);
v_a_997_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_984_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_984_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_981_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_981_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_box(0);
v___x_972_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_970_, v___y_961_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v___x_972_, 0);
lean_dec(v_unused_980_);
v___x_974_ = v___x_972_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_971_);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1___boxed(lean_object* v_type_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v_type_3687__boxed_1023_; lean_object* v_res_1024_; 
v_type_3687__boxed_1023_ = lean_unbox(v_type_1013_);
v_res_1024_ = l_Lean_Elab_Tactic_evalSplit___lam__1(v_type_3687__boxed_1023_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2(lean_object* v_a_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_a_1036_; lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1027_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc_n(v_a_1048_, 2);
lean_dec_ref_known(v___x_1047_, 1);
lean_inc(v_a_1025_);
v___x_1049_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_1048_, v_a_1025_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
if (lean_obj_tag(v_a_1050_) == 1)
{
lean_object* v_val_1051_; 
lean_dec(v_a_1048_);
lean_dec(v_a_1025_);
v_val_1051_ = lean_ctor_get(v_a_1050_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v_a_1050_, 1);
v_a_1036_ = v_val_1051_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1052_; 
lean_dec(v_a_1050_);
v___x_1052_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_a_1025_, v_a_1048_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v_a_1036_ = v_a_1053_;
goto v___jp_1035_;
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1052_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_a_1048_);
lean_dec(v_a_1025_);
v_a_1062_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1049_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1049_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_a_1025_);
v_a_1070_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1047_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1047_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_1036_, v___y_1027_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v___x_1038_, 0);
lean_dec(v_unused_1046_);
v___x_1040_ = v___x_1038_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_dec(v___x_1038_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1037_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2___boxed(lean_object* v_a_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Elab_Tactic_evalSplit___lam__2(v_a_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object* v_stx_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1144_; lean_object* v___y_1145_; uint8_t v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___f_1100_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSplit___closed__0));
v___x_1101_ = lean_box(0);
v___x_1179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc(v_stx_1090_);
v___x_1180_ = l_Lean_Syntax_isOfKind(v_stx_1090_, v___x_1179_);
if (v___x_1180_ == 0)
{
v___y_1160_ = v_a_1091_;
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = l_Lean_Syntax_getArg(v_stx_1090_, v___x_1181_);
lean_inc(v___x_1182_);
v___x_1183_ = l_Lean_Syntax_matchesNull(v___x_1182_, v___x_1181_);
if (v___x_1183_ == 0)
{
lean_dec(v___x_1182_);
v___y_1160_ = v_a_1091_;
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1184_; lean_object* v_t_1185_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1184_ = lean_unsigned_to_nat(0u);
v_t_1185_ = l_Lean_Syntax_getArg(v___x_1182_, v___x_1184_);
lean_dec(v___x_1182_);
v___x_1197_ = lean_unsigned_to_nat(2u);
v___x_1198_ = l_Lean_Syntax_getArg(v_stx_1090_, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_isNone(v___x_1198_);
if (v___x_1199_ == 0)
{
uint8_t v___x_1200_; 
lean_inc(v___x_1198_);
v___x_1200_ = l_Lean_Syntax_matchesNull(v___x_1198_, v___x_1181_);
if (v___x_1200_ == 0)
{
lean_dec(v___x_1198_);
lean_dec(v_t_1185_);
v___y_1160_ = v_a_1091_;
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = l_Lean_Syntax_getArg(v___x_1198_, v___x_1184_);
lean_dec(v___x_1198_);
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
lean_inc(v___x_1201_);
v___x_1203_ = l_Lean_Syntax_isOfKind(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_dec(v___x_1201_);
lean_dec(v_t_1185_);
v___y_1160_ = v_a_1091_;
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
goto v___jp_1159_;
}
else
{
lean_object* v_loc_1204_; lean_object* v___x_1205_; 
v_loc_1204_ = l_Lean_Syntax_getArg(v___x_1201_, v___x_1181_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_loc_1204_);
v___y_1187_ = v_a_1098_;
v___y_1188_ = v_a_1092_;
v___y_1189_ = v_a_1096_;
v___y_1190_ = v_a_1091_;
v___y_1191_ = v_a_1094_;
v___y_1192_ = v_a_1097_;
v___y_1193_ = v_a_1095_;
v___y_1194_ = v_a_1093_;
v___y_1195_ = v___x_1205_;
goto v___jp_1186_;
}
}
}
else
{
lean_object* v___x_1206_; 
lean_dec(v___x_1198_);
v___x_1206_ = lean_box(0);
v___y_1187_ = v_a_1098_;
v___y_1188_ = v_a_1092_;
v___y_1189_ = v_a_1096_;
v___y_1190_ = v_a_1091_;
v___y_1191_ = v_a_1094_;
v___y_1192_ = v_a_1097_;
v___y_1193_ = v_a_1095_;
v___y_1194_ = v_a_1093_;
v___y_1195_ = v___x_1206_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_1185_, v___y_1195_, v___y_1190_, v___y_1188_, v___y_1194_, v___y_1191_, v___y_1193_, v___y_1189_, v___y_1192_, v___y_1187_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_dec_ref_known(v___x_1196_, 1);
v___y_1160_ = v___y_1190_;
v___y_1161_ = v___y_1188_;
v___y_1162_ = v___y_1194_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1193_;
v___y_1165_ = v___y_1189_;
v___y_1166_ = v___y_1192_;
v___y_1167_ = v___y_1187_;
goto v___jp_1159_;
}
else
{
lean_dec(v_stx_1090_);
return v___x_1196_;
}
}
}
}
v___jp_1102_:
{
if (v___y_1105_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec_ref(v___y_1103_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_array_get(v___x_1101_, v___y_1104_, v___x_1114_);
lean_dec_ref(v___y_1104_);
v___x_1116_ = l_Lean_Elab_Tactic_getFVarId(v___x_1115_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1118_, 0, v_a_1117_);
v___x_1119_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1118_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1116_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1116_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___x_1128_; 
lean_dec_ref(v___y_1104_);
v___x_1128_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1103_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1128_;
}
}
v___jp_1129_:
{
lean_object* v___x_1142_; 
lean_dec_ref(v___y_1130_);
v___x_1142_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v___y_1139_, v___y_1141_, v___y_1131_, v___y_1134_, v___y_1137_, v___y_1140_, v___y_1133_);
lean_dec(v___y_1139_);
return v___x_1142_;
}
v___jp_1143_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_array_get_size(v___y_1144_);
v___x_1158_ = lean_nat_dec_lt(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec(v___y_1154_);
v___y_1103_ = v___y_1145_;
v___y_1104_ = v___y_1144_;
v___y_1105_ = v___y_1146_;
v___y_1106_ = v___y_1151_;
v___y_1107_ = v___y_1147_;
v___y_1108_ = v___y_1150_;
v___y_1109_ = v___y_1153_;
v___y_1110_ = v___y_1149_;
v___y_1111_ = v___y_1152_;
v___y_1112_ = v___y_1155_;
v___y_1113_ = v___y_1148_;
goto v___jp_1102_;
}
else
{
v___y_1130_ = v___y_1145_;
v___y_1131_ = v___y_1144_;
v___y_1132_ = v___y_1147_;
v___y_1133_ = v___y_1148_;
v___y_1134_ = v___y_1149_;
v___y_1135_ = v___y_1150_;
v___y_1136_ = v___y_1151_;
v___y_1137_ = v___y_1152_;
v___y_1138_ = v___y_1153_;
v___y_1139_ = v___y_1154_;
v___y_1140_ = v___y_1155_;
v___y_1141_ = v___y_1146_;
goto v___jp_1129_;
}
}
v___jp_1159_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_loc_1170_; 
v___x_1168_ = lean_unsigned_to_nat(2u);
v___x_1169_ = l_Lean_Syntax_getArg(v_stx_1090_, v___x_1168_);
lean_dec(v_stx_1090_);
v_loc_1170_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1169_);
if (lean_obj_tag(v_loc_1170_) == 0)
{
lean_object* v___x_1171_; 
lean_dec(v___x_1169_);
v___x_1171_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1100_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1171_;
}
else
{
lean_object* v_hypotheses_1172_; uint8_t v_type_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_hypotheses_1172_ = lean_ctor_get(v_loc_1170_, 0);
lean_inc_ref(v_hypotheses_1172_);
v_type_1173_ = lean_ctor_get_uint8(v_loc_1170_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_1170_, 1);
v___x_1174_ = lean_box(v_type_1173_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1175_, 0, v___x_1174_);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_array_get_size(v_hypotheses_1172_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
v___y_1144_ = v_hypotheses_1172_;
v___y_1145_ = v___f_1175_;
v___y_1146_ = v_type_1173_;
v___y_1147_ = v___y_1161_;
v___y_1148_ = v___y_1167_;
v___y_1149_ = v___y_1164_;
v___y_1150_ = v___y_1162_;
v___y_1151_ = v___y_1160_;
v___y_1152_ = v___y_1165_;
v___y_1153_ = v___y_1163_;
v___y_1154_ = v___x_1169_;
v___y_1155_ = v___y_1166_;
goto v___jp_1143_;
}
else
{
if (v_type_1173_ == 0)
{
v___y_1144_ = v_hypotheses_1172_;
v___y_1145_ = v___f_1175_;
v___y_1146_ = v_type_1173_;
v___y_1147_ = v___y_1161_;
v___y_1148_ = v___y_1167_;
v___y_1149_ = v___y_1164_;
v___y_1150_ = v___y_1162_;
v___y_1151_ = v___y_1160_;
v___y_1152_ = v___y_1165_;
v___y_1153_ = v___y_1163_;
v___y_1154_ = v___x_1169_;
v___y_1155_ = v___y_1166_;
goto v___jp_1143_;
}
else
{
v___y_1130_ = v___f_1175_;
v___y_1131_ = v_hypotheses_1172_;
v___y_1132_ = v___y_1161_;
v___y_1133_ = v___y_1167_;
v___y_1134_ = v___y_1164_;
v___y_1135_ = v___y_1162_;
v___y_1136_ = v___y_1160_;
v___y_1137_ = v___y_1165_;
v___y_1138_ = v___y_1163_;
v___y_1139_ = v___x_1169_;
v___y_1140_ = v___y_1166_;
v___y_1141_ = v_type_1173_;
goto v___jp_1129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object* v_stx_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Elab_Tactic_evalSplit(v_stx_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1(){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1226_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
v___x_1228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1229_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___boxed), 10, 0);
v___x_1230_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1226_, v___x_1227_, v___x_1228_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___boxed(lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3(){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6));
v___x_1261_ = l_Lean_addBuiltinDeclarationRanges(v___x_1259_, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
return v_res_1263_;
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
