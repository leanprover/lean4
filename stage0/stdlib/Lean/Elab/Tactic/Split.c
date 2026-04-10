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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
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
lean_object* v_options_5_; lean_object* v_map_6_; lean_object* v___x_7_; 
v_options_5_ = lean_ctor_get(v___y_3_, 2);
v_map_6_ = lean_ctor_get(v_options_5_, 0);
v___x_7_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6_, v_k_1_);
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
lean_dec_ref(v_val_10_);
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
uint8_t v___x_689__boxed_81_; lean_object* v_res_82_; 
v___x_689__boxed_81_ = lean_unbox(v___x_75_);
v_res_82_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(v___x_74_, v___x_689__boxed_81_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
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
lean_object* v___x_106_; lean_object* v_env_107_; lean_object* v___x_108_; lean_object* v_mctx_109_; lean_object* v_lctx_110_; lean_object* v_options_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = lean_st_ref_get(v___y_102_);
v_mctx_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_mctx_109_);
lean_dec(v___x_108_);
v_lctx_110_ = lean_ctor_get(v___y_101_, 2);
v_options_111_ = lean_ctor_get(v___y_103_, 2);
lean_inc_ref(v_options_111_);
lean_inc_ref(v_lctx_110_);
v___x_112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_112_, 0, v_env_107_);
lean_ctor_set(v___x_112_, 1, v_mctx_109_);
lean_ctor_set(v___x_112_, 2, v_lctx_110_);
lean_ctor_set(v___x_112_, 3, v_options_111_);
v___x_113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_msgData_100_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(lean_object* v_msg_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_ref_128_; lean_object* v___x_129_; lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_ref_128_ = lean_ctor_get(v___y_125_, 5);
v___x_129_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_138_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_inc(v_ref_128_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_ref_128_);
lean_ctor_set(v___x_134_, 1, v_a_130_);
if (v_isShared_133_ == 0)
{
lean_ctor_set_tag(v___x_132_, 1);
lean_ctor_set(v___x_132_, 0, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg___boxed(lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(lean_object* v_ref_146_, lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_fileName_157_; lean_object* v_fileMap_158_; lean_object* v_options_159_; lean_object* v_currRecDepth_160_; lean_object* v_maxRecDepth_161_; lean_object* v_ref_162_; lean_object* v_currNamespace_163_; lean_object* v_openDecls_164_; lean_object* v_initHeartbeats_165_; lean_object* v_maxHeartbeats_166_; lean_object* v_quotContext_167_; lean_object* v_currMacroScope_168_; uint8_t v_diag_169_; lean_object* v_cancelTk_x3f_170_; uint8_t v_suppressElabErrors_171_; lean_object* v_inheritedTraceOptions_172_; lean_object* v_ref_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_fileName_157_ = lean_ctor_get(v___y_154_, 0);
v_fileMap_158_ = lean_ctor_get(v___y_154_, 1);
v_options_159_ = lean_ctor_get(v___y_154_, 2);
v_currRecDepth_160_ = lean_ctor_get(v___y_154_, 3);
v_maxRecDepth_161_ = lean_ctor_get(v___y_154_, 4);
v_ref_162_ = lean_ctor_get(v___y_154_, 5);
v_currNamespace_163_ = lean_ctor_get(v___y_154_, 6);
v_openDecls_164_ = lean_ctor_get(v___y_154_, 7);
v_initHeartbeats_165_ = lean_ctor_get(v___y_154_, 8);
v_maxHeartbeats_166_ = lean_ctor_get(v___y_154_, 9);
v_quotContext_167_ = lean_ctor_get(v___y_154_, 10);
v_currMacroScope_168_ = lean_ctor_get(v___y_154_, 11);
v_diag_169_ = lean_ctor_get_uint8(v___y_154_, sizeof(void*)*14);
v_cancelTk_x3f_170_ = lean_ctor_get(v___y_154_, 12);
v_suppressElabErrors_171_ = lean_ctor_get_uint8(v___y_154_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_172_ = lean_ctor_get(v___y_154_, 13);
v_ref_173_ = l_Lean_replaceRef(v_ref_146_, v_ref_162_);
lean_inc_ref(v_inheritedTraceOptions_172_);
lean_inc(v_cancelTk_x3f_170_);
lean_inc(v_currMacroScope_168_);
lean_inc(v_quotContext_167_);
lean_inc(v_maxHeartbeats_166_);
lean_inc(v_initHeartbeats_165_);
lean_inc(v_openDecls_164_);
lean_inc(v_currNamespace_163_);
lean_inc(v_maxRecDepth_161_);
lean_inc(v_currRecDepth_160_);
lean_inc_ref(v_options_159_);
lean_inc_ref(v_fileMap_158_);
lean_inc_ref(v_fileName_157_);
v___x_174_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_174_, 0, v_fileName_157_);
lean_ctor_set(v___x_174_, 1, v_fileMap_158_);
lean_ctor_set(v___x_174_, 2, v_options_159_);
lean_ctor_set(v___x_174_, 3, v_currRecDepth_160_);
lean_ctor_set(v___x_174_, 4, v_maxRecDepth_161_);
lean_ctor_set(v___x_174_, 5, v_ref_173_);
lean_ctor_set(v___x_174_, 6, v_currNamespace_163_);
lean_ctor_set(v___x_174_, 7, v_openDecls_164_);
lean_ctor_set(v___x_174_, 8, v_initHeartbeats_165_);
lean_ctor_set(v___x_174_, 9, v_maxHeartbeats_166_);
lean_ctor_set(v___x_174_, 10, v_quotContext_167_);
lean_ctor_set(v___x_174_, 11, v_currMacroScope_168_);
lean_ctor_set(v___x_174_, 12, v_cancelTk_x3f_170_);
lean_ctor_set(v___x_174_, 13, v_inheritedTraceOptions_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*14, v_diag_169_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*14 + 1, v_suppressElabErrors_171_);
v___x_175_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_147_, v___y_152_, v___y_153_, v___x_174_, v___y_155_);
lean_dec_ref(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(lean_object* v_ref_176_, lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_176_, v_msg_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v_ref_176_);
return v_res_187_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Array_mkArray0(lean_box(0));
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14));
v___x_218_ = l_Lean_stringToMessageData(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16));
v___x_221_ = l_Lean_stringToMessageData(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(uint8_t v___x_225_, lean_object* v_t_226_, lean_object* v_error_227_, lean_object* v_loc_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
if (v___x_225_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_226_, v_error_227_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_238_;
}
else
{
lean_object* v_lctx_239_; lean_object* v_name_240_; uint8_t v___y_242_; uint8_t v___x_296_; 
v_lctx_239_ = lean_ctor_get(v___y_233_, 2);
v_name_240_ = l_Lean_Syntax_getId(v_t_226_);
v___x_296_ = l_Lean_Name_isStr(v_name_240_);
if (v___x_296_ == 0)
{
v___y_242_ = v___x_296_;
goto v___jp_241_;
}
else
{
if (lean_obj_tag(v_loc_228_) == 0)
{
v___y_242_ = v___x_296_;
goto v___jp_241_;
}
else
{
lean_object* v___x_297_; 
lean_dec(v_name_240_);
v___x_297_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_226_, v_error_227_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_297_;
}
}
v___jp_241_:
{
if (v___y_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v_name_240_);
v___x_243_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_226_, v_error_227_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_239_, v_name_240_);
if (lean_obj_tag(v___x_244_) == 1)
{
lean_object* v_val_245_; lean_object* v_ref_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_val_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_val_245_);
lean_dec_ref(v___x_244_);
v_ref_246_ = lean_ctor_get(v___y_235_, 5);
v___x_247_ = l_Lean_LocalDecl_toExpr(v_val_245_);
v___x_248_ = 0;
v___x_249_ = l_Lean_SourceInfo_fromRef(v_ref_246_, v___x_248_);
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1));
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1));
v___x_252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc_n(v___x_249_, 7);
v___x_253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_249_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
v___x_254_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7));
v___x_255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_249_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_255_);
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11));
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_249_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13));
v___x_261_ = lean_mk_syntax_ident(v_name_240_);
v___x_262_ = l_Lean_Syntax_node1(v___x_249_, v___x_254_, v___x_261_);
v___x_263_ = l_Lean_Syntax_node1(v___x_249_, v___x_260_, v___x_262_);
v___x_264_ = l_Lean_Syntax_node2(v___x_249_, v___x_257_, v___x_259_, v___x_263_);
v___x_265_ = l_Lean_Syntax_node1(v___x_249_, v___x_254_, v___x_264_);
v___x_266_ = l_Lean_Syntax_node3(v___x_249_, v___x_252_, v___x_253_, v___x_256_, v___x_265_);
v___x_267_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15);
v___x_268_ = l_Lean_MessageData_ofExpr(v___x_247_);
lean_inc_ref(v___x_268_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
v___x_273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_250_);
lean_ctor_set(v___x_275_, 1, v___x_266_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_ctor_set(v___x_277_, 3, v___x_276_);
lean_ctor_set(v___x_277_, 4, v___x_276_);
lean_ctor_set(v___x_277_, 5, v___x_276_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_276_);
lean_ctor_set(v___x_279_, 2, v___x_276_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*3, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_280_);
v___x_282_ = lean_array_push(v___x_281_, v___x_279_);
v___x_283_ = l_Lean_MessageData_hint(v___x_274_, v___x_282_, v___x_276_, v___x_276_, v___x_248_, v___y_235_, v___y_236_);
lean_dec_ref(v___x_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v_error_227_);
lean_ctor_set(v___x_285_, 1, v_a_284_);
v___x_286_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_226_, v___x_285_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_286_;
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_error_227_);
v_a_287_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_283_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_295_; 
lean_dec(v___x_244_);
lean_dec(v_name_240_);
v___x_295_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_226_, v_error_227_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed(lean_object* v___x_298_, lean_object* v_t_299_, lean_object* v_error_300_, lean_object* v_loc_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
uint8_t v___x_6767__boxed_311_; lean_object* v_res_312_; 
v___x_6767__boxed_311_ = lean_unbox(v___x_298_);
v_res_312_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_6767__boxed_311_, v_t_299_, v_error_300_, v_loc_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v_loc_301_);
lean_dec(v_t_299_);
return v_res_312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v_error_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0));
v_error_315_ = l_Lean_stringToMessageData(v___x_314_);
return v_error_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(lean_object* v_t_316_, lean_object* v_loc_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_error_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___y_330_; lean_object* v___x_331_; 
v_error_327_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1);
v___x_328_ = l_Lean_Syntax_isIdent(v_t_316_);
v___x_329_ = lean_box(v___x_328_);
v___y_330_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed), 13, 4);
lean_closure_set(v___y_330_, 0, v___x_329_);
lean_closure_set(v___y_330_, 1, v_t_316_);
lean_closure_set(v___y_330_, 2, v_error_327_);
lean_closure_set(v___y_330_, 3, v_loc_317_);
v___x_331_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_330_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_331_;
}
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(lean_object* v_00_u03b1_344_, lean_object* v_ref_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_345_, v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(lean_object* v_00_u03b1_357_, lean_object* v_ref_358_, lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(v_00_u03b1_357_, v_ref_358_, v_msg_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v_ref_358_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_371_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(v_00_u03b1_382_, v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_393_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
if (lean_obj_tag(v_a_397_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = l_List_reverse___redArg(v_a_398_);
return v___x_399_;
}
else
{
lean_object* v_head_400_; lean_object* v_tail_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_413_; 
v_head_400_ = lean_ctor_get(v_a_397_, 0);
v_tail_401_ = lean_ctor_get(v_a_397_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_a_397_);
if (v_isSharedCheck_413_ == 0)
{
v___x_403_ = v_a_397_;
v_isShared_404_ = v_isSharedCheck_413_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_tail_401_);
lean_inc(v_head_400_);
lean_dec(v_a_397_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_413_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_405_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_406_ = l_Lean_MessageData_ofSyntax(v_head_400_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_405_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_a_398_);
lean_ctor_set(v___x_403_, 0, v___x_408_);
v___x_410_ = v___x_403_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_398_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v_a_397_ = v_tail_401_;
v_a_398_ = v___x_410_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_ref_420_; lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_ref_420_ = lean_ctor_get(v___y_417_, 5);
v___x_421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_ref_420_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_ref_420_);
lean_ctor_set(v___x_426_, 1, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg___boxed(lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(lean_object* v_ref_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_fileName_445_; lean_object* v_fileMap_446_; lean_object* v_options_447_; lean_object* v_currRecDepth_448_; lean_object* v_maxRecDepth_449_; lean_object* v_ref_450_; lean_object* v_currNamespace_451_; lean_object* v_openDecls_452_; lean_object* v_initHeartbeats_453_; lean_object* v_maxHeartbeats_454_; lean_object* v_quotContext_455_; lean_object* v_currMacroScope_456_; uint8_t v_diag_457_; lean_object* v_cancelTk_x3f_458_; uint8_t v_suppressElabErrors_459_; lean_object* v_inheritedTraceOptions_460_; lean_object* v_ref_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_fileName_445_ = lean_ctor_get(v___y_442_, 0);
v_fileMap_446_ = lean_ctor_get(v___y_442_, 1);
v_options_447_ = lean_ctor_get(v___y_442_, 2);
v_currRecDepth_448_ = lean_ctor_get(v___y_442_, 3);
v_maxRecDepth_449_ = lean_ctor_get(v___y_442_, 4);
v_ref_450_ = lean_ctor_get(v___y_442_, 5);
v_currNamespace_451_ = lean_ctor_get(v___y_442_, 6);
v_openDecls_452_ = lean_ctor_get(v___y_442_, 7);
v_initHeartbeats_453_ = lean_ctor_get(v___y_442_, 8);
v_maxHeartbeats_454_ = lean_ctor_get(v___y_442_, 9);
v_quotContext_455_ = lean_ctor_get(v___y_442_, 10);
v_currMacroScope_456_ = lean_ctor_get(v___y_442_, 11);
v_diag_457_ = lean_ctor_get_uint8(v___y_442_, sizeof(void*)*14);
v_cancelTk_x3f_458_ = lean_ctor_get(v___y_442_, 12);
v_suppressElabErrors_459_ = lean_ctor_get_uint8(v___y_442_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_460_ = lean_ctor_get(v___y_442_, 13);
v_ref_461_ = l_Lean_replaceRef(v_ref_438_, v_ref_450_);
lean_inc_ref(v_inheritedTraceOptions_460_);
lean_inc(v_cancelTk_x3f_458_);
lean_inc(v_currMacroScope_456_);
lean_inc(v_quotContext_455_);
lean_inc(v_maxHeartbeats_454_);
lean_inc(v_initHeartbeats_453_);
lean_inc(v_openDecls_452_);
lean_inc(v_currNamespace_451_);
lean_inc(v_maxRecDepth_449_);
lean_inc(v_currRecDepth_448_);
lean_inc_ref(v_options_447_);
lean_inc_ref(v_fileMap_446_);
lean_inc_ref(v_fileName_445_);
v___x_462_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_462_, 0, v_fileName_445_);
lean_ctor_set(v___x_462_, 1, v_fileMap_446_);
lean_ctor_set(v___x_462_, 2, v_options_447_);
lean_ctor_set(v___x_462_, 3, v_currRecDepth_448_);
lean_ctor_set(v___x_462_, 4, v_maxRecDepth_449_);
lean_ctor_set(v___x_462_, 5, v_ref_461_);
lean_ctor_set(v___x_462_, 6, v_currNamespace_451_);
lean_ctor_set(v___x_462_, 7, v_openDecls_452_);
lean_ctor_set(v___x_462_, 8, v_initHeartbeats_453_);
lean_ctor_set(v___x_462_, 9, v_maxHeartbeats_454_);
lean_ctor_set(v___x_462_, 10, v_quotContext_455_);
lean_ctor_set(v___x_462_, 11, v_currMacroScope_456_);
lean_ctor_set(v___x_462_, 12, v_cancelTk_x3f_458_);
lean_ctor_set(v___x_462_, 13, v_inheritedTraceOptions_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*14, v_diag_457_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*14 + 1, v_suppressElabErrors_459_);
v___x_463_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_439_, v___y_440_, v___y_441_, v___x_462_, v___y_443_);
lean_dec_ref(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(lean_object* v_ref_464_, lean_object* v_msg_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_464_, v_msg_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v_ref_464_);
return v_res_471_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5);
v___x_482_ = l_Lean_MessageData_hint_x27(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(lean_object* v_stx_491_, uint8_t v_simplifyTarget_492_, lean_object* v_hyps_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_518_; 
if (v_simplifyTarget_492_ == 0)
{
lean_object* v___x_524_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11));
v___y_518_ = v___x_524_;
goto v___jp_517_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12));
v___y_518_ = v___x_525_;
goto v___jp_517_;
}
v___jp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_hypsStr_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_502_ = lean_array_to_list(v_hyps_493_);
v___x_503_ = lean_box(0);
v___x_504_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(v___x_502_, v___x_503_);
v___x_505_ = l_Lean_MessageData_andList(v___x_504_);
lean_inc_ref(v___y_501_);
v_hypsStr_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hypsStr_506_, 0, v___y_501_);
lean_ctor_set(v_hypsStr_506_, 1, v___x_505_);
v___x_507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1);
lean_inc_ref(v___y_500_);
v___x_508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_508_, 0, v___y_500_);
v___x_509_ = l_Lean_MessageData_ofFormat(v___x_508_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_hypsStr_506_);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_507_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_stx_491_, v___x_515_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_516_;
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_array_get_size(v_hyps_493_);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8);
v___y_500_ = v___y_518_;
v___y_501_ = v___x_522_;
goto v___jp_499_;
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10);
v___y_500_ = v___y_518_;
v___y_501_ = v___x_523_;
goto v___jp_499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___boxed(lean_object* v_stx_526_, lean_object* v_simplifyTarget_527_, lean_object* v_hyps_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
uint8_t v_simplifyTarget_boxed_534_; lean_object* v_res_535_; 
v_simplifyTarget_boxed_534_ = lean_unbox(v_simplifyTarget_527_);
v_res_535_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_526_, v_simplifyTarget_boxed_534_, v_hyps_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_stx_526_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(lean_object* v_stx_536_, uint8_t v_simplifyTarget_537_, lean_object* v_hyps_538_, lean_object* v_00_u03b1_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_536_, v_simplifyTarget_537_, v_hyps_538_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(lean_object* v_stx_546_, lean_object* v_simplifyTarget_547_, lean_object* v_hyps_548_, lean_object* v_00_u03b1_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
uint8_t v_simplifyTarget_boxed_555_; lean_object* v_res_556_; 
v_simplifyTarget_boxed_555_ = lean_unbox(v_simplifyTarget_547_);
v_res_556_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(v_stx_546_, v_simplifyTarget_boxed_555_, v_hyps_548_, v_00_u03b1_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_stx_546_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(lean_object* v_00_u03b1_557_, lean_object* v_ref_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_558_, v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(lean_object* v_00_u03b1_566_, lean_object* v_ref_567_, lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(v_00_u03b1_566_, v_ref_567_, v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_ref_567_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(lean_object* v_00_u03b1_575_, lean_object* v_msg_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_583_, lean_object* v_msg_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(v_00_u03b1_583_, v_msg_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_590_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2));
v___x_596_ = l_Lean_stringToMessageData(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(lean_object* v_type_606_, lean_object* v___x_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_val_614_; uint8_t v_a_623_; lean_object* v___x_633_; 
v___x_633_ = l_Lean_Expr_getAppFn(v___x_607_);
if (lean_obj_tag(v___x_633_) == 4)
{
lean_object* v_declName_634_; lean_object* v___x_635_; lean_object* v_env_636_; uint8_t v___x_637_; 
v_declName_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_n(v_declName_634_, 2);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_st_ref_get(v___y_611_);
v_env_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref_n(v_env_636_, 2);
lean_dec(v___x_635_);
v___x_637_ = l_Lean_isStructure(v_env_636_, v_declName_634_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_env_636_);
lean_dec(v_declName_634_);
v_a_623_ = v___x_637_;
goto v___jp_622_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Lean_getStructureFields(v_env_636_, v_declName_634_);
v___x_640_ = lean_array_get_size(v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = lean_nat_dec_lt(v___x_638_, v___x_640_);
v_a_623_ = v___x_641_;
goto v___jp_622_;
}
}
else
{
uint8_t v___x_642_; 
lean_dec_ref(v___x_633_);
v___x_642_ = 0;
v_a_623_ = v___x_642_;
goto v___jp_622_;
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_615_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1);
lean_inc_ref(v_val_614_);
v___x_616_ = l_Lean_stringToMessageData(v_val_614_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_MessageData_hint_x27(v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
v___jp_622_:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5));
v___x_625_ = l_Lean_Expr_isAppOf(v_type_606_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7));
v___x_627_ = l_Lean_Expr_isAppOf(v_type_606_, v___x_626_);
if (v___x_627_ == 0)
{
if (v_a_623_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = l_Lean_MessageData_nil;
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8));
v_val_614_ = v___x_630_;
goto v___jp_613_;
}
}
else
{
lean_object* v___x_631_; 
v___x_631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9));
v_val_614_ = v___x_631_;
goto v___jp_613_;
}
}
else
{
lean_object* v___x_632_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10));
v_val_614_ = v___x_632_;
goto v___jp_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed(lean_object* v_type_643_, lean_object* v___x_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(v_type_643_, v___x_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___x_644_);
lean_dec_ref(v_type_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(lean_object* v_type_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = l_Lean_Expr_getAppFn(v_type_651_);
v___f_653_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_653_, 0, v_type_651_);
lean_closure_set(v___f_653_, 1, v___x_652_);
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5));
v___x_655_ = l_Lean_MessageData_ofLazyM(v___f_653_, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(lean_object* v_mvarId_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; 
lean_inc(v_mvarId_661_);
v___x_667_ = l_Lean_MVarId_getType(v_mvarId_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_667_);
v___x_669_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_668_);
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_671_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_669_);
v___x_673_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v___x_676_ = l_Lean_Meta_throwTacticEx___redArg(v___x_670_, v_mvarId_661_, v___x_675_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
return v___x_676_;
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_mvarId_661_);
v_a_677_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_667_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_667_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(lean_object* v_fvarId_698_, lean_object* v_mvarId_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
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
lean_dec_ref(v___x_705_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___boxed(lean_object* v_fvarId_733_, lean_object* v_mvarId_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_fvarId_733_, v_mvarId_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
if (lean_obj_tag(v_a_741_) == 0)
{
lean_object* v___x_743_; 
v___x_743_ = l_List_reverse___redArg(v_a_742_);
return v___x_743_;
}
else
{
lean_object* v_head_744_; lean_object* v_tail_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_758_; 
v_head_744_ = lean_ctor_get(v_a_741_, 0);
v_tail_745_ = lean_ctor_get(v_a_741_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_741_);
if (v_isSharedCheck_758_ == 0)
{
v___x_747_ = v_a_741_;
v_isShared_748_ = v_isSharedCheck_758_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_tail_745_);
lean_inc(v_head_744_);
lean_dec(v_a_741_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_758_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_749_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_750_ = l_Lean_Expr_fvar___override(v_head_744_);
v___x_751_ = l_Lean_MessageData_ofExpr(v___x_750_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_749_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_749_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_a_742_);
lean_ctor_set(v___x_747_, 0, v___x_753_);
v___x_755_ = v___x_747_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_a_742_);
v___x_755_ = v_reuseFailAlloc_757_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v_a_741_ = v_tail_745_;
v_a_742_ = v___x_755_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1));
v___x_763_ = l_Lean_MessageData_ofFormat(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3(void){
_start:
{
lean_object* v___x_764_; lean_object* v_note_765_; 
v___x_764_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2);
v_note_765_ = l_Lean_MessageData_note(v___x_764_);
return v_note_765_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6(void){
_start:
{
lean_object* v_note_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_note_769_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_770_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_note_769_);
return v___x_771_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_773_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
return v___x_774_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10));
v___x_781_ = l_Lean_MessageData_ofFormat(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(lean_object* v_fvarIds_785_, lean_object* v_mvarId_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_note_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_note_792_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_array_get_size(v_fvarIds_785_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v_fvarIds_785_);
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_797_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8);
v___x_798_ = l_Lean_Meta_throwTacticEx___redArg(v___x_796_, v_mvarId_786_, v___x_797_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_fvarMsgs_801_; lean_object* v___x_802_; lean_object* v_fvarMsgs_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_799_ = lean_array_to_list(v_fvarIds_785_);
v___x_800_ = lean_box(0);
v_fvarMsgs_801_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(v___x_799_, v___x_800_);
v___x_802_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11);
v_fvarMsgs_803_ = l_Lean_MessageData_joinSep(v_fvarMsgs_801_, v___x_802_);
v___x_804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_805_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v_fvarMsgs_803_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_note_792_);
v___x_808_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = l_Lean_Meta_throwTacticEx___redArg(v___x_804_, v_mvarId_786_, v___x_810_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___boxed(lean_object* v_fvarIds_812_, lean_object* v_mvarId_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_812_, v_mvarId_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(lean_object* v_00_u03b1_820_, lean_object* v_fvarIds_821_, lean_object* v_mvarId_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_821_, v_mvarId_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(lean_object* v_00_u03b1_829_, lean_object* v_fvarIds_830_, lean_object* v_mvarId_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(v_00_u03b1_829_, v_fvarIds_830_, v_mvarId_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(lean_object* v_a_841_, lean_object* v_as_842_, size_t v_sz_843_, size_t v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_lt(v_i_844_, v_sz_843_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
lean_dec(v_a_841_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_b_845_);
return v___x_852_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_854_; 
lean_dec_ref(v_b_845_);
v_a_853_ = lean_array_uget_borrowed(v_as_842_, v_i_844_);
lean_inc(v_a_853_);
lean_inc(v_a_841_);
v___x_854_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_841_, v_a_853_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_868_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_868_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_868_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_868_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_box(0);
if (lean_obj_tag(v_a_855_) == 1)
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_a_841_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_a_855_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v___x_864_; size_t v___x_865_; size_t v___x_866_; 
lean_del_object(v___x_857_);
lean_dec(v_a_855_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_844_, v___x_865_);
v_i_844_ = v___x_866_;
v_b_845_ = v___x_864_;
goto _start;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_a_841_);
v_a_869_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_854_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_854_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___boxed(lean_object* v_a_877_, lean_object* v_as_878_, lean_object* v_sz_879_, lean_object* v_i_880_, lean_object* v_b_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
size_t v_sz_boxed_887_; size_t v_i_boxed_888_; lean_object* v_res_889_; 
v_sz_boxed_887_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_888_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_877_, v_as_878_, v_sz_boxed_887_, v_i_boxed_888_, v_b_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v_as_878_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0(lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_a_900_; lean_object* v___x_911_; 
v___x_911_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_891_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_n(v_a_912_, 2);
lean_dec_ref(v___x_911_);
v___x_913_ = l_Lean_MVarId_getNondepPropHyps(v_a_912_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; size_t v_sz_916_; size_t v___x_917_; lean_object* v___x_918_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
v___x_915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_sz_916_ = lean_array_size(v_a_914_);
v___x_917_ = ((size_t)0ULL);
lean_inc(v_a_912_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_912_, v_a_914_, v_sz_916_, v___x_917_, v___x_915_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v_fst_920_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref(v___x_918_);
v_fst_920_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_fst_920_);
lean_dec(v_a_919_);
if (lean_obj_tag(v_fst_920_) == 0)
{
uint8_t v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; 
v___x_921_ = 1;
v___x_922_ = 0;
lean_inc(v_a_912_);
v___x_923_ = l_Lean_Meta_splitTarget_x3f(v_a_912_, v___x_921_, v___x_922_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
if (lean_obj_tag(v_a_924_) == 1)
{
lean_object* v_val_925_; 
lean_dec(v_a_914_);
lean_dec(v_a_912_);
v_val_925_ = lean_ctor_get(v_a_924_, 0);
lean_inc(v_val_925_);
lean_dec_ref(v_a_924_);
v_a_900_ = v_val_925_;
goto v___jp_899_;
}
else
{
lean_object* v___x_926_; 
lean_dec(v_a_924_);
v___x_926_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_a_914_, v_a_912_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v_a_900_ = v_a_927_;
goto v___jp_899_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_926_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_a_914_);
lean_dec(v_a_912_);
v_a_936_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_923_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_923_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v_val_944_; 
lean_dec(v_a_914_);
lean_dec(v_a_912_);
v_val_944_ = lean_ctor_get(v_fst_920_, 0);
lean_inc(v_val_944_);
lean_dec_ref(v_fst_920_);
v_a_900_ = v_val_944_;
goto v___jp_899_;
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_914_);
lean_dec(v_a_912_);
v_a_945_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_918_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_918_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_a_912_);
v_a_953_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_913_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_913_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_911_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_911_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
v___jp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_900_, v___y_891_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_909_; 
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v___x_901_, 0);
lean_dec(v_unused_910_);
v___x_903_ = v___x_901_;
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
else
{
lean_dec(v___x_901_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0___boxed(lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Elab_Tactic_evalSplit___lam__0(v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1(uint8_t v_type_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_a_990_; lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_981_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc_n(v_a_1002_, 2);
lean_dec_ref(v___x_1001_);
v___x_1003_ = 0;
v___x_1004_ = l_Lean_Meta_splitTarget_x3f(v_a_1002_, v_type_979_, v___x_1003_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
if (lean_obj_tag(v_a_1005_) == 1)
{
lean_object* v_val_1006_; 
lean_dec(v_a_1002_);
v_val_1006_ = lean_ctor_get(v_a_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v_a_1005_);
v_a_990_ = v_val_1006_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1007_; 
lean_dec(v_a_1005_);
v___x_1007_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_a_1002_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
v_a_990_ = v_a_1008_;
goto v___jp_989_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1007_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_a_1002_);
v_a_1017_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1004_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1004_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1001_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1001_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
v___jp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_990_, v___y_981_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1000_);
v___x_993_ = v___x_991_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_991_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1___boxed(lean_object* v_type_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
uint8_t v_type_4505__boxed_1043_; lean_object* v_res_1044_; 
v_type_4505__boxed_1043_ = lean_unbox(v_type_1033_);
v_res_1044_ = l_Lean_Elab_Tactic_evalSplit___lam__1(v_type_4505__boxed_1043_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2(lean_object* v_a_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_a_1056_; lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1047_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_n(v_a_1068_, 2);
lean_dec_ref(v___x_1067_);
lean_inc(v_a_1045_);
v___x_1069_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_1068_, v_a_1045_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
if (lean_obj_tag(v_a_1070_) == 1)
{
lean_object* v_val_1071_; 
lean_dec(v_a_1068_);
lean_dec(v_a_1045_);
v_val_1071_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_val_1071_);
lean_dec_ref(v_a_1070_);
v_a_1056_ = v_val_1071_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_a_1070_);
v___x_1072_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_a_1045_, v_a_1068_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1072_);
v_a_1056_ = v_a_1073_;
goto v___jp_1055_;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1072_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1072_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_a_1068_);
lean_dec(v_a_1045_);
v_a_1082_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1069_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1069_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1045_);
v_a_1090_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1067_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1067_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
v___jp_1055_:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_1056_, v___y_1047_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1065_; 
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___x_1057_, 0);
lean_dec(v_unused_1066_);
v___x_1059_ = v___x_1057_;
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v___x_1057_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_box(0);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
else
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2___boxed(lean_object* v_a_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Elab_Tactic_evalSplit___lam__2(v_a_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object* v_stx_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; uint8_t v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; uint8_t v___y_1175_; lean_object* v___f_1179_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___f_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSplit___closed__0));
v___x_1200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc(v_stx_1110_);
v___x_1201_ = l_Lean_Syntax_isOfKind(v_stx_1110_, v___x_1200_);
if (v___x_1201_ == 0)
{
v___y_1181_ = v_a_1111_;
v___y_1182_ = v_a_1112_;
v___y_1183_ = v_a_1113_;
v___y_1184_ = v_a_1114_;
v___y_1185_ = v_a_1115_;
v___y_1186_ = v_a_1116_;
v___y_1187_ = v_a_1117_;
v___y_1188_ = v_a_1118_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = l_Lean_Syntax_getArg(v_stx_1110_, v___x_1202_);
lean_inc(v___x_1203_);
v___x_1204_ = l_Lean_Syntax_matchesNull(v___x_1203_, v___x_1202_);
if (v___x_1204_ == 0)
{
lean_dec(v___x_1203_);
v___y_1181_ = v_a_1111_;
v___y_1182_ = v_a_1112_;
v___y_1183_ = v_a_1113_;
v___y_1184_ = v_a_1114_;
v___y_1185_ = v_a_1115_;
v___y_1186_ = v_a_1116_;
v___y_1187_ = v_a_1117_;
v___y_1188_ = v_a_1118_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1205_; lean_object* v_t_1206_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v_t_1206_ = l_Lean_Syntax_getArg(v___x_1203_, v___x_1205_);
lean_dec(v___x_1203_);
v___x_1218_ = lean_unsigned_to_nat(2u);
v___x_1219_ = l_Lean_Syntax_getArg(v_stx_1110_, v___x_1218_);
v___x_1220_ = l_Lean_Syntax_isNone(v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; 
lean_inc(v___x_1219_);
v___x_1221_ = l_Lean_Syntax_matchesNull(v___x_1219_, v___x_1202_);
if (v___x_1221_ == 0)
{
lean_dec(v___x_1219_);
lean_dec(v_t_1206_);
v___y_1181_ = v_a_1111_;
v___y_1182_ = v_a_1112_;
v___y_1183_ = v_a_1113_;
v___y_1184_ = v_a_1114_;
v___y_1185_ = v_a_1115_;
v___y_1186_ = v_a_1116_;
v___y_1187_ = v_a_1117_;
v___y_1188_ = v_a_1118_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = l_Lean_Syntax_getArg(v___x_1219_, v___x_1205_);
lean_dec(v___x_1219_);
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
lean_inc(v___x_1222_);
v___x_1224_ = l_Lean_Syntax_isOfKind(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_dec(v___x_1222_);
lean_dec(v_t_1206_);
v___y_1181_ = v_a_1111_;
v___y_1182_ = v_a_1112_;
v___y_1183_ = v_a_1113_;
v___y_1184_ = v_a_1114_;
v___y_1185_ = v_a_1115_;
v___y_1186_ = v_a_1116_;
v___y_1187_ = v_a_1117_;
v___y_1188_ = v_a_1118_;
goto v___jp_1180_;
}
else
{
lean_object* v_loc_1225_; lean_object* v___x_1226_; 
v_loc_1225_ = l_Lean_Syntax_getArg(v___x_1222_, v___x_1202_);
lean_dec(v___x_1222_);
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_loc_1225_);
v___y_1208_ = v_a_1117_;
v___y_1209_ = v_a_1113_;
v___y_1210_ = v_a_1115_;
v___y_1211_ = v_a_1118_;
v___y_1212_ = v_a_1112_;
v___y_1213_ = v_a_1111_;
v___y_1214_ = v_a_1114_;
v___y_1215_ = v_a_1116_;
v___y_1216_ = v___x_1226_;
goto v___jp_1207_;
}
}
}
else
{
lean_object* v___x_1227_; 
lean_dec(v___x_1219_);
v___x_1227_ = lean_box(0);
v___y_1208_ = v_a_1117_;
v___y_1209_ = v_a_1113_;
v___y_1210_ = v_a_1115_;
v___y_1211_ = v_a_1118_;
v___y_1212_ = v_a_1112_;
v___y_1213_ = v_a_1111_;
v___y_1214_ = v_a_1114_;
v___y_1215_ = v_a_1116_;
v___y_1216_ = v___x_1227_;
goto v___jp_1207_;
}
v___jp_1207_:
{
lean_object* v___x_1217_; 
v___x_1217_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_1206_, v___y_1216_, v___y_1213_, v___y_1212_, v___y_1209_, v___y_1214_, v___y_1210_, v___y_1215_, v___y_1208_, v___y_1211_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_dec_ref(v___x_1217_);
v___y_1181_ = v___y_1213_;
v___y_1182_ = v___y_1212_;
v___y_1183_ = v___y_1209_;
v___y_1184_ = v___y_1214_;
v___y_1185_ = v___y_1210_;
v___y_1186_ = v___y_1215_;
v___y_1187_ = v___y_1208_;
v___y_1188_ = v___y_1211_;
goto v___jp_1180_;
}
else
{
lean_dec(v_stx_1110_);
return v___x_1217_;
}
}
}
}
v___jp_1120_:
{
if (v___y_1122_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v___y_1121_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get(v___x_1132_, v___y_1123_, v___x_1133_);
lean_dec_ref(v___y_1123_);
v___x_1135_ = l_Lean_Elab_Tactic_getFVarId(v___x_1134_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1137_, 0, v_a_1136_);
v___x_1138_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1137_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1138_;
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1135_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1135_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v___x_1147_; 
lean_dec_ref(v___y_1123_);
v___x_1147_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1121_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1147_;
}
}
v___jp_1148_:
{
lean_object* v___x_1161_; 
lean_dec_ref(v___y_1149_);
v___x_1161_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v___y_1160_, v___y_1154_, v___y_1155_, v___y_1152_, v___y_1153_, v___y_1159_, v___y_1157_);
lean_dec(v___y_1160_);
return v___x_1161_;
}
v___jp_1162_:
{
if (v___y_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_array_get_size(v___y_1165_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v___y_1174_);
v___y_1121_ = v___y_1164_;
v___y_1122_ = v___y_1163_;
v___y_1123_ = v___y_1165_;
v___y_1124_ = v___y_1170_;
v___y_1125_ = v___y_1173_;
v___y_1126_ = v___y_1168_;
v___y_1127_ = v___y_1167_;
v___y_1128_ = v___y_1166_;
v___y_1129_ = v___y_1169_;
v___y_1130_ = v___y_1172_;
v___y_1131_ = v___y_1171_;
goto v___jp_1120_;
}
else
{
v___y_1149_ = v___y_1164_;
v___y_1150_ = v___y_1167_;
v___y_1151_ = v___y_1168_;
v___y_1152_ = v___y_1166_;
v___y_1153_ = v___y_1169_;
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1165_;
v___y_1156_ = v___y_1170_;
v___y_1157_ = v___y_1171_;
v___y_1158_ = v___y_1173_;
v___y_1159_ = v___y_1172_;
v___y_1160_ = v___y_1174_;
goto v___jp_1148_;
}
}
else
{
v___y_1149_ = v___y_1164_;
v___y_1150_ = v___y_1167_;
v___y_1151_ = v___y_1168_;
v___y_1152_ = v___y_1166_;
v___y_1153_ = v___y_1169_;
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1165_;
v___y_1156_ = v___y_1170_;
v___y_1157_ = v___y_1171_;
v___y_1158_ = v___y_1173_;
v___y_1159_ = v___y_1172_;
v___y_1160_ = v___y_1174_;
goto v___jp_1148_;
}
}
v___jp_1180_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_loc_1191_; 
v___x_1189_ = lean_unsigned_to_nat(2u);
v___x_1190_ = l_Lean_Syntax_getArg(v_stx_1110_, v___x_1189_);
lean_dec(v_stx_1110_);
v_loc_1191_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1190_);
if (lean_obj_tag(v_loc_1191_) == 0)
{
lean_object* v___x_1192_; 
lean_dec(v___x_1190_);
v___x_1192_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1192_;
}
else
{
lean_object* v_hypotheses_1193_; uint8_t v_type_1194_; lean_object* v___x_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_hypotheses_1193_ = lean_ctor_get(v_loc_1191_, 0);
lean_inc_ref(v_hypotheses_1193_);
v_type_1194_ = lean_ctor_get_uint8(v_loc_1191_, sizeof(void*)*1);
lean_dec_ref(v_loc_1191_);
v___x_1195_ = lean_box(v_type_1194_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1196_, 0, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_array_get_size(v_hypotheses_1193_);
v___x_1199_ = lean_nat_dec_lt(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
v___y_1163_ = v_type_1194_;
v___y_1164_ = v___f_1196_;
v___y_1165_ = v_hypotheses_1193_;
v___y_1166_ = v___y_1185_;
v___y_1167_ = v___y_1184_;
v___y_1168_ = v___y_1183_;
v___y_1169_ = v___y_1186_;
v___y_1170_ = v___y_1181_;
v___y_1171_ = v___y_1188_;
v___y_1172_ = v___y_1187_;
v___y_1173_ = v___y_1182_;
v___y_1174_ = v___x_1190_;
v___y_1175_ = v___x_1199_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v_type_1194_;
v___y_1164_ = v___f_1196_;
v___y_1165_ = v_hypotheses_1193_;
v___y_1166_ = v___y_1185_;
v___y_1167_ = v___y_1184_;
v___y_1168_ = v___y_1183_;
v___y_1169_ = v___y_1186_;
v___y_1170_ = v___y_1181_;
v___y_1171_ = v___y_1188_;
v___y_1172_ = v___y_1187_;
v___y_1173_ = v___y_1182_;
v___y_1174_ = v___x_1190_;
v___y_1175_ = v_type_1194_;
goto v___jp_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object* v_stx_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Elab_Tactic_evalSplit(v_stx_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1(){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1247_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1250_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___boxed), 10, 0);
v___x_1251_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1247_, v___x_1248_, v___x_1249_, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___boxed(lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3(){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6));
v___x_1282_ = l_Lean_addBuiltinDeclarationRanges(v___x_1280_, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
return v_res_1284_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
