// Lean compiler output
// Module: Lake.DSL.VerLit
// Imports: public import Lean.ToExpr public import Lake.Util.Version public import Lake.Config.Dependency import Lake.DSL.Syntax import Lean.Meta.Eval
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static const lean_string_object l_Lake_DSL_SemVerCore_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_SemVerCore_toExpr___closed__0 = (const lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value;
static const lean_string_object l_Lake_DSL_SemVerCore_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "SemVerCore"};
static const lean_object* l_Lake_DSL_SemVerCore_toExpr___closed__1 = (const lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__1_value;
static const lean_string_object l_Lake_DSL_SemVerCore_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lake_DSL_SemVerCore_toExpr___closed__2 = (const lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__2_value;
static const lean_ctor_object l_Lake_DSL_SemVerCore_toExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_SemVerCore_toExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__3_value_aux_0),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 6, 10, 27, 76, 25, 44, 113)}};
static const lean_ctor_object l_Lake_DSL_SemVerCore_toExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__3_value_aux_1),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(95, 12, 49, 177, 238, 160, 185, 135)}};
static const lean_object* l_Lake_DSL_SemVerCore_toExpr___closed__3 = (const lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__3_value;
static lean_once_cell_t l_Lake_DSL_SemVerCore_toExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_SemVerCore_toExpr___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_SemVerCore_toExpr(lean_object*);
static const lean_closure_object l_Lake_DSL_instToExprSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_SemVerCore_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instToExprSemVerCore___closed__0 = (const lean_object*)&l_Lake_DSL_instToExprSemVerCore___closed__0_value;
static const lean_ctor_object l_Lake_DSL_instToExprSemVerCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_instToExprSemVerCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_instToExprSemVerCore___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 6, 10, 27, 76, 25, 44, 113)}};
static const lean_object* l_Lake_DSL_instToExprSemVerCore___closed__1 = (const lean_object*)&l_Lake_DSL_instToExprSemVerCore___closed__1_value;
static lean_once_cell_t l_Lake_DSL_instToExprSemVerCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprSemVerCore___closed__2;
static lean_once_cell_t l_Lake_DSL_instToExprSemVerCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprSemVerCore___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_instToExprSemVerCore;
static const lean_string_object l_Lake_DSL_StdVer_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "StdVer"};
static const lean_object* l_Lake_DSL_StdVer_toExpr___closed__0 = (const lean_object*)&l_Lake_DSL_StdVer_toExpr___closed__0_value;
static const lean_ctor_object l_Lake_DSL_StdVer_toExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_StdVer_toExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_StdVer_toExpr___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_StdVer_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 146, 19, 103, 232, 226, 61, 158)}};
static const lean_ctor_object l_Lake_DSL_StdVer_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_StdVer_toExpr___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 219, 233, 135, 152, 103, 227, 200)}};
static const lean_object* l_Lake_DSL_StdVer_toExpr___closed__1 = (const lean_object*)&l_Lake_DSL_StdVer_toExpr___closed__1_value;
static lean_once_cell_t l_Lake_DSL_StdVer_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_StdVer_toExpr___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_StdVer_toExpr(lean_object*);
static const lean_closure_object l_Lake_DSL_instToExprStdVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_StdVer_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instToExprStdVer___closed__0 = (const lean_object*)&l_Lake_DSL_instToExprStdVer___closed__0_value;
static const lean_ctor_object l_Lake_DSL_instToExprStdVer___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_instToExprStdVer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_instToExprStdVer___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_StdVer_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 146, 19, 103, 232, 226, 61, 158)}};
static const lean_object* l_Lake_DSL_instToExprStdVer___closed__1 = (const lean_object*)&l_Lake_DSL_instToExprStdVer___closed__1_value;
static lean_once_cell_t l_Lake_DSL_instToExprStdVer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprStdVer___closed__2;
static lean_once_cell_t l_Lake_DSL_instToExprStdVer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprStdVer___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_instToExprStdVer;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ComparatorOp"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__0 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__1 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__1_value;
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__2_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__2_value_aux_1),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(206, 254, 206, 101, 1, 105, 92, 124)}};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__2 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__2_value;
static lean_once_cell_t l_Lake_DSL_ComparatorOp_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__3;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__4 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__4_value;
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__5_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__5_value_aux_1),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(198, 65, 63, 188, 146, 202, 245, 211)}};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__5 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__5_value;
static lean_once_cell_t l_Lake_DSL_ComparatorOp_toExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__6;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__7 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__7_value;
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(252, 195, 77, 247, 71, 137, 186, 146)}};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__8 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__8_value;
static lean_once_cell_t l_Lake_DSL_ComparatorOp_toExpr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__9;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__10 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__10_value;
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__11_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__11_value_aux_1),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 128, 56, 165, 113, 70, 122, 227)}};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__11 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__11_value;
static lean_once_cell_t l_Lake_DSL_ComparatorOp_toExpr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__12;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__13 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__13_value;
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__14_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__14_value_aux_1),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(94, 55, 98, 73, 116, 66, 173, 142)}};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__14 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__14_value;
static lean_once_cell_t l_Lake_DSL_ComparatorOp_toExpr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__15;
static const lean_string_object l_Lake_DSL_ComparatorOp_toExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ne"};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__16 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__16_value;
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__17_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_ctor_object l_Lake_DSL_ComparatorOp_toExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__17_value_aux_1),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(242, 18, 232, 247, 244, 252, 188, 196)}};
static const lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__17 = (const lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__17_value;
static lean_once_cell_t l_Lake_DSL_ComparatorOp_toExpr___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_ComparatorOp_toExpr___closed__18;
LEAN_EXPORT lean_object* l_Lake_DSL_ComparatorOp_toExpr(uint8_t);
LEAN_EXPORT lean_object* l_Lake_DSL_ComparatorOp_toExpr___boxed(lean_object*);
static const lean_closure_object l_Lake_DSL_instToExprComparatorOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_ComparatorOp_toExpr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instToExprComparatorOp___closed__0 = (const lean_object*)&l_Lake_DSL_instToExprComparatorOp___closed__0_value;
static const lean_ctor_object l_Lake_DSL_instToExprComparatorOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_instToExprComparatorOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_instToExprComparatorOp___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_ComparatorOp_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 59, 82, 229, 190, 167, 67, 17)}};
static const lean_object* l_Lake_DSL_instToExprComparatorOp___closed__1 = (const lean_object*)&l_Lake_DSL_instToExprComparatorOp___closed__1_value;
static lean_once_cell_t l_Lake_DSL_instToExprComparatorOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprComparatorOp___closed__2;
static lean_once_cell_t l_Lake_DSL_instToExprComparatorOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprComparatorOp___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_instToExprComparatorOp;
static const lean_string_object l_Lake_DSL_VerComparator_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "VerComparator"};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__0 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__0_value;
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 173, 77, 193, 175, 239, 241, 197)}};
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 168, 184, 142, 178, 100, 228, 229)}};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__1 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__1_value;
static lean_once_cell_t l_Lake_DSL_VerComparator_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerComparator_toExpr___closed__2;
static const lean_string_object l_Lake_DSL_VerComparator_toExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__3 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__3_value;
static const lean_string_object l_Lake_DSL_VerComparator_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__4 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__4_value;
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__5_value_aux_0),((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__5 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__5_value;
static lean_once_cell_t l_Lake_DSL_VerComparator_toExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerComparator_toExpr___closed__6;
static const lean_string_object l_Lake_DSL_VerComparator_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__7 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__7_value;
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lake_DSL_VerComparator_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lake_DSL_VerComparator_toExpr___closed__8 = (const lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__8_value;
static lean_once_cell_t l_Lake_DSL_VerComparator_toExpr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerComparator_toExpr___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_VerComparator_toExpr(lean_object*);
static const lean_closure_object l_Lake_DSL_instToExprVerComparator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_VerComparator_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instToExprVerComparator___closed__0 = (const lean_object*)&l_Lake_DSL_instToExprVerComparator___closed__0_value;
static const lean_ctor_object l_Lake_DSL_instToExprVerComparator___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_instToExprVerComparator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_instToExprVerComparator___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_VerComparator_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 173, 77, 193, 175, 239, 241, 197)}};
static const lean_object* l_Lake_DSL_instToExprVerComparator___closed__1 = (const lean_object*)&l_Lake_DSL_instToExprVerComparator___closed__1_value;
static lean_once_cell_t l_Lake_DSL_instToExprVerComparator___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprVerComparator___closed__2;
static lean_once_cell_t l_Lake_DSL_instToExprVerComparator___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprVerComparator___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_instToExprVerComparator;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__1_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__5_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__9_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_DSL_VerRange_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "VerRange"};
static const lean_object* l_Lake_DSL_VerRange_toExpr___closed__0 = (const lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__0_value;
static const lean_ctor_object l_Lake_DSL_VerRange_toExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_VerRange_toExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 206, 162, 7, 236, 12, 145, 251)}};
static const lean_ctor_object l_Lake_DSL_VerRange_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__1_value_aux_1),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 157, 137, 23, 86, 187, 191, 168)}};
static const lean_object* l_Lake_DSL_VerRange_toExpr___closed__1 = (const lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__1_value;
static lean_once_cell_t l_Lake_DSL_VerRange_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerRange_toExpr___closed__2;
static const lean_string_object l_Lake_DSL_VerRange_toExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lake_DSL_VerRange_toExpr___closed__3 = (const lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__3_value;
static const lean_ctor_object l_Lake_DSL_VerRange_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lake_DSL_VerRange_toExpr___closed__4 = (const lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__4_value;
static lean_once_cell_t l_Lake_DSL_VerRange_toExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerRange_toExpr___closed__5;
static lean_once_cell_t l_Lake_DSL_VerRange_toExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerRange_toExpr___closed__6;
static lean_once_cell_t l_Lake_DSL_VerRange_toExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerRange_toExpr___closed__7;
static lean_once_cell_t l_Lake_DSL_VerRange_toExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_VerRange_toExpr___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_VerRange_toExpr(lean_object*);
static const lean_closure_object l_Lake_DSL_instToExprVerRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_VerRange_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instToExprVerRange___closed__0 = (const lean_object*)&l_Lake_DSL_instToExprVerRange___closed__0_value;
static const lean_ctor_object l_Lake_DSL_instToExprVerRange___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_instToExprVerRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_instToExprVerRange___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_VerRange_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 206, 162, 7, 236, 12, 145, 251)}};
static const lean_object* l_Lake_DSL_instToExprVerRange___closed__1 = (const lean_object*)&l_Lake_DSL_instToExprVerRange___closed__1_value;
static lean_once_cell_t l_Lake_DSL_instToExprVerRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprVerRange___closed__2;
static lean_once_cell_t l_Lake_DSL_instToExprVerRange___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprVerRange___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_instToExprVerRange;
static const lean_string_object l_Lake_DSL_InputVer_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "InputVer"};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__0 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__0_value;
static const lean_string_object l_Lake_DSL_InputVer_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__1 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__1_value;
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__2_value_aux_0),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__2_value_aux_1),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(56, 190, 59, 35, 131, 146, 80, 44)}};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__2 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__2_value;
static lean_once_cell_t l_Lake_DSL_InputVer_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_InputVer_toExpr___closed__3;
static const lean_string_object l_Lake_DSL_InputVer_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__4 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__4_value;
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__5_value_aux_0),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__5_value_aux_1),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 200, 168, 53, 212, 85, 80, 128)}};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__5 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__5_value;
static lean_once_cell_t l_Lake_DSL_InputVer_toExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_InputVer_toExpr___closed__6;
static const lean_string_object l_Lake_DSL_InputVer_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ver"};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__7 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__7_value;
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__8_value_aux_0),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_ctor_object l_Lake_DSL_InputVer_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__8_value_aux_1),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(114, 244, 198, 157, 121, 115, 31, 95)}};
static const lean_object* l_Lake_DSL_InputVer_toExpr___closed__8 = (const lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__8_value;
static lean_once_cell_t l_Lake_DSL_InputVer_toExpr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_InputVer_toExpr___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_InputVer_toExpr(lean_object*);
static const lean_closure_object l_Lake_DSL_instToExprInputVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_DSL_InputVer_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_DSL_instToExprInputVer___closed__0 = (const lean_object*)&l_Lake_DSL_instToExprInputVer___closed__0_value;
static const lean_ctor_object l_Lake_DSL_instToExprInputVer___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_instToExprInputVer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_instToExprInputVer___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_InputVer_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 40, 241, 211, 193, 106, 100, 83)}};
static const lean_object* l_Lake_DSL_instToExprInputVer___closed__1 = (const lean_object*)&l_Lake_DSL_instToExprInputVer___closed__1_value;
static lean_once_cell_t l_Lake_DSL_instToExprInputVer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprInputVer___closed__2;
static lean_once_cell_t l_Lake_DSL_instToExprInputVer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_instToExprInputVer___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_instToExprInputVer;
LEAN_EXPORT lean_object* l_Lake_DSL_toResultExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_toResultExpr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Except"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__0 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 113, 136, 33, 237, 151, 233, 210)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__1 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__1_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__2 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__3 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__6 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__6_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__7 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__7_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__8 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__8_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__9 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value_aux_1),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__8_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value_aux_2),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "decodeVersion"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11_value;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 51, 6, 126, 144, 142, 7, 116)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__13 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__13_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DecodeVersion"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__14 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__14_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value_aux_0),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__14_value),LEAN_SCALAR_PTR_LITERAL(214, 242, 230, 144, 77, 175, 29, 111)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value_aux_1),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 111, 39, 77, 209, 199, 208, 149)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__16 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__16_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__17 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__17_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__18 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__18_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__18_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__19 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__19_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__20 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__20_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21_value_aux_0),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__20_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21_value;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toResultExpr"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__25 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__25_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26_value_aux_0),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26_value_aux_1),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__25_value),LEAN_SCALAR_PTR_LITERAL(204, 128, 107, 14, 105, 224, 197, 105)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalVer"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__0 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 252, 213, 234, 103, 11, 172, 191)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ill-formed `eval_ver%` syntax"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__2 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__2_value;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected type is not known"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__4 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__4_value;
static lean_once_cell_t l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__1_value),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "VerLit"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 108, 128, 72, 64, 52, 219, 22)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(68, 219, 34, 172, 50, 79, 1, 2)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__6_value),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 6, 201, 146, 243, 158, 174, 52)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value),LEAN_SCALAR_PTR_LITERAL(159, 145, 83, 239, 231, 84, 206, 143)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabEvalVersion"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 54, 81, 105, 139, 172, 6)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "verLit"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__0 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_SemVerCore_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1_value_aux_0),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__24_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 205, 236, 50, 125, 9, 172, 134)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "ill-formed version literal"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__2 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__2_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eval_ver%"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__3 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__3_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termS!_"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__4 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 130, 93, 49, 63, 146, 201, 153)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__5 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__5_value;
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s!"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__6 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expandVerLit"};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 93, 53, 69, 16, 147, 6, 21)}};
static const lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___boxed(lean_object*);
static lean_object* _init_l_Lake_DSL_SemVerCore_toExpr___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = ((lean_object*)(l_Lake_DSL_SemVerCore_toExpr___closed__3));
v___x_10_ = l_Lean_mkConst(v___x_9_, v___x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_SemVerCore_toExpr(lean_object* v_self_11_){
_start:
{
lean_object* v_major_12_; lean_object* v_minor_13_; lean_object* v_patch_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_major_12_ = lean_ctor_get(v_self_11_, 0);
lean_inc(v_major_12_);
v_minor_13_ = lean_ctor_get(v_self_11_, 1);
lean_inc(v_minor_13_);
v_patch_14_ = lean_ctor_get(v_self_11_, 2);
lean_inc(v_patch_14_);
lean_dec_ref(v_self_11_);
v___x_15_ = lean_obj_once(&l_Lake_DSL_SemVerCore_toExpr___closed__4, &l_Lake_DSL_SemVerCore_toExpr___closed__4_once, _init_l_Lake_DSL_SemVerCore_toExpr___closed__4);
v___x_16_ = l_Lean_mkNatLit(v_major_12_);
v___x_17_ = l_Lean_mkNatLit(v_minor_13_);
v___x_18_ = l_Lean_mkNatLit(v_patch_14_);
v___x_19_ = l_Lean_mkApp3(v___x_15_, v___x_16_, v___x_17_, v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprSemVerCore___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_box(0);
v___x_25_ = ((lean_object*)(l_Lake_DSL_instToExprSemVerCore___closed__1));
v___x_26_ = l_Lean_mkConst(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprSemVerCore___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_Lake_DSL_instToExprSemVerCore___closed__2, &l_Lake_DSL_instToExprSemVerCore___closed__2_once, _init_l_Lake_DSL_instToExprSemVerCore___closed__2);
v___x_28_ = ((lean_object*)(l_Lake_DSL_instToExprSemVerCore___closed__0));
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprSemVerCore(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lake_DSL_instToExprSemVerCore___closed__3, &l_Lake_DSL_instToExprSemVerCore___closed__3_once, _init_l_Lake_DSL_instToExprSemVerCore___closed__3);
return v___x_30_;
}
}
static lean_object* _init_l_Lake_DSL_StdVer_toExpr___closed__2(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_box(0);
v___x_37_ = ((lean_object*)(l_Lake_DSL_StdVer_toExpr___closed__1));
v___x_38_ = l_Lean_mkConst(v___x_37_, v___x_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_StdVer_toExpr(lean_object* v_self_39_){
_start:
{
lean_object* v_toSemVerCore_40_; lean_object* v_specialDescr_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_toSemVerCore_40_ = lean_ctor_get(v_self_39_, 0);
lean_inc_ref(v_toSemVerCore_40_);
v_specialDescr_41_ = lean_ctor_get(v_self_39_, 1);
lean_inc_ref(v_specialDescr_41_);
lean_dec_ref(v_self_39_);
v___x_42_ = lean_obj_once(&l_Lake_DSL_StdVer_toExpr___closed__2, &l_Lake_DSL_StdVer_toExpr___closed__2_once, _init_l_Lake_DSL_StdVer_toExpr___closed__2);
v___x_43_ = l_Lake_DSL_SemVerCore_toExpr(v_toSemVerCore_40_);
v___x_44_ = l_Lean_mkStrLit(v_specialDescr_41_);
v___x_45_ = l_Lean_mkAppB(v___x_42_, v___x_43_, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprStdVer___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lake_DSL_instToExprStdVer___closed__1));
v___x_52_ = l_Lean_mkConst(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprStdVer___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Lake_DSL_instToExprStdVer___closed__2, &l_Lake_DSL_instToExprStdVer___closed__2_once, _init_l_Lake_DSL_instToExprStdVer___closed__2);
v___x_54_ = ((lean_object*)(l_Lake_DSL_instToExprStdVer___closed__0));
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprStdVer(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Lake_DSL_instToExprStdVer___closed__3, &l_Lake_DSL_instToExprStdVer___closed__3_once, _init_l_Lake_DSL_instToExprStdVer___closed__3);
return v___x_56_;
}
}
static lean_object* _init_l_Lake_DSL_ComparatorOp_toExpr___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_box(0);
v___x_64_ = ((lean_object*)(l_Lake_DSL_ComparatorOp_toExpr___closed__2));
v___x_65_ = l_Lean_mkConst(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lake_DSL_ComparatorOp_toExpr___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_box(0);
v___x_72_ = ((lean_object*)(l_Lake_DSL_ComparatorOp_toExpr___closed__5));
v___x_73_ = l_Lean_mkConst(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Lake_DSL_ComparatorOp_toExpr___closed__9(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = ((lean_object*)(l_Lake_DSL_ComparatorOp_toExpr___closed__8));
v___x_81_ = l_Lean_mkConst(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lake_DSL_ComparatorOp_toExpr___closed__12(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = ((lean_object*)(l_Lake_DSL_ComparatorOp_toExpr___closed__11));
v___x_89_ = l_Lean_mkConst(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lake_DSL_ComparatorOp_toExpr___closed__15(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_box(0);
v___x_96_ = ((lean_object*)(l_Lake_DSL_ComparatorOp_toExpr___closed__14));
v___x_97_ = l_Lean_mkConst(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_DSL_ComparatorOp_toExpr___closed__18(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_box(0);
v___x_104_ = ((lean_object*)(l_Lake_DSL_ComparatorOp_toExpr___closed__17));
v___x_105_ = l_Lean_mkConst(v___x_104_, v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_ComparatorOp_toExpr(uint8_t v_self_106_){
_start:
{
switch(v_self_106_)
{
case 0:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lake_DSL_ComparatorOp_toExpr___closed__3, &l_Lake_DSL_ComparatorOp_toExpr___closed__3_once, _init_l_Lake_DSL_ComparatorOp_toExpr___closed__3);
return v___x_107_;
}
case 1:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_DSL_ComparatorOp_toExpr___closed__6, &l_Lake_DSL_ComparatorOp_toExpr___closed__6_once, _init_l_Lake_DSL_ComparatorOp_toExpr___closed__6);
return v___x_108_;
}
case 2:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_DSL_ComparatorOp_toExpr___closed__9, &l_Lake_DSL_ComparatorOp_toExpr___closed__9_once, _init_l_Lake_DSL_ComparatorOp_toExpr___closed__9);
return v___x_109_;
}
case 3:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lake_DSL_ComparatorOp_toExpr___closed__12, &l_Lake_DSL_ComparatorOp_toExpr___closed__12_once, _init_l_Lake_DSL_ComparatorOp_toExpr___closed__12);
return v___x_110_;
}
case 4:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lake_DSL_ComparatorOp_toExpr___closed__15, &l_Lake_DSL_ComparatorOp_toExpr___closed__15_once, _init_l_Lake_DSL_ComparatorOp_toExpr___closed__15);
return v___x_111_;
}
default: 
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lake_DSL_ComparatorOp_toExpr___closed__18, &l_Lake_DSL_ComparatorOp_toExpr___closed__18_once, _init_l_Lake_DSL_ComparatorOp_toExpr___closed__18);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_ComparatorOp_toExpr___boxed(lean_object* v_self_113_){
_start:
{
uint8_t v_self_boxed_114_; lean_object* v_res_115_; 
v_self_boxed_114_ = lean_unbox(v_self_113_);
v_res_115_ = l_Lake_DSL_ComparatorOp_toExpr(v_self_boxed_114_);
return v_res_115_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprComparatorOp___closed__2(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_box(0);
v___x_121_ = ((lean_object*)(l_Lake_DSL_instToExprComparatorOp___closed__1));
v___x_122_ = l_Lean_mkConst(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprComparatorOp___closed__3(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_obj_once(&l_Lake_DSL_instToExprComparatorOp___closed__2, &l_Lake_DSL_instToExprComparatorOp___closed__2_once, _init_l_Lake_DSL_instToExprComparatorOp___closed__2);
v___x_124_ = ((lean_object*)(l_Lake_DSL_instToExprComparatorOp___closed__0));
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprComparatorOp(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lake_DSL_instToExprComparatorOp___closed__3, &l_Lake_DSL_instToExprComparatorOp___closed__3_once, _init_l_Lake_DSL_instToExprComparatorOp___closed__3);
return v___x_126_;
}
}
static lean_object* _init_l_Lake_DSL_VerComparator_toExpr___closed__2(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_box(0);
v___x_133_ = ((lean_object*)(l_Lake_DSL_VerComparator_toExpr___closed__1));
v___x_134_ = l_Lean_mkConst(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lake_DSL_VerComparator_toExpr___closed__6(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = ((lean_object*)(l_Lake_DSL_VerComparator_toExpr___closed__5));
v___x_142_ = l_Lean_mkConst(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Lake_DSL_VerComparator_toExpr___closed__9(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lake_DSL_VerComparator_toExpr___closed__8));
v___x_149_ = l_Lean_mkConst(v___x_148_, v___x_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_VerComparator_toExpr(lean_object* v_self_150_){
_start:
{
lean_object* v_ver_151_; uint8_t v_op_152_; uint8_t v_includeSuffixes_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_ver_151_ = lean_ctor_get(v_self_150_, 0);
lean_inc_ref(v_ver_151_);
v_op_152_ = lean_ctor_get_uint8(v_self_150_, sizeof(void*)*1);
v_includeSuffixes_153_ = lean_ctor_get_uint8(v_self_150_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_150_);
v___x_154_ = lean_obj_once(&l_Lake_DSL_VerComparator_toExpr___closed__2, &l_Lake_DSL_VerComparator_toExpr___closed__2_once, _init_l_Lake_DSL_VerComparator_toExpr___closed__2);
v___x_155_ = l_Lake_DSL_StdVer_toExpr(v_ver_151_);
v___x_156_ = l_Lake_DSL_ComparatorOp_toExpr(v_op_152_);
if (v_includeSuffixes_153_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l_Lake_DSL_VerComparator_toExpr___closed__6, &l_Lake_DSL_VerComparator_toExpr___closed__6_once, _init_l_Lake_DSL_VerComparator_toExpr___closed__6);
v___x_158_ = l_Lean_mkApp3(v___x_154_, v___x_155_, v___x_156_, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lake_DSL_VerComparator_toExpr___closed__9, &l_Lake_DSL_VerComparator_toExpr___closed__9_once, _init_l_Lake_DSL_VerComparator_toExpr___closed__9);
v___x_160_ = l_Lean_mkApp3(v___x_154_, v___x_155_, v___x_156_, v___x_159_);
return v___x_160_;
}
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerComparator___closed__2(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lake_DSL_instToExprVerComparator___closed__1));
v___x_167_ = l_Lean_mkConst(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerComparator___closed__3(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_169_ = ((lean_object*)(l_Lake_DSL_instToExprVerComparator___closed__0));
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerComparator(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__3, &l_Lake_DSL_instToExprVerComparator___closed__3_once, _init_l_Lake_DSL_instToExprVerComparator___closed__3);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(lean_object* v_nilFn_172_, lean_object* v_consFn_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_dec_ref(v_consFn_173_);
lean_inc_ref(v_nilFn_172_);
return v_nilFn_172_;
}
else
{
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_head_175_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_head_175_);
v_tail_176_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_tail_176_);
lean_dec_ref_known(v_x_174_, 2);
v___x_177_ = l_Lake_DSL_VerComparator_toExpr(v_head_175_);
lean_inc_ref(v_consFn_173_);
v___x_178_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(v_nilFn_172_, v_consFn_173_, v_tail_176_);
v___x_179_ = l_Lean_mkAppB(v_consFn_173_, v___x_177_, v___x_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0___boxed(lean_object* v_nilFn_180_, lean_object* v_consFn_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(v_nilFn_180_, v_consFn_181_, v_x_182_);
lean_dec_ref(v_nilFn_180_);
return v_res_183_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_193_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2));
v___x_194_ = l_Lean_mkConst(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_200_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6));
v___x_201_ = l_Lean_mkConst(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8(void){
_start:
{
lean_object* v_type_202_; lean_object* v___x_203_; lean_object* v_nil_204_; 
v_type_202_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_203_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7);
v_nil_204_ = l_Lean_Expr_app___override(v___x_203_, v_type_202_);
return v_nil_204_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_210_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10));
v___x_211_ = l_Lean_mkConst(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12(void){
_start:
{
lean_object* v_type_212_; lean_object* v___x_213_; lean_object* v_cons_214_; 
v_type_212_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_213_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11);
v_cons_214_ = l_Lean_Expr_app___override(v___x_213_, v_type_212_);
return v_cons_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(lean_object* v_nilFn_215_, lean_object* v_consFn_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_dec_ref(v_consFn_216_);
lean_inc_ref(v_nilFn_215_);
return v_nilFn_215_;
}
else
{
lean_object* v_head_218_; lean_object* v_tail_219_; lean_object* v_type_220_; lean_object* v___x_221_; lean_object* v_nil_222_; lean_object* v_cons_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_head_218_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_head_218_);
v_tail_219_ = lean_ctor_get(v_x_217_, 1);
lean_inc(v_tail_219_);
lean_dec_ref_known(v_x_217_, 2);
v_type_220_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_221_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4);
v_nil_222_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8);
v_cons_223_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12);
v___x_224_ = lean_array_to_list(v_head_218_);
v___x_225_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(v_nil_222_, v_cons_223_, v___x_224_);
v___x_226_ = l_Lean_mkAppB(v___x_221_, v_type_220_, v___x_225_);
lean_inc_ref(v_consFn_216_);
v___x_227_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(v_nilFn_215_, v_consFn_216_, v_tail_219_);
v___x_228_ = l_Lean_mkAppB(v_consFn_216_, v___x_226_, v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___boxed(lean_object* v_nilFn_229_, lean_object* v_consFn_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(v_nilFn_229_, v_consFn_230_, v_x_231_);
lean_dec_ref(v_nilFn_229_);
return v_res_232_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_box(0);
v___x_239_ = ((lean_object*)(l_Lake_DSL_VerRange_toExpr___closed__1));
v___x_240_ = l_Lean_mkConst(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__5(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_245_ = ((lean_object*)(l_Lake_DSL_VerRange_toExpr___closed__4));
v___x_246_ = l_Lean_mkConst(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__6(void){
_start:
{
lean_object* v_type_247_; lean_object* v___x_248_; lean_object* v_type_249_; 
v_type_247_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_248_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__5, &l_Lake_DSL_VerRange_toExpr___closed__5_once, _init_l_Lake_DSL_VerRange_toExpr___closed__5);
v_type_249_ = l_Lean_Expr_app___override(v___x_248_, v_type_247_);
return v_type_249_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__7(void){
_start:
{
lean_object* v_type_250_; lean_object* v___x_251_; lean_object* v_nil_252_; 
v_type_250_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__6, &l_Lake_DSL_VerRange_toExpr___closed__6_once, _init_l_Lake_DSL_VerRange_toExpr___closed__6);
v___x_251_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7);
v_nil_252_ = l_Lean_Expr_app___override(v___x_251_, v_type_250_);
return v_nil_252_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__8(void){
_start:
{
lean_object* v_type_253_; lean_object* v___x_254_; lean_object* v_cons_255_; 
v_type_253_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__6, &l_Lake_DSL_VerRange_toExpr___closed__6_once, _init_l_Lake_DSL_VerRange_toExpr___closed__6);
v___x_254_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11);
v_cons_255_ = l_Lean_Expr_app___override(v___x_254_, v_type_253_);
return v_cons_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_VerRange_toExpr(lean_object* v_self_256_){
_start:
{
lean_object* v_toString_257_; lean_object* v_clauses_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_type_261_; lean_object* v___x_262_; lean_object* v_nil_263_; lean_object* v_cons_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_toString_257_ = lean_ctor_get(v_self_256_, 0);
lean_inc_ref(v_toString_257_);
v_clauses_258_ = lean_ctor_get(v_self_256_, 1);
lean_inc_ref(v_clauses_258_);
lean_dec_ref(v_self_256_);
v___x_259_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__2, &l_Lake_DSL_VerRange_toExpr___closed__2_once, _init_l_Lake_DSL_VerRange_toExpr___closed__2);
v___x_260_ = l_Lean_mkStrLit(v_toString_257_);
v_type_261_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__6, &l_Lake_DSL_VerRange_toExpr___closed__6_once, _init_l_Lake_DSL_VerRange_toExpr___closed__6);
v___x_262_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4);
v_nil_263_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__7, &l_Lake_DSL_VerRange_toExpr___closed__7_once, _init_l_Lake_DSL_VerRange_toExpr___closed__7);
v_cons_264_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__8, &l_Lake_DSL_VerRange_toExpr___closed__8_once, _init_l_Lake_DSL_VerRange_toExpr___closed__8);
v___x_265_ = lean_array_to_list(v_clauses_258_);
v___x_266_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(v_nil_263_, v_cons_264_, v___x_265_);
v___x_267_ = l_Lean_mkAppB(v___x_262_, v_type_261_, v___x_266_);
v___x_268_ = l_Lean_mkAppB(v___x_259_, v___x_260_, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerRange___closed__2(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = ((lean_object*)(l_Lake_DSL_instToExprVerRange___closed__1));
v___x_275_ = l_Lean_mkConst(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerRange___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Lake_DSL_instToExprVerRange___closed__2, &l_Lake_DSL_instToExprVerRange___closed__2_once, _init_l_Lake_DSL_instToExprVerRange___closed__2);
v___x_277_ = ((lean_object*)(l_Lake_DSL_instToExprVerRange___closed__0));
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerRange(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lake_DSL_instToExprVerRange___closed__3, &l_Lake_DSL_instToExprVerRange___closed__3_once, _init_l_Lake_DSL_instToExprVerRange___closed__3);
return v___x_279_;
}
}
static lean_object* _init_l_Lake_DSL_InputVer_toExpr___closed__3(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_box(0);
v___x_287_ = ((lean_object*)(l_Lake_DSL_InputVer_toExpr___closed__2));
v___x_288_ = l_Lean_mkConst(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lake_DSL_InputVer_toExpr___closed__6(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_box(0);
v___x_295_ = ((lean_object*)(l_Lake_DSL_InputVer_toExpr___closed__5));
v___x_296_ = l_Lean_mkConst(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Lake_DSL_InputVer_toExpr___closed__9(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_box(0);
v___x_303_ = ((lean_object*)(l_Lake_DSL_InputVer_toExpr___closed__8));
v___x_304_ = l_Lean_mkConst(v___x_303_, v___x_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_InputVer_toExpr(lean_object* v_self_305_){
_start:
{
switch(lean_obj_tag(v_self_305_))
{
case 0:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lake_DSL_InputVer_toExpr___closed__3, &l_Lake_DSL_InputVer_toExpr___closed__3_once, _init_l_Lake_DSL_InputVer_toExpr___closed__3);
return v___x_306_;
}
case 1:
{
lean_object* v_rev_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_rev_307_ = lean_ctor_get(v_self_305_, 0);
lean_inc_ref(v_rev_307_);
lean_dec_ref_known(v_self_305_, 1);
v___x_308_ = lean_obj_once(&l_Lake_DSL_InputVer_toExpr___closed__6, &l_Lake_DSL_InputVer_toExpr___closed__6_once, _init_l_Lake_DSL_InputVer_toExpr___closed__6);
v___x_309_ = l_Lean_mkStrLit(v_rev_307_);
v___x_310_ = l_Lean_Expr_app___override(v___x_308_, v___x_309_);
return v___x_310_;
}
default: 
{
lean_object* v_ver_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_ver_311_ = lean_ctor_get(v_self_305_, 0);
lean_inc_ref(v_ver_311_);
lean_dec_ref_known(v_self_305_, 1);
v___x_312_ = lean_obj_once(&l_Lake_DSL_InputVer_toExpr___closed__9, &l_Lake_DSL_InputVer_toExpr___closed__9_once, _init_l_Lake_DSL_InputVer_toExpr___closed__9);
v___x_313_ = l_Lake_DSL_VerRange_toExpr(v_ver_311_);
v___x_314_ = l_Lean_Expr_app___override(v___x_312_, v___x_313_);
return v___x_314_;
}
}
}
}
static lean_object* _init_l_Lake_DSL_instToExprInputVer___closed__2(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
v___x_320_ = ((lean_object*)(l_Lake_DSL_instToExprInputVer___closed__1));
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprInputVer___closed__3(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Lake_DSL_instToExprInputVer___closed__2, &l_Lake_DSL_instToExprInputVer___closed__2_once, _init_l_Lake_DSL_instToExprInputVer___closed__2);
v___x_323_ = ((lean_object*)(l_Lake_DSL_instToExprInputVer___closed__0));
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprInputVer(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Lake_DSL_instToExprInputVer___closed__3, &l_Lake_DSL_instToExprInputVer___closed__3_once, _init_l_Lake_DSL_instToExprInputVer___closed__3);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toResultExpr___redArg(lean_object* v_inst_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_inst_326_);
v_a_328_ = lean_ctor_get(v_x_327_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v_x_327_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v_x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v_toExpr_336_; lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_toExpr_336_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toExpr_336_);
lean_dec_ref(v_inst_326_);
v_a_337_ = lean_ctor_get(v_x_327_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_345_ == 0)
{
v___x_339_ = v_x_327_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v_x_327_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_apply_1(v_toExpr_336_, v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toResultExpr(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_x_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lake_DSL_toResultExpr___redArg(v_inst_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(lean_object* v_resT_350_, lean_object* v_resE_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
uint8_t v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 1;
v___x_358_ = 1;
v___x_359_ = l_Lean_Meta_evalExpr___redArg(v_resT_350_, v_resE_351_, v___x_357_, v___x_358_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1___boxed(lean_object* v_resT_360_, lean_object* v_resE_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(v_resT_360_, v_resE_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(lean_object* v_msgData_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v_env_375_; lean_object* v___x_376_; lean_object* v_mctx_377_; lean_object* v_lctx_378_; lean_object* v_options_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_374_ = lean_st_ref_get(v___y_372_);
v_env_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc_ref(v_env_375_);
lean_dec(v___x_374_);
v___x_376_ = lean_st_ref_get(v___y_370_);
v_mctx_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_mctx_377_);
lean_dec(v___x_376_);
v_lctx_378_ = lean_ctor_get(v___y_369_, 2);
v_options_379_ = lean_ctor_get(v___y_371_, 2);
lean_inc_ref(v_options_379_);
lean_inc_ref(v_lctx_378_);
v___x_380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_380_, 0, v_env_375_);
lean_ctor_set(v___x_380_, 1, v_mctx_377_);
lean_ctor_set(v___x_380_, 2, v_lctx_378_);
lean_ctor_set(v___x_380_, 3, v_options_379_);
v___x_381_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_msgData_368_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0___boxed(lean_object* v_msgData_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(v_msgData_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(1);
v___x_391_ = l_Lean_MessageData_ofFormat(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__2));
v___x_396_ = l_Lean_MessageData_ofFormat(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3(lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
return v_x_397_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_422_; 
v_head_399_ = lean_ctor_get(v_x_398_, 0);
v_tail_400_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_422_ == 0)
{
v___x_402_ = v_x_398_;
v_isShared_403_ = v_isSharedCheck_422_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_tail_400_);
lean_inc(v_head_399_);
lean_dec(v_x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_422_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_before_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_420_; 
v_before_404_ = lean_ctor_get(v_head_399_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_head_399_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_head_399_, 1);
lean_dec(v_unused_421_);
v___x_406_ = v_head_399_;
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_before_404_);
lean_dec(v_head_399_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_420_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 7);
lean_ctor_set(v___x_406_, 1, v___x_408_);
lean_ctor_set(v___x_406_, 0, v_x_397_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_x_397_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_419_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 7);
lean_ctor_set(v___x_402_, 1, v___x_411_);
lean_ctor_set(v___x_402_, 0, v___x_410_);
v___x_413_ = v___x_402_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_418_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_MessageData_ofSyntax(v_before_404_);
v___x_415_ = l_Lean_indentD(v___x_414_);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_413_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v_x_397_ = v___x_416_;
v_x_398_ = v_tail_400_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(lean_object* v_opts_423_, lean_object* v_opt_424_){
_start:
{
lean_object* v_name_425_; lean_object* v_defValue_426_; lean_object* v_map_427_; lean_object* v___x_428_; 
v_name_425_ = lean_ctor_get(v_opt_424_, 0);
v_defValue_426_ = lean_ctor_get(v_opt_424_, 1);
v_map_427_ = lean_ctor_get(v_opts_423_, 0);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_427_, v_name_425_);
if (lean_obj_tag(v___x_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = lean_unbox(v_defValue_426_);
return v___x_429_;
}
else
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___x_428_, 1);
if (lean_obj_tag(v_val_430_) == 1)
{
uint8_t v_v_431_; 
v_v_431_ = lean_ctor_get_uint8(v_val_430_, 0);
lean_dec_ref_known(v_val_430_, 0);
return v_v_431_;
}
else
{
uint8_t v___x_432_; 
lean_dec(v_val_430_);
v___x_432_ = lean_unbox(v_defValue_426_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_433_, lean_object* v_opt_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(v_opts_433_, v_opt_434_);
lean_dec_ref(v_opt_434_);
lean_dec_ref(v_opts_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__1));
v___x_441_ = l_Lean_MessageData_ofFormat(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(lean_object* v_msgData_442_, lean_object* v_macroStack_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_options_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_options_446_ = lean_ctor_get(v___y_444_, 2);
v___x_447_ = l_Lean_Elab_pp_macroStack;
v___x_448_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(v_options_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_macroStack_443_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_msgData_442_);
return v___x_449_;
}
else
{
if (lean_obj_tag(v_macroStack_443_) == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_msgData_442_);
return v___x_450_;
}
else
{
lean_object* v_head_451_; lean_object* v_after_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_467_; 
v_head_451_ = lean_ctor_get(v_macroStack_443_, 0);
lean_inc(v_head_451_);
v_after_452_ = lean_ctor_get(v_head_451_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_head_451_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v_head_451_, 0);
lean_dec(v_unused_468_);
v___x_454_ = v_head_451_;
v_isShared_455_ = v_isSharedCheck_467_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_after_452_);
lean_dec(v_head_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_467_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 7);
lean_ctor_set(v___x_454_, 1, v___x_456_);
lean_ctor_set(v___x_454_, 0, v_msgData_442_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_msgData_442_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_466_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_msgData_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_MessageData_ofSyntax(v_after_452_);
v___x_462_ = l_Lean_indentD(v___x_461_);
v_msgData_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_463_, 0, v___x_460_);
lean_ctor_set(v_msgData_463_, 1, v___x_462_);
v___x_464_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3(v_msgData_463_, v_macroStack_443_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_469_, lean_object* v_macroStack_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_msgData_469_, v_macroStack_470_, v___y_471_);
lean_dec_ref(v___y_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_ref_482_; lean_object* v___x_483_; lean_object* v_a_484_; lean_object* v_macroStack_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_ref_482_ = lean_ctor_get(v___y_479_, 5);
v___x_483_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(v_msg_474_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
v_macroStack_485_ = lean_ctor_get(v___y_475_, 1);
v___x_486_ = l_Lean_Elab_getBetterRef(v_ref_482_, v_macroStack_485_);
lean_inc(v_macroStack_485_);
v___x_487_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_a_484_, v_macroStack_485_, v___y_479_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_486_);
lean_ctor_set(v___x_492_, 1, v_a_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 1);
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg___boxed(lean_object* v_msg_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v_msg_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_505_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_box(0);
v___x_513_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__3));
v___x_514_ = l_Lean_mkConst(v___x_513_, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4);
v___x_516_ = lean_unsigned_to_nat(2u);
v___x_517_ = lean_mk_empty_array_with_capacity(v___x_516_);
v___x_518_ = lean_array_push(v___x_517_, v___x_515_);
return v___x_518_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11));
v___x_530_ = l_String_toRawSubstring_x27(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
v___x_552_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21));
v___x_553_ = l_Lean_mkConst(v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22);
v___x_555_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5);
v___x_556_ = lean_array_push(v___x_555_, v___x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(lean_object* v_stx_563_, lean_object* v_expectedType_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__1));
v___x_573_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5);
v___x_574_ = lean_array_push(v___x_573_, v_expectedType_564_);
v___x_575_ = l_Lean_Meta_mkAppM(v___x_572_, v___x_574_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_638_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_638_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_638_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_638_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_ref_580_; lean_object* v_quotContext_581_; lean_object* v_currMacroScope_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v_ref_580_ = lean_ctor_get(v_a_569_, 5);
v_quotContext_581_ = lean_ctor_get(v_a_569_, 10);
v_currMacroScope_582_ = lean_ctor_get(v_a_569_, 11);
v___x_583_ = 0;
v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_580_, v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10));
v___x_586_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12);
v___x_587_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__13));
lean_inc(v_currMacroScope_582_);
lean_inc(v_quotContext_581_);
v___x_588_ = l_Lean_addMacroScope(v_quotContext_581_, v___x_587_, v_currMacroScope_582_);
v___x_589_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__17));
lean_inc_n(v___x_584_, 2);
v___x_590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_590_, 0, v___x_584_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
lean_ctor_set(v___x_590_, 2, v___x_588_);
lean_ctor_set(v___x_590_, 3, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__19));
v___x_592_ = l_Lean_Syntax_node1(v___x_584_, v___x_591_, v_stx_563_);
v___x_593_ = l_Lean_Syntax_node2(v___x_584_, v___x_585_, v___x_590_, v___x_592_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 1);
v___x_595_ = v___x_578_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_576_);
v___x_595_ = v_reuseFailAlloc_637_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = 1;
v___x_597_ = lean_box(0);
v___x_598_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_593_, v___x_595_, v___x_596_, v___x_596_, v___x_597_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23);
v___x_601_ = l_Lean_Meta_mkAppM(v___x_572_, v___x_600_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26));
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_array_push(v___x_605_, v_a_599_);
v___x_607_ = l_Lean_Meta_mkAppM(v___x_603_, v___x_606_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(v_a_602_, v_a_608_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_628_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_628_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_628_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_628_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
if (lean_obj_tag(v_a_610_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
lean_del_object(v___x_612_);
v_a_614_ = lean_ctor_get(v_a_610_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_616_ = v_a_610_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v_a_610_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 3);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = l_Lean_MessageData_ofFormat(v___x_619_);
v___x_621_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v___x_620_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; 
v_a_624_ = lean_ctor_get(v_a_610_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v_a_610_, 1);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_a_624_);
v___x_626_ = v___x_612_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_a_629_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_609_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_609_);
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
lean_dec(v_a_602_);
return v___x_607_;
}
}
else
{
lean_dec(v_a_599_);
return v___x_601_;
}
}
else
{
return v___x_598_;
}
}
}
}
else
{
lean_dec(v_stx_563_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___boxed(lean_object* v_stx_639_, lean_object* v_expectedType_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(v_stx_639_, v_expectedType_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0(lean_object* v_00_u03b1_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___boxed(lean_object* v_00_u03b1_659_, lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0(v_00_u03b1_659_, v_msg_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1(lean_object* v_msgData_669_, lean_object* v_macroStack_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_msgData_669_, v_macroStack_670_, v___y_675_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___boxed(lean_object* v_msgData_679_, lean_object* v_macroStack_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1(v_msgData_679_, v_macroStack_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_688_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__2));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__4));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion(lean_object* v_stx_700_, lean_object* v_expectedType_x3f_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1));
lean_inc(v_stx_700_);
v___x_710_ = l_Lean_Syntax_isOfKind(v_stx_700_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v_expectedType_x3f_701_);
lean_dec(v_stx_700_);
v___x_711_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3, &l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3);
v___x_712_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v___x_711_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
lean_inc(v_expectedType_x3f_701_);
v___x_713_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec_ref_known(v___x_713_, 1);
if (lean_obj_tag(v_expectedType_x3f_701_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; lean_object* v_v_716_; lean_object* v___x_717_; 
v_val_714_ = lean_ctor_get(v_expectedType_x3f_701_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_expectedType_x3f_701_, 1);
v___x_715_ = lean_unsigned_to_nat(1u);
v_v_716_ = l_Lean_Syntax_getArg(v_stx_700_, v___x_715_);
lean_dec(v_stx_700_);
v___x_717_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(v_v_716_, v_val_714_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v_expectedType_x3f_701_);
lean_dec(v_stx_700_);
v___x_718_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5, &l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5);
v___x_719_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v___x_718_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
return v___x_719_;
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_expectedType_x3f_701_);
lean_dec(v_stx_700_);
v_a_720_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_713_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_713_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___boxed(lean_object* v_stx_728_, lean_object* v_expectedType_x3f_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion(v_stx_728_, v_expectedType_x3f_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1(){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_766_ = l_Lean_Elab_Term_termElabAttribute;
v___x_767_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1));
v___x_768_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__10));
v___x_769_ = lean_alloc_closure((void*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___boxed), 9, 0);
v___x_770_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_766_, v___x_767_, v___x_768_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___boxed(lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1();
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit(lean_object* v_stx_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1));
lean_inc(v_stx_784_);
v___x_788_ = l_Lean_Syntax_isOfKind(v_stx_784_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_stx_784_);
v___x_789_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__2));
v___x_790_ = l_Lean_Macro_throwError___redArg(v___x_789_, v_a_785_, v_a_786_);
return v___x_790_;
}
else
{
lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_ref_791_ = lean_ctor_get(v_a_785_, 5);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = l_Lean_Syntax_getArg(v_stx_784_, v___x_792_);
lean_dec(v_stx_784_);
v___x_794_ = 0;
v___x_795_ = l_Lean_SourceInfo_fromRef(v_ref_791_, v___x_794_);
v___x_796_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1));
v___x_797_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__3));
lean_inc_n(v___x_795_, 3);
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__5));
v___x_800_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__6));
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_795_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_Syntax_node2(v___x_795_, v___x_799_, v___x_801_, v___x_793_);
v___x_803_ = l_Lean_Syntax_node2(v___x_795_, v___x_796_, v___x_798_, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_a_786_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___boxed(lean_object* v_stx_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit(v_stx_805_, v_a_806_, v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1(){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_814_ = l_Lean_Elab_macroAttribute;
v___x_815_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1));
v___x_816_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__1));
v___x_817_ = lean_alloc_closure((void*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___boxed), 3, 0);
v___x_818_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_814_, v___x_815_, v___x_816_, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___boxed(lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1();
return v_res_820_;
}
}
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_VerLit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_instToExprSemVerCore = _init_l_Lake_DSL_instToExprSemVerCore();
lean_mark_persistent(l_Lake_DSL_instToExprSemVerCore);
l_Lake_DSL_instToExprStdVer = _init_l_Lake_DSL_instToExprStdVer();
lean_mark_persistent(l_Lake_DSL_instToExprStdVer);
l_Lake_DSL_instToExprComparatorOp = _init_l_Lake_DSL_instToExprComparatorOp();
lean_mark_persistent(l_Lake_DSL_instToExprComparatorOp);
l_Lake_DSL_instToExprVerComparator = _init_l_Lake_DSL_instToExprVerComparator();
lean_mark_persistent(l_Lake_DSL_instToExprVerComparator);
l_Lake_DSL_instToExprVerRange = _init_l_Lake_DSL_instToExprVerRange();
lean_mark_persistent(l_Lake_DSL_instToExprVerRange);
l_Lake_DSL_instToExprInputVer = _init_l_Lake_DSL_instToExprInputVer();
lean_mark_persistent(l_Lake_DSL_instToExprInputVer);
res = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_VerLit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_VerLit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_VerLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_VerLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_VerLit(builtin);
}
#ifdef __cplusplus
}
#endif
