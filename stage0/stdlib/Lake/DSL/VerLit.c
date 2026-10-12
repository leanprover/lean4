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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lake_DSL_ComparatorOp_toExpr(uint8_t v_self_106_){
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
LEAN_EXPORT void l_Lake_DSL_ComparatorOp_toExpr_0interp(lean_interpreter_value* stack)
{
uint8_t v_self_106_ = stack[0].m_num;
lean_object* v_res_113_;
v_res_113_ = l_Lake_DSL_ComparatorOp_toExpr(v_self_106_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lake_DSL_ComparatorOp_toExpr___boxed(lean_object* v_self_114_){
_start:
{
uint8_t v_self_boxed_115_; lean_object* v_res_116_; 
v_self_boxed_115_ = lean_unbox(v_self_114_);
v_res_116_ = l_Lake_DSL_ComparatorOp_toExpr(v_self_boxed_115_);
return v_res_116_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprComparatorOp___closed__2(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_box(0);
v___x_122_ = ((lean_object*)(l_Lake_DSL_instToExprComparatorOp___closed__1));
v___x_123_ = l_Lean_mkConst(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprComparatorOp___closed__3(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l_Lake_DSL_instToExprComparatorOp___closed__2, &l_Lake_DSL_instToExprComparatorOp___closed__2_once, _init_l_Lake_DSL_instToExprComparatorOp___closed__2);
v___x_125_ = ((lean_object*)(l_Lake_DSL_instToExprComparatorOp___closed__0));
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprComparatorOp(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lake_DSL_instToExprComparatorOp___closed__3, &l_Lake_DSL_instToExprComparatorOp___closed__3_once, _init_l_Lake_DSL_instToExprComparatorOp___closed__3);
return v___x_127_;
}
}
static lean_object* _init_l_Lake_DSL_VerComparator_toExpr___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_box(0);
v___x_134_ = ((lean_object*)(l_Lake_DSL_VerComparator_toExpr___closed__1));
v___x_135_ = l_Lean_mkConst(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lake_DSL_VerComparator_toExpr___closed__6(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
v___x_142_ = ((lean_object*)(l_Lake_DSL_VerComparator_toExpr___closed__5));
v___x_143_ = l_Lean_mkConst(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Lake_DSL_VerComparator_toExpr___closed__9(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = ((lean_object*)(l_Lake_DSL_VerComparator_toExpr___closed__8));
v___x_150_ = l_Lean_mkConst(v___x_149_, v___x_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_VerComparator_toExpr(lean_object* v_self_151_){
_start:
{
lean_object* v_ver_152_; uint8_t v_op_153_; uint8_t v_includeSuffixes_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_ver_152_ = lean_ctor_get(v_self_151_, 0);
lean_inc_ref(v_ver_152_);
v_op_153_ = lean_ctor_get_uint8(v_self_151_, sizeof(void*)*1);
v_includeSuffixes_154_ = lean_ctor_get_uint8(v_self_151_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_151_);
v___x_155_ = lean_obj_once(&l_Lake_DSL_VerComparator_toExpr___closed__2, &l_Lake_DSL_VerComparator_toExpr___closed__2_once, _init_l_Lake_DSL_VerComparator_toExpr___closed__2);
v___x_156_ = l_Lake_DSL_StdVer_toExpr(v_ver_152_);
v___x_157_ = l_Lake_DSL_ComparatorOp_toExpr(v_op_153_);
if (v_includeSuffixes_154_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lake_DSL_VerComparator_toExpr___closed__6, &l_Lake_DSL_VerComparator_toExpr___closed__6_once, _init_l_Lake_DSL_VerComparator_toExpr___closed__6);
v___x_159_ = l_Lean_mkApp3(v___x_155_, v___x_156_, v___x_157_, v___x_158_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l_Lake_DSL_VerComparator_toExpr___closed__9, &l_Lake_DSL_VerComparator_toExpr___closed__9_once, _init_l_Lake_DSL_VerComparator_toExpr___closed__9);
v___x_161_ = l_Lean_mkApp3(v___x_155_, v___x_156_, v___x_157_, v___x_160_);
return v___x_161_;
}
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerComparator___closed__2(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_box(0);
v___x_167_ = ((lean_object*)(l_Lake_DSL_instToExprVerComparator___closed__1));
v___x_168_ = l_Lean_mkConst(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerComparator___closed__3(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_170_ = ((lean_object*)(l_Lake_DSL_instToExprVerComparator___closed__0));
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerComparator(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__3, &l_Lake_DSL_instToExprVerComparator___closed__3_once, _init_l_Lake_DSL_instToExprVerComparator___closed__3);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(lean_object* v_nilFn_173_, lean_object* v_consFn_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_dec_ref(v_consFn_174_);
lean_inc_ref(v_nilFn_173_);
return v_nilFn_173_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_head_176_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_head_176_);
v_tail_177_ = lean_ctor_get(v_x_175_, 1);
lean_inc(v_tail_177_);
lean_dec_ref_known(v_x_175_, 2);
v___x_178_ = l_Lake_DSL_VerComparator_toExpr(v_head_176_);
lean_inc_ref(v_consFn_174_);
v___x_179_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(v_nilFn_173_, v_consFn_174_, v_tail_177_);
v___x_180_ = l_Lean_mkAppB(v_consFn_174_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0___boxed(lean_object* v_nilFn_181_, lean_object* v_consFn_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(v_nilFn_181_, v_consFn_182_, v_x_183_);
lean_dec_ref(v_nilFn_181_);
return v_res_184_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_194_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__2));
v___x_195_ = l_Lean_mkConst(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_201_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__6));
v___x_202_ = l_Lean_mkConst(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8(void){
_start:
{
lean_object* v_type_203_; lean_object* v___x_204_; lean_object* v_nil_205_; 
v_type_203_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_204_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7);
v_nil_205_ = l_Lean_Expr_app___override(v___x_204_, v_type_203_);
return v_nil_205_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_211_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__10));
v___x_212_ = l_Lean_mkConst(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12(void){
_start:
{
lean_object* v_type_213_; lean_object* v___x_214_; lean_object* v_cons_215_; 
v_type_213_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_214_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11);
v_cons_215_ = l_Lean_Expr_app___override(v___x_214_, v_type_213_);
return v_cons_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(lean_object* v_nilFn_216_, lean_object* v_consFn_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_dec_ref(v_consFn_217_);
lean_inc_ref(v_nilFn_216_);
return v_nilFn_216_;
}
else
{
lean_object* v_head_219_; lean_object* v_tail_220_; lean_object* v_type_221_; lean_object* v___x_222_; lean_object* v_nil_223_; lean_object* v_cons_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_head_219_ = lean_ctor_get(v_x_218_, 0);
lean_inc(v_head_219_);
v_tail_220_ = lean_ctor_get(v_x_218_, 1);
lean_inc(v_tail_220_);
lean_dec_ref_known(v_x_218_, 2);
v_type_221_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_222_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4);
v_nil_223_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__8);
v_cons_224_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__12);
v___x_225_ = lean_array_to_list(v_head_219_);
v___x_226_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0_spec__0(v_nil_223_, v_cons_224_, v___x_225_);
v___x_227_ = l_Lean_mkAppB(v___x_222_, v_type_221_, v___x_226_);
lean_inc_ref(v_consFn_217_);
v___x_228_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(v_nilFn_216_, v_consFn_217_, v_tail_220_);
v___x_229_ = l_Lean_mkAppB(v_consFn_217_, v___x_227_, v___x_228_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___boxed(lean_object* v_nilFn_230_, lean_object* v_consFn_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(v_nilFn_230_, v_consFn_231_, v_x_232_);
lean_dec_ref(v_nilFn_230_);
return v_res_233_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__2(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_box(0);
v___x_240_ = ((lean_object*)(l_Lake_DSL_VerRange_toExpr___closed__1));
v___x_241_ = l_Lean_mkConst(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__5(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__3));
v___x_246_ = ((lean_object*)(l_Lake_DSL_VerRange_toExpr___closed__4));
v___x_247_ = l_Lean_mkConst(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__6(void){
_start:
{
lean_object* v_type_248_; lean_object* v___x_249_; lean_object* v_type_250_; 
v_type_248_ = lean_obj_once(&l_Lake_DSL_instToExprVerComparator___closed__2, &l_Lake_DSL_instToExprVerComparator___closed__2_once, _init_l_Lake_DSL_instToExprVerComparator___closed__2);
v___x_249_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__5, &l_Lake_DSL_VerRange_toExpr___closed__5_once, _init_l_Lake_DSL_VerRange_toExpr___closed__5);
v_type_250_ = l_Lean_Expr_app___override(v___x_249_, v_type_248_);
return v_type_250_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__7(void){
_start:
{
lean_object* v_type_251_; lean_object* v___x_252_; lean_object* v_nil_253_; 
v_type_251_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__6, &l_Lake_DSL_VerRange_toExpr___closed__6_once, _init_l_Lake_DSL_VerRange_toExpr___closed__6);
v___x_252_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__7);
v_nil_253_ = l_Lean_Expr_app___override(v___x_252_, v_type_251_);
return v_nil_253_;
}
}
static lean_object* _init_l_Lake_DSL_VerRange_toExpr___closed__8(void){
_start:
{
lean_object* v_type_254_; lean_object* v___x_255_; lean_object* v_cons_256_; 
v_type_254_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__6, &l_Lake_DSL_VerRange_toExpr___closed__6_once, _init_l_Lake_DSL_VerRange_toExpr___closed__6);
v___x_255_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__11);
v_cons_256_ = l_Lean_Expr_app___override(v___x_255_, v_type_254_);
return v_cons_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_VerRange_toExpr(lean_object* v_self_257_){
_start:
{
lean_object* v_toString_258_; lean_object* v_clauses_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_type_262_; lean_object* v___x_263_; lean_object* v_nil_264_; lean_object* v_cons_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_toString_258_ = lean_ctor_get(v_self_257_, 0);
lean_inc_ref(v_toString_258_);
v_clauses_259_ = lean_ctor_get(v_self_257_, 1);
lean_inc_ref(v_clauses_259_);
lean_dec_ref(v_self_257_);
v___x_260_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__2, &l_Lake_DSL_VerRange_toExpr___closed__2_once, _init_l_Lake_DSL_VerRange_toExpr___closed__2);
v___x_261_ = l_Lean_mkStrLit(v_toString_258_);
v_type_262_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__6, &l_Lake_DSL_VerRange_toExpr___closed__6_once, _init_l_Lake_DSL_VerRange_toExpr___closed__6);
v___x_263_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0___closed__4);
v_nil_264_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__7, &l_Lake_DSL_VerRange_toExpr___closed__7_once, _init_l_Lake_DSL_VerRange_toExpr___closed__7);
v_cons_265_ = lean_obj_once(&l_Lake_DSL_VerRange_toExpr___closed__8, &l_Lake_DSL_VerRange_toExpr___closed__8_once, _init_l_Lake_DSL_VerRange_toExpr___closed__8);
v___x_266_ = lean_array_to_list(v_clauses_259_);
v___x_267_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lake_DSL_VerRange_toExpr_spec__0(v_nil_264_, v_cons_265_, v___x_266_);
v___x_268_ = l_Lean_mkAppB(v___x_263_, v_type_262_, v___x_267_);
v___x_269_ = l_Lean_mkAppB(v___x_260_, v___x_261_, v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerRange___closed__2(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l_Lake_DSL_instToExprVerRange___closed__1));
v___x_276_ = l_Lean_mkConst(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerRange___closed__3(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_obj_once(&l_Lake_DSL_instToExprVerRange___closed__2, &l_Lake_DSL_instToExprVerRange___closed__2_once, _init_l_Lake_DSL_instToExprVerRange___closed__2);
v___x_278_ = ((lean_object*)(l_Lake_DSL_instToExprVerRange___closed__0));
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprVerRange(void){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lake_DSL_instToExprVerRange___closed__3, &l_Lake_DSL_instToExprVerRange___closed__3_once, _init_l_Lake_DSL_instToExprVerRange___closed__3);
return v___x_280_;
}
}
static lean_object* _init_l_Lake_DSL_InputVer_toExpr___closed__3(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_box(0);
v___x_288_ = ((lean_object*)(l_Lake_DSL_InputVer_toExpr___closed__2));
v___x_289_ = l_Lean_mkConst(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lake_DSL_InputVer_toExpr___closed__6(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
v___x_296_ = ((lean_object*)(l_Lake_DSL_InputVer_toExpr___closed__5));
v___x_297_ = l_Lean_mkConst(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lake_DSL_InputVer_toExpr___closed__9(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_box(0);
v___x_304_ = ((lean_object*)(l_Lake_DSL_InputVer_toExpr___closed__8));
v___x_305_ = l_Lean_mkConst(v___x_304_, v___x_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_InputVer_toExpr(lean_object* v_self_306_){
_start:
{
switch(lean_obj_tag(v_self_306_))
{
case 0:
{
lean_object* v___x_307_; 
v___x_307_ = lean_obj_once(&l_Lake_DSL_InputVer_toExpr___closed__3, &l_Lake_DSL_InputVer_toExpr___closed__3_once, _init_l_Lake_DSL_InputVer_toExpr___closed__3);
return v___x_307_;
}
case 1:
{
lean_object* v_rev_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_rev_308_ = lean_ctor_get(v_self_306_, 0);
lean_inc_ref(v_rev_308_);
lean_dec_ref_known(v_self_306_, 1);
v___x_309_ = lean_obj_once(&l_Lake_DSL_InputVer_toExpr___closed__6, &l_Lake_DSL_InputVer_toExpr___closed__6_once, _init_l_Lake_DSL_InputVer_toExpr___closed__6);
v___x_310_ = l_Lean_mkStrLit(v_rev_308_);
v___x_311_ = l_Lean_Expr_app___override(v___x_309_, v___x_310_);
return v___x_311_;
}
default: 
{
lean_object* v_ver_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_ver_312_ = lean_ctor_get(v_self_306_, 0);
lean_inc_ref(v_ver_312_);
lean_dec_ref_known(v_self_306_, 1);
v___x_313_ = lean_obj_once(&l_Lake_DSL_InputVer_toExpr___closed__9, &l_Lake_DSL_InputVer_toExpr___closed__9_once, _init_l_Lake_DSL_InputVer_toExpr___closed__9);
v___x_314_ = l_Lake_DSL_VerRange_toExpr(v_ver_312_);
v___x_315_ = l_Lean_Expr_app___override(v___x_313_, v___x_314_);
return v___x_315_;
}
}
}
}
static lean_object* _init_l_Lake_DSL_instToExprInputVer___closed__2(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_box(0);
v___x_321_ = ((lean_object*)(l_Lake_DSL_instToExprInputVer___closed__1));
v___x_322_ = l_Lean_mkConst(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprInputVer___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_Lake_DSL_instToExprInputVer___closed__2, &l_Lake_DSL_instToExprInputVer___closed__2_once, _init_l_Lake_DSL_instToExprInputVer___closed__2);
v___x_324_ = ((lean_object*)(l_Lake_DSL_instToExprInputVer___closed__0));
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lake_DSL_instToExprInputVer(void){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Lake_DSL_instToExprInputVer___closed__3, &l_Lake_DSL_instToExprInputVer___closed__3_once, _init_l_Lake_DSL_instToExprInputVer___closed__3);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toResultExpr___redArg(lean_object* v_inst_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_inst_327_);
v_a_329_ = lean_ctor_get(v_x_328_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v_x_328_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v_x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
else
{
lean_object* v_toExpr_337_; lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_346_; 
v_toExpr_337_ = lean_ctor_get(v_inst_327_, 0);
lean_inc_ref(v_toExpr_337_);
lean_dec_ref(v_inst_327_);
v_a_338_ = lean_ctor_get(v_x_328_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_346_ == 0)
{
v___x_340_ = v_x_328_;
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v_x_328_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_apply_1(v_toExpr_337_, v_a_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_toResultExpr(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lake_DSL_toResultExpr___redArg(v_inst_348_, v_x_349_);
return v___x_350_;
}
}
lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(lean_object* v_resT_351_, lean_object* v_resE_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
uint8_t v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_358_ = 1;
v___x_359_ = 1;
v___x_360_ = l_Lean_Meta_evalExpr___redArg(v_resT_351_, v_resE_352_, v___x_358_, v___x_359_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_360_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_resT_351_ = stack[0].m_obj;
lean_object* v_resE_352_ = stack[1].m_obj;
lean_object* v_a_353_ = stack[2].m_obj;
lean_object* v_a_354_ = stack[3].m_obj;
lean_object* v_a_355_ = stack[4].m_obj;
lean_object* v_a_356_ = stack[5].m_obj;
lean_object* v_res_361_;
v_res_361_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(v_resT_351_, v_resE_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1___boxed(lean_object* v_resT_362_, lean_object* v_resE_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_unsafe__1(v_resT_362_, v_resE_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_369_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(lean_object* v_msgData_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_env_377_; uint8_t v___x_378_; lean_object* v_env_379_; lean_object* v___x_380_; lean_object* v_toCold_381_; lean_object* v_mctx_382_; lean_object* v_lctx_383_; lean_object* v_options_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = 0;
v_env_379_ = l_Lean_Environment_setRecordingDeps(v_env_377_, v___x_378_);
v___x_380_ = lean_st_ref_get(v___y_372_);
v_toCold_381_ = lean_ctor_get(v___y_373_, 0);
v_mctx_382_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_mctx_382_);
lean_dec(v___x_380_);
v_lctx_383_ = lean_ctor_get(v___y_371_, 2);
v_options_384_ = lean_ctor_get(v_toCold_381_, 2);
lean_inc_ref(v_options_384_);
lean_inc_ref(v_lctx_383_);
v___x_385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_385_, 0, v_env_379_);
lean_ctor_set(v___x_385_, 1, v_mctx_382_);
lean_ctor_set(v___x_385_, 2, v_lctx_383_);
lean_ctor_set(v___x_385_, 3, v_options_384_);
v___x_386_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_msgData_370_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_370_ = stack[0].m_obj;
lean_object* v___y_371_ = stack[1].m_obj;
lean_object* v___y_372_ = stack[2].m_obj;
lean_object* v___y_373_ = stack[3].m_obj;
lean_object* v___y_374_ = stack[4].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(v_msgData_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0___boxed(lean_object* v_msgData_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(v_msgData_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_395_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_box(1);
v___x_397_ = l_Lean_MessageData_ofFormat(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__2));
v___x_402_ = l_Lean_MessageData_ofFormat(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
return v_x_403_;
}
else
{
lean_object* v_head_405_; lean_object* v_tail_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_428_; 
v_head_405_ = lean_ctor_get(v_x_404_, 0);
v_tail_406_ = lean_ctor_get(v_x_404_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_404_);
if (v_isSharedCheck_428_ == 0)
{
v___x_408_ = v_x_404_;
v_isShared_409_ = v_isSharedCheck_428_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_tail_406_);
lean_inc(v_head_405_);
lean_dec(v_x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_428_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_before_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_426_; 
v_before_410_ = lean_ctor_get(v_head_405_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_head_405_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_head_405_, 1);
lean_dec(v_unused_427_);
v___x_412_ = v_head_405_;
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_before_410_);
lean_dec(v_head_405_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 7);
lean_ctor_set(v___x_412_, 1, v___x_414_);
lean_ctor_set(v___x_412_, 0, v_x_403_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_x_403_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_414_);
v___x_416_ = v_reuseFailAlloc_425_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 7);
lean_ctor_set(v___x_408_, 1, v___x_417_);
lean_ctor_set(v___x_408_, 0, v___x_416_);
v___x_419_ = v___x_408_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_424_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_MessageData_ofSyntax(v_before_410_);
v___x_421_ = l_Lean_indentD(v___x_420_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v_x_403_ = v___x_422_;
v_x_404_ = v_tail_406_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(lean_object* v_opts_429_, lean_object* v_opt_430_){
_start:
{
lean_object* v_name_431_; lean_object* v_defValue_432_; lean_object* v_map_433_; lean_object* v___x_434_; 
v_name_431_ = lean_ctor_get(v_opt_430_, 0);
v_defValue_432_ = lean_ctor_get(v_opt_430_, 1);
v_map_433_ = lean_ctor_get(v_opts_429_, 0);
v___x_434_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_433_, v_name_431_);
if (lean_obj_tag(v___x_434_) == 0)
{
uint8_t v___x_435_; 
v___x_435_ = lean_unbox(v_defValue_432_);
return v___x_435_;
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_434_, 1);
if (lean_obj_tag(v_val_436_) == 1)
{
uint8_t v_v_437_; 
v_v_437_ = lean_ctor_get_uint8(v_val_436_, 0);
lean_dec_ref_known(v_val_436_, 0);
return v_v_437_;
}
else
{
uint8_t v___x_438_; 
lean_dec(v_val_436_);
v___x_438_ = lean_unbox(v_defValue_432_);
return v___x_438_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_429_ = stack[0].m_obj;
lean_object* v_opt_430_ = stack[1].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(v_opts_429_, v_opt_430_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_440_, lean_object* v_opt_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(v_opts_440_, v_opt_441_);
lean_dec_ref(v_opt_441_);
lean_dec_ref(v_opts_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__1));
v___x_448_ = l_Lean_MessageData_ofFormat(v___x_447_);
return v___x_448_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(lean_object* v_msgData_449_, lean_object* v_macroStack_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_451_);
v___x_454_ = l_Lean_Elab_pp_macroStack;
v___x_455_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__2(v___x_453_, v___x_454_);
lean_dec_ref(v___x_453_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v_macroStack_450_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v_msgData_449_);
return v___x_456_;
}
else
{
if (lean_obj_tag(v_macroStack_450_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_msgData_449_);
return v___x_457_;
}
else
{
lean_object* v_head_458_; lean_object* v_after_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_474_; 
v_head_458_ = lean_ctor_get(v_macroStack_450_, 0);
lean_inc(v_head_458_);
v_after_459_ = lean_ctor_get(v_head_458_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_head_458_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_head_458_, 0);
lean_dec(v_unused_475_);
v___x_461_ = v_head_458_;
v_isShared_462_ = v_isSharedCheck_474_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_after_459_);
lean_dec(v_head_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_474_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 7);
lean_ctor_set(v___x_461_, 1, v___x_463_);
lean_ctor_set(v___x_461_, 0, v_msgData_449_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_msgData_449_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_473_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_msgData_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_466_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___closed__2);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_MessageData_ofSyntax(v_after_459_);
v___x_469_ = l_Lean_indentD(v___x_468_);
v_msgData_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_470_, 0, v___x_467_);
lean_ctor_set(v_msgData_470_, 1, v___x_469_);
v___x_471_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_spec__3(v_msgData_470_, v_macroStack_450_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_449_ = stack[0].m_obj;
lean_object* v_macroStack_450_ = stack[1].m_obj;
lean_object* v___y_451_ = stack[2].m_obj;
lean_object* v_res_476_;
v_res_476_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_msgData_449_, v_macroStack_450_, v___y_451_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_477_, lean_object* v_macroStack_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_msgData_477_, v_macroStack_478_, v___y_479_);
lean_dec_ref(v___y_479_);
return v_res_481_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(lean_object* v_msg_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_ref_490_; lean_object* v_macroStack_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_ref_490_ = lean_ctor_get(v___y_487_, 2);
v_macroStack_491_ = lean_ctor_get(v___y_483_, 1);
v___x_492_ = l_Lean_Elab_getBetterRef(v_ref_490_, v_macroStack_491_);
v___x_493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__0(v_msg_482_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
lean_inc(v_macroStack_491_);
v___x_495_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_a_494_, v_macroStack_491_, v___y_487_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_492_);
lean_ctor_set(v___x_500_, 1, v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 1);
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_482_ = stack[0].m_obj;
lean_object* v___y_483_ = stack[1].m_obj;
lean_object* v___y_484_ = stack[2].m_obj;
lean_object* v___y_485_ = stack[3].m_obj;
lean_object* v___y_486_ = stack[4].m_obj;
lean_object* v___y_487_ = stack[5].m_obj;
lean_object* v___y_488_ = stack[6].m_obj;
lean_object* v_res_505_;
v_res_505_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v_msg_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
stack->m_obj
 = v_res_505_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg___boxed(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_514_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_box(0);
v___x_522_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__3));
v___x_523_ = l_Lean_mkConst(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__4);
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_array_push(v___x_526_, v___x_524_);
return v___x_527_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__11));
v___x_539_ = l_String_toRawSubstring_x27(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(0);
v___x_561_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__21));
v___x_562_ = l_Lean_mkConst(v___x_561_, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__22);
v___x_564_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5);
v___x_565_ = lean_array_push(v___x_564_, v___x_563_);
return v___x_565_;
}
}
lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(lean_object* v_stx_572_, lean_object* v_expectedType_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__1));
v___x_582_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__5);
v___x_583_ = lean_array_push(v___x_582_, v_expectedType_573_);
v___x_584_ = l_Lean_Meta_mkAppM(v___x_581_, v___x_583_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_toCold_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_649_; 
v_toCold_585_ = lean_ctor_get(v_a_578_, 0);
v_a_586_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_649_ == 0)
{
v___x_588_ = v___x_584_;
v_isShared_589_ = v_isSharedCheck_649_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_649_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_ref_590_; lean_object* v_quotContext_591_; lean_object* v_currMacroScope_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v_ref_590_ = lean_ctor_get(v_a_578_, 2);
v_quotContext_591_ = lean_ctor_get(v_toCold_585_, 8);
v_currMacroScope_592_ = lean_ctor_get(v_toCold_585_, 9);
v___x_593_ = 0;
v___x_594_ = l_Lean_SourceInfo_fromRef(v_ref_590_, v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__10));
v___x_596_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__12);
v___x_597_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__13));
lean_inc(v_currMacroScope_592_);
lean_inc(v_quotContext_591_);
v___x_598_ = l_Lean_addMacroScope(v_quotContext_591_, v___x_597_, v_currMacroScope_592_);
v___x_599_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__17));
lean_inc_n(v___x_594_, 2);
v___x_600_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_600_, 0, v___x_594_);
lean_ctor_set(v___x_600_, 1, v___x_596_);
lean_ctor_set(v___x_600_, 2, v___x_598_);
lean_ctor_set(v___x_600_, 3, v___x_599_);
v___x_601_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__19));
v___x_602_ = l_Lean_Syntax_node1(v___x_594_, v___x_601_, v_stx_572_);
v___x_603_ = l_Lean_Syntax_node2(v___x_594_, v___x_595_, v___x_600_, v___x_602_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
v___x_605_ = v___x_588_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_586_);
v___x_605_ = v_reuseFailAlloc_648_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = 1;
v___x_607_ = lean_box(0);
v___x_608_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_603_, v___x_605_, v___x_606_, v___x_606_, v___x_607_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23, &l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__23);
v___x_611_ = l_Lean_Meta_mkAppM(v___x_581_, v___x_610_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v___x_613_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___closed__26));
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_array_push(v___x_615_, v_a_609_);
v___x_617_ = l_Lean_Meta_mkAppM(v___x_613_, v___x_616_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; uint8_t v___x_619_; lean_object* v___x_620_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = 1;
v___x_620_ = l_Lean_Meta_evalExpr___redArg(v_a_612_, v_a_618_, v___x_619_, v___x_606_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_639_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_639_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_639_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_639_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
if (lean_obj_tag(v_a_621_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_634_; 
lean_del_object(v___x_623_);
v_a_625_ = lean_ctor_get(v_a_621_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_621_);
if (v_isSharedCheck_634_ == 0)
{
v___x_627_ = v_a_621_;
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v_a_621_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_634_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 3);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_633_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = l_Lean_MessageData_ofFormat(v___x_630_);
v___x_632_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v___x_631_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
return v___x_632_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; 
v_a_635_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v_a_621_, 1);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_a_635_);
v___x_637_ = v___x_623_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_620_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_620_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_dec(v_a_612_);
return v___x_617_;
}
}
else
{
lean_dec(v_a_609_);
return v___x_611_;
}
}
else
{
return v___x_608_;
}
}
}
}
else
{
lean_dec(v_stx_572_);
return v___x_584_;
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_572_ = stack[0].m_obj;
lean_object* v_expectedType_573_ = stack[1].m_obj;
lean_object* v_a_574_ = stack[2].m_obj;
lean_object* v_a_575_ = stack[3].m_obj;
lean_object* v_a_576_ = stack[4].m_obj;
lean_object* v_a_577_ = stack[5].m_obj;
lean_object* v_a_578_ = stack[6].m_obj;
lean_object* v_a_579_ = stack[7].m_obj;
lean_object* v_res_650_;
v_res_650_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(v_stx_572_, v_expectedType_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion___boxed(lean_object* v_stx_651_, lean_object* v_expectedType_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(v_stx_651_, v_expectedType_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
return v_res_660_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0(lean_object* v_00_u03b1_661_, lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_670_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_662_ = stack[1].m_obj;
lean_object* v___y_663_ = stack[2].m_obj;
lean_object* v___y_664_ = stack[3].m_obj;
lean_object* v___y_665_ = stack[4].m_obj;
lean_object* v___y_666_ = stack[5].m_obj;
lean_object* v___y_667_ = stack[6].m_obj;
lean_object* v___y_668_ = stack[7].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0(lean_box(0), v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___boxed(lean_object* v_00_u03b1_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0(v_00_u03b1_672_, v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_681_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1(lean_object* v_msgData_682_, lean_object* v_macroStack_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___redArg(v_msgData_682_, v_macroStack_683_, v___y_688_);
return v___x_691_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_682_ = stack[0].m_obj;
lean_object* v_macroStack_683_ = stack[1].m_obj;
lean_object* v___y_684_ = stack[2].m_obj;
lean_object* v___y_685_ = stack[3].m_obj;
lean_object* v___y_686_ = stack[4].m_obj;
lean_object* v___y_687_ = stack[5].m_obj;
lean_object* v___y_688_ = stack[6].m_obj;
lean_object* v___y_689_ = stack[7].m_obj;
lean_object* v_res_692_;
v_res_692_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1(v_msgData_682_, v_macroStack_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1___boxed(lean_object* v_msgData_693_, lean_object* v_macroStack_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0_spec__1(v_msgData_693_, v_macroStack_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__2));
v___x_710_ = l_Lean_stringToMessageData(v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__4));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion(lean_object* v_stx_714_, lean_object* v_expectedType_x3f_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1));
lean_inc(v_stx_714_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_stx_714_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v_expectedType_x3f_715_);
lean_dec(v_stx_714_);
v___x_725_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3, &l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__3);
v___x_726_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v___x_725_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v_v_728_; lean_object* v___x_729_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v_v_728_ = l_Lean_Syntax_getArg(v_stx_714_, v___x_727_);
lean_dec(v_stx_714_);
lean_inc(v_expectedType_x3f_715_);
v___x_729_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_dec_ref_known(v___x_729_, 1);
if (lean_obj_tag(v_expectedType_x3f_715_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_731_; 
v_val_730_ = lean_ctor_get(v_expectedType_x3f_715_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_expectedType_x3f_715_, 1);
v___x_731_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion(v_v_728_, v_val_730_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v_v_728_);
lean_dec(v_expectedType_x3f_715_);
v___x_732_ = lean_obj_once(&l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5, &l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5_once, _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__5);
v___x_733_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_evalDecodeVersion_spec__0___redArg(v___x_732_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_733_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_v_728_);
lean_dec(v_expectedType_x3f_715_);
v_a_734_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_729_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_714_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_715_ = stack[1].m_obj;
lean_object* v_a_716_ = stack[2].m_obj;
lean_object* v_a_717_ = stack[3].m_obj;
lean_object* v_a_718_ = stack[4].m_obj;
lean_object* v_a_719_ = stack[5].m_obj;
lean_object* v_a_720_ = stack[6].m_obj;
lean_object* v_a_721_ = stack[7].m_obj;
lean_object* v_res_742_;
v_res_742_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion(v_stx_714_, v_expectedType_x3f_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___boxed(lean_object* v_stx_743_, lean_object* v_expectedType_x3f_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion(v_stx_743_, v_expectedType_x3f_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_752_;
}
}
lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1(){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = l_Lean_Elab_Term_termElabAttribute;
v___x_782_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1));
v___x_783_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___closed__10));
v___x_784_ = lean_alloc_closure((void*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___boxed), 9, 0);
v___x_785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_781_, v___x_782_, v___x_783_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_786_;
v_res_786_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1();
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1___boxed(lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion__1();
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit(lean_object* v_stx_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1));
lean_inc(v_stx_800_);
v___x_804_ = l_Lean_Syntax_isOfKind(v_stx_800_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_stx_800_);
v___x_805_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__2));
v___x_806_ = l_Lean_Macro_throwError___redArg(v___x_805_, v_a_801_, v_a_802_);
return v___x_806_;
}
else
{
lean_object* v_ref_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_ref_807_ = lean_ctor_get(v_a_801_, 5);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = l_Lean_Syntax_getArg(v_stx_800_, v___x_808_);
lean_dec(v_stx_800_);
v___x_810_ = 0;
v___x_811_ = l_Lean_SourceInfo_fromRef(v_ref_807_, v___x_810_);
v___x_812_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabEvalVersion___closed__1));
v___x_813_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__3));
lean_inc_n(v___x_811_, 3);
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__5));
v___x_816_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__6));
v___x_817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_811_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_Syntax_node2(v___x_811_, v___x_815_, v___x_817_, v___x_809_);
v___x_819_ = l_Lean_Syntax_node2(v___x_811_, v___x_812_, v___x_814_, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_a_802_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___boxed(lean_object* v_stx_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit(v_stx_821_, v_a_822_, v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_824_;
}
}
lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1(){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_830_ = l_Lean_Elab_macroAttribute;
v___x_831_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___closed__1));
v___x_832_ = ((lean_object*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___closed__1));
v___x_833_ = lean_alloc_closure((void*)(l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___boxed), 3, 0);
v___x_834_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_830_, v___x_831_, v___x_832_, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_835_;
v_res_835_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1();
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1___boxed(lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_expandVerLit__1();
return v_res_837_;
}
}
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_VerLit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
