// Lean compiler output
// Module: Lean.Meta.Match.Basic
// Imports: public import Lean.Meta.Tactic.FVarSubst public import Lean.Meta.CollectFVars import Lean.Meta.Match.Value import Lean.Meta.AppBuilder import Lean.Meta.Match.NamedPatterns
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkInaccessible(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_inaccessible_x3f(lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instInhabitedPattern_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instInhabitedPattern_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedPattern_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedPattern_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedPattern_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedPattern;
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__1;
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__2 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__3;
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__4 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__5;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__6;
static const lean_string_object l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0_value)}};
static const lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__7 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__8;
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__9 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Match_Pattern_toMessageData___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__9_value)}};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__10 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__11;
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__12 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__13;
static const lean_string_object l_Lean_Meta_Match_Pattern_toMessageData___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__14 = (const lean_object*)&l_Lean_Meta_Match_Pattern_toMessageData___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Pattern_toMessageData___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedAltLHS_default = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedAltLHS = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltLHS_default___closed__0_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Match_instInhabitedAlt_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_instInhabitedAlt_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAlt_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedAlt_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAlt_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedAlt;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\n  | "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≋ "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":("};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Alt_toMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "|- "};
static const lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Alt_toMessageData___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_Alt_toMessageData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__1;
static const lean_string_object l_Lean_Meta_Match_Alt_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__2 = (const lean_object*)&l_Lean_Meta_Match_Alt_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Match_Alt_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__3;
static const lean_string_object l_Lean_Meta_Match_Alt_toMessageData___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__4 = (const lean_object*)&l_Lean_Meta_Match_Alt_toMessageData___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Match_Alt_toMessageData___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__5;
static const lean_string_object l_Lean_Meta_Match_Alt_toMessageData___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__6 = (const lean_object*)&l_Lean_Meta_Match_Alt_toMessageData___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_Alt_toMessageData___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Example_toMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Example_toMessageData___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_Example_toMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_Example_toMessageData___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__1 = (const lean_object*)&l_Lean_Meta_Match_Example_toMessageData___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Match_Example_toMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__2;
static lean_once_cell_t l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Example_toMessageData___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__3 = (const lean_object*)&l_Lean_Meta_Match_Example_toMessageData___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Match_Example_toMessageData___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_Example_toMessageData___closed__3_value)}};
static const lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__4 = (const lean_object*)&l_Lean_Meta_Match_Example_toMessageData___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Match_Example_toMessageData___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Example_toMessageData___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object*);
static const lean_ctor_object l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Match_instInhabitedProblem_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedProblem_default = (const lean_object*)&l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedProblem = (const lean_object*)&l_Lean_Meta_Match_instInhabitedProblem_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "remaining variables: "};
static const lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nalternatives:"};
static const lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nexamples:"};
static const lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_toPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unexpected pattern"};
static const lean_object* l_Lean_Meta_Match_toPattern___closed__0 = (const lean_object*)&l_Lean_Meta_Match_toPattern___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_toPattern___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_toPattern___closed__1;
static const lean_string_object l_Lean_Meta_Match_toPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected occurrence of auxiliary declaration 'namedPattern'"};
static const lean_object* l_Lean_Meta_Match_toPattern___closed__2 = (const lean_object*)&l_Lean_Meta_Match_toPattern___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Match_toPattern___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_toPattern___closed__3;
static lean_once_cell_t l_Lean_Meta_Match_toPattern___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_toPattern___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congr_eq"};
static const lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0 = (const lean_object*)&l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBase = (const lean_object*)&l_Lean_Meta_Match_congrEqnThmSuffixBase___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congr_eq_"};
static const lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0 = (const lean_object*)&l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix = (const lean_object*)&l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "congr_eq_1"};
static const lean_object* l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0 = (const lean_object*)&l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_congrEqn1ThmSuffix = (const lean_object*)&l_Lean_Meta_Match_congrEqn1ThmSuffix___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Match_Pattern_ctorIdx(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
switch(lean_obj_tag(v_t_10_))
{
case 1:
{
lean_object* v_fvarId_12_; lean_object* v___x_13_; 
v_fvarId_12_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_fvarId_12_);
lean_dec_ref_known(v_t_10_, 1);
v___x_13_ = lean_apply_1(v_k_11_, v_fvarId_12_);
return v___x_13_;
}
case 2:
{
lean_object* v_ctorName_14_; lean_object* v_us_15_; lean_object* v_params_16_; lean_object* v_fields_17_; lean_object* v___x_18_; 
v_ctorName_14_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_ctorName_14_);
v_us_15_ = lean_ctor_get(v_t_10_, 1);
lean_inc(v_us_15_);
v_params_16_ = lean_ctor_get(v_t_10_, 2);
lean_inc(v_params_16_);
v_fields_17_ = lean_ctor_get(v_t_10_, 3);
lean_inc(v_fields_17_);
lean_dec_ref_known(v_t_10_, 4);
v___x_18_ = lean_apply_4(v_k_11_, v_ctorName_14_, v_us_15_, v_params_16_, v_fields_17_);
return v___x_18_;
}
case 4:
{
lean_object* v_type_19_; lean_object* v_xs_20_; lean_object* v___x_21_; 
v_type_19_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_type_19_);
v_xs_20_ = lean_ctor_get(v_t_10_, 1);
lean_inc(v_xs_20_);
lean_dec_ref_known(v_t_10_, 2);
v___x_21_ = lean_apply_2(v_k_11_, v_type_19_, v_xs_20_);
return v___x_21_;
}
case 5:
{
lean_object* v_varId_22_; lean_object* v_p_23_; lean_object* v_hId_24_; lean_object* v___x_25_; 
v_varId_22_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_varId_22_);
v_p_23_ = lean_ctor_get(v_t_10_, 1);
lean_inc_ref(v_p_23_);
v_hId_24_ = lean_ctor_get(v_t_10_, 2);
lean_inc(v_hId_24_);
lean_dec_ref_known(v_t_10_, 3);
v___x_25_ = lean_apply_3(v_k_11_, v_varId_22_, v_p_23_, v_hId_24_);
return v___x_25_;
}
default: 
{
lean_object* v_e_26_; lean_object* v___x_27_; 
v_e_26_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_e_26_);
lean_dec_ref(v_t_10_);
v___x_27_ = lean_apply_1(v_k_11_, v_e_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim(lean_object* v_motive__1_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_30_, v_k_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___boxed(lean_object* v_motive__1_34_, lean_object* v_ctorIdx_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_k_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Match_Pattern_ctorElim(v_motive__1_34_, v_ctorIdx_35_, v_t_36_, v_h_37_, v_k_38_);
lean_dec(v_ctorIdx_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(lean_object* v_t_40_, lean_object* v_inaccessible_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_40_, v_inaccessible_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim(lean_object* v_motive__1_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_inaccessible_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_44_, v_inaccessible_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim___redArg(lean_object* v_t_48_, lean_object* v_var_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_48_, v_var_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim(lean_object* v_motive__1_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_var_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_52_, v_var_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim___redArg(lean_object* v_t_56_, lean_object* v_ctor_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_56_, v_ctor_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim(lean_object* v_motive__1_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_ctor_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_60_, v_ctor_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim___redArg(lean_object* v_t_64_, lean_object* v_val_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_64_, v_val_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim(lean_object* v_motive__1_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_val_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_68_, v_val_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(lean_object* v_t_72_, lean_object* v_arrayLit_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_72_, v_arrayLit_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim(lean_object* v_motive__1_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_arrayLit_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_76_, v_arrayLit_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim___redArg(lean_object* v_t_80_, lean_object* v_as_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_80_, v_as_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim(lean_object* v_motive__1_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_as_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_84_, v_as_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedPattern_default___closed__1));
v___x_93_ = l_Lean_Expr_const___override(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__3, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Match_instInhabitedPattern_default;
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__0));
v___x_100_ = l_Lean_stringToMessageData(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__2));
v___x_103_ = l_Lean_stringToMessageData(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__4));
v___x_106_ = l_Lean_stringToMessageData(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_Lean_MessageData_ofFormat(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1));
v___x_113_ = l_Lean_MessageData_ofFormat(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
return v_x_114_;
}
else
{
lean_object* v_head_116_; lean_object* v_tail_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_128_; 
v_head_116_ = lean_ctor_get(v_x_115_, 0);
v_tail_117_ = lean_ctor_get(v_x_115_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_128_ == 0)
{
v___x_119_ = v_x_115_;
v_isShared_120_ = v_isSharedCheck_128_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_tail_117_);
lean_inc(v_head_116_);
lean_dec(v_x_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_128_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2, &l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once, _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 7);
lean_ctor_set(v___x_119_, 1, v___x_121_);
lean_ctor_set(v___x_119_, 0, v_x_114_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_x_114_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_127_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_116_);
v___x_125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v_x_114_ = v___x_125_;
v_x_115_ = v_tail_117_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__7));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__10));
v___x_136_ = l_Lean_MessageData_ofFormat(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__12));
v___x_139_ = l_Lean_stringToMessageData(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__14));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object* v_x_143_){
_start:
{
switch(lean_obj_tag(v_x_143_))
{
case 0:
{
lean_object* v_e_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_e_144_ = lean_ctor_get(v_x_143_, 0);
lean_inc_ref(v_e_144_);
lean_dec_ref_known(v_x_143_, 1);
v___x_145_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__1, &l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1);
v___x_146_ = l_Lean_MessageData_ofExpr(v_e_144_);
v___x_147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
case 1:
{
lean_object* v_fvarId_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_fvarId_150_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_fvarId_150_);
lean_dec_ref_known(v_x_143_, 1);
v___x_151_ = l_Lean_mkFVar(v_fvarId_150_);
v___x_152_ = l_Lean_MessageData_ofExpr(v___x_151_);
return v___x_152_;
}
case 2:
{
lean_object* v_fields_153_; 
v_fields_153_ = lean_ctor_get(v_x_143_, 3);
if (lean_obj_tag(v_fields_153_) == 0)
{
lean_object* v_ctorName_154_; lean_object* v___x_155_; 
v_ctorName_154_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_ctorName_154_);
lean_dec_ref_known(v_x_143_, 4);
v___x_155_ = l_Lean_MessageData_ofName(v_ctorName_154_);
return v___x_155_;
}
else
{
lean_object* v_ctorName_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc(v_fields_153_);
v_ctorName_156_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_ctorName_156_);
lean_dec_ref_known(v_x_143_, 4);
v___x_157_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_158_ = l_Lean_MessageData_ofName(v_ctorName_156_);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_161_ = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(v___x_160_, v_fields_153_);
v___x_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_159_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
return v___x_164_;
}
}
case 3:
{
lean_object* v_e_165_; lean_object* v___x_166_; 
v_e_165_ = lean_ctor_get(v_x_143_, 0);
lean_inc_ref(v_e_165_);
lean_dec_ref_known(v_x_143_, 1);
v___x_166_ = l_Lean_MessageData_ofExpr(v_e_165_);
return v___x_166_;
}
case 4:
{
lean_object* v_xs_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_181_; 
v_xs_167_ = lean_ctor_get(v_x_143_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_x_143_, 0);
lean_dec(v_unused_182_);
v___x_169_ = v_x_143_;
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_xs_167_);
lean_dec(v_x_143_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_171_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__8, &l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8);
v___x_172_ = lean_box(0);
v___x_173_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(v_xs_167_, v___x_172_);
v___x_174_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_175_ = l_Lean_MessageData_joinSep(v___x_173_, v___x_174_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 7);
lean_ctor_set(v___x_169_, 1, v___x_175_);
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_177_ = v___x_169_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_180_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__13, &l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
}
}
default: 
{
lean_object* v_varId_183_; lean_object* v_p_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_varId_183_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_varId_183_);
v_p_184_ = lean_ctor_get(v_x_143_, 1);
lean_inc_ref(v_p_184_);
lean_dec_ref_known(v_x_143_, 3);
v___x_185_ = l_Lean_mkFVar(v_varId_183_);
v___x_186_ = l_Lean_MessageData_ofExpr(v___x_185_);
v___x_187_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__15, &l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15);
v___x_188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Lean_Meta_Match_Pattern_toMessageData(v_p_184_);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
if (lean_obj_tag(v_a_191_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = l_List_reverse___redArg(v_a_192_);
return v___x_193_;
}
else
{
lean_object* v_head_194_; lean_object* v_tail_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_head_194_ = lean_ctor_get(v_a_191_, 0);
v_tail_195_ = lean_ctor_get(v_a_191_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_a_191_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v_a_191_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_tail_195_);
lean_inc(v_head_194_);
lean_dec(v_a_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_194_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v_a_192_);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_a_192_);
v___x_201_ = v_reuseFailAlloc_203_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v_a_191_ = v_tail_195_;
v_a_192_ = v___x_201_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(uint8_t v_annotate_205_, lean_object* v_p_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
switch(lean_obj_tag(v_p_206_))
{
case 0:
{
if (v_annotate_205_ == 0)
{
lean_object* v_e_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_e_212_ = lean_ctor_get(v_p_206_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_p_206_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v_p_206_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_e_212_);
lean_dec(v_p_206_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_e_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_e_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_e_220_ = lean_ctor_get(v_p_206_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_p_206_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v_p_206_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_e_220_);
lean_dec(v_p_206_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = l_Lean_mkInaccessible(v_e_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_fvarId_229_ = lean_ctor_get(v_p_206_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_p_206_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v_p_206_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_fvarId_229_);
lean_dec(v_p_206_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = l_Lean_mkFVar(v_fvarId_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 0);
lean_ctor_set(v___x_231_, 0, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
case 2:
{
lean_object* v_ctorName_238_; lean_object* v_us_239_; lean_object* v_params_240_; lean_object* v_fields_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_ctorName_238_ = lean_ctor_get(v_p_206_, 0);
lean_inc(v_ctorName_238_);
v_us_239_ = lean_ctor_get(v_p_206_, 1);
lean_inc(v_us_239_);
v_params_240_ = lean_ctor_get(v_p_206_, 2);
lean_inc(v_params_240_);
v_fields_241_ = lean_ctor_get(v_p_206_, 3);
lean_inc(v_fields_241_);
lean_dec_ref_known(v_p_206_, 4);
v___x_242_ = lean_box(0);
v___x_243_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_205_, v_fields_241_, v___x_242_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_255_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_255_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_255_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_255_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_248_ = l_Lean_mkConst(v_ctorName_238_, v_us_239_);
v___x_249_ = l_List_appendTR___redArg(v_params_240_, v_a_244_);
v___x_250_ = lean_array_mk(v___x_249_);
v___x_251_ = l_Lean_mkAppN(v___x_248_, v___x_250_);
lean_dec_ref(v___x_250_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_251_);
v___x_253_ = v___x_246_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_params_240_);
lean_dec(v_us_239_);
lean_dec(v_ctorName_238_);
v_a_256_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_243_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_243_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
case 3:
{
lean_object* v_e_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_e_264_ = lean_ctor_get(v_p_206_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_p_206_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v_p_206_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_e_264_);
lean_dec(v_p_206_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 0);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_e_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
case 4:
{
lean_object* v_type_272_; lean_object* v_xs_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_type_272_ = lean_ctor_get(v_p_206_, 0);
lean_inc_ref(v_type_272_);
v_xs_273_ = lean_ctor_get(v_p_206_, 1);
lean_inc(v_xs_273_);
lean_dec_ref_known(v_p_206_, 2);
v___x_274_ = lean_box(0);
v___x_275_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_205_, v_xs_273_, v___x_274_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = l_Lean_Meta_mkArrayLit(v_type_272_, v_a_276_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_277_;
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_type_272_);
v_a_278_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_275_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
default: 
{
if (v_annotate_205_ == 0)
{
lean_object* v_p_286_; 
v_p_286_ = lean_ctor_get(v_p_206_, 1);
lean_inc_ref(v_p_286_);
lean_dec_ref_known(v_p_206_, 3);
v_p_206_ = v_p_286_;
goto _start;
}
else
{
lean_object* v_varId_288_; lean_object* v_p_289_; lean_object* v_hId_290_; lean_object* v___x_291_; 
v_varId_288_ = lean_ctor_get(v_p_206_, 0);
lean_inc(v_varId_288_);
v_p_289_ = lean_ctor_get(v_p_206_, 1);
lean_inc_ref(v_p_289_);
v_hId_290_ = lean_ctor_get(v_p_206_, 2);
lean_inc(v_hId_290_);
lean_dec_ref_known(v_p_206_, 3);
v___x_291_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_205_, v_p_289_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
v___x_293_ = l_Lean_mkFVar(v_varId_288_);
v___x_294_ = l_Lean_mkFVar(v_hId_290_);
v___x_295_ = l_Lean_Meta_Match_mkNamedPattern(v___x_293_, v___x_294_, v_a_292_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_295_;
}
else
{
lean_dec(v_hId_290_);
lean_dec(v_varId_288_);
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(uint8_t v_annotate_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = l_List_reverse___redArg(v_x_298_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v_head_306_; lean_object* v_tail_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_325_; 
v_head_306_ = lean_ctor_get(v_x_297_, 0);
v_tail_307_ = lean_ctor_get(v_x_297_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_325_ == 0)
{
v___x_309_ = v_x_297_;
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_tail_307_);
lean_inc(v_head_306_);
lean_dec(v_x_297_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_296_, v_head_306_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_x_298_);
lean_ctor_set(v___x_309_, 0, v_a_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_312_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_x_298_);
v___x_314_ = v_reuseFailAlloc_316_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
v_x_297_ = v_tail_307_;
v_x_298_ = v___x_314_;
goto _start;
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_del_object(v___x_309_);
lean_dec(v_tail_307_);
lean_dec(v_x_298_);
v_a_317_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_311_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_311_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(lean_object* v_annotate_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
uint8_t v_annotate_boxed_334_; lean_object* v_res_335_; 
v_annotate_boxed_334_ = lean_unbox(v_annotate_326_);
v_res_335_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_boxed_334_, v_x_327_, v_x_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object* v_annotate_336_, lean_object* v_p_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
uint8_t v_annotate_boxed_343_; lean_object* v_res_344_; 
v_annotate_boxed_343_ = lean_unbox(v_annotate_336_);
v_res_344_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_boxed_343_, v_p_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object* v_p_345_, uint8_t v_annotate_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_346_, v_p_345_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object* v_p_353_, lean_object* v_annotate_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
uint8_t v_annotate_boxed_360_; lean_object* v_res_361_; 
v_annotate_boxed_360_ = lean_unbox(v_annotate_354_);
v_res_361_ = l_Lean_Meta_Match_Pattern_toExpr(v_p_353_, v_annotate_boxed_360_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(lean_object* v_s_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
if (lean_obj_tag(v_a_363_) == 0)
{
lean_object* v___x_365_; 
lean_dec(v_s_362_);
v___x_365_ = l_List_reverse___redArg(v_a_364_);
return v___x_365_;
}
else
{
lean_object* v_head_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_376_; 
v_head_366_ = lean_ctor_get(v_a_363_, 0);
v_tail_367_ = lean_ctor_get(v_a_363_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_a_363_);
if (v_isSharedCheck_376_ == 0)
{
v___x_369_ = v_a_363_;
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_head_366_);
lean_dec(v_a_363_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
lean_inc(v_s_362_);
v___x_371_ = l_Lean_Meta_FVarSubst_apply(v_s_362_, v_head_366_);
lean_dec(v_head_366_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_a_364_);
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_a_364_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v_a_363_ = v_tail_367_;
v_a_364_ = v___x_373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object* v_s_377_, lean_object* v_x_378_){
_start:
{
switch(lean_obj_tag(v_x_378_))
{
case 0:
{
lean_object* v_e_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_387_; 
v_e_379_ = lean_ctor_get(v_x_378_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_387_ == 0)
{
v___x_381_ = v_x_378_;
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_e_379_);
lean_dec(v_x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = l_Lean_Meta_FVarSubst_apply(v_s_377_, v_e_379_);
lean_dec_ref(v_e_379_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
case 1:
{
lean_object* v_fvarId_388_; lean_object* v___x_389_; 
v_fvarId_388_ = lean_ctor_get(v_x_378_, 0);
v___x_389_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_377_, v_fvarId_388_);
lean_dec(v_s_377_);
if (lean_obj_tag(v___x_389_) == 0)
{
return v_x_378_;
}
else
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_x_378_, 0);
lean_dec(v_unused_398_);
v___x_391_ = v_x_378_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_x_378_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_val_393_; lean_object* v___x_395_; 
v_val_393_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v___x_389_, 1);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 0);
lean_ctor_set(v___x_391_, 0, v_val_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_val_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
case 2:
{
lean_object* v_ctorName_399_; lean_object* v_us_400_; lean_object* v_params_401_; lean_object* v_fields_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_412_; 
v_ctorName_399_ = lean_ctor_get(v_x_378_, 0);
v_us_400_ = lean_ctor_get(v_x_378_, 1);
v_params_401_ = lean_ctor_get(v_x_378_, 2);
v_fields_402_ = lean_ctor_get(v_x_378_, 3);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_412_ == 0)
{
v___x_404_ = v_x_378_;
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_fields_402_);
lean_inc(v_params_401_);
lean_inc(v_us_400_);
lean_inc(v_ctorName_399_);
lean_dec(v_x_378_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_406_ = lean_box(0);
lean_inc(v_s_377_);
v___x_407_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(v_s_377_, v_params_401_, v___x_406_);
v___x_408_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(v_s_377_, v_fields_402_, v___x_406_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 3, v___x_408_);
lean_ctor_set(v___x_404_, 2, v___x_407_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_ctorName_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_us_400_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
case 3:
{
lean_object* v_e_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_e_413_ = lean_ctor_get(v_x_378_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_x_378_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_e_413_);
lean_dec(v_x_378_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = l_Lean_Meta_FVarSubst_apply(v_s_377_, v_e_413_);
lean_dec_ref(v_e_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(3, 1, 0);
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
case 4:
{
lean_object* v_type_422_; lean_object* v_xs_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v_type_422_ = lean_ctor_get(v_x_378_, 0);
v_xs_423_ = lean_ctor_get(v_x_378_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_433_ == 0)
{
v___x_425_ = v_x_378_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_xs_423_);
lean_inc(v_type_422_);
lean_dec(v_x_378_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
lean_inc(v_s_377_);
v___x_427_ = l_Lean_Meta_FVarSubst_apply(v_s_377_, v_type_422_);
lean_dec_ref(v_type_422_);
v___x_428_ = lean_box(0);
v___x_429_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(v_s_377_, v_xs_423_, v___x_428_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_429_);
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
default: 
{
lean_object* v_varId_434_; lean_object* v_p_435_; lean_object* v_hId_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_varId_434_ = lean_ctor_get(v_x_378_, 0);
v_p_435_ = lean_ctor_get(v_x_378_, 1);
v_hId_436_ = lean_ctor_get(v_x_378_, 2);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_x_378_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_hId_436_);
lean_inc(v_p_435_);
lean_inc(v_varId_434_);
lean_dec(v_x_378_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_377_, v_varId_434_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_377_, v_p_435_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_varId_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_hId_436_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
else
{
lean_dec_ref_known(v___x_440_, 1);
lean_del_object(v___x_438_);
lean_dec(v_hId_436_);
lean_dec(v_varId_434_);
v_x_378_ = v_p_435_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(lean_object* v_s_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
if (lean_obj_tag(v_a_448_) == 0)
{
lean_object* v___x_450_; 
lean_dec(v_s_447_);
v___x_450_ = l_List_reverse___redArg(v_a_449_);
return v___x_450_;
}
else
{
lean_object* v_head_451_; lean_object* v_tail_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_461_; 
v_head_451_ = lean_ctor_get(v_a_448_, 0);
v_tail_452_ = lean_ctor_get(v_a_448_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_461_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_tail_452_);
lean_inc(v_head_451_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_s_447_);
v___x_456_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_447_, v_head_451_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v_a_449_);
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_a_449_);
v___x_458_ = v_reuseFailAlloc_460_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
v_a_448_ = v_tail_452_;
v_a_449_ = v___x_458_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object* v_fvarId_462_, lean_object* v_v_463_, lean_object* v_p_464_){
_start:
{
lean_object* v_s_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_s_465_ = lean_box(0);
v___x_466_ = l_Lean_Meta_FVarSubst_insert(v_s_465_, v_fvarId_462_, v_v_463_);
v___x_467_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v___x_466_, v_p_464_);
return v___x_467_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
else
{
lean_object* v_head_470_; lean_object* v_tail_471_; uint8_t v___x_472_; 
v_head_470_ = lean_ctor_get(v_x_468_, 0);
v_tail_471_ = lean_ctor_get(v_x_468_, 1);
v___x_472_ = l_Lean_Expr_hasExprMVar(v_head_470_);
if (v___x_472_ == 0)
{
v_x_468_ = v_tail_471_;
goto _start;
}
else
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0___boxed(lean_object* v_x_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_x_474_);
lean_dec(v_x_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object* v_x_477_){
_start:
{
switch(lean_obj_tag(v_x_477_))
{
case 0:
{
lean_object* v_e_478_; uint8_t v___x_479_; 
v_e_478_ = lean_ctor_get(v_x_477_, 0);
v___x_479_ = l_Lean_Expr_hasExprMVar(v_e_478_);
return v___x_479_;
}
case 2:
{
lean_object* v_params_480_; lean_object* v_fields_481_; uint8_t v___x_482_; 
v_params_480_ = lean_ctor_get(v_x_477_, 2);
v_fields_481_ = lean_ctor_get(v_x_477_, 3);
v___x_482_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_params_480_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_fields_481_);
return v___x_483_;
}
else
{
return v___x_482_;
}
}
case 3:
{
lean_object* v_e_484_; uint8_t v___x_485_; 
v_e_484_ = lean_ctor_get(v_x_477_, 0);
v___x_485_ = l_Lean_Expr_hasExprMVar(v_e_484_);
return v___x_485_;
}
case 5:
{
lean_object* v_p_486_; 
v_p_486_ = lean_ctor_get(v_x_477_, 1);
v_x_477_ = v_p_486_;
goto _start;
}
case 4:
{
lean_object* v_type_488_; lean_object* v_xs_489_; uint8_t v___x_490_; 
v_type_488_ = lean_ctor_get(v_x_477_, 0);
v_xs_489_ = lean_ctor_get(v_x_477_, 1);
v___x_490_ = l_Lean_Expr_hasExprMVar(v_type_488_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
v___x_491_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_xs_489_);
return v___x_491_;
}
else
{
return v___x_490_;
}
}
default: 
{
uint8_t v___x_492_; 
v___x_492_ = 0;
return v___x_492_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
uint8_t v___x_494_; 
v___x_494_ = 0;
return v___x_494_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; uint8_t v___x_497_; 
v_head_495_ = lean_ctor_get(v_x_493_, 0);
v_tail_496_ = lean_ctor_get(v_x_493_, 1);
v___x_497_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_head_495_);
if (v___x_497_ == 0)
{
v_x_493_ = v_tail_496_;
goto _start;
}
else
{
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1___boxed(lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_x_499_);
lean_dec(v_x_499_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object* v_x_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_502_);
lean_dec_ref(v_x_502_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object* v_as_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
if (lean_obj_tag(v_as_505_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
else
{
lean_object* v_head_514_; lean_object* v_tail_515_; lean_object* v___x_516_; 
v_head_514_ = lean_ctor_get(v_as_505_, 0);
lean_inc(v_head_514_);
v_tail_515_ = lean_ctor_get(v_as_505_, 1);
lean_inc(v_tail_515_);
lean_dec_ref_known(v_as_505_, 2);
v___x_516_ = l_Lean_Expr_collectFVars(v_head_514_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_dec_ref_known(v___x_516_, 1);
v_as_505_ = v_tail_515_;
goto _start;
}
else
{
lean_dec(v_tail_515_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object* v_as_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_as_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object* v_p_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
switch(lean_obj_tag(v_p_526_))
{
case 1:
{
lean_object* v_fvarId_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_fvarId_533_ = lean_ctor_get(v_p_526_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_p_526_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v_p_526_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_fvarId_533_);
lean_dec(v_p_526_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_537_ = lean_st_ref_take(v_a_527_);
v___x_538_ = l_Lean_CollectFVars_State_add(v___x_537_, v_fvarId_533_);
v___x_539_ = lean_st_ref_set(v_a_527_, v___x_538_);
v___x_540_ = lean_box(0);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 0);
lean_ctor_set(v___x_535_, 0, v___x_540_);
v___x_542_ = v___x_535_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
case 2:
{
lean_object* v_params_545_; lean_object* v_fields_546_; lean_object* v___x_547_; 
v_params_545_ = lean_ctor_get(v_p_526_, 2);
lean_inc(v_params_545_);
v_fields_546_ = lean_ctor_get(v_p_526_, 3);
lean_inc(v_fields_546_);
lean_dec_ref_known(v_p_526_, 4);
v___x_547_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_params_545_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_548_; 
lean_dec_ref_known(v___x_547_, 1);
v___x_548_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_fields_546_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
return v___x_548_;
}
else
{
lean_dec(v_fields_546_);
return v___x_547_;
}
}
case 4:
{
lean_object* v_type_549_; lean_object* v_xs_550_; lean_object* v___x_551_; 
v_type_549_ = lean_ctor_get(v_p_526_, 0);
lean_inc_ref(v_type_549_);
v_xs_550_ = lean_ctor_get(v_p_526_, 1);
lean_inc(v_xs_550_);
lean_dec_ref_known(v_p_526_, 2);
v___x_551_ = l_Lean_Expr_collectFVars(v_type_549_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_552_; 
lean_dec_ref_known(v___x_551_, 1);
v___x_552_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_xs_550_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
return v___x_552_;
}
else
{
lean_dec(v_xs_550_);
return v___x_551_;
}
}
case 5:
{
lean_object* v_varId_553_; lean_object* v_p_554_; lean_object* v_hId_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_varId_553_ = lean_ctor_get(v_p_526_, 0);
lean_inc(v_varId_553_);
v_p_554_ = lean_ctor_get(v_p_526_, 1);
lean_inc_ref(v_p_554_);
v_hId_555_ = lean_ctor_get(v_p_526_, 2);
lean_inc(v_hId_555_);
lean_dec_ref_known(v_p_526_, 3);
v___x_556_ = lean_st_ref_take(v_a_527_);
v___x_557_ = l_Lean_CollectFVars_State_add(v___x_556_, v_varId_553_);
v___x_558_ = l_Lean_CollectFVars_State_add(v___x_557_, v_hId_555_);
v___x_559_ = lean_st_ref_set(v_a_527_, v___x_558_);
v_p_526_ = v_p_554_;
goto _start;
}
default: 
{
lean_object* v_e_561_; lean_object* v___x_562_; 
v_e_561_ = lean_ctor_get(v_p_526_, 0);
lean_inc_ref(v_e_561_);
lean_dec_ref(v_p_526_);
v___x_562_ = l_Lean_Expr_collectFVars(v_e_561_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object* v_as_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
if (lean_obj_tag(v_as_563_) == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_head_572_; lean_object* v_tail_573_; lean_object* v___x_574_; 
v_head_572_ = lean_ctor_get(v_as_563_, 0);
lean_inc(v_head_572_);
v_tail_573_ = lean_ctor_get(v_as_563_, 1);
lean_inc(v_tail_573_);
lean_dec_ref_known(v_as_563_, 2);
v___x_574_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_572_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_dec_ref_known(v___x_574_, 1);
v_as_563_ = v_tail_573_;
goto _start;
}
else
{
lean_dec(v_tail_573_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object* v_as_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_as_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object* v_p_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_Match_Pattern_collectFVars(v_p_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object* v_e_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_Expr_hasMVar(v_e_592_);
v___x_596_ = lean_bool_not(v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v_mctx_598_; lean_object* v___x_599_; lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_602_; lean_object* v_cache_603_; lean_object* v_zetaDeltaFVarIds_604_; lean_object* v_postponed_605_; lean_object* v_diag_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v___x_597_ = lean_st_ref_get(v___y_593_);
v_mctx_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_mctx_598_);
lean_dec(v___x_597_);
v___x_599_ = l_Lean_instantiateMVarsCore(v_mctx_598_, v_e_592_);
v_fst_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_fst_600_);
v_snd_601_ = lean_ctor_get(v___x_599_, 1);
lean_inc(v_snd_601_);
lean_dec_ref(v___x_599_);
v___x_602_ = lean_st_ref_take(v___y_593_);
v_cache_603_ = lean_ctor_get(v___x_602_, 1);
v_zetaDeltaFVarIds_604_ = lean_ctor_get(v___x_602_, 2);
v_postponed_605_ = lean_ctor_get(v___x_602_, 3);
v_diag_606_ = lean_ctor_get(v___x_602_, 4);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_602_, 0);
lean_dec(v_unused_616_);
v___x_608_ = v___x_602_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_diag_606_);
lean_inc(v_postponed_605_);
lean_inc(v_zetaDeltaFVarIds_604_);
lean_inc(v_cache_603_);
lean_dec(v___x_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_snd_601_);
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_snd_601_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_cache_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_zetaDeltaFVarIds_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_postponed_605_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_diag_606_);
v___x_611_ = v_reuseFailAlloc_614_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_st_ref_set(v___y_593_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_fst_600_);
return v___x_613_;
}
}
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_e_592_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object* v_e_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_618_, v___y_619_);
lean_dec(v___y_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object* v_e_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_622_, v___y_624_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object* v_e_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(v_e_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = l_List_reverse___redArg(v_x_637_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v_head_645_; lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_656_; 
v_head_645_ = lean_ctor_get(v_x_636_, 0);
v_tail_646_ = lean_ctor_get(v_x_636_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_656_ == 0)
{
v___x_648_ = v_x_636_;
v_isShared_649_ = v_isSharedCheck_656_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_inc(v_head_645_);
lean_dec(v_x_636_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_656_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v___x_653_; 
v___x_650_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_645_, v___y_639_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_x_637_);
lean_ctor_set(v___x_648_, 0, v_a_651_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_651_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_x_637_);
v___x_653_ = v_reuseFailAlloc_655_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v_x_636_ = v_tail_646_;
v_x_637_ = v___x_653_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_x_657_, v_x_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* v_x_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
switch(lean_obj_tag(v_x_665_))
{
case 0:
{
lean_object* v_e_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_695_; 
v_e_671_ = lean_ctor_get(v_x_665_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_695_ == 0)
{
v___x_673_ = v_x_665_;
v_isShared_674_ = v_isSharedCheck_695_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_e_671_);
lean_dec(v_x_665_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_695_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_671_, v_a_667_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_686_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_686_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_a_676_);
v___x_681_ = v___x_673_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
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
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_del_object(v___x_673_);
v_a_687_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_675_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_675_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
case 3:
{
lean_object* v_e_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_720_; 
v_e_696_ = lean_ctor_get(v_x_665_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_720_ == 0)
{
v___x_698_ = v_x_665_;
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_e_696_);
lean_dec(v_x_665_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_696_, v_a_667_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_711_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_a_701_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_del_object(v___x_698_);
v_a_712_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_700_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_700_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
case 2:
{
lean_object* v_ctorName_721_; lean_object* v_us_722_; lean_object* v_params_723_; lean_object* v_fields_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_759_; 
v_ctorName_721_ = lean_ctor_get(v_x_665_, 0);
v_us_722_ = lean_ctor_get(v_x_665_, 1);
v_params_723_ = lean_ctor_get(v_x_665_, 2);
v_fields_724_ = lean_ctor_get(v_x_665_, 3);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_759_ == 0)
{
v___x_726_ = v_x_665_;
v_isShared_727_ = v_isSharedCheck_759_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_fields_724_);
lean_inc(v_params_723_);
lean_inc(v_us_722_);
lean_inc(v_ctorName_721_);
lean_dec(v_x_665_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_759_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_box(0);
v___x_729_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_params_723_, v___x_728_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_fields_724_, v___x_728_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_742_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_742_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 3, v_a_732_);
lean_ctor_set(v___x_726_, 2, v_a_730_);
v___x_737_ = v___x_726_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_ctorName_721_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_us_722_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_a_730_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_a_732_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_737_);
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
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
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_a_730_);
lean_del_object(v___x_726_);
lean_dec(v_us_722_);
lean_dec(v_ctorName_721_);
v_a_743_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_731_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_731_);
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
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_del_object(v___x_726_);
lean_dec(v_fields_724_);
lean_dec(v_us_722_);
lean_dec(v_ctorName_721_);
v_a_751_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_729_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_729_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
case 5:
{
lean_object* v_varId_760_; lean_object* v_p_761_; lean_object* v_hId_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_778_; 
v_varId_760_ = lean_ctor_get(v_x_665_, 0);
v_p_761_ = lean_ctor_get(v_x_665_, 1);
v_hId_762_ = lean_ctor_get(v_x_665_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_778_ == 0)
{
v___x_764_ = v_x_665_;
v_isShared_765_ = v_isSharedCheck_778_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_hId_762_);
lean_inc(v_p_761_);
lean_inc(v_varId_760_);
lean_dec(v_x_665_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_778_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_Match_instantiatePatternMVars(v_p_761_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_777_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_777_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_777_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v_a_767_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_varId_760_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_a_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_hId_762_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_del_object(v___x_764_);
lean_dec(v_hId_762_);
lean_dec(v_varId_760_);
return v___x_766_;
}
}
}
case 4:
{
lean_object* v_type_779_; lean_object* v_xs_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_815_; 
v_type_779_ = lean_ctor_get(v_x_665_, 0);
v_xs_780_ = lean_ctor_get(v_x_665_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_815_ == 0)
{
v___x_782_ = v_x_665_;
v_isShared_783_ = v_isSharedCheck_815_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_xs_780_);
lean_inc(v_type_779_);
lean_dec(v_x_665_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_815_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_779_, v_a_667_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___x_786_ = lean_box(0);
v___x_787_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_xs_780_, v___x_786_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_798_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_798_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_a_788_);
lean_ctor_set(v___x_782_, 0, v_a_785_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_785_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_a_788_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_785_);
lean_del_object(v___x_782_);
v_a_799_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_787_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_787_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_del_object(v___x_782_);
lean_dec(v_xs_780_);
v_a_807_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_784_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_784_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
default: 
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v_x_665_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = l_List_reverse___redArg(v_x_818_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_head_826_; lean_object* v_tail_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_845_; 
v_head_826_ = lean_ctor_get(v_x_817_, 0);
v_tail_827_ = lean_ctor_get(v_x_817_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_x_817_);
if (v_isSharedCheck_845_ == 0)
{
v___x_829_ = v_x_817_;
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_tail_827_);
lean_inc(v_head_826_);
lean_dec(v_x_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Match_instantiatePatternMVars(v_head_826_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v_x_818_);
lean_ctor_set(v___x_829_, 0, v_a_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_832_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_x_818_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v_x_817_ = v_tail_827_;
v_x_818_ = v___x_834_;
goto _start;
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_829_);
lean_dec(v_tail_827_);
lean_dec(v_x_818_);
v_a_837_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_831_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_831_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_x_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* v_x_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_Match_instantiatePatternMVars(v_x_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object* v_as_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
if (lean_obj_tag(v_as_866_) == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
else
{
lean_object* v_head_875_; lean_object* v_tail_876_; lean_object* v___x_877_; 
v_head_875_ = lean_ctor_get(v_as_866_, 0);
lean_inc(v_head_875_);
v_tail_876_ = lean_ctor_get(v_as_866_, 1);
lean_inc(v_tail_876_);
lean_dec_ref_known(v_as_866_, 2);
v___x_877_ = l_Lean_LocalDecl_collectFVars(v_head_875_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_dec_ref_known(v___x_877_, 1);
v_as_866_ = v_tail_876_;
goto _start;
}
else
{
lean_dec(v_tail_876_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object* v_as_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_as_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object* v_as_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
if (lean_obj_tag(v_as_887_) == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_box(0);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v___x_898_; 
v_head_896_ = lean_ctor_get(v_as_887_, 0);
lean_inc(v_head_896_);
v_tail_897_ = lean_ctor_get(v_as_887_, 1);
lean_inc(v_tail_897_);
lean_dec_ref_known(v_as_887_, 2);
v___x_898_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_896_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_dec_ref_known(v___x_898_, 1);
v_as_887_ = v_tail_897_;
goto _start;
}
else
{
lean_dec(v_tail_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object* v_as_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_as_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* v_altLHS_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_fvarDecls_915_; lean_object* v_patterns_916_; lean_object* v___x_917_; 
v_fvarDecls_915_ = lean_ctor_get(v_altLHS_908_, 1);
lean_inc(v_fvarDecls_915_);
v_patterns_916_ = lean_ctor_get(v_altLHS_908_, 2);
lean_inc(v_patterns_916_);
lean_dec_ref(v_altLHS_908_);
v___x_917_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_fvarDecls_915_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_patterns_916_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
return v___x_918_;
}
else
{
lean_dec(v_patterns_916_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* v_altLHS_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Match_AltLHS_collectFVars(v_altLHS_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object* v_localDecl_927_, lean_object* v___y_928_){
_start:
{
if (lean_obj_tag(v_localDecl_927_) == 0)
{
lean_object* v_index_930_; lean_object* v_fvarId_931_; lean_object* v_userName_932_; lean_object* v_type_933_; uint8_t v_bi_934_; uint8_t v_kind_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_951_; 
v_index_930_ = lean_ctor_get(v_localDecl_927_, 0);
v_fvarId_931_ = lean_ctor_get(v_localDecl_927_, 1);
v_userName_932_ = lean_ctor_get(v_localDecl_927_, 2);
v_type_933_ = lean_ctor_get(v_localDecl_927_, 3);
v_bi_934_ = lean_ctor_get_uint8(v_localDecl_927_, sizeof(void*)*4);
v_kind_935_ = lean_ctor_get_uint8(v_localDecl_927_, sizeof(void*)*4 + 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_localDecl_927_);
if (v_isSharedCheck_951_ == 0)
{
v___x_937_ = v_localDecl_927_;
v_isShared_938_ = v_isSharedCheck_951_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_type_933_);
lean_inc(v_userName_932_);
lean_inc(v_fvarId_931_);
lean_inc(v_index_930_);
lean_dec(v_localDecl_927_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_951_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
v___x_939_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_933_, v___y_928_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_950_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 3, v_a_940_);
v___x_945_ = v___x_937_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_index_930_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_fvarId_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_userName_932_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_a_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_949_, sizeof(void*)*4, v_bi_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_949_, sizeof(void*)*4 + 1, v_kind_935_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
else
{
lean_object* v_index_952_; lean_object* v_fvarId_953_; lean_object* v_userName_954_; lean_object* v_type_955_; lean_object* v_value_956_; uint8_t v_nondep_957_; uint8_t v_kind_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_976_; 
v_index_952_ = lean_ctor_get(v_localDecl_927_, 0);
v_fvarId_953_ = lean_ctor_get(v_localDecl_927_, 1);
v_userName_954_ = lean_ctor_get(v_localDecl_927_, 2);
v_type_955_ = lean_ctor_get(v_localDecl_927_, 3);
v_value_956_ = lean_ctor_get(v_localDecl_927_, 4);
v_nondep_957_ = lean_ctor_get_uint8(v_localDecl_927_, sizeof(void*)*5);
v_kind_958_ = lean_ctor_get_uint8(v_localDecl_927_, sizeof(void*)*5 + 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_localDecl_927_);
if (v_isSharedCheck_976_ == 0)
{
v___x_960_ = v_localDecl_927_;
v_isShared_961_ = v_isSharedCheck_976_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_value_956_);
lean_inc(v_type_955_);
lean_inc(v_userName_954_);
lean_inc(v_fvarId_953_);
lean_inc(v_index_952_);
lean_dec(v_localDecl_927_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_976_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_975_; 
v___x_962_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_955_, v___y_928_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_962_);
v___x_964_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_956_, v___y_928_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v_a_965_);
lean_ctor_set(v___x_960_, 3, v_a_963_);
v___x_970_ = v___x_960_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_index_952_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_fvarId_953_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_userName_954_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_a_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_a_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*5, v_nondep_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*5 + 1, v_kind_958_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_970_);
v___x_972_ = v___x_967_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object* v_localDecl_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_977_, v___y_978_);
lean_dec(v___y_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l_List_reverse___redArg(v_x_982_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v_head_990_; lean_object* v_tail_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1009_; 
v_head_990_ = lean_ctor_get(v_x_981_, 0);
v_tail_991_ = lean_ctor_get(v_x_981_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_993_ = v_x_981_;
v_isShared_994_ = v_isSharedCheck_1009_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_tail_991_);
lean_inc(v_head_990_);
lean_dec(v_x_981_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1009_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_990_, v___y_984_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_x_982_);
lean_ctor_set(v___x_993_, 0, v_a_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_996_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_x_982_);
v___x_998_ = v_reuseFailAlloc_1000_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v_x_981_ = v_tail_991_;
v_x_982_ = v___x_998_;
goto _start;
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_del_object(v___x_993_);
lean_dec(v_tail_991_);
lean_dec(v_x_982_);
v_a_1001_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_995_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_995_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_x_1010_, v_x_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* v_altLHS_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_ref_1024_; lean_object* v_fvarDecls_1025_; lean_object* v_patterns_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1061_; 
v_ref_1024_ = lean_ctor_get(v_altLHS_1018_, 0);
v_fvarDecls_1025_ = lean_ctor_get(v_altLHS_1018_, 1);
v_patterns_1026_ = lean_ctor_get(v_altLHS_1018_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_altLHS_1018_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1028_ = v_altLHS_1018_;
v_isShared_1029_ = v_isSharedCheck_1061_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_patterns_1026_);
lean_inc(v_fvarDecls_1025_);
lean_inc(v_ref_1024_);
lean_dec(v_altLHS_1018_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1061_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_fvarDecls_1025_, v___x_1030_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_patterns_1026_, v___x_1030_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1044_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 2, v_a_1034_);
lean_ctor_set(v___x_1028_, 1, v_a_1032_);
v___x_1039_ = v___x_1028_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_ref_1024_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_a_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_a_1032_);
lean_del_object(v___x_1028_);
lean_dec(v_ref_1024_);
v_a_1045_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1033_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1033_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_del_object(v___x_1028_);
lean_dec(v_patterns_1026_);
lean_dec(v_ref_1024_);
v_a_1053_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1031_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1031_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* v_altLHS_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_Match_instantiateAltLHSMVars(v_altLHS_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object* v_localDecl_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_1069_, v___y_1071_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object* v_localDecl_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(v_localDecl_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
return v_res_1082_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0));
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
lean_ctor_set(v___x_1090_, 2, v___x_1087_);
lean_ctor_set(v___x_1090_, 3, v___x_1086_);
lean_ctor_set(v___x_1090_, 4, v___x_1086_);
lean_ctor_set(v___x_1090_, 5, v___x_1086_);
lean_ctor_set(v___x_1090_, 6, v___x_1085_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default(void){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedAlt_default___closed__1, &l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt(void){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Meta_Match_instInhabitedAlt_default;
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object* v_msgData_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_env_1100_; lean_object* v___x_1101_; lean_object* v_mctx_1102_; lean_object* v_lctx_1103_; lean_object* v_options_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1099_ = lean_st_ref_get(v___y_1097_);
v_env_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc_ref(v_env_1100_);
lean_dec(v___x_1099_);
v___x_1101_ = lean_st_ref_get(v___y_1095_);
v_mctx_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_mctx_1102_);
lean_dec(v___x_1101_);
v_lctx_1103_ = lean_ctor_get(v___y_1094_, 2);
v_options_1104_ = lean_ctor_get(v___y_1096_, 2);
lean_inc_ref(v_options_1104_);
lean_inc_ref(v_lctx_1103_);
v___x_1105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1105_, 0, v_env_1100_);
lean_ctor_set(v___x_1105_, 1, v_mctx_1102_);
lean_ctor_set(v___x_1105_, 2, v_lctx_1103_);
lean_ctor_set(v___x_1105_, 3, v_options_1104_);
v___x_1106_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v_msgData_1093_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object* v_msgData_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msgData_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(lean_object* v_decls_1115_, lean_object* v_x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1115_, v_x_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1122_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1122_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(lean_object* v_decls_1139_, lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1139_, v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object* v_00_u03b1_1147_, lean_object* v_decls_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1148_, v_x_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_decls_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(v_00_u03b1_1156_, v_decls_1157_, v_x_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(lean_object* v_as_x27_1171_, lean_object* v_b_1172_){
_start:
{
if (lean_obj_tag(v_as_x27_1171_) == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_b_1172_);
return v___x_1174_;
}
else
{
lean_object* v_head_1175_; lean_object* v_tail_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_head_1175_ = lean_ctor_get(v_as_x27_1171_, 0);
v_tail_1176_ = lean_ctor_get(v_as_x27_1171_, 1);
v_fst_1177_ = lean_ctor_get(v_head_1175_, 0);
v_snd_1178_ = lean_ctor_get(v_head_1175_, 1);
v___x_1179_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_b_1172_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
lean_inc(v_fst_1177_);
v___x_1181_ = l_Lean_MessageData_ofExpr(v_fst_1177_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_inc(v_snd_1178_);
v___x_1185_ = l_Lean_MessageData_ofExpr(v_snd_1178_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v_as_x27_1171_ = v_tail_1176_;
v_b_1172_ = v___x_1186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(lean_object* v_as_x27_1188_, lean_object* v_b_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1188_, v_b_1189_);
lean_dec(v_as_x27_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object* v_cnstrs_1192_, lean_object* v_msg_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v_a_1200_; lean_object* v___x_1201_; 
v___x_1199_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_cnstrs_1192_, v_msg_1193_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_a_1200_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object* v_cnstrs_1202_, lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(v_cnstrs_1202_, v_msg_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v_cnstrs_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
if (lean_obj_tag(v_a_1210_) == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = l_List_reverse___redArg(v_a_1211_);
return v___x_1212_;
}
else
{
lean_object* v_head_1213_; lean_object* v_tail_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_head_1213_ = lean_ctor_get(v_a_1210_, 0);
v_tail_1214_ = lean_ctor_get(v_a_1210_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1216_ = v_a_1210_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_tail_1214_);
lean_inc(v_head_1213_);
lean_dec(v_a_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_a_1211_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_head_1213_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_a_1211_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v_a_1210_ = v_tail_1214_;
v_a_1211_ = v___x_1219_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = l_List_reverse___redArg(v_a_1227_);
return v___x_1228_;
}
else
{
lean_object* v_head_1229_; lean_object* v_tail_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1247_; 
v_head_1229_ = lean_ctor_get(v_a_1226_, 0);
v_tail_1230_ = lean_ctor_get(v_a_1226_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1232_ = v_a_1226_;
v_isShared_1233_ = v_isSharedCheck_1247_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_tail_1230_);
lean_inc(v_head_1229_);
lean_dec(v_a_1226_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1247_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_inc(v_head_1229_);
v___x_1234_ = l_Lean_LocalDecl_toExpr(v_head_1229_);
v___x_1235_ = l_Lean_MessageData_ofExpr(v___x_1234_);
v___x_1236_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_LocalDecl_type(v_head_1229_);
lean_dec(v_head_1229_);
v___x_1239_ = l_Lean_MessageData_ofExpr(v___x_1238_);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v_a_1227_);
lean_ctor_set(v___x_1232_, 0, v___x_1242_);
v___x_1244_ = v___x_1232_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_a_1227_);
v___x_1244_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
v_a_1226_ = v_tail_1230_;
v_a_1227_ = v___x_1244_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__0));
v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__2));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__4));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__6));
v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object* v_alt_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_rhs_1266_; lean_object* v_fvarDecls_1267_; lean_object* v_patterns_1268_; lean_object* v_cnstrs_1269_; lean_object* v___y_1271_; uint8_t v___x_1285_; 
v_rhs_1266_ = lean_ctor_get(v_alt_1260_, 2);
lean_inc_ref(v_rhs_1266_);
v_fvarDecls_1267_ = lean_ctor_get(v_alt_1260_, 3);
lean_inc(v_fvarDecls_1267_);
v_patterns_1268_ = lean_ctor_get(v_alt_1260_, 4);
lean_inc(v_patterns_1268_);
v_cnstrs_1269_ = lean_ctor_get(v_alt_1260_, 5);
lean_inc(v_cnstrs_1269_);
lean_dec_ref(v_alt_1260_);
v___x_1285_ = l_List_isEmpty___redArg(v_fvarDecls_1267_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1286_ = lean_box(0);
lean_inc(v_fvarDecls_1267_);
v___x_1287_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(v_fvarDecls_1267_, v___x_1286_);
v___x_1288_ = l_Lean_MessageData_ofList(v___x_1287_);
v___x_1289_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___y_1271_ = v___x_1290_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__7, &l_Lean_Meta_Match_Alt_toMessageData___closed__7_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7);
v___y_1271_ = v___x_1291_;
goto v___jp_1270_;
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_msg_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; 
v___x_1272_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__1, &l_Lean_Meta_Match_Alt_toMessageData___closed__1_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1);
v___x_1273_ = lean_box(0);
v___x_1274_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(v_patterns_1268_, v___x_1273_);
v___x_1275_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v___x_1274_, v___x_1273_);
v___x_1276_ = l_Lean_MessageData_ofList(v___x_1275_);
v___x_1277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1272_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__3, &l_Lean_Meta_Match_Alt_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_MessageData_ofExpr(v_rhs_1266_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v_msg_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_1282_, 0, v___y_1271_);
lean_ctor_set(v_msg_1282_, 1, v___x_1281_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1283_, 0, v_cnstrs_1269_);
lean_closure_set(v___f_1283_, 1, v_msg_1282_);
v___x_1284_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_fvarDecls_1267_, v___f_1283_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object* v_alt_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Meta_Match_Alt_toMessageData(v_alt_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object* v_as_1299_, lean_object* v_as_x27_1300_, lean_object* v_b_1301_, lean_object* v_a_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1300_, v_b_1301_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(lean_object* v_as_1309_, lean_object* v_as_x27_1310_, lean_object* v_b_1311_, lean_object* v_a_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(v_as_1309_, v_as_x27_1310_, v_b_1311_, v_a_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v_as_x27_1310_);
lean_dec(v_as_1309_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object* v_s_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
if (lean_obj_tag(v_a_1320_) == 0)
{
lean_object* v___x_1322_; 
lean_dec(v_s_1319_);
v___x_1322_ = l_List_reverse___redArg(v_a_1321_);
return v___x_1322_;
}
else
{
lean_object* v_head_1323_; lean_object* v_tail_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1333_; 
v_head_1323_ = lean_ctor_get(v_a_1320_, 0);
v_tail_1324_ = lean_ctor_get(v_a_1320_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1326_ = v_a_1320_;
v_isShared_1327_ = v_isSharedCheck_1333_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_tail_1324_);
lean_inc(v_head_1323_);
lean_dec(v_a_1320_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1333_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_inc(v_s_1319_);
v___x_1328_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_1319_, v_head_1323_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_a_1321_);
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_a_1321_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
v_a_1320_ = v_tail_1324_;
v_a_1321_ = v___x_1330_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object* v_s_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
if (lean_obj_tag(v_a_1335_) == 0)
{
lean_object* v___x_1337_; 
lean_dec(v_s_1334_);
v___x_1337_ = l_List_reverse___redArg(v_a_1336_);
return v___x_1337_;
}
else
{
lean_object* v_head_1338_; lean_object* v_tail_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
v_head_1338_ = lean_ctor_get(v_a_1335_, 0);
v_tail_1339_ = lean_ctor_get(v_a_1335_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_a_1335_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1341_ = v_a_1335_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_tail_1339_);
lean_inc(v_head_1338_);
lean_dec(v_a_1335_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
lean_inc(v_s_1334_);
v___x_1343_ = l_Lean_LocalDecl_applyFVarSubst(v_s_1334_, v_head_1338_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_a_1336_);
lean_ctor_set(v___x_1341_, 0, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_a_1336_);
v___x_1345_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
v_a_1335_ = v_tail_1339_;
v_a_1336_ = v___x_1345_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object* v_s_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
if (lean_obj_tag(v_a_1350_) == 0)
{
lean_object* v___x_1352_; 
lean_dec(v_s_1349_);
v___x_1352_ = l_List_reverse___redArg(v_a_1351_);
return v___x_1352_;
}
else
{
lean_object* v_head_1353_; lean_object* v_tail_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1373_; 
v_head_1353_ = lean_ctor_get(v_a_1350_, 0);
v_tail_1354_ = lean_ctor_get(v_a_1350_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1356_ = v_a_1350_;
v_isShared_1357_ = v_isSharedCheck_1373_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_tail_1354_);
lean_inc(v_head_1353_);
lean_dec(v_a_1350_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1373_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1372_; 
v_fst_1358_ = lean_ctor_get(v_head_1353_, 0);
v_snd_1359_ = lean_ctor_get(v_head_1353_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_head_1353_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1361_ = v_head_1353_;
v_isShared_1362_ = v_isSharedCheck_1372_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_inc(v_fst_1358_);
lean_dec(v_head_1353_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1372_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_inc_n(v_s_1349_, 2);
v___x_1363_ = l_Lean_Meta_FVarSubst_apply(v_s_1349_, v_fst_1358_);
lean_dec(v_fst_1358_);
v___x_1364_ = l_Lean_Meta_FVarSubst_apply(v_s_1349_, v_snd_1359_);
lean_dec(v_snd_1359_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1364_);
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_a_1351_);
lean_ctor_set(v___x_1356_, 0, v___x_1366_);
v___x_1368_ = v___x_1356_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1351_);
v___x_1368_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
v_a_1350_ = v_tail_1354_;
v_a_1351_ = v___x_1368_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object* v_s_1374_, lean_object* v_alt_1375_){
_start:
{
lean_object* v_ref_1376_; lean_object* v_idx_1377_; lean_object* v_rhs_1378_; lean_object* v_fvarDecls_1379_; lean_object* v_patterns_1380_; lean_object* v_cnstrs_1381_; lean_object* v_notAltIdxs_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1394_; 
v_ref_1376_ = lean_ctor_get(v_alt_1375_, 0);
v_idx_1377_ = lean_ctor_get(v_alt_1375_, 1);
v_rhs_1378_ = lean_ctor_get(v_alt_1375_, 2);
v_fvarDecls_1379_ = lean_ctor_get(v_alt_1375_, 3);
v_patterns_1380_ = lean_ctor_get(v_alt_1375_, 4);
v_cnstrs_1381_ = lean_ctor_get(v_alt_1375_, 5);
v_notAltIdxs_1382_ = lean_ctor_get(v_alt_1375_, 6);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_alt_1375_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1384_ = v_alt_1375_;
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_notAltIdxs_1382_);
lean_inc(v_cnstrs_1381_);
lean_inc(v_patterns_1380_);
lean_inc(v_fvarDecls_1379_);
lean_inc(v_rhs_1378_);
lean_inc(v_idx_1377_);
lean_inc(v_ref_1376_);
lean_dec(v_alt_1375_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_inc_n(v_s_1374_, 3);
v___x_1386_ = l_Lean_Meta_FVarSubst_apply(v_s_1374_, v_rhs_1378_);
lean_dec_ref(v_rhs_1378_);
v___x_1387_ = lean_box(0);
v___x_1388_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(v_s_1374_, v_fvarDecls_1379_, v___x_1387_);
v___x_1389_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(v_s_1374_, v_patterns_1380_, v___x_1387_);
v___x_1390_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(v_s_1374_, v_cnstrs_1381_, v___x_1387_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 5, v___x_1390_);
lean_ctor_set(v___x_1384_, 4, v___x_1389_);
lean_ctor_set(v___x_1384_, 3, v___x_1388_);
lean_ctor_set(v___x_1384_, 2, v___x_1386_);
v___x_1392_ = v___x_1384_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_ref_1376_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_idx_1377_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1393_, 5, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1393_, 6, v_notAltIdxs_1382_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object* v_fvarId_1395_, lean_object* v_v_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
if (lean_obj_tag(v_a_1397_) == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref(v_v_1396_);
lean_dec(v_fvarId_1395_);
v___x_1399_ = l_List_reverse___redArg(v_a_1398_);
return v___x_1399_;
}
else
{
lean_object* v_head_1400_; lean_object* v_tail_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1410_; 
v_head_1400_ = lean_ctor_get(v_a_1397_, 0);
v_tail_1401_ = lean_ctor_get(v_a_1397_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1403_ = v_a_1397_;
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_tail_1401_);
lean_inc(v_head_1400_);
lean_dec(v_a_1397_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_inc_ref(v_v_1396_);
lean_inc(v_fvarId_1395_);
v___x_1405_ = l_Lean_Meta_Match_Pattern_replaceFVarId(v_fvarId_1395_, v_v_1396_, v_head_1400_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v_a_1398_);
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1398_);
v___x_1407_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
v_a_1397_ = v_tail_1401_;
v_a_1398_ = v___x_1407_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object* v_fvarId_1411_, lean_object* v_v_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
if (lean_obj_tag(v_a_1413_) == 0)
{
lean_object* v___x_1415_; 
lean_dec(v_fvarId_1411_);
v___x_1415_ = l_List_reverse___redArg(v_a_1414_);
return v___x_1415_;
}
else
{
lean_object* v_head_1416_; lean_object* v_tail_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1426_; 
v_head_1416_ = lean_ctor_get(v_a_1413_, 0);
v_tail_1417_ = lean_ctor_get(v_a_1413_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_a_1413_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1419_ = v_a_1413_;
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_tail_1417_);
lean_inc(v_head_1416_);
lean_dec(v_a_1413_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
lean_inc(v_fvarId_1411_);
v___x_1421_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_1411_, v_v_1412_, v_head_1416_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_a_1414_);
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_a_1414_);
v___x_1423_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
v_a_1413_ = v_tail_1417_;
v_a_1414_ = v___x_1423_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_1427_, lean_object* v_v_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1427_, v_v_1428_, v_a_1429_, v_a_1430_);
lean_dec_ref(v_v_1428_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object* v_fvarId_1432_, lean_object* v_v_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
if (lean_obj_tag(v_a_1434_) == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_fvarId_1432_);
v___x_1436_ = l_List_reverse___redArg(v_a_1435_);
return v___x_1436_;
}
else
{
lean_object* v_head_1437_; lean_object* v_tail_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1457_; 
v_head_1437_ = lean_ctor_get(v_a_1434_, 0);
v_tail_1438_ = lean_ctor_get(v_a_1434_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1434_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1440_ = v_a_1434_;
v_isShared_1441_ = v_isSharedCheck_1457_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_tail_1438_);
lean_inc(v_head_1437_);
lean_dec(v_a_1434_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1457_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_fst_1442_; lean_object* v_snd_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1456_; 
v_fst_1442_ = lean_ctor_get(v_head_1437_, 0);
v_snd_1443_ = lean_ctor_get(v_head_1437_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_head_1437_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1445_ = v_head_1437_;
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_snd_1443_);
lean_inc(v_fst_1442_);
lean_dec(v_head_1437_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_inc_n(v_fvarId_1432_, 2);
v___x_1447_ = l_Lean_Expr_replaceFVarId(v_fst_1442_, v_fvarId_1432_, v_v_1433_);
lean_dec(v_fst_1442_);
v___x_1448_ = l_Lean_Expr_replaceFVarId(v_snd_1443_, v_fvarId_1432_, v_v_1433_);
lean_dec(v_snd_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v___x_1448_);
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1450_ = v___x_1445_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v_a_1435_);
lean_ctor_set(v___x_1440_, 0, v___x_1450_);
v___x_1452_ = v___x_1440_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_a_1435_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_a_1434_ = v_tail_1438_;
v_a_1435_ = v___x_1452_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object* v_fvarId_1458_, lean_object* v_v_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1458_, v_v_1459_, v_a_1460_, v_a_1461_);
lean_dec_ref(v_v_1459_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object* v_fvarId_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
if (lean_obj_tag(v_a_1464_) == 0)
{
lean_object* v___x_1466_; 
v___x_1466_ = l_List_reverse___redArg(v_a_1465_);
return v___x_1466_;
}
else
{
lean_object* v_head_1467_; lean_object* v_tail_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1480_; 
v_head_1467_ = lean_ctor_get(v_a_1464_, 0);
v_tail_1468_ = lean_ctor_get(v_a_1464_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1464_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1470_ = v_a_1464_;
v_isShared_1471_ = v_isSharedCheck_1480_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_tail_1468_);
lean_inc(v_head_1467_);
lean_dec(v_a_1464_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1480_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = l_Lean_LocalDecl_fvarId(v_head_1467_);
v___x_1473_ = l_Lean_instBEqFVarId_beq(v___x_1472_, v_fvarId_1463_);
lean_dec(v___x_1472_);
v___x_1474_ = lean_bool_not(v___x_1473_);
if (v___x_1474_ == 0)
{
lean_del_object(v___x_1470_);
lean_dec(v_head_1467_);
v_a_1464_ = v_tail_1468_;
goto _start;
}
else
{
lean_object* v___x_1477_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v_a_1465_);
v___x_1477_ = v___x_1470_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_head_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1465_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v_a_1464_ = v_tail_1468_;
v_a_1465_ = v___x_1477_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_fvarId_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object* v_fvarId_1485_, lean_object* v_v_1486_, lean_object* v_alt_1487_){
_start:
{
lean_object* v_ref_1488_; lean_object* v_idx_1489_; lean_object* v_rhs_1490_; lean_object* v_fvarDecls_1491_; lean_object* v_patterns_1492_; lean_object* v_cnstrs_1493_; lean_object* v_notAltIdxs_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1507_; 
v_ref_1488_ = lean_ctor_get(v_alt_1487_, 0);
v_idx_1489_ = lean_ctor_get(v_alt_1487_, 1);
v_rhs_1490_ = lean_ctor_get(v_alt_1487_, 2);
v_fvarDecls_1491_ = lean_ctor_get(v_alt_1487_, 3);
v_patterns_1492_ = lean_ctor_get(v_alt_1487_, 4);
v_cnstrs_1493_ = lean_ctor_get(v_alt_1487_, 5);
v_notAltIdxs_1494_ = lean_ctor_get(v_alt_1487_, 6);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_alt_1487_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1496_ = v_alt_1487_;
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_notAltIdxs_1494_);
lean_inc(v_cnstrs_1493_);
lean_inc(v_patterns_1492_);
lean_inc(v_fvarDecls_1491_);
lean_inc(v_rhs_1490_);
lean_inc(v_idx_1489_);
lean_inc(v_ref_1488_);
lean_dec(v_alt_1487_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_decls_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_inc_n(v_fvarId_1485_, 3);
v___x_1498_ = l_Lean_Expr_replaceFVarId(v_rhs_1490_, v_fvarId_1485_, v_v_1486_);
lean_dec_ref(v_rhs_1490_);
v___x_1499_ = lean_box(0);
v_decls_1500_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1485_, v_fvarDecls_1491_, v___x_1499_);
v___x_1501_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1485_, v_v_1486_, v_decls_1500_, v___x_1499_);
lean_inc_ref(v_v_1486_);
v___x_1502_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(v_fvarId_1485_, v_v_1486_, v_patterns_1492_, v___x_1499_);
v___x_1503_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1485_, v_v_1486_, v_cnstrs_1493_, v___x_1499_);
lean_dec_ref(v_v_1486_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 5, v___x_1503_);
lean_ctor_set(v___x_1496_, 4, v___x_1502_);
lean_ctor_set(v___x_1496_, 3, v___x_1501_);
lean_ctor_set(v___x_1496_, 2, v___x_1498_);
v___x_1505_ = v___x_1496_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_ref_1488_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_idx_1489_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1506_, 5, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_notAltIdxs_1494_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(lean_object* v_fvarId_1508_, lean_object* v_x_1509_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
else
{
lean_object* v_head_1511_; lean_object* v_tail_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_head_1511_ = lean_ctor_get(v_x_1509_, 0);
v_tail_1512_ = lean_ctor_get(v_x_1509_, 1);
v___x_1513_ = l_Lean_LocalDecl_fvarId(v_head_1511_);
v___x_1514_ = l_Lean_instBEqFVarId_beq(v___x_1513_, v_fvarId_1508_);
lean_dec(v___x_1513_);
if (v___x_1514_ == 0)
{
v_x_1509_ = v_tail_1512_;
goto _start;
}
else
{
return v___x_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(lean_object* v_fvarId_1516_, lean_object* v_x_1517_){
_start:
{
uint8_t v_res_1518_; lean_object* v_r_1519_; 
v_res_1518_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1516_, v_x_1517_);
lean_dec(v_x_1517_);
lean_dec(v_fvarId_1516_);
v_r_1519_ = lean_box(v_res_1518_);
return v_r_1519_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object* v_fvarId_1520_, lean_object* v_alt_1521_){
_start:
{
lean_object* v_fvarDecls_1522_; uint8_t v___x_1523_; 
v_fvarDecls_1522_ = lean_ctor_get(v_alt_1521_, 3);
v___x_1523_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1520_, v_fvarDecls_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object* v_fvarId_1524_, lean_object* v_alt_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_1524_, v_alt_1525_);
lean_dec_ref(v_alt_1525_);
lean_dec(v_fvarId_1524_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx(lean_object* v_x_1528_){
_start:
{
switch(lean_obj_tag(v_x_1528_))
{
case 0:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_unsigned_to_nat(0u);
return v___x_1529_;
}
case 1:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_unsigned_to_nat(1u);
return v___x_1530_;
}
case 2:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(2u);
return v___x_1531_;
}
case 3:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_unsigned_to_nat(3u);
return v___x_1532_;
}
default: 
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(4u);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___boxed(lean_object* v_x_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Meta_Match_Example_ctorIdx(v_x_1534_);
lean_dec(v_x_1534_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object* v_t_1536_, lean_object* v_k_1537_){
_start:
{
switch(lean_obj_tag(v_t_1536_))
{
case 1:
{
return v_k_1537_;
}
case 2:
{
lean_object* v_a_1538_; lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1538_ = lean_ctor_get(v_t_1536_, 0);
lean_inc(v_a_1538_);
v_a_1539_ = lean_ctor_get(v_t_1536_, 1);
lean_inc(v_a_1539_);
lean_dec_ref_known(v_t_1536_, 2);
v___x_1540_ = lean_apply_2(v_k_1537_, v_a_1538_, v_a_1539_);
return v___x_1540_;
}
case 3:
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v_t_1536_, 0);
lean_inc_ref(v_a_1541_);
lean_dec_ref_known(v_t_1536_, 1);
v___x_1542_ = lean_apply_1(v_k_1537_, v_a_1541_);
return v___x_1542_;
}
default: 
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v_t_1536_, 0);
lean_inc(v_a_1543_);
lean_dec(v_t_1536_);
v___x_1544_ = lean_apply_1(v_k_1537_, v_a_1543_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object* v_motive__1_1545_, lean_object* v_ctorIdx_1546_, lean_object* v_t_1547_, lean_object* v_h_1548_, lean_object* v_k_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1547_, v_k_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object* v_motive__1_1551_, lean_object* v_ctorIdx_1552_, lean_object* v_t_1553_, lean_object* v_h_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Meta_Match_Example_ctorElim(v_motive__1_1551_, v_ctorIdx_1552_, v_t_1553_, v_h_1554_, v_k_1555_);
lean_dec(v_ctorIdx_1552_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object* v_t_1557_, lean_object* v_var_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1557_, v_var_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object* v_motive__1_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_var_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1561_, v_var_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object* v_t_1565_, lean_object* v_underscore_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1565_, v_underscore_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object* v_motive__1_1568_, lean_object* v_t_1569_, lean_object* v_h_1570_, lean_object* v_underscore_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1569_, v_underscore_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object* v_t_1573_, lean_object* v_ctor_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1573_, v_ctor_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object* v_motive__1_1576_, lean_object* v_t_1577_, lean_object* v_h_1578_, lean_object* v_ctor_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1577_, v_ctor_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object* v_t_1581_, lean_object* v_val_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1581_, v_val_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object* v_motive__1_1584_, lean_object* v_t_1585_, lean_object* v_h_1586_, lean_object* v_val_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1585_, v_val_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object* v_t_1589_, lean_object* v_arrayLit_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1589_, v_arrayLit_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object* v_motive__1_1592_, lean_object* v_t_1593_, lean_object* v_h_1594_, lean_object* v_arrayLit_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1593_, v_arrayLit_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object* v_fvarId_1597_, lean_object* v_ex_1598_, lean_object* v_x_1599_){
_start:
{
switch(lean_obj_tag(v_x_1599_))
{
case 0:
{
lean_object* v_a_1600_; uint8_t v___x_1601_; 
v_a_1600_ = lean_ctor_get(v_x_1599_, 0);
v___x_1601_ = l_Lean_instBEqFVarId_beq(v_a_1600_, v_fvarId_1597_);
if (v___x_1601_ == 0)
{
return v_x_1599_;
}
else
{
lean_dec_ref_known(v_x_1599_, 1);
lean_inc(v_ex_1598_);
return v_ex_1598_;
}
}
case 2:
{
lean_object* v_a_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
v_a_1602_ = lean_ctor_get(v_x_1599_, 0);
v_a_1603_ = lean_ctor_get(v_x_1599_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1605_ = v_x_1599_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_inc(v_a_1602_);
lean_dec(v_x_1599_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1597_, v_ex_1598_, v_a_1603_, v___x_1607_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v___x_1608_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1602_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
case 4:
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1622_; 
v_a_1613_ = lean_ctor_get(v_x_1599_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1615_ = v_x_1599_;
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v_x_1599_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1597_, v_ex_1598_, v_a_1613_, v___x_1617_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1618_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
default: 
{
return v_x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object* v_fvarId_1623_, lean_object* v_ex_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
if (lean_obj_tag(v_a_1625_) == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = l_List_reverse___redArg(v_a_1626_);
return v___x_1627_;
}
else
{
lean_object* v_head_1628_; lean_object* v_tail_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1638_; 
v_head_1628_ = lean_ctor_get(v_a_1625_, 0);
v_tail_1629_ = lean_ctor_get(v_a_1625_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_a_1625_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1631_ = v_a_1625_;
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_tail_1629_);
lean_inc(v_head_1628_);
lean_dec(v_a_1625_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1623_, v_ex_1624_, v_head_1628_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v_a_1626_);
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_a_1626_);
v___x_1635_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v_a_1625_ = v_tail_1629_;
v_a_1626_ = v___x_1635_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1639_, lean_object* v_ex_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1639_, v_ex_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_ex_1640_);
lean_dec(v_fvarId_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object* v_fvarId_1644_, lean_object* v_ex_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1644_, v_ex_1645_, v_x_1646_);
lean_dec(v_ex_1645_);
lean_dec(v_fvarId_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object* v_s_1648_, lean_object* v_x_1649_){
_start:
{
switch(lean_obj_tag(v_x_1649_))
{
case 0:
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1660_; 
v_a_1650_ = lean_ctor_get(v_x_1649_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1652_ = v_x_1649_;
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v_x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_FVarSubst_get(v_s_1648_, v_a_1650_);
if (lean_obj_tag(v___x_1654_) == 1)
{
lean_object* v_fvarId_1655_; lean_object* v___x_1657_; 
v_fvarId_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_fvarId_1655_);
lean_dec_ref_known(v___x_1654_, 1);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_fvarId_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_fvarId_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v___x_1654_);
lean_del_object(v___x_1652_);
v___x_1659_ = lean_box(1);
return v___x_1659_;
}
}
}
case 2:
{
lean_object* v_a_1661_; lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1671_; 
v_a_1661_ = lean_ctor_get(v_x_1649_, 0);
v_a_1662_ = lean_ctor_get(v_x_1649_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1664_ = v_x_1649_;
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_inc(v_a_1661_);
lean_dec(v_x_1649_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1648_, v_a_1662_, v___x_1666_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1661_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
case 4:
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1681_; 
v_a_1672_ = lean_ctor_get(v_x_1649_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1674_ = v_x_1649_;
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v_x_1649_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1648_, v_a_1672_, v___x_1676_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
default: 
{
return v_x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object* v_s_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
if (lean_obj_tag(v_a_1683_) == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = l_List_reverse___redArg(v_a_1684_);
return v___x_1685_;
}
else
{
lean_object* v_head_1686_; lean_object* v_tail_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1696_; 
v_head_1686_ = lean_ctor_get(v_a_1683_, 0);
v_tail_1687_ = lean_ctor_get(v_a_1683_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_a_1683_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1689_ = v_a_1683_;
v_isShared_1690_ = v_isSharedCheck_1696_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_tail_1687_);
lean_inc(v_head_1686_);
lean_dec(v_a_1683_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1696_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1682_, v_head_1686_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v_a_1684_);
lean_ctor_set(v___x_1689_, 0, v___x_1691_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_a_1684_);
v___x_1693_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v_a_1683_ = v_tail_1687_;
v_a_1684_ = v___x_1693_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object* v_s_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_s_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object* v_s_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1701_, v_x_1702_);
lean_dec(v_s_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object* v_x_1704_){
_start:
{
switch(lean_obj_tag(v_x_1704_))
{
case 0:
{
lean_object* v___x_1705_; 
lean_dec_ref_known(v_x_1704_, 1);
v___x_1705_ = lean_box(1);
return v___x_1705_;
}
case 2:
{
lean_object* v_a_1706_; lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1716_; 
v_a_1706_ = lean_ctor_get(v_x_1704_, 0);
v_a_1707_ = lean_ctor_get(v_x_1704_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1709_ = v_x_1704_;
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_inc(v_a_1706_);
lean_dec(v_x_1704_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1707_, v___x_1711_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1706_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
case 4:
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
v_a_1717_ = lean_ctor_get(v_x_1704_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1719_ = v_x_1704_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v_x_1704_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1717_, v___x_1721_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1722_);
v___x_1724_ = v___x_1719_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
default: 
{
return v_x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
if (lean_obj_tag(v_a_1727_) == 0)
{
lean_object* v___x_1729_; 
v___x_1729_ = l_List_reverse___redArg(v_a_1728_);
return v___x_1729_;
}
else
{
lean_object* v_head_1730_; lean_object* v_tail_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1740_; 
v_head_1730_ = lean_ctor_get(v_a_1727_, 0);
v_tail_1731_ = lean_ctor_get(v_a_1727_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_a_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1733_ = v_a_1727_;
v_isShared_1734_ = v_isSharedCheck_1740_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_tail_1731_);
lean_inc(v_head_1730_);
lean_dec(v_a_1727_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1740_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1730_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_a_1728_);
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1728_);
v___x_1737_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
v_a_1727_ = v_tail_1731_;
v_a_1728_ = v___x_1737_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__1));
v___x_1745_ = l_Lean_MessageData_ofFormat(v___x_1744_);
return v___x_1745_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0));
v___x_1747_ = l_Lean_stringToMessageData(v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
if (lean_obj_tag(v_x_1749_) == 0)
{
return v_x_1748_;
}
else
{
lean_object* v_head_1750_; lean_object* v_tail_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1762_; 
v_head_1750_ = lean_ctor_get(v_x_1749_, 0);
v_tail_1751_ = lean_ctor_get(v_x_1749_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1749_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1753_ = v_x_1749_;
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_tail_1751_);
lean_inc(v_head_1750_);
lean_dec(v_x_1749_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1762_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0, &l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once, _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 7);
lean_ctor_set(v___x_1753_, 1, v___x_1755_);
lean_ctor_set(v___x_1753_, 0, v_x_1748_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_x_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1750_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v_x_1748_ = v___x_1759_;
v_x_1749_ = v_tail_1751_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__4));
v___x_1767_ = l_Lean_MessageData_ofFormat(v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object* v_x_1768_){
_start:
{
switch(lean_obj_tag(v_x_1768_))
{
case 0:
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1769_ = lean_ctor_get(v_x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v_x_1768_, 1);
v___x_1770_ = l_Lean_mkFVar(v_a_1769_);
v___x_1771_ = l_Lean_MessageData_ofExpr(v___x_1770_);
return v___x_1771_;
}
case 1:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__2, &l_Lean_Meta_Match_Example_toMessageData___closed__2_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__2);
return v___x_1772_;
}
case 2:
{
lean_object* v_a_1773_; 
v_a_1773_ = lean_ctor_get(v_x_1768_, 1);
if (lean_obj_tag(v_a_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_a_1774_ = lean_ctor_get(v_x_1768_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v_x_1768_, 2);
v___x_1775_ = lean_box(0);
v___x_1776_ = l_Lean_mkConst(v_a_1774_, v___x_1775_);
v___x_1777_ = l_Lean_MessageData_ofExpr(v___x_1776_);
return v___x_1777_;
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1793_; 
lean_inc(v_a_1773_);
v_a_1778_ = lean_ctor_get(v_x_1768_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_x_1768_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_x_1768_, 1);
lean_dec(v_unused_1794_);
v___x_1780_ = v_x_1768_;
v_isShared_1781_ = v_isSharedCheck_1793_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v_x_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1793_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1782_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_1783_ = 0;
v___x_1784_ = l_Lean_MessageData_ofConstName(v_a_1778_, v___x_1783_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 7);
lean_ctor_set(v___x_1780_, 1, v___x_1784_);
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1786_ = v___x_1780_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_1788_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(v___x_1787_, v_a_1773_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1786_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
return v___x_1791_;
}
}
}
}
case 3:
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v_x_1768_, 0);
lean_inc_ref(v_a_1795_);
lean_dec_ref_known(v_x_1768_, 1);
v___x_1796_ = l_Lean_MessageData_ofExpr(v_a_1795_);
return v___x_1796_;
}
default: 
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_a_1797_ = lean_ctor_get(v_x_1768_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v_x_1768_, 1);
v___x_1798_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__5, &l_Lean_Meta_Match_Example_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__5);
v___x_1799_ = lean_box(0);
v___x_1800_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_1797_, v___x_1799_);
v___x_1801_ = l_Lean_MessageData_ofList(v___x_1800_);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1798_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
if (lean_obj_tag(v_a_1803_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = l_List_reverse___redArg(v_a_1804_);
return v___x_1805_;
}
else
{
lean_object* v_head_1806_; lean_object* v_tail_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v_head_1806_ = lean_ctor_get(v_a_1803_, 0);
v_tail_1807_ = lean_ctor_get(v_a_1803_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_a_1803_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1809_ = v_a_1803_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_tail_1807_);
lean_inc(v_head_1806_);
lean_dec(v_a_1803_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1806_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v_a_1804_);
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_a_1804_);
v___x_1813_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
v_a_1803_ = v_tail_1807_;
v_a_1804_ = v___x_1813_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
if (lean_obj_tag(v_a_1817_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = l_List_reverse___redArg(v_a_1818_);
return v___x_1819_;
}
else
{
lean_object* v_head_1820_; lean_object* v_tail_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1831_; 
v_head_1820_ = lean_ctor_get(v_a_1817_, 0);
v_tail_1821_ = lean_ctor_get(v_a_1817_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_a_1817_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1823_ = v_a_1817_;
v_isShared_1824_ = v_isSharedCheck_1831_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_tail_1821_);
lean_inc(v_head_1820_);
lean_dec(v_a_1817_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1831_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1825_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1820_);
v___x_1826_ = l_Lean_Meta_Match_Example_toMessageData(v___x_1825_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v_a_1818_);
lean_ctor_set(v___x_1823_, 0, v___x_1826_);
v___x_1828_ = v___x_1823_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_a_1818_);
v___x_1828_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v_a_1817_ = v_tail_1821_;
v_a_1818_ = v___x_1828_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object* v_cex_1832_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1833_ = lean_box(0);
v___x_1834_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(v_cex_1832_, v___x_1833_);
v___x_1835_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_1836_ = l_Lean_MessageData_joinSep(v___x_1834_, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object* v_mvarId_1842_, lean_object* v_x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1842_, v_x_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
v_a_1858_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1849_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1849_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object* v_mvarId_1866_, lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1866_, v_x_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object* v_00_u03b1_1874_, lean_object* v_mvarId_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1875_, v_x_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object* v_00_u03b1_1883_, lean_object* v_mvarId_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(v_00_u03b1_1883_, v_mvarId_1884_, v_x_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object* v_p_1892_, lean_object* v_x_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_mvarId_1899_; lean_object* v___x_1900_; 
v_mvarId_1899_ = lean_ctor_get(v_p_1892_, 0);
lean_inc(v_mvarId_1899_);
lean_dec_ref(v_p_1892_);
v___x_1900_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1899_, v_x_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object* v_p_1901_, lean_object* v_x_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1901_, v_x_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* v_00_u03b1_1909_, lean_object* v_p_1910_, lean_object* v_x_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1910_, v_x_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_p_1919_, lean_object* v_x_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Meta_Match_withGoalOf(v_00_u03b1_1918_, v_p_1919_, v_x_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = l_List_reverse___redArg(v_x_1928_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
else
{
lean_object* v_head_1936_; lean_object* v_tail_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1955_; 
v_head_1936_ = lean_ctor_get(v_x_1927_, 0);
v_tail_1937_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1939_ = v_x_1927_;
v_isShared_1940_ = v_isSharedCheck_1955_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_tail_1937_);
lean_inc(v_head_1936_);
lean_dec(v_x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1955_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_Meta_Match_Alt_toMessageData(v_head_1936_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v_x_1928_);
lean_ctor_set(v___x_1939_, 0, v_a_1942_);
v___x_1944_ = v___x_1939_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1942_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_x_1928_);
v___x_1944_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
v_x_1927_ = v_tail_1937_;
v_x_1928_ = v___x_1944_;
goto _start;
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_del_object(v___x_1939_);
lean_dec(v_tail_1937_);
lean_dec(v_x_1928_);
v_a_1947_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1941_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1941_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_x_1956_, v_x_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
if (lean_obj_tag(v_x_1964_) == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = l_List_reverse___redArg(v_x_1965_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
else
{
lean_object* v_head_1973_; lean_object* v_tail_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1999_; 
v_head_1973_ = lean_ctor_get(v_x_1964_, 0);
v_tail_1974_ = lean_ctor_get(v_x_1964_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_x_1964_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1976_ = v_x_1964_;
v_isShared_1977_ = v_isSharedCheck_1999_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_tail_1974_);
lean_inc(v_head_1973_);
lean_dec(v_x_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1999_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; 
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
lean_inc(v_head_1973_);
v___x_1978_ = lean_infer_type(v_head_1973_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_MessageData_ofExpr(v_head_1973_);
v___x_1981_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = l_Lean_MessageData_ofExpr(v_a_1979_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_x_1965_);
lean_ctor_set(v___x_1976_, 0, v___x_1986_);
v___x_1988_ = v___x_1976_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_x_1965_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
v_x_1964_ = v_tail_1974_;
v_x_1965_ = v___x_1988_;
goto _start;
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_del_object(v___x_1976_);
lean_dec(v_tail_1974_);
lean_dec(v_head_1973_);
lean_dec(v_x_1965_);
v_a_1991_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1978_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1978_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_x_2000_, v_x_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2));
v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
return v___x_2013_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_box(1);
v___x_2015_ = l_Lean_MessageData_ofFormat(v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object* v_alts_2019_, lean_object* v___x_2020_, lean_object* v_vars_2021_, lean_object* v_examples_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; 
lean_inc(v___x_2020_);
v___x_2028_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_alts_2019_, v___x_2020_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
lean_inc(v___x_2020_);
v___x_2030_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_vars_2021_, v___x_2020_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2054_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2054_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2054_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2035_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1);
v___x_2036_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v_a_2031_, v___x_2020_);
v___x_2037_ = l_Lean_MessageData_ofList(v___x_2036_);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2035_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2042_ = l_Lean_MessageData_joinSep(v_a_2029_, v___x_2041_);
v___x_2043_ = l_Lean_indentD(v___x_2042_);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2040_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_2022_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2050_);
v___x_2052_ = v___x_2033_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_2029_);
lean_dec(v_examples_2022_);
lean_dec(v___x_2020_);
v_a_2055_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2030_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2030_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_examples_2022_);
lean_dec(v_vars_2021_);
lean_dec(v___x_2020_);
v_a_2063_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2028_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2028_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object* v_alts_2071_, lean_object* v___x_2072_, lean_object* v_vars_2073_, lean_object* v_examples_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(v_alts_2071_, v___x_2072_, v_vars_2073_, v_examples_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* v_p_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_vars_2087_; lean_object* v_alts_2088_; lean_object* v_examples_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; 
v_vars_2087_ = lean_ctor_get(v_p_2081_, 1);
v_alts_2088_ = lean_ctor_get(v_p_2081_, 2);
v_examples_2089_ = lean_ctor_get(v_p_2081_, 3);
v___x_2090_ = lean_box(0);
lean_inc(v_examples_2089_);
lean_inc(v_vars_2087_);
lean_inc(v_alts_2088_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2091_, 0, v_alts_2088_);
lean_closure_set(v___f_2091_, 1, v___x_2090_);
lean_closure_set(v___f_2091_, 2, v_vars_2087_);
lean_closure_set(v___f_2091_, 3, v_examples_2089_);
v___x_2092_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_2081_, v___f_2091_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object* v_p_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Meta_Match_Problem_toMessageData(v_p_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object* v_cex_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
if (lean_obj_tag(v_a_2102_) == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = l_List_reverse___redArg(v_a_2103_);
return v___x_2104_;
}
else
{
lean_object* v_head_2105_; lean_object* v_tail_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2115_; 
v_head_2105_ = lean_ctor_get(v_a_2102_, 0);
v_tail_2106_ = lean_ctor_get(v_a_2102_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2102_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2108_ = v_a_2102_;
v_isShared_2109_ = v_isSharedCheck_2115_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_tail_2106_);
lean_inc(v_head_2105_);
lean_dec(v_a_2102_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2115_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = l_Lean_Meta_Match_examplesToMessageData(v_head_2105_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v_a_2103_);
lean_ctor_set(v___x_2108_, 0, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_a_2103_);
v___x_2112_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
v_a_2102_ = v_tail_2106_;
v_a_2103_ = v___x_2112_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object* v_cexs_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2117_ = lean_array_to_list(v_cexs_2116_);
v___x_2118_ = lean_box(0);
v___x_2119_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(v___x_2117_, v___x_2118_);
v___x_2120_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2121_ = l_Lean_MessageData_joinSep(v___x_2119_, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_ref_2128_; lean_object* v___x_2129_; lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_ref_2128_ = lean_ctor_get(v___y_2125_, 5);
v___x_2129_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msg_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
lean_inc(v_ref_2128_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v_ref_2128_);
lean_ctor_set(v___x_2134_, 1, v_a_2130_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 1);
lean_ctor_set(v___x_2132_, 0, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object* v_msg_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__0));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__2));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4(void){
_start:
{
lean_object* v___x_2152_; lean_object* v_dummy_2153_; 
v___x_2152_ = lean_box(0);
v_dummy_2153_ = l_Lean_Expr_sort___override(v___x_2152_);
return v_dummy_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t v_sz_2154_, size_t v_i_2155_, lean_object* v_bs_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_usize_dec_lt(v_i_2155_, v_sz_2154_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_bs_2156_);
return v___x_2163_;
}
else
{
lean_object* v_v_2164_; lean_object* v___x_2165_; 
v_v_2164_ = lean_array_uget_borrowed(v_bs_2156_, v_i_2155_);
lean_inc(v_v_2164_);
v___x_2165_ = l_Lean_Meta_Match_toPattern(v_v_2164_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; lean_object* v_bs_x27_2168_; size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = lean_unsigned_to_nat(0u);
v_bs_x27_2168_ = lean_array_uset(v_bs_2156_, v_i_2155_, v___x_2167_);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2155_, v___x_2169_);
v___x_2171_ = lean_array_uset(v_bs_x27_2168_, v_i_2155_, v_a_2166_);
v_i_2155_ = v___x_2170_;
v_bs_2156_ = v___x_2171_;
goto _start;
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_bs_2156_);
v_a_2173_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2165_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2165_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object* v_e_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_inaccessible_x3f(v_e_2181_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Expr_arrayLit_x3f(v_e_2181_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_2181_);
if (lean_obj_tag(v___x_2198_) == 1)
{
lean_object* v_val_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_e_2181_);
v_val_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = lean_unsigned_to_nat(2u);
v___x_2201_ = l_Lean_Expr_getAppNumArgs(v_val_2199_);
v___x_2202_ = lean_nat_sub(v___x_2201_, v___x_2200_);
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_nat_sub(v___x_2202_, v___x_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = l_Lean_Expr_getRevArg_x21(v_val_2199_, v___x_2204_);
v___x_2206_ = l_Lean_Meta_Match_toPattern(v___x_2205_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2231_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_nat_sub(v___x_2201_, v___x_2203_);
v___x_2219_ = lean_nat_sub(v___x_2218_, v___x_2203_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_Expr_getRevArg_x21(v_val_2199_, v___x_2219_);
if (lean_obj_tag(v___x_2220_) == 1)
{
lean_object* v_fvarId_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_fvarId_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_fvarId_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2222_ = lean_unsigned_to_nat(3u);
v___x_2223_ = lean_nat_sub(v___x_2201_, v___x_2222_);
lean_dec(v___x_2201_);
v___x_2224_ = lean_nat_sub(v___x_2223_, v___x_2203_);
lean_dec(v___x_2223_);
v___x_2225_ = l_Lean_Expr_getRevArg_x21(v_val_2199_, v___x_2224_);
lean_dec(v_val_2199_);
if (lean_obj_tag(v___x_2225_) == 1)
{
lean_object* v_fvarId_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v_fvarId_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_fvarId_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_2227_, 0, v_fvarId_2221_);
lean_ctor_set(v___x_2227_, 1, v_a_2207_);
lean_ctor_set(v___x_2227_, 2, v_fvarId_2226_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2227_);
v___x_2229_ = v___x_2209_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_dec_ref(v___x_2225_);
lean_dec(v_fvarId_2221_);
lean_del_object(v___x_2209_);
lean_dec(v_a_2207_);
v___y_2212_ = v_a_2182_;
v___y_2213_ = v_a_2183_;
v___y_2214_ = v_a_2184_;
v___y_2215_ = v_a_2185_;
goto v___jp_2211_;
}
}
else
{
lean_dec_ref(v___x_2220_);
lean_del_object(v___x_2209_);
lean_dec(v_a_2207_);
lean_dec(v___x_2201_);
lean_dec(v_val_2199_);
v___y_2212_ = v_a_2182_;
v___y_2213_ = v_a_2183_;
v___y_2214_ = v_a_2184_;
v___y_2215_ = v_a_2185_;
goto v___jp_2211_;
}
v___jp_2211_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__3, &l_Lean_Meta_Match_toPattern___closed__3_once, _init_l_Lean_Meta_Match_toPattern___closed__3);
v___x_2217_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2216_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2217_;
}
}
}
else
{
lean_dec(v___x_2201_);
lean_dec(v_val_2199_);
return v___x_2206_;
}
}
else
{
lean_object* v___x_2232_; 
lean_dec(v___x_2198_);
lean_inc_ref(v_e_2181_);
v___x_2232_ = l_Lean_Meta_isMatchValue(v_e_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2325_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2325_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2325_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_unbox(v_a_2233_);
lean_dec(v_a_2233_);
if (v___x_2237_ == 0)
{
uint8_t v___x_2238_; 
v___x_2238_ = l_Lean_Expr_isFVar(v_e_2181_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_del_object(v___x_2235_);
lean_inc(v_a_2185_);
lean_inc_ref(v_a_2184_);
lean_inc(v_a_2183_);
lean_inc_ref(v_a_2182_);
lean_inc_ref(v_e_2181_);
v___x_2239_ = lean_whnf(v_e_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; uint8_t v___x_2241_; uint8_t v___x_2242_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = lean_expr_eqv(v_a_2240_, v_e_2181_);
v___x_2242_ = lean_bool_not(v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec(v_a_2240_);
v___x_2243_ = l_Lean_Expr_getAppFn(v_e_2181_);
if (lean_obj_tag(v___x_2243_) == 4)
{
lean_object* v_declName_2244_; lean_object* v_us_2245_; lean_object* v___x_2246_; lean_object* v_env_2247_; lean_object* v___x_2248_; 
v_declName_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_declName_2244_);
v_us_2245_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_us_2245_);
lean_dec_ref_known(v___x_2243_, 2);
v___x_2246_ = lean_st_ref_get(v_a_2185_);
v_env_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc_ref(v_env_2247_);
lean_dec(v___x_2246_);
v___x_2248_ = l_Lean_Environment_find_x3f(v_env_2247_, v_declName_2244_, v___x_2242_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_dec(v_us_2245_);
v___y_2188_ = v_a_2182_;
v___y_2189_ = v_a_2183_;
v___y_2190_ = v_a_2184_;
v___y_2191_ = v_a_2185_;
goto v___jp_2187_;
}
else
{
lean_object* v_val_2249_; 
v_val_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2248_, 1);
if (lean_obj_tag(v_val_2249_) == 6)
{
lean_object* v_val_2250_; lean_object* v_toConstantVal_2251_; lean_object* v_numParams_2252_; lean_object* v_numFields_2253_; lean_object* v_nargs_2254_; lean_object* v_dummy_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_val_2250_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_val_2250_);
lean_dec_ref_known(v_val_2249_, 1);
v_toConstantVal_2251_ = lean_ctor_get(v_val_2250_, 0);
lean_inc_ref(v_toConstantVal_2251_);
v_numParams_2252_ = lean_ctor_get(v_val_2250_, 3);
lean_inc(v_numParams_2252_);
v_numFields_2253_ = lean_ctor_get(v_val_2250_, 4);
lean_inc(v_numFields_2253_);
lean_dec_ref(v_val_2250_);
v_nargs_2254_ = l_Lean_Expr_getAppNumArgs(v_e_2181_);
v_dummy_2255_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__4, &l_Lean_Meta_Match_toPattern___closed__4_once, _init_l_Lean_Meta_Match_toPattern___closed__4);
lean_inc(v_nargs_2254_);
v___x_2256_ = lean_mk_array(v_nargs_2254_, v_dummy_2255_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_sub(v_nargs_2254_, v___x_2257_);
lean_dec(v_nargs_2254_);
lean_inc_ref(v_e_2181_);
v___x_2259_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2181_, v___x_2256_, v___x_2258_);
v___x_2292_ = lean_array_get_size(v___x_2259_);
v___x_2293_ = lean_nat_add(v_numParams_2252_, v_numFields_2253_);
lean_dec(v_numFields_2253_);
v___x_2294_ = lean_nat_dec_eq(v___x_2292_, v___x_2293_);
lean_dec(v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2296_ = l_Lean_indentExpr(v_e_2181_);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2297_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_dec_ref_known(v___x_2298_, 1);
v___y_2261_ = v_a_2182_;
v___y_2262_ = v_a_2183_;
v___y_2263_ = v_a_2184_;
v___y_2264_ = v_a_2185_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v___x_2259_);
lean_dec(v_numParams_2252_);
lean_dec_ref(v_toConstantVal_2251_);
lean_dec(v_us_2245_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_dec_ref(v_e_2181_);
v___y_2261_ = v_a_2182_;
v___y_2262_ = v_a_2183_;
v___y_2263_ = v_a_2184_;
v___y_2264_ = v_a_2185_;
goto v___jp_2260_;
}
v___jp_2260_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; size_t v_sz_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2252_);
v___x_2266_ = l_Array_extract___redArg(v___x_2259_, v___x_2265_, v_numParams_2252_);
v___x_2267_ = lean_array_get_size(v___x_2259_);
v___x_2268_ = l_Array_extract___redArg(v___x_2259_, v_numParams_2252_, v___x_2267_);
lean_dec_ref(v___x_2259_);
v_sz_2269_ = lean_array_size(v___x_2268_);
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_2269_, v___x_2270_, v___x_2268_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2283_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_name_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v_name_2276_ = lean_ctor_get(v_toConstantVal_2251_, 0);
lean_inc(v_name_2276_);
lean_dec_ref(v_toConstantVal_2251_);
v___x_2277_ = lean_array_to_list(v___x_2266_);
v___x_2278_ = lean_array_to_list(v_a_2272_);
v___x_2279_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2279_, 0, v_name_2276_);
lean_ctor_set(v___x_2279_, 1, v_us_2245_);
lean_ctor_set(v___x_2279_, 2, v___x_2277_);
lean_ctor_set(v___x_2279_, 3, v___x_2278_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2279_);
v___x_2281_ = v___x_2274_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v___x_2266_);
lean_dec_ref(v_toConstantVal_2251_);
lean_dec(v_us_2245_);
v_a_2284_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2271_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2271_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
else
{
lean_dec(v_val_2249_);
lean_dec(v_us_2245_);
v___y_2188_ = v_a_2182_;
v___y_2189_ = v_a_2183_;
v___y_2190_ = v_a_2184_;
v___y_2191_ = v_a_2185_;
goto v___jp_2187_;
}
}
}
else
{
lean_dec_ref(v___x_2243_);
v___y_2188_ = v_a_2182_;
v___y_2189_ = v_a_2183_;
v___y_2190_ = v_a_2184_;
v___y_2191_ = v_a_2185_;
goto v___jp_2187_;
}
}
else
{
lean_dec_ref(v_e_2181_);
v_e_2181_ = v_a_2240_;
goto _start;
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_e_2181_);
v_a_2308_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2239_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2239_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2316_ = l_Lean_Expr_fvarId_x21(v_e_2181_);
lean_dec_ref(v_e_2181_);
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2317_);
v___x_2319_ = v___x_2235_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_e_2181_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2321_);
v___x_2323_ = v___x_2235_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_e_2181_);
v_a_2326_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2232_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2232_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
lean_object* v_val_2334_; lean_object* v_fst_2335_; lean_object* v_snd_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_e_2181_);
v_val_2334_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_val_2334_);
lean_dec_ref_known(v___x_2197_, 1);
v_fst_2335_ = lean_ctor_get(v_val_2334_, 0);
v_snd_2336_ = lean_ctor_get(v_val_2334_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_val_2334_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2338_ = v_val_2334_;
v_isShared_2339_ = v_isSharedCheck_2361_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snd_2336_);
lean_inc(v_fst_2335_);
lean_dec(v_val_2334_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2361_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_snd_2336_, v___x_2340_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2352_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2352_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2352_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 4);
lean_ctor_set(v___x_2338_, 1, v_a_2342_);
v___x_2347_ = v___x_2338_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_fst_2335_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2347_);
v___x_2349_ = v___x_2344_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_del_object(v___x_2338_);
lean_dec(v_fst_2335_);
v_a_2353_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2341_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2341_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v_e_2181_);
v_val_2362_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2364_ = v___x_2196_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v___x_2196_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 0);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_val_2362_);
v___x_2367_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
}
v___jp_2187_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2192_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2193_ = l_Lean_indentExpr(v_e_2181_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2194_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
if (lean_obj_tag(v_x_2371_) == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = l_List_reverse___redArg(v_x_2372_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
else
{
lean_object* v_head_2380_; lean_object* v_tail_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2399_; 
v_head_2380_ = lean_ctor_get(v_x_2371_, 0);
v_tail_2381_ = lean_ctor_get(v_x_2371_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_x_2371_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2383_ = v_x_2371_;
v_isShared_2384_ = v_isSharedCheck_2399_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_tail_2381_);
lean_inc(v_head_2380_);
lean_dec(v_x_2371_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2399_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Meta_Match_toPattern(v_head_2380_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v_x_2372_);
lean_ctor_set(v___x_2383_, 0, v_a_2386_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2386_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_x_2372_);
v___x_2388_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
v_x_2371_ = v_tail_2381_;
v_x_2372_ = v___x_2388_;
goto _start;
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_del_object(v___x_2383_);
lean_dec(v_tail_2381_);
lean_dec(v_x_2372_);
v_a_2391_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2385_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2385_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_x_2400_, v_x_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object* v_sz_2408_, lean_object* v_i_2409_, lean_object* v_bs_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
size_t v_sz_boxed_2416_; size_t v_i_boxed_2417_; lean_object* v_res_2418_; 
v_sz_boxed_2416_ = lean_unbox_usize(v_sz_2408_);
lean_dec(v_sz_2408_);
v_i_boxed_2417_ = lean_unbox_usize(v_i_2409_);
lean_dec(v_i_2409_);
v_res_2418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_2416_, v_i_boxed_2417_, v_bs_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object* v_e_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_Match_toPattern(v_e_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object* v_00_u03b1_2426_, lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_msg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(v_00_u03b1_2434_, v_msg_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2449_ = lean_string_utf8_byte_size(v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(lean_object* v_s_2450_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2451_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2452_ = lean_string_utf8_byte_size(v_s_2450_);
v___x_2453_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0, &l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg___closed__0);
v___x_2454_ = lean_nat_dec_le(v___x_2453_, v___x_2452_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v_s_2450_);
v___x_2455_ = lean_box(0);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_string_memcmp(v_s_2450_, v___x_2451_, v___x_2456_, v___x_2456_, v___x_2453_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
lean_dec_ref(v_s_2450_);
v___x_2458_ = lean_box(0);
return v___x_2458_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_inc_ref(v_s_2450_);
v___x_2459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2459_, 0, v_s_2450_);
lean_ctor_set(v___x_2459_, 1, v___x_2456_);
lean_ctor_set(v___x_2459_, 2, v___x_2452_);
v___x_2460_ = l_String_Slice_pos_x21(v___x_2459_, v___x_2453_);
lean_dec_ref_known(v___x_2459_, 3);
v___x_2461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2461_, 0, v_s_2450_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
lean_ctor_set(v___x_2461_, 2, v___x_2452_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(lean_object* v_s_2463_, lean_object* v_pat_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_2463_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object* v_s_2466_, lean_object* v_pat_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(v_s_2466_, v_pat_2467_);
lean_dec_ref(v_pat_2467_);
return v_res_2468_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object* v_s_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
uint8_t v___x_2471_; 
v___x_2471_ = 0;
return v___x_2471_;
}
else
{
lean_object* v_val_2472_; uint8_t v___x_2473_; 
v_val_2472_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2472_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2473_ = l_String_Slice_isNat(v_val_2472_);
lean_dec(v_val_2472_);
return v___x_2473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object* v_s_2474_){
_start:
{
uint8_t v_res_2475_; lean_object* v_r_2476_; 
v_res_2475_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_2474_);
v_r_2476_ = lean_box(v_res_2475_);
return v_r_2476_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Value(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_instInhabitedPattern_default = _init_l_Lean_Meta_Match_instInhabitedPattern_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern_default);
l_Lean_Meta_Match_instInhabitedPattern = _init_l_Lean_Meta_Match_instInhabitedPattern();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedPattern);
l_Lean_Meta_Match_instInhabitedAlt_default = _init_l_Lean_Meta_Match_instInhabitedAlt_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt_default);
l_Lean_Meta_Match_instInhabitedAlt = _init_l_Lean_Meta_Match_instInhabitedAlt();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedAlt);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_NamedPatterns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
