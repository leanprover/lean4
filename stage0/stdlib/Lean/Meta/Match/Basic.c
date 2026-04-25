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
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0;
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
lean_dec_ref(v_t_10_);
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
lean_dec_ref(v_t_10_);
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
lean_dec_ref(v_t_10_);
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
lean_dec_ref(v_t_10_);
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
lean_dec_ref(v_x_143_);
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
lean_dec_ref(v_x_143_);
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
lean_dec_ref(v_x_143_);
v___x_155_ = l_Lean_MessageData_ofName(v_ctorName_154_);
return v___x_155_;
}
else
{
lean_object* v_ctorName_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc(v_fields_153_);
v_ctorName_156_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_ctorName_156_);
lean_dec_ref(v_x_143_);
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
lean_dec_ref(v_x_143_);
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
lean_dec_ref(v_x_143_);
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
lean_dec_ref(v_p_206_);
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
lean_dec_ref(v_p_206_);
v___x_274_ = lean_box(0);
v___x_275_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_205_, v_xs_273_, v___x_274_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
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
lean_dec_ref(v_p_206_);
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
lean_dec_ref(v_p_206_);
v___x_291_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_205_, v_p_289_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref(v___x_291_);
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
lean_dec_ref(v___x_311_);
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
lean_dec_ref(v___x_389_);
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
lean_dec_ref(v___x_440_);
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
lean_dec_ref(v_as_505_);
v___x_516_ = l_Lean_Expr_collectFVars(v_head_514_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_dec_ref(v___x_516_);
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
lean_dec_ref(v_p_526_);
v___x_547_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_params_545_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v___x_547_);
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
lean_dec_ref(v_p_526_);
v___x_551_ = l_Lean_Expr_collectFVars(v_type_549_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_552_; 
lean_dec_ref(v___x_551_);
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
lean_dec_ref(v_p_526_);
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
lean_dec_ref(v_as_563_);
v___x_574_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_572_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_dec_ref(v___x_574_);
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
uint8_t v___x_595_; 
v___x_595_ = l_Lean_Expr_hasMVar(v_e_592_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_e_592_);
return v___x_596_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object* v_e_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_617_, v___y_618_);
lean_dec(v___y_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object* v_e_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_621_, v___y_623_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object* v_e_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(v_e_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_List_reverse___redArg(v_x_636_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_655_; 
v_head_644_ = lean_ctor_get(v_x_635_, 0);
v_tail_645_ = lean_ctor_get(v_x_635_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_655_ == 0)
{
v___x_647_ = v_x_635_;
v_isShared_648_ = v_isSharedCheck_655_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_tail_645_);
lean_inc(v_head_644_);
lean_dec(v_x_635_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_655_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v_a_650_; lean_object* v___x_652_; 
v___x_649_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_644_, v___y_638_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_x_636_);
lean_ctor_set(v___x_647_, 0, v_a_650_);
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_x_636_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_x_635_ = v_tail_645_;
v_x_636_ = v___x_652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_x_656_, v_x_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* v_x_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
switch(lean_obj_tag(v_x_664_))
{
case 0:
{
lean_object* v_e_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_694_; 
v_e_670_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_694_ == 0)
{
v___x_672_ = v_x_664_;
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_e_670_);
lean_dec(v_x_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_694_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_670_, v_a_666_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_685_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_685_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_a_675_);
v___x_680_ = v___x_672_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
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
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_del_object(v___x_672_);
v_a_686_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_674_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_674_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
case 3:
{
lean_object* v_e_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_719_; 
v_e_695_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_719_ == 0)
{
v___x_697_ = v_x_664_;
v_isShared_698_ = v_isSharedCheck_719_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_e_695_);
lean_dec(v_x_664_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_719_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_695_, v_a_666_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_710_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v_a_700_);
v___x_705_ = v___x_697_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_705_);
v___x_707_ = v___x_702_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_del_object(v___x_697_);
v_a_711_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_699_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_699_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
case 2:
{
lean_object* v_ctorName_720_; lean_object* v_us_721_; lean_object* v_params_722_; lean_object* v_fields_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_758_; 
v_ctorName_720_ = lean_ctor_get(v_x_664_, 0);
v_us_721_ = lean_ctor_get(v_x_664_, 1);
v_params_722_ = lean_ctor_get(v_x_664_, 2);
v_fields_723_ = lean_ctor_get(v_x_664_, 3);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_758_ == 0)
{
v___x_725_ = v_x_664_;
v_isShared_726_ = v_isSharedCheck_758_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_fields_723_);
lean_inc(v_params_722_);
lean_inc(v_us_721_);
lean_inc(v_ctorName_720_);
lean_dec(v_x_664_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_758_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_params_722_, v___x_727_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_728_);
v___x_730_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_fields_723_, v___x_727_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_741_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 3, v_a_731_);
lean_ctor_set(v___x_725_, 2, v_a_729_);
v___x_736_ = v___x_725_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_ctorName_720_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_us_721_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_a_729_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_a_731_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_736_);
v___x_738_ = v___x_733_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_729_);
lean_del_object(v___x_725_);
lean_dec(v_us_721_);
lean_dec(v_ctorName_720_);
v_a_742_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_730_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_730_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_del_object(v___x_725_);
lean_dec(v_fields_723_);
lean_dec(v_us_721_);
lean_dec(v_ctorName_720_);
v_a_750_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_728_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_728_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
case 5:
{
lean_object* v_varId_759_; lean_object* v_p_760_; lean_object* v_hId_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_777_; 
v_varId_759_ = lean_ctor_get(v_x_664_, 0);
v_p_760_ = lean_ctor_get(v_x_664_, 1);
v_hId_761_ = lean_ctor_get(v_x_664_, 2);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_777_ == 0)
{
v___x_763_ = v_x_664_;
v_isShared_764_ = v_isSharedCheck_777_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_hId_761_);
lean_inc(v_p_760_);
lean_inc(v_varId_759_);
lean_dec(v_x_664_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_777_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Match_instantiatePatternMVars(v_p_760_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_776_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_776_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_776_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_776_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v_a_766_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_varId_759_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_766_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_hId_761_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_del_object(v___x_763_);
lean_dec(v_hId_761_);
lean_dec(v_varId_759_);
return v___x_765_;
}
}
}
case 4:
{
lean_object* v_type_778_; lean_object* v_xs_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_814_; 
v_type_778_ = lean_ctor_get(v_x_664_, 0);
v_xs_779_ = lean_ctor_get(v_x_664_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_814_ == 0)
{
v___x_781_ = v_x_664_;
v_isShared_782_ = v_isSharedCheck_814_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_xs_779_);
lean_inc(v_type_778_);
lean_dec(v_x_664_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_814_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_778_, v_a_666_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_box(0);
v___x_786_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_xs_779_, v___x_785_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_797_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_797_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_a_787_);
lean_ctor_set(v___x_781_, 0, v_a_784_);
v___x_792_ = v___x_781_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_784_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_a_787_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_a_784_);
lean_del_object(v___x_781_);
v_a_798_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_786_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_786_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_del_object(v___x_781_);
lean_dec(v_xs_779_);
v_a_806_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_783_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_783_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
default: 
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_x_664_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = l_List_reverse___redArg(v_x_817_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
else
{
lean_object* v_head_825_; lean_object* v_tail_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_844_; 
v_head_825_ = lean_ctor_get(v_x_816_, 0);
v_tail_826_ = lean_ctor_get(v_x_816_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_844_ == 0)
{
v___x_828_ = v_x_816_;
v_isShared_829_ = v_isSharedCheck_844_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_tail_826_);
lean_inc(v_head_825_);
lean_dec(v_x_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_844_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_Match_instantiatePatternMVars(v_head_825_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_x_817_);
lean_ctor_set(v___x_828_, 0, v_a_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_831_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_x_817_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_x_816_ = v_tail_826_;
v_x_817_ = v___x_833_;
goto _start;
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_828_);
lean_dec(v_tail_826_);
lean_dec(v_x_817_);
v_a_836_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_830_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_830_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_x_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* v_x_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_Match_instantiatePatternMVars(v_x_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object* v_as_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
if (lean_obj_tag(v_as_865_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v_head_874_; lean_object* v_tail_875_; lean_object* v___x_876_; 
v_head_874_ = lean_ctor_get(v_as_865_, 0);
lean_inc(v_head_874_);
v_tail_875_ = lean_ctor_get(v_as_865_, 1);
lean_inc(v_tail_875_);
lean_dec_ref(v_as_865_);
v___x_876_ = l_Lean_LocalDecl_collectFVars(v_head_874_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_dec_ref(v___x_876_);
v_as_865_ = v_tail_875_;
goto _start;
}
else
{
lean_dec(v_tail_875_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object* v_as_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_as_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object* v_as_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
if (lean_obj_tag(v_as_886_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_box(0);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v___x_897_; 
v_head_895_ = lean_ctor_get(v_as_886_, 0);
lean_inc(v_head_895_);
v_tail_896_ = lean_ctor_get(v_as_886_, 1);
lean_inc(v_tail_896_);
lean_dec_ref(v_as_886_);
v___x_897_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_895_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref(v___x_897_);
v_as_886_ = v_tail_896_;
goto _start;
}
else
{
lean_dec(v_tail_896_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object* v_as_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_as_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* v_altLHS_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_fvarDecls_914_; lean_object* v_patterns_915_; lean_object* v___x_916_; 
v_fvarDecls_914_ = lean_ctor_get(v_altLHS_907_, 1);
lean_inc(v_fvarDecls_914_);
v_patterns_915_ = lean_ctor_get(v_altLHS_907_, 2);
lean_inc(v_patterns_915_);
lean_dec_ref(v_altLHS_907_);
v___x_916_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_fvarDecls_914_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; 
lean_dec_ref(v___x_916_);
v___x_917_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_patterns_915_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_917_;
}
else
{
lean_dec(v_patterns_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* v_altLHS_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Meta_Match_AltLHS_collectFVars(v_altLHS_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object* v_localDecl_926_, lean_object* v___y_927_){
_start:
{
if (lean_obj_tag(v_localDecl_926_) == 0)
{
lean_object* v_index_929_; lean_object* v_fvarId_930_; lean_object* v_userName_931_; lean_object* v_type_932_; uint8_t v_bi_933_; uint8_t v_kind_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_950_; 
v_index_929_ = lean_ctor_get(v_localDecl_926_, 0);
v_fvarId_930_ = lean_ctor_get(v_localDecl_926_, 1);
v_userName_931_ = lean_ctor_get(v_localDecl_926_, 2);
v_type_932_ = lean_ctor_get(v_localDecl_926_, 3);
v_bi_933_ = lean_ctor_get_uint8(v_localDecl_926_, sizeof(void*)*4);
v_kind_934_ = lean_ctor_get_uint8(v_localDecl_926_, sizeof(void*)*4 + 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_localDecl_926_);
if (v_isSharedCheck_950_ == 0)
{
v___x_936_ = v_localDecl_926_;
v_isShared_937_ = v_isSharedCheck_950_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_type_932_);
lean_inc(v_userName_931_);
lean_inc(v_fvarId_930_);
lean_inc(v_index_929_);
lean_dec(v_localDecl_926_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_950_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_949_; 
v___x_938_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_932_, v___y_927_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_949_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_949_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 3, v_a_939_);
v___x_944_ = v___x_936_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_index_929_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_fvarId_930_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_userName_931_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_a_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*4, v_bi_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_948_, sizeof(void*)*4 + 1, v_kind_934_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
else
{
lean_object* v_index_951_; lean_object* v_fvarId_952_; lean_object* v_userName_953_; lean_object* v_type_954_; lean_object* v_value_955_; uint8_t v_nondep_956_; uint8_t v_kind_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_975_; 
v_index_951_ = lean_ctor_get(v_localDecl_926_, 0);
v_fvarId_952_ = lean_ctor_get(v_localDecl_926_, 1);
v_userName_953_ = lean_ctor_get(v_localDecl_926_, 2);
v_type_954_ = lean_ctor_get(v_localDecl_926_, 3);
v_value_955_ = lean_ctor_get(v_localDecl_926_, 4);
v_nondep_956_ = lean_ctor_get_uint8(v_localDecl_926_, sizeof(void*)*5);
v_kind_957_ = lean_ctor_get_uint8(v_localDecl_926_, sizeof(void*)*5 + 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_localDecl_926_);
if (v_isSharedCheck_975_ == 0)
{
v___x_959_ = v_localDecl_926_;
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_value_955_);
lean_inc(v_type_954_);
lean_inc(v_userName_953_);
lean_inc(v_fvarId_952_);
lean_inc(v_index_951_);
lean_dec(v_localDecl_926_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_975_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_974_; 
v___x_961_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_954_, v___y_927_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_955_, v___y_927_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_974_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 4, v_a_964_);
lean_ctor_set(v___x_959_, 3, v_a_962_);
v___x_969_ = v___x_959_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_index_951_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_fvarId_952_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_userName_953_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v_a_962_);
lean_ctor_set(v_reuseFailAlloc_973_, 4, v_a_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*5, v_nondep_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*5 + 1, v_kind_957_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object* v_localDecl_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_976_, v___y_977_);
lean_dec(v___y_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
if (lean_obj_tag(v_x_980_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_List_reverse___redArg(v_x_981_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1008_; 
v_head_989_ = lean_ctor_get(v_x_980_, 0);
v_tail_990_ = lean_ctor_get(v_x_980_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_x_980_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_992_ = v_x_980_;
v_isShared_993_ = v_isSharedCheck_1008_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_tail_990_);
lean_inc(v_head_989_);
lean_dec(v_x_980_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1008_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_989_, v___y_983_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v___x_994_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v_x_981_);
lean_ctor_set(v___x_992_, 0, v_a_995_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_995_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_x_981_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_x_980_ = v_tail_990_;
v_x_981_ = v___x_997_;
goto _start;
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_del_object(v___x_992_);
lean_dec(v_tail_990_);
lean_dec(v_x_981_);
v_a_1000_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_994_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_x_1009_, v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* v_altLHS_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_ref_1023_; lean_object* v_fvarDecls_1024_; lean_object* v_patterns_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1060_; 
v_ref_1023_ = lean_ctor_get(v_altLHS_1017_, 0);
v_fvarDecls_1024_ = lean_ctor_get(v_altLHS_1017_, 1);
v_patterns_1025_ = lean_ctor_get(v_altLHS_1017_, 2);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_altLHS_1017_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1027_ = v_altLHS_1017_;
v_isShared_1028_ = v_isSharedCheck_1060_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_patterns_1025_);
lean_inc(v_fvarDecls_1024_);
lean_inc(v_ref_1023_);
lean_dec(v_altLHS_1017_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1060_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_fvarDecls_1024_, v___x_1029_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_patterns_1025_, v___x_1029_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1043_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1043_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 2, v_a_1033_);
lean_ctor_set(v___x_1027_, 1, v_a_1031_);
v___x_1038_ = v___x_1027_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_ref_1023_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_a_1031_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1038_);
v___x_1040_ = v___x_1035_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_a_1031_);
lean_del_object(v___x_1027_);
lean_dec(v_ref_1023_);
v_a_1044_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1032_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1032_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1027_);
lean_dec(v_patterns_1025_);
lean_dec(v_ref_1023_);
v_a_1052_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1030_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1030_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* v_altLHS_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_Match_instantiateAltLHSMVars(v_altLHS_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object* v_localDecl_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_1068_, v___y_1070_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object* v_localDecl_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(v_localDecl_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0));
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v___x_1087_);
lean_ctor_set(v___x_1089_, 2, v___x_1086_);
lean_ctor_set(v___x_1089_, 3, v___x_1085_);
lean_ctor_set(v___x_1089_, 4, v___x_1085_);
lean_ctor_set(v___x_1089_, 5, v___x_1085_);
lean_ctor_set(v___x_1089_, 6, v___x_1084_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default(void){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedAlt_default___closed__1, &l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt(void){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_Match_instInhabitedAlt_default;
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object* v_msgData_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; lean_object* v_env_1099_; lean_object* v___x_1100_; lean_object* v_mctx_1101_; lean_object* v_lctx_1102_; lean_object* v_options_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1098_ = lean_st_ref_get(v___y_1096_);
v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_env_1099_);
lean_dec(v___x_1098_);
v___x_1100_ = lean_st_ref_get(v___y_1094_);
v_mctx_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_mctx_1101_);
lean_dec(v___x_1100_);
v_lctx_1102_ = lean_ctor_get(v___y_1093_, 2);
v_options_1103_ = lean_ctor_get(v___y_1095_, 2);
lean_inc_ref(v_options_1103_);
lean_inc_ref(v_lctx_1102_);
v___x_1104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1104_, 0, v_env_1099_);
lean_ctor_set(v___x_1104_, 1, v_mctx_1101_);
lean_ctor_set(v___x_1104_, 2, v_lctx_1102_);
lean_ctor_set(v___x_1104_, 3, v_options_1103_);
v___x_1105_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_msgData_1092_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object* v_msgData_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msgData_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(lean_object* v_decls_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1114_, v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_a_1130_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1121_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(lean_object* v_decls_1138_, lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1138_, v_x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object* v_00_u03b1_1146_, lean_object* v_decls_1147_, lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1147_, v_x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_decls_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(v_00_u03b1_1155_, v_decls_1156_, v_x_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1163_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2));
v___x_1169_ = l_Lean_stringToMessageData(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(lean_object* v_as_x27_1170_, lean_object* v_b_1171_){
_start:
{
if (lean_obj_tag(v_as_x27_1170_) == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_b_1171_);
return v___x_1173_;
}
else
{
lean_object* v_head_1174_; lean_object* v_tail_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_head_1174_ = lean_ctor_get(v_as_x27_1170_, 0);
v_tail_1175_ = lean_ctor_get(v_as_x27_1170_, 1);
v_fst_1176_ = lean_ctor_get(v_head_1174_, 0);
v_snd_1177_ = lean_ctor_get(v_head_1174_, 1);
v___x_1178_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_b_1171_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
lean_inc(v_fst_1176_);
v___x_1180_ = l_Lean_MessageData_ofExpr(v_fst_1176_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
lean_inc(v_snd_1177_);
v___x_1184_ = l_Lean_MessageData_ofExpr(v_snd_1177_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v_as_x27_1170_ = v_tail_1175_;
v_b_1171_ = v___x_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(lean_object* v_as_x27_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1187_, v_b_1188_);
lean_dec(v_as_x27_1187_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object* v_cnstrs_1191_, lean_object* v_msg_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1200_; 
v___x_1198_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_cnstrs_1191_, v_msg_1192_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_a_1199_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object* v_cnstrs_1201_, lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(v_cnstrs_1201_, v_msg_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v_cnstrs_1201_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
if (lean_obj_tag(v_a_1209_) == 0)
{
lean_object* v___x_1211_; 
v___x_1211_ = l_List_reverse___redArg(v_a_1210_);
return v___x_1211_;
}
else
{
lean_object* v_head_1212_; lean_object* v_tail_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_head_1212_ = lean_ctor_get(v_a_1209_, 0);
v_tail_1213_ = lean_ctor_get(v_a_1209_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1209_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v_a_1209_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_tail_1213_);
lean_inc(v_head_1212_);
lean_dec(v_a_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v_a_1210_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_head_1212_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_a_1210_);
v___x_1218_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
v_a_1209_ = v_tail_1213_;
v_a_1210_ = v___x_1218_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
if (lean_obj_tag(v_a_1225_) == 0)
{
lean_object* v___x_1227_; 
v___x_1227_ = l_List_reverse___redArg(v_a_1226_);
return v___x_1227_;
}
else
{
lean_object* v_head_1228_; lean_object* v_tail_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1246_; 
v_head_1228_ = lean_ctor_get(v_a_1225_, 0);
v_tail_1229_ = lean_ctor_get(v_a_1225_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1225_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1231_ = v_a_1225_;
v_isShared_1232_ = v_isSharedCheck_1246_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_tail_1229_);
lean_inc(v_head_1228_);
lean_dec(v_a_1225_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1246_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_inc(v_head_1228_);
v___x_1233_ = l_Lean_LocalDecl_toExpr(v_head_1228_);
v___x_1234_ = l_Lean_MessageData_ofExpr(v___x_1233_);
v___x_1235_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = l_Lean_LocalDecl_type(v_head_1228_);
lean_dec(v_head_1228_);
v___x_1238_ = l_Lean_MessageData_ofExpr(v___x_1237_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1236_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_a_1226_);
lean_ctor_set(v___x_1231_, 0, v___x_1241_);
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_a_1226_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
v_a_1225_ = v_tail_1229_;
v_a_1226_ = v___x_1243_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__0));
v___x_1249_ = l_Lean_stringToMessageData(v___x_1248_);
return v___x_1249_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__2));
v___x_1252_ = l_Lean_stringToMessageData(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__4));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__6));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object* v_alt_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_rhs_1265_; lean_object* v_fvarDecls_1266_; lean_object* v_patterns_1267_; lean_object* v_cnstrs_1268_; lean_object* v___y_1270_; uint8_t v___x_1284_; 
v_rhs_1265_ = lean_ctor_get(v_alt_1259_, 2);
lean_inc_ref(v_rhs_1265_);
v_fvarDecls_1266_ = lean_ctor_get(v_alt_1259_, 3);
lean_inc(v_fvarDecls_1266_);
v_patterns_1267_ = lean_ctor_get(v_alt_1259_, 4);
lean_inc(v_patterns_1267_);
v_cnstrs_1268_ = lean_ctor_get(v_alt_1259_, 5);
lean_inc(v_cnstrs_1268_);
lean_dec_ref(v_alt_1259_);
v___x_1284_ = l_List_isEmpty___redArg(v_fvarDecls_1266_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1285_ = lean_box(0);
lean_inc(v_fvarDecls_1266_);
v___x_1286_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(v_fvarDecls_1266_, v___x_1285_);
v___x_1287_ = l_Lean_MessageData_ofList(v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___y_1270_ = v___x_1289_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__7, &l_Lean_Meta_Match_Alt_toMessageData___closed__7_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7);
v___y_1270_ = v___x_1290_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_msg_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; 
v___x_1271_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__1, &l_Lean_Meta_Match_Alt_toMessageData___closed__1_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1);
v___x_1272_ = lean_box(0);
v___x_1273_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(v_patterns_1267_, v___x_1272_);
v___x_1274_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v___x_1273_, v___x_1272_);
v___x_1275_ = l_Lean_MessageData_ofList(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1271_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__3, &l_Lean_Meta_Match_Alt_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_MessageData_ofExpr(v_rhs_1265_);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v_msg_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_1281_, 0, v___y_1270_);
lean_ctor_set(v_msg_1281_, 1, v___x_1280_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1282_, 0, v_cnstrs_1268_);
lean_closure_set(v___f_1282_, 1, v_msg_1281_);
v___x_1283_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_fvarDecls_1266_, v___f_1282_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object* v_alt_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Meta_Match_Alt_toMessageData(v_alt_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object* v_as_1298_, lean_object* v_as_x27_1299_, lean_object* v_b_1300_, lean_object* v_a_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1299_, v_b_1300_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(lean_object* v_as_1308_, lean_object* v_as_x27_1309_, lean_object* v_b_1310_, lean_object* v_a_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(v_as_1308_, v_as_x27_1309_, v_b_1310_, v_a_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v_as_x27_1309_);
lean_dec(v_as_1308_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object* v_s_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
if (lean_obj_tag(v_a_1319_) == 0)
{
lean_object* v___x_1321_; 
lean_dec(v_s_1318_);
v___x_1321_ = l_List_reverse___redArg(v_a_1320_);
return v___x_1321_;
}
else
{
lean_object* v_head_1322_; lean_object* v_tail_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1332_; 
v_head_1322_ = lean_ctor_get(v_a_1319_, 0);
v_tail_1323_ = lean_ctor_get(v_a_1319_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1319_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1325_ = v_a_1319_;
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_tail_1323_);
lean_inc(v_head_1322_);
lean_dec(v_a_1319_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_inc(v_s_1318_);
v___x_1327_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_1318_, v_head_1322_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_a_1320_);
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_a_1320_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v_a_1319_ = v_tail_1323_;
v_a_1320_ = v___x_1329_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object* v_s_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
if (lean_obj_tag(v_a_1334_) == 0)
{
lean_object* v___x_1336_; 
lean_dec(v_s_1333_);
v___x_1336_ = l_List_reverse___redArg(v_a_1335_);
return v___x_1336_;
}
else
{
lean_object* v_head_1337_; lean_object* v_tail_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1347_; 
v_head_1337_ = lean_ctor_get(v_a_1334_, 0);
v_tail_1338_ = lean_ctor_get(v_a_1334_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_a_1334_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1340_ = v_a_1334_;
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_tail_1338_);
lean_inc(v_head_1337_);
lean_dec(v_a_1334_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
lean_inc(v_s_1333_);
v___x_1342_ = l_Lean_LocalDecl_applyFVarSubst(v_s_1333_, v_head_1337_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v_a_1335_);
lean_ctor_set(v___x_1340_, 0, v___x_1342_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_a_1335_);
v___x_1344_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
v_a_1334_ = v_tail_1338_;
v_a_1335_ = v___x_1344_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object* v_s_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
if (lean_obj_tag(v_a_1349_) == 0)
{
lean_object* v___x_1351_; 
lean_dec(v_s_1348_);
v___x_1351_ = l_List_reverse___redArg(v_a_1350_);
return v___x_1351_;
}
else
{
lean_object* v_head_1352_; lean_object* v_tail_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1372_; 
v_head_1352_ = lean_ctor_get(v_a_1349_, 0);
v_tail_1353_ = lean_ctor_get(v_a_1349_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1349_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1355_ = v_a_1349_;
v_isShared_1356_ = v_isSharedCheck_1372_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_tail_1353_);
lean_inc(v_head_1352_);
lean_dec(v_a_1349_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1372_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_fst_1357_; lean_object* v_snd_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1371_; 
v_fst_1357_ = lean_ctor_get(v_head_1352_, 0);
v_snd_1358_ = lean_ctor_get(v_head_1352_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_head_1352_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1360_ = v_head_1352_;
v_isShared_1361_ = v_isSharedCheck_1371_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_snd_1358_);
lean_inc(v_fst_1357_);
lean_dec(v_head_1352_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1371_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_inc_n(v_s_1348_, 2);
v___x_1362_ = l_Lean_Meta_FVarSubst_apply(v_s_1348_, v_fst_1357_);
lean_dec(v_fst_1357_);
v___x_1363_ = l_Lean_Meta_FVarSubst_apply(v_s_1348_, v_snd_1358_);
lean_dec(v_snd_1358_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1363_);
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v_a_1350_);
lean_ctor_set(v___x_1355_, 0, v___x_1365_);
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1350_);
v___x_1367_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
v_a_1349_ = v_tail_1353_;
v_a_1350_ = v___x_1367_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object* v_s_1373_, lean_object* v_alt_1374_){
_start:
{
lean_object* v_ref_1375_; lean_object* v_idx_1376_; lean_object* v_rhs_1377_; lean_object* v_fvarDecls_1378_; lean_object* v_patterns_1379_; lean_object* v_cnstrs_1380_; lean_object* v_notAltIdxs_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1393_; 
v_ref_1375_ = lean_ctor_get(v_alt_1374_, 0);
v_idx_1376_ = lean_ctor_get(v_alt_1374_, 1);
v_rhs_1377_ = lean_ctor_get(v_alt_1374_, 2);
v_fvarDecls_1378_ = lean_ctor_get(v_alt_1374_, 3);
v_patterns_1379_ = lean_ctor_get(v_alt_1374_, 4);
v_cnstrs_1380_ = lean_ctor_get(v_alt_1374_, 5);
v_notAltIdxs_1381_ = lean_ctor_get(v_alt_1374_, 6);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_alt_1374_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1383_ = v_alt_1374_;
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_notAltIdxs_1381_);
lean_inc(v_cnstrs_1380_);
lean_inc(v_patterns_1379_);
lean_inc(v_fvarDecls_1378_);
lean_inc(v_rhs_1377_);
lean_inc(v_idx_1376_);
lean_inc(v_ref_1375_);
lean_dec(v_alt_1374_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_inc_n(v_s_1373_, 3);
v___x_1385_ = l_Lean_Meta_FVarSubst_apply(v_s_1373_, v_rhs_1377_);
lean_dec_ref(v_rhs_1377_);
v___x_1386_ = lean_box(0);
v___x_1387_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(v_s_1373_, v_fvarDecls_1378_, v___x_1386_);
v___x_1388_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(v_s_1373_, v_patterns_1379_, v___x_1386_);
v___x_1389_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(v_s_1373_, v_cnstrs_1380_, v___x_1386_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 5, v___x_1389_);
lean_ctor_set(v___x_1383_, 4, v___x_1388_);
lean_ctor_set(v___x_1383_, 3, v___x_1387_);
lean_ctor_set(v___x_1383_, 2, v___x_1385_);
v___x_1391_ = v___x_1383_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_ref_1375_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_idx_1376_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1392_, 5, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 6, v_notAltIdxs_1381_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object* v_fvarId_1394_, lean_object* v_v_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
if (lean_obj_tag(v_a_1396_) == 0)
{
lean_object* v___x_1398_; 
lean_dec_ref(v_v_1395_);
lean_dec(v_fvarId_1394_);
v___x_1398_ = l_List_reverse___redArg(v_a_1397_);
return v___x_1398_;
}
else
{
lean_object* v_head_1399_; lean_object* v_tail_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1409_; 
v_head_1399_ = lean_ctor_get(v_a_1396_, 0);
v_tail_1400_ = lean_ctor_get(v_a_1396_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1402_ = v_a_1396_;
v_isShared_1403_ = v_isSharedCheck_1409_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_tail_1400_);
lean_inc(v_head_1399_);
lean_dec(v_a_1396_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1409_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_inc_ref(v_v_1395_);
lean_inc(v_fvarId_1394_);
v___x_1404_ = l_Lean_Meta_Match_Pattern_replaceFVarId(v_fvarId_1394_, v_v_1395_, v_head_1399_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v_a_1397_);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_a_1397_);
v___x_1406_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v_a_1396_ = v_tail_1400_;
v_a_1397_ = v___x_1406_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object* v_fvarId_1410_, lean_object* v_v_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
if (lean_obj_tag(v_a_1412_) == 0)
{
lean_object* v___x_1414_; 
lean_dec(v_fvarId_1410_);
v___x_1414_ = l_List_reverse___redArg(v_a_1413_);
return v___x_1414_;
}
else
{
lean_object* v_head_1415_; lean_object* v_tail_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1425_; 
v_head_1415_ = lean_ctor_get(v_a_1412_, 0);
v_tail_1416_ = lean_ctor_get(v_a_1412_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_a_1412_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1418_ = v_a_1412_;
v_isShared_1419_ = v_isSharedCheck_1425_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_tail_1416_);
lean_inc(v_head_1415_);
lean_dec(v_a_1412_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1425_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_inc(v_fvarId_1410_);
v___x_1420_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_1410_, v_v_1411_, v_head_1415_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_a_1413_);
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_a_1413_);
v___x_1422_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
v_a_1412_ = v_tail_1416_;
v_a_1413_ = v___x_1422_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_1426_, lean_object* v_v_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1426_, v_v_1427_, v_a_1428_, v_a_1429_);
lean_dec_ref(v_v_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object* v_fvarId_1431_, lean_object* v_v_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_fvarId_1431_);
v___x_1435_ = l_List_reverse___redArg(v_a_1434_);
return v___x_1435_;
}
else
{
lean_object* v_head_1436_; lean_object* v_tail_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1456_; 
v_head_1436_ = lean_ctor_get(v_a_1433_, 0);
v_tail_1437_ = lean_ctor_get(v_a_1433_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1433_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1439_ = v_a_1433_;
v_isShared_1440_ = v_isSharedCheck_1456_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_tail_1437_);
lean_inc(v_head_1436_);
lean_dec(v_a_1433_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1456_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_fst_1441_; lean_object* v_snd_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1455_; 
v_fst_1441_ = lean_ctor_get(v_head_1436_, 0);
v_snd_1442_ = lean_ctor_get(v_head_1436_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_head_1436_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1444_ = v_head_1436_;
v_isShared_1445_ = v_isSharedCheck_1455_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snd_1442_);
lean_inc(v_fst_1441_);
lean_dec(v_head_1436_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1455_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_inc_n(v_fvarId_1431_, 2);
v___x_1446_ = l_Lean_Expr_replaceFVarId(v_fst_1441_, v_fvarId_1431_, v_v_1432_);
lean_dec(v_fst_1441_);
v___x_1447_ = l_Lean_Expr_replaceFVarId(v_snd_1442_, v_fvarId_1431_, v_v_1432_);
lean_dec(v_snd_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1447_);
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1451_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v_a_1434_);
lean_ctor_set(v___x_1439_, 0, v___x_1449_);
v___x_1451_ = v___x_1439_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_a_1434_);
v___x_1451_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
v_a_1433_ = v_tail_1437_;
v_a_1434_ = v___x_1451_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object* v_fvarId_1457_, lean_object* v_v_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1457_, v_v_1458_, v_a_1459_, v_a_1460_);
lean_dec_ref(v_v_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object* v_fvarId_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
if (lean_obj_tag(v_a_1463_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = l_List_reverse___redArg(v_a_1464_);
return v___x_1465_;
}
else
{
lean_object* v_head_1466_; lean_object* v_tail_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1478_; 
v_head_1466_ = lean_ctor_get(v_a_1463_, 0);
v_tail_1467_ = lean_ctor_get(v_a_1463_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_a_1463_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1469_ = v_a_1463_;
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_tail_1467_);
lean_inc(v_head_1466_);
lean_dec(v_a_1463_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1478_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = l_Lean_LocalDecl_fvarId(v_head_1466_);
v___x_1472_ = l_Lean_instBEqFVarId_beq(v___x_1471_, v_fvarId_1462_);
lean_dec(v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1474_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v_a_1464_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_head_1466_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1464_);
v___x_1474_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
v_a_1463_ = v_tail_1467_;
v_a_1464_ = v___x_1474_;
goto _start;
}
}
else
{
lean_del_object(v___x_1469_);
lean_dec(v_head_1466_);
v_a_1463_ = v_tail_1467_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1479_, v_a_1480_, v_a_1481_);
lean_dec(v_fvarId_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object* v_fvarId_1483_, lean_object* v_v_1484_, lean_object* v_alt_1485_){
_start:
{
lean_object* v_ref_1486_; lean_object* v_idx_1487_; lean_object* v_rhs_1488_; lean_object* v_fvarDecls_1489_; lean_object* v_patterns_1490_; lean_object* v_cnstrs_1491_; lean_object* v_notAltIdxs_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1505_; 
v_ref_1486_ = lean_ctor_get(v_alt_1485_, 0);
v_idx_1487_ = lean_ctor_get(v_alt_1485_, 1);
v_rhs_1488_ = lean_ctor_get(v_alt_1485_, 2);
v_fvarDecls_1489_ = lean_ctor_get(v_alt_1485_, 3);
v_patterns_1490_ = lean_ctor_get(v_alt_1485_, 4);
v_cnstrs_1491_ = lean_ctor_get(v_alt_1485_, 5);
v_notAltIdxs_1492_ = lean_ctor_get(v_alt_1485_, 6);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_alt_1485_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1494_ = v_alt_1485_;
v_isShared_1495_ = v_isSharedCheck_1505_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_notAltIdxs_1492_);
lean_inc(v_cnstrs_1491_);
lean_inc(v_patterns_1490_);
lean_inc(v_fvarDecls_1489_);
lean_inc(v_rhs_1488_);
lean_inc(v_idx_1487_);
lean_inc(v_ref_1486_);
lean_dec(v_alt_1485_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1505_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_decls_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_inc_n(v_fvarId_1483_, 3);
v___x_1496_ = l_Lean_Expr_replaceFVarId(v_rhs_1488_, v_fvarId_1483_, v_v_1484_);
lean_dec_ref(v_rhs_1488_);
v___x_1497_ = lean_box(0);
v_decls_1498_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1483_, v_fvarDecls_1489_, v___x_1497_);
v___x_1499_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1483_, v_v_1484_, v_decls_1498_, v___x_1497_);
lean_inc_ref(v_v_1484_);
v___x_1500_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(v_fvarId_1483_, v_v_1484_, v_patterns_1490_, v___x_1497_);
v___x_1501_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1483_, v_v_1484_, v_cnstrs_1491_, v___x_1497_);
lean_dec_ref(v_v_1484_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 5, v___x_1501_);
lean_ctor_set(v___x_1494_, 4, v___x_1500_);
lean_ctor_set(v___x_1494_, 3, v___x_1499_);
lean_ctor_set(v___x_1494_, 2, v___x_1496_);
v___x_1503_ = v___x_1494_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_ref_1486_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_idx_1487_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1504_, 5, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1504_, 6, v_notAltIdxs_1492_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(lean_object* v_fvarId_1506_, lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
uint8_t v___x_1508_; 
v___x_1508_ = 0;
return v___x_1508_;
}
else
{
lean_object* v_head_1509_; lean_object* v_tail_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_head_1509_ = lean_ctor_get(v_x_1507_, 0);
v_tail_1510_ = lean_ctor_get(v_x_1507_, 1);
v___x_1511_ = l_Lean_LocalDecl_fvarId(v_head_1509_);
v___x_1512_ = l_Lean_instBEqFVarId_beq(v___x_1511_, v_fvarId_1506_);
lean_dec(v___x_1511_);
if (v___x_1512_ == 0)
{
v_x_1507_ = v_tail_1510_;
goto _start;
}
else
{
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(lean_object* v_fvarId_1514_, lean_object* v_x_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1514_, v_x_1515_);
lean_dec(v_x_1515_);
lean_dec(v_fvarId_1514_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object* v_fvarId_1518_, lean_object* v_alt_1519_){
_start:
{
lean_object* v_fvarDecls_1520_; uint8_t v___x_1521_; 
v_fvarDecls_1520_ = lean_ctor_get(v_alt_1519_, 3);
v___x_1521_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1518_, v_fvarDecls_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object* v_fvarId_1522_, lean_object* v_alt_1523_){
_start:
{
uint8_t v_res_1524_; lean_object* v_r_1525_; 
v_res_1524_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_1522_, v_alt_1523_);
lean_dec_ref(v_alt_1523_);
lean_dec(v_fvarId_1522_);
v_r_1525_ = lean_box(v_res_1524_);
return v_r_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx(lean_object* v_x_1526_){
_start:
{
switch(lean_obj_tag(v_x_1526_))
{
case 0:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
return v___x_1527_;
}
case 1:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
return v___x_1528_;
}
case 2:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_unsigned_to_nat(2u);
return v___x_1529_;
}
case 3:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_unsigned_to_nat(3u);
return v___x_1530_;
}
default: 
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(4u);
return v___x_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___boxed(lean_object* v_x_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Meta_Match_Example_ctorIdx(v_x_1532_);
lean_dec(v_x_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object* v_t_1534_, lean_object* v_k_1535_){
_start:
{
switch(lean_obj_tag(v_t_1534_))
{
case 1:
{
return v_k_1535_;
}
case 2:
{
lean_object* v_a_1536_; lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1536_ = lean_ctor_get(v_t_1534_, 0);
lean_inc(v_a_1536_);
v_a_1537_ = lean_ctor_get(v_t_1534_, 1);
lean_inc(v_a_1537_);
lean_dec_ref(v_t_1534_);
v___x_1538_ = lean_apply_2(v_k_1535_, v_a_1536_, v_a_1537_);
return v___x_1538_;
}
case 3:
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v_t_1534_, 0);
lean_inc_ref(v_a_1539_);
lean_dec_ref(v_t_1534_);
v___x_1540_ = lean_apply_1(v_k_1535_, v_a_1539_);
return v___x_1540_;
}
default: 
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v_t_1534_, 0);
lean_inc(v_a_1541_);
lean_dec(v_t_1534_);
v___x_1542_ = lean_apply_1(v_k_1535_, v_a_1541_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object* v_motive__1_1543_, lean_object* v_ctorIdx_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1545_, v_k_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object* v_motive__1_1549_, lean_object* v_ctorIdx_1550_, lean_object* v_t_1551_, lean_object* v_h_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Meta_Match_Example_ctorElim(v_motive__1_1549_, v_ctorIdx_1550_, v_t_1551_, v_h_1552_, v_k_1553_);
lean_dec(v_ctorIdx_1550_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object* v_t_1555_, lean_object* v_var_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1555_, v_var_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object* v_motive__1_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_var_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1559_, v_var_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object* v_t_1563_, lean_object* v_underscore_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1563_, v_underscore_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object* v_motive__1_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_underscore_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1567_, v_underscore_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object* v_t_1571_, lean_object* v_ctor_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1571_, v_ctor_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object* v_motive__1_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_ctor_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1575_, v_ctor_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object* v_t_1579_, lean_object* v_val_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1579_, v_val_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object* v_motive__1_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_val_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1583_, v_val_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object* v_t_1587_, lean_object* v_arrayLit_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1587_, v_arrayLit_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object* v_motive__1_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_arrayLit_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1591_, v_arrayLit_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object* v_fvarId_1595_, lean_object* v_ex_1596_, lean_object* v_x_1597_){
_start:
{
switch(lean_obj_tag(v_x_1597_))
{
case 0:
{
lean_object* v_a_1598_; uint8_t v___x_1599_; 
v_a_1598_ = lean_ctor_get(v_x_1597_, 0);
v___x_1599_ = l_Lean_instBEqFVarId_beq(v_a_1598_, v_fvarId_1595_);
if (v___x_1599_ == 0)
{
return v_x_1597_;
}
else
{
lean_dec_ref(v_x_1597_);
lean_inc(v_ex_1596_);
return v_ex_1596_;
}
}
case 2:
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1610_; 
v_a_1600_ = lean_ctor_get(v_x_1597_, 0);
v_a_1601_ = lean_ctor_get(v_x_1597_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_x_1597_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1603_ = v_x_1597_;
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_inc(v_a_1600_);
lean_dec(v_x_1597_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1595_, v_ex_1596_, v_a_1601_, v___x_1605_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1600_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
case 4:
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
v_a_1611_ = lean_ctor_get(v_x_1597_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1597_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1613_ = v_x_1597_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v_x_1597_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1615_ = lean_box(0);
v___x_1616_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1595_, v_ex_1596_, v_a_1611_, v___x_1615_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
default: 
{
return v_x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object* v_fvarId_1621_, lean_object* v_ex_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v___x_1625_; 
v___x_1625_ = l_List_reverse___redArg(v_a_1624_);
return v___x_1625_;
}
else
{
lean_object* v_head_1626_; lean_object* v_tail_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1636_; 
v_head_1626_ = lean_ctor_get(v_a_1623_, 0);
v_tail_1627_ = lean_ctor_get(v_a_1623_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_a_1623_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1629_ = v_a_1623_;
v_isShared_1630_ = v_isSharedCheck_1636_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_tail_1627_);
lean_inc(v_head_1626_);
lean_dec(v_a_1623_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1636_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1621_, v_ex_1622_, v_head_1626_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 1, v_a_1624_);
lean_ctor_set(v___x_1629_, 0, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_a_1624_);
v___x_1633_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
v_a_1623_ = v_tail_1627_;
v_a_1624_ = v___x_1633_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1637_, lean_object* v_ex_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1637_, v_ex_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_ex_1638_);
lean_dec(v_fvarId_1637_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object* v_fvarId_1642_, lean_object* v_ex_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1642_, v_ex_1643_, v_x_1644_);
lean_dec(v_ex_1643_);
lean_dec(v_fvarId_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object* v_s_1646_, lean_object* v_x_1647_){
_start:
{
switch(lean_obj_tag(v_x_1647_))
{
case 0:
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1658_; 
v_a_1648_ = lean_ctor_get(v_x_1647_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1650_ = v_x_1647_;
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v_x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Meta_FVarSubst_get(v_s_1646_, v_a_1648_);
if (lean_obj_tag(v___x_1652_) == 1)
{
lean_object* v_fvarId_1653_; lean_object* v___x_1655_; 
v_fvarId_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_fvarId_1653_);
lean_dec_ref(v___x_1652_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v_fvarId_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_fvarId_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
else
{
lean_object* v___x_1657_; 
lean_dec_ref(v___x_1652_);
lean_del_object(v___x_1650_);
v___x_1657_ = lean_box(1);
return v___x_1657_;
}
}
}
case 2:
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1669_; 
v_a_1659_ = lean_ctor_get(v_x_1647_, 0);
v_a_1660_ = lean_ctor_get(v_x_1647_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1662_ = v_x_1647_;
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v_x_1647_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1664_ = lean_box(0);
v___x_1665_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1646_, v_a_1660_, v___x_1664_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1659_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
case 4:
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1679_; 
v_a_1670_ = lean_ctor_get(v_x_1647_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1672_ = v_x_1647_;
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v_x_1647_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1646_, v_a_1670_, v___x_1674_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
default: 
{
return v_x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object* v_s_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
if (lean_obj_tag(v_a_1681_) == 0)
{
lean_object* v___x_1683_; 
v___x_1683_ = l_List_reverse___redArg(v_a_1682_);
return v___x_1683_;
}
else
{
lean_object* v_head_1684_; lean_object* v_tail_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1694_; 
v_head_1684_ = lean_ctor_get(v_a_1681_, 0);
v_tail_1685_ = lean_ctor_get(v_a_1681_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_a_1681_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1687_ = v_a_1681_;
v_isShared_1688_ = v_isSharedCheck_1694_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_tail_1685_);
lean_inc(v_head_1684_);
lean_dec(v_a_1681_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1694_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1680_, v_head_1684_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 1, v_a_1682_);
lean_ctor_set(v___x_1687_, 0, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_a_1682_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v_a_1681_ = v_tail_1685_;
v_a_1682_ = v___x_1691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object* v_s_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1695_, v_a_1696_, v_a_1697_);
lean_dec(v_s_1695_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object* v_s_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1699_, v_x_1700_);
lean_dec(v_s_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object* v_x_1702_){
_start:
{
switch(lean_obj_tag(v_x_1702_))
{
case 0:
{
lean_object* v___x_1703_; 
lean_dec_ref(v_x_1702_);
v___x_1703_ = lean_box(1);
return v___x_1703_;
}
case 2:
{
lean_object* v_a_1704_; lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1714_; 
v_a_1704_ = lean_ctor_get(v_x_1702_, 0);
v_a_1705_ = lean_ctor_get(v_x_1702_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1707_ = v_x_1702_;
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_inc(v_a_1704_);
lean_dec(v_x_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1705_, v___x_1709_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___x_1710_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1704_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
case 4:
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1724_; 
v_a_1715_ = lean_ctor_get(v_x_1702_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1717_ = v_x_1702_;
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v_x_1702_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1719_ = lean_box(0);
v___x_1720_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1715_, v___x_1719_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1720_);
v___x_1722_ = v___x_1717_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
default: 
{
return v_x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
if (lean_obj_tag(v_a_1725_) == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = l_List_reverse___redArg(v_a_1726_);
return v___x_1727_;
}
else
{
lean_object* v_head_1728_; lean_object* v_tail_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1738_; 
v_head_1728_ = lean_ctor_get(v_a_1725_, 0);
v_tail_1729_ = lean_ctor_get(v_a_1725_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_a_1725_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1731_ = v_a_1725_;
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_tail_1729_);
lean_inc(v_head_1728_);
lean_dec(v_a_1725_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1728_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v_a_1726_);
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_a_1726_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
v_a_1725_ = v_tail_1729_;
v_a_1726_ = v___x_1735_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__1));
v___x_1743_ = l_Lean_MessageData_ofFormat(v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0));
v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
return v_x_1746_;
}
else
{
lean_object* v_head_1748_; lean_object* v_tail_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1760_; 
v_head_1748_ = lean_ctor_get(v_x_1747_, 0);
v_tail_1749_ = lean_ctor_get(v_x_1747_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1751_ = v_x_1747_;
v_isShared_1752_ = v_isSharedCheck_1760_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_tail_1749_);
lean_inc(v_head_1748_);
lean_dec(v_x_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1760_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0, &l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once, _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 7);
lean_ctor_set(v___x_1751_, 1, v___x_1753_);
lean_ctor_set(v___x_1751_, 0, v_x_1746_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_x_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1748_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v_x_1746_ = v___x_1757_;
v_x_1747_ = v_tail_1749_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__4));
v___x_1765_ = l_Lean_MessageData_ofFormat(v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object* v_x_1766_){
_start:
{
switch(lean_obj_tag(v_x_1766_))
{
case 0:
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v_x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v_x_1766_);
v___x_1768_ = l_Lean_mkFVar(v_a_1767_);
v___x_1769_ = l_Lean_MessageData_ofExpr(v___x_1768_);
return v___x_1769_;
}
case 1:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__2, &l_Lean_Meta_Match_Example_toMessageData___closed__2_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__2);
return v___x_1770_;
}
case 2:
{
lean_object* v_a_1771_; 
v_a_1771_ = lean_ctor_get(v_x_1766_, 1);
if (lean_obj_tag(v_a_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1772_ = lean_ctor_get(v_x_1766_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v_x_1766_);
v___x_1773_ = lean_box(0);
v___x_1774_ = l_Lean_mkConst(v_a_1772_, v___x_1773_);
v___x_1775_ = l_Lean_MessageData_ofExpr(v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1791_; 
lean_inc(v_a_1771_);
v_a_1776_ = lean_ctor_get(v_x_1766_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_x_1766_, 1);
lean_dec(v_unused_1792_);
v___x_1778_ = v_x_1766_;
v_isShared_1779_ = v_isSharedCheck_1791_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v_x_1766_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1791_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1780_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_1781_ = 0;
v___x_1782_ = l_Lean_MessageData_ofConstName(v_a_1776_, v___x_1781_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 7);
lean_ctor_set(v___x_1778_, 1, v___x_1782_);
lean_ctor_set(v___x_1778_, 0, v___x_1780_);
v___x_1784_ = v___x_1778_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1785_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_1786_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(v___x_1785_, v_a_1771_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1784_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
return v___x_1789_;
}
}
}
}
case 3:
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v_x_1766_, 0);
lean_inc_ref(v_a_1793_);
lean_dec_ref(v_x_1766_);
v___x_1794_ = l_Lean_MessageData_ofExpr(v_a_1793_);
return v___x_1794_;
}
default: 
{
lean_object* v_a_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1795_ = lean_ctor_get(v_x_1766_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v_x_1766_);
v___x_1796_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__5, &l_Lean_Meta_Match_Example_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__5);
v___x_1797_ = lean_box(0);
v___x_1798_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_1795_, v___x_1797_);
v___x_1799_ = l_Lean_MessageData_ofList(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1796_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
if (lean_obj_tag(v_a_1801_) == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = l_List_reverse___redArg(v_a_1802_);
return v___x_1803_;
}
else
{
lean_object* v_head_1804_; lean_object* v_tail_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1814_; 
v_head_1804_ = lean_ctor_get(v_a_1801_, 0);
v_tail_1805_ = lean_ctor_get(v_a_1801_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1801_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1807_ = v_a_1801_;
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_tail_1805_);
lean_inc(v_head_1804_);
lean_dec(v_a_1801_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1804_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v_a_1802_);
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_a_1802_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v_a_1801_ = v_tail_1805_;
v_a_1802_ = v___x_1811_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
if (lean_obj_tag(v_a_1815_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = l_List_reverse___redArg(v_a_1816_);
return v___x_1817_;
}
else
{
lean_object* v_head_1818_; lean_object* v_tail_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1829_; 
v_head_1818_ = lean_ctor_get(v_a_1815_, 0);
v_tail_1819_ = lean_ctor_get(v_a_1815_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_a_1815_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1821_ = v_a_1815_;
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_tail_1819_);
lean_inc(v_head_1818_);
lean_dec(v_a_1815_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1818_);
v___x_1824_ = l_Lean_Meta_Match_Example_toMessageData(v___x_1823_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v_a_1816_);
lean_ctor_set(v___x_1821_, 0, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_a_1816_);
v___x_1826_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v_a_1815_ = v_tail_1819_;
v_a_1816_ = v___x_1826_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object* v_cex_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(v_cex_1830_, v___x_1831_);
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_1834_ = l_Lean_MessageData_joinSep(v___x_1832_, v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object* v_mvarId_1840_, lean_object* v_x_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1840_, v_x_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1847_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1847_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object* v_mvarId_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object* v_00_u03b1_1872_, lean_object* v_mvarId_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1873_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object* v_00_u03b1_1881_, lean_object* v_mvarId_1882_, lean_object* v_x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(v_00_u03b1_1881_, v_mvarId_1882_, v_x_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object* v_p_1890_, lean_object* v_x_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_mvarId_1897_; lean_object* v___x_1898_; 
v_mvarId_1897_ = lean_ctor_get(v_p_1890_, 0);
lean_inc(v_mvarId_1897_);
lean_dec_ref(v_p_1890_);
v___x_1898_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1897_, v_x_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object* v_p_1899_, lean_object* v_x_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1899_, v_x_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* v_00_u03b1_1907_, lean_object* v_p_1908_, lean_object* v_x_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1908_, v_x_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_p_1917_, lean_object* v_x_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Meta_Match_withGoalOf(v_00_u03b1_1916_, v_p_1917_, v_x_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object* v_x_1925_, lean_object* v_x_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = l_List_reverse___redArg(v_x_1926_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
else
{
lean_object* v_head_1934_; lean_object* v_tail_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1953_; 
v_head_1934_ = lean_ctor_get(v_x_1925_, 0);
v_tail_1935_ = lean_ctor_get(v_x_1925_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1925_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1937_ = v_x_1925_;
v_isShared_1938_ = v_isSharedCheck_1953_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_tail_1935_);
lean_inc(v_head_1934_);
lean_dec(v_x_1925_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1953_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_Meta_Match_Alt_toMessageData(v_head_1934_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v_x_1926_);
lean_ctor_set(v___x_1937_, 0, v_a_1940_);
v___x_1942_ = v___x_1937_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1940_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_x_1926_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_x_1925_ = v_tail_1935_;
v_x_1926_ = v___x_1942_;
goto _start;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1937_);
lean_dec(v_tail_1935_);
lean_dec(v_x_1926_);
v_a_1945_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1939_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1939_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object* v_x_1954_, lean_object* v_x_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_x_1954_, v_x_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object* v_x_1962_, lean_object* v_x_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
if (lean_obj_tag(v_x_1962_) == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = l_List_reverse___redArg(v_x_1963_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
else
{
lean_object* v_head_1971_; lean_object* v_tail_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1997_; 
v_head_1971_ = lean_ctor_get(v_x_1962_, 0);
v_tail_1972_ = lean_ctor_get(v_x_1962_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_x_1962_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1974_ = v_x_1962_;
v_isShared_1975_ = v_isSharedCheck_1997_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_tail_1972_);
lean_inc(v_head_1971_);
lean_dec(v_x_1962_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1997_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; 
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
lean_inc(v_head_1971_);
v___x_1976_ = lean_infer_type(v_head_1971_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_MessageData_ofExpr(v_head_1971_);
v___x_1979_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_MessageData_ofExpr(v_a_1977_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v_x_1963_);
lean_ctor_set(v___x_1974_, 0, v___x_1984_);
v___x_1986_ = v___x_1974_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_x_1963_);
v___x_1986_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v_x_1962_ = v_tail_1972_;
v_x_1963_ = v___x_1986_;
goto _start;
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_del_object(v___x_1974_);
lean_dec(v_tail_1972_);
lean_dec(v_head_1971_);
lean_dec(v_x_1963_);
v_a_1989_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1976_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1976_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_x_1998_, v_x_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2005_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2));
v___x_2011_ = l_Lean_stringToMessageData(v___x_2010_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_box(1);
v___x_2013_ = l_Lean_MessageData_ofFormat(v___x_2012_);
return v___x_2013_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object* v_alts_2017_, lean_object* v___x_2018_, lean_object* v_vars_2019_, lean_object* v_examples_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
lean_inc(v___x_2018_);
v___x_2026_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_alts_2017_, v___x_2018_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
lean_inc(v___x_2018_);
v___x_2028_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_vars_2019_, v___x_2018_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2052_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2052_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2052_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2033_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1);
v___x_2034_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v_a_2029_, v___x_2018_);
v___x_2035_ = l_Lean_MessageData_ofList(v___x_2034_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2033_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2040_ = l_Lean_MessageData_joinSep(v_a_2027_, v___x_2039_);
v___x_2041_ = l_Lean_indentD(v___x_2040_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2038_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_2020_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2048_);
v___x_2050_ = v___x_2031_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2027_);
lean_dec(v_examples_2020_);
lean_dec(v___x_2018_);
v_a_2053_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2028_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2028_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_examples_2020_);
lean_dec(v_vars_2019_);
lean_dec(v___x_2018_);
v_a_2061_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2026_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2026_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object* v_alts_2069_, lean_object* v___x_2070_, lean_object* v_vars_2071_, lean_object* v_examples_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(v_alts_2069_, v___x_2070_, v_vars_2071_, v_examples_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* v_p_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_vars_2085_; lean_object* v_alts_2086_; lean_object* v_examples_2087_; lean_object* v___x_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; 
v_vars_2085_ = lean_ctor_get(v_p_2079_, 1);
v_alts_2086_ = lean_ctor_get(v_p_2079_, 2);
v_examples_2087_ = lean_ctor_get(v_p_2079_, 3);
v___x_2088_ = lean_box(0);
lean_inc(v_examples_2087_);
lean_inc(v_vars_2085_);
lean_inc(v_alts_2086_);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2089_, 0, v_alts_2086_);
lean_closure_set(v___f_2089_, 1, v___x_2088_);
lean_closure_set(v___f_2089_, 2, v_vars_2085_);
lean_closure_set(v___f_2089_, 3, v_examples_2087_);
v___x_2090_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_2079_, v___f_2089_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object* v_p_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Meta_Match_Problem_toMessageData(v_p_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object* v_cex_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
if (lean_obj_tag(v_a_2100_) == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = l_List_reverse___redArg(v_a_2101_);
return v___x_2102_;
}
else
{
lean_object* v_head_2103_; lean_object* v_tail_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2113_; 
v_head_2103_ = lean_ctor_get(v_a_2100_, 0);
v_tail_2104_ = lean_ctor_get(v_a_2100_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_a_2100_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2106_ = v_a_2100_;
v_isShared_2107_ = v_isSharedCheck_2113_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_tail_2104_);
lean_inc(v_head_2103_);
lean_dec(v_a_2100_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2113_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = l_Lean_Meta_Match_examplesToMessageData(v_head_2103_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v_a_2101_);
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_a_2101_);
v___x_2110_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
v_a_2100_ = v_tail_2104_;
v_a_2101_ = v___x_2110_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object* v_cexs_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2115_ = lean_array_to_list(v_cexs_2114_);
v___x_2116_ = lean_box(0);
v___x_2117_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(v___x_2115_, v___x_2116_);
v___x_2118_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2119_ = l_Lean_MessageData_joinSep(v___x_2117_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object* v_msg_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_ref_2126_; lean_object* v___x_2127_; lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2136_; 
v_ref_2126_ = lean_ctor_get(v___y_2123_, 5);
v___x_2127_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msg_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2136_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2136_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_inc(v_ref_2126_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_ref_2126_);
lean_ctor_set(v___x_2132_, 1, v_a_2128_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 1);
lean_ctor_set(v___x_2130_, 0, v___x_2132_);
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object* v_msg_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2143_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__0));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__2));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4(void){
_start:
{
lean_object* v___x_2150_; lean_object* v_dummy_2151_; 
v___x_2150_ = lean_box(0);
v_dummy_2151_ = l_Lean_Expr_sort___override(v___x_2150_);
return v_dummy_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t v_sz_2152_, size_t v_i_2153_, lean_object* v_bs_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_usize_dec_lt(v_i_2153_, v_sz_2152_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_bs_2154_);
return v___x_2161_;
}
else
{
lean_object* v_v_2162_; lean_object* v___x_2163_; 
v_v_2162_ = lean_array_uget_borrowed(v_bs_2154_, v_i_2153_);
lean_inc(v_v_2162_);
v___x_2163_ = l_Lean_Meta_Match_toPattern(v_v_2162_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; lean_object* v_bs_x27_2166_; size_t v___x_2167_; size_t v___x_2168_; lean_object* v___x_2169_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v_bs_x27_2166_ = lean_array_uset(v_bs_2154_, v_i_2153_, v___x_2165_);
v___x_2167_ = ((size_t)1ULL);
v___x_2168_ = lean_usize_add(v_i_2153_, v___x_2167_);
v___x_2169_ = lean_array_uset(v_bs_x27_2166_, v_i_2153_, v_a_2164_);
v_i_2153_ = v___x_2168_;
v_bs_2154_ = v___x_2169_;
goto _start;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_bs_2154_);
v_a_2171_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2163_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2163_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object* v_e_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_inaccessible_x3f(v_e_2179_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Expr_arrayLit_x3f(v_e_2179_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_2179_);
if (lean_obj_tag(v___x_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v_e_2179_);
v_val_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = lean_unsigned_to_nat(2u);
v___x_2199_ = l_Lean_Expr_getAppNumArgs(v_val_2197_);
v___x_2200_ = lean_nat_sub(v___x_2199_, v___x_2198_);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_sub(v___x_2200_, v___x_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = l_Lean_Expr_getRevArg_x21(v_val_2197_, v___x_2202_);
v___x_2204_ = l_Lean_Meta_Match_toPattern(v___x_2203_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2229_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2229_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2229_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_nat_sub(v___x_2199_, v___x_2201_);
v___x_2217_ = lean_nat_sub(v___x_2216_, v___x_2201_);
lean_dec(v___x_2216_);
v___x_2218_ = l_Lean_Expr_getRevArg_x21(v_val_2197_, v___x_2217_);
if (lean_obj_tag(v___x_2218_) == 1)
{
lean_object* v_fvarId_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_fvarId_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_fvarId_2219_);
lean_dec_ref(v___x_2218_);
v___x_2220_ = lean_unsigned_to_nat(3u);
v___x_2221_ = lean_nat_sub(v___x_2199_, v___x_2220_);
lean_dec(v___x_2199_);
v___x_2222_ = lean_nat_sub(v___x_2221_, v___x_2201_);
lean_dec(v___x_2221_);
v___x_2223_ = l_Lean_Expr_getRevArg_x21(v_val_2197_, v___x_2222_);
lean_dec(v_val_2197_);
if (lean_obj_tag(v___x_2223_) == 1)
{
lean_object* v_fvarId_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v_fvarId_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_fvarId_2224_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_2225_, 0, v_fvarId_2219_);
lean_ctor_set(v___x_2225_, 1, v_a_2205_);
lean_ctor_set(v___x_2225_, 2, v_fvarId_2224_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2225_);
v___x_2227_ = v___x_2207_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_dec_ref(v___x_2223_);
lean_dec(v_fvarId_2219_);
lean_del_object(v___x_2207_);
lean_dec(v_a_2205_);
v___y_2210_ = v_a_2180_;
v___y_2211_ = v_a_2181_;
v___y_2212_ = v_a_2182_;
v___y_2213_ = v_a_2183_;
goto v___jp_2209_;
}
}
else
{
lean_dec_ref(v___x_2218_);
lean_del_object(v___x_2207_);
lean_dec(v_a_2205_);
lean_dec(v___x_2199_);
lean_dec(v_val_2197_);
v___y_2210_ = v_a_2180_;
v___y_2211_ = v_a_2181_;
v___y_2212_ = v_a_2182_;
v___y_2213_ = v_a_2183_;
goto v___jp_2209_;
}
v___jp_2209_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__3, &l_Lean_Meta_Match_toPattern___closed__3_once, _init_l_Lean_Meta_Match_toPattern___closed__3);
v___x_2215_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2214_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2215_;
}
}
}
else
{
lean_dec(v___x_2199_);
lean_dec(v_val_2197_);
return v___x_2204_;
}
}
else
{
lean_object* v___x_2230_; 
lean_dec(v___x_2196_);
lean_inc_ref(v_e_2179_);
v___x_2230_ = l_Lean_Meta_isMatchValue(v_e_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2323_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2323_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2323_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_unbox(v_a_2231_);
lean_dec(v_a_2231_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
v___x_2236_ = l_Lean_Expr_isFVar(v_e_2179_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; 
lean_del_object(v___x_2233_);
lean_inc(v_a_2183_);
lean_inc_ref(v_a_2182_);
lean_inc(v_a_2181_);
lean_inc_ref(v_a_2180_);
lean_inc_ref(v_e_2179_);
v___x_2237_ = lean_whnf(v_e_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; uint8_t v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = lean_expr_eqv(v_a_2238_, v_e_2179_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_e_2179_);
v_e_2179_ = v_a_2238_;
goto _start;
}
else
{
if (v___x_2236_ == 0)
{
lean_object* v___x_2241_; 
lean_dec(v_a_2238_);
v___x_2241_ = l_Lean_Expr_getAppFn(v_e_2179_);
if (lean_obj_tag(v___x_2241_) == 4)
{
lean_object* v_declName_2242_; lean_object* v_us_2243_; lean_object* v___x_2244_; lean_object* v_env_2245_; lean_object* v___x_2246_; 
v_declName_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_declName_2242_);
v_us_2243_ = lean_ctor_get(v___x_2241_, 1);
lean_inc(v_us_2243_);
lean_dec_ref(v___x_2241_);
v___x_2244_ = lean_st_ref_get(v_a_2183_);
v_env_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc_ref(v_env_2245_);
lean_dec(v___x_2244_);
v___x_2246_ = l_Lean_Environment_find_x3f(v_env_2245_, v_declName_2242_, v___x_2236_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec(v_us_2243_);
v___y_2186_ = v_a_2180_;
v___y_2187_ = v_a_2181_;
v___y_2188_ = v_a_2182_;
v___y_2189_ = v_a_2183_;
goto v___jp_2185_;
}
else
{
lean_object* v_val_2247_; 
v_val_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_val_2247_);
lean_dec_ref(v___x_2246_);
if (lean_obj_tag(v_val_2247_) == 6)
{
lean_object* v_val_2248_; lean_object* v_toConstantVal_2249_; lean_object* v_numParams_2250_; lean_object* v_numFields_2251_; lean_object* v_nargs_2252_; lean_object* v_dummy_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_val_2248_ = lean_ctor_get(v_val_2247_, 0);
lean_inc_ref(v_val_2248_);
lean_dec_ref(v_val_2247_);
v_toConstantVal_2249_ = lean_ctor_get(v_val_2248_, 0);
lean_inc_ref(v_toConstantVal_2249_);
v_numParams_2250_ = lean_ctor_get(v_val_2248_, 3);
lean_inc(v_numParams_2250_);
v_numFields_2251_ = lean_ctor_get(v_val_2248_, 4);
lean_inc(v_numFields_2251_);
lean_dec_ref(v_val_2248_);
v_nargs_2252_ = l_Lean_Expr_getAppNumArgs(v_e_2179_);
v_dummy_2253_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__4, &l_Lean_Meta_Match_toPattern___closed__4_once, _init_l_Lean_Meta_Match_toPattern___closed__4);
lean_inc(v_nargs_2252_);
v___x_2254_ = lean_mk_array(v_nargs_2252_, v_dummy_2253_);
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_nat_sub(v_nargs_2252_, v___x_2255_);
lean_dec(v_nargs_2252_);
lean_inc_ref(v_e_2179_);
v___x_2257_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2179_, v___x_2254_, v___x_2256_);
v___x_2290_ = lean_array_get_size(v___x_2257_);
v___x_2291_ = lean_nat_add(v_numParams_2250_, v_numFields_2251_);
lean_dec(v_numFields_2251_);
v___x_2292_ = lean_nat_dec_eq(v___x_2290_, v___x_2291_);
lean_dec(v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2294_ = l_Lean_indentExpr(v_e_2179_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2295_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_dec_ref(v___x_2296_);
v___y_2259_ = v_a_2180_;
v___y_2260_ = v_a_2181_;
v___y_2261_ = v_a_2182_;
v___y_2262_ = v_a_2183_;
goto v___jp_2258_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v___x_2257_);
lean_dec(v_numParams_2250_);
lean_dec_ref(v_toConstantVal_2249_);
lean_dec(v_us_2243_);
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_dec_ref(v_e_2179_);
v___y_2259_ = v_a_2180_;
v___y_2260_ = v_a_2181_;
v___y_2261_ = v_a_2182_;
v___y_2262_ = v_a_2183_;
goto v___jp_2258_;
}
v___jp_2258_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; size_t v_sz_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2263_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2250_);
v___x_2264_ = l_Array_extract___redArg(v___x_2257_, v___x_2263_, v_numParams_2250_);
v___x_2265_ = lean_array_get_size(v___x_2257_);
v___x_2266_ = l_Array_extract___redArg(v___x_2257_, v_numParams_2250_, v___x_2265_);
lean_dec_ref(v___x_2257_);
v_sz_2267_ = lean_array_size(v___x_2266_);
v___x_2268_ = ((size_t)0ULL);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_2267_, v___x_2268_, v___x_2266_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2281_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_name_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v_name_2274_ = lean_ctor_get(v_toConstantVal_2249_, 0);
lean_inc(v_name_2274_);
lean_dec_ref(v_toConstantVal_2249_);
v___x_2275_ = lean_array_to_list(v___x_2264_);
v___x_2276_ = lean_array_to_list(v_a_2270_);
v___x_2277_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2277_, 0, v_name_2274_);
lean_ctor_set(v___x_2277_, 1, v_us_2243_);
lean_ctor_set(v___x_2277_, 2, v___x_2275_);
lean_ctor_set(v___x_2277_, 3, v___x_2276_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2277_);
v___x_2279_ = v___x_2272_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec_ref(v___x_2264_);
lean_dec_ref(v_toConstantVal_2249_);
lean_dec(v_us_2243_);
v_a_2282_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2269_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2269_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
else
{
lean_dec(v_val_2247_);
lean_dec(v_us_2243_);
v___y_2186_ = v_a_2180_;
v___y_2187_ = v_a_2181_;
v___y_2188_ = v_a_2182_;
v___y_2189_ = v_a_2183_;
goto v___jp_2185_;
}
}
}
else
{
lean_dec_ref(v___x_2241_);
v___y_2186_ = v_a_2180_;
v___y_2187_ = v_a_2181_;
v___y_2188_ = v_a_2182_;
v___y_2189_ = v_a_2183_;
goto v___jp_2185_;
}
}
else
{
lean_dec_ref(v_e_2179_);
v_e_2179_ = v_a_2238_;
goto _start;
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_e_2179_);
v_a_2306_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2237_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2237_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2314_ = l_Lean_Expr_fvarId_x21(v_e_2179_);
lean_dec_ref(v_e_2179_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2315_);
v___x_2317_ = v___x_2233_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_e_2179_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2319_);
v___x_2321_ = v___x_2233_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_e_2179_);
v_a_2324_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2230_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2230_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v_val_2332_; lean_object* v_fst_2333_; lean_object* v_snd_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_e_2179_);
v_val_2332_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_val_2332_);
lean_dec_ref(v___x_2195_);
v_fst_2333_ = lean_ctor_get(v_val_2332_, 0);
v_snd_2334_ = lean_ctor_get(v_val_2332_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_val_2332_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2336_ = v_val_2332_;
v_isShared_2337_ = v_isSharedCheck_2359_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snd_2334_);
lean_inc(v_fst_2333_);
lean_dec(v_val_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2359_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_box(0);
v___x_2339_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_snd_2334_, v___x_2338_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2350_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2350_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2350_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 4);
lean_ctor_set(v___x_2336_, 1, v_a_2340_);
v___x_2345_ = v___x_2336_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_fst_2333_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2345_);
v___x_2347_ = v___x_2342_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2336_);
lean_dec(v_fst_2333_);
v_a_2351_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2339_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2339_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
else
{
lean_object* v_val_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v_e_2179_);
v_val_2360_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2362_ = v___x_2194_;
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_val_2360_);
lean_dec(v___x_2194_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 0);
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_val_2360_);
v___x_2365_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
}
}
v___jp_2185_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2190_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2191_ = l_Lean_indentExpr(v_e_2179_);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2192_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
return v___x_2193_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object* v_x_2369_, lean_object* v_x_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = l_List_reverse___redArg(v_x_2370_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
else
{
lean_object* v_head_2378_; lean_object* v_tail_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2397_; 
v_head_2378_ = lean_ctor_get(v_x_2369_, 0);
v_tail_2379_ = lean_ctor_get(v_x_2369_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_x_2369_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2381_ = v_x_2369_;
v_isShared_2382_ = v_isSharedCheck_2397_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_tail_2379_);
lean_inc(v_head_2378_);
lean_dec(v_x_2369_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2397_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_Meta_Match_toPattern(v_head_2378_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref(v___x_2383_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v_x_2370_);
lean_ctor_set(v___x_2381_, 0, v_a_2384_);
v___x_2386_ = v___x_2381_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2384_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_x_2370_);
v___x_2386_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
v_x_2369_ = v_tail_2379_;
v_x_2370_ = v___x_2386_;
goto _start;
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_del_object(v___x_2381_);
lean_dec(v_tail_2379_);
lean_dec(v_x_2370_);
v_a_2389_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2383_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2383_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object* v_x_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_x_2398_, v_x_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object* v_sz_2406_, lean_object* v_i_2407_, lean_object* v_bs_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
size_t v_sz_boxed_2414_; size_t v_i_boxed_2415_; lean_object* v_res_2416_; 
v_sz_boxed_2414_ = lean_unbox_usize(v_sz_2406_);
lean_dec(v_sz_2406_);
v_i_boxed_2415_ = lean_unbox_usize(v_i_2407_);
lean_dec(v_i_2407_);
v_res_2416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_2414_, v_i_boxed_2415_, v_bs_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object* v_e_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_Match_toPattern(v_e_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object* v_00_u03b1_2424_, lean_object* v_msg_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_msg_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(v_00_u03b1_2432_, v_msg_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2439_;
}
}
static lean_object* _init_l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2447_ = lean_string_utf8_byte_size(v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object* v_s_2448_){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2449_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2450_ = lean_string_utf8_byte_size(v_s_2448_);
v___x_2451_ = lean_obj_once(&l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0, &l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0);
v___x_2452_ = lean_nat_dec_le(v___x_2451_, v___x_2450_);
if (v___x_2452_ == 0)
{
lean_dec_ref(v_s_2448_);
return v___x_2452_;
}
else
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = lean_string_memcmp(v_s_2448_, v___x_2449_, v___x_2453_, v___x_2453_, v___x_2451_);
if (v___x_2454_ == 0)
{
lean_dec_ref(v_s_2448_);
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2455_ = lean_unsigned_to_nat(9u);
lean_inc_ref(v_s_2448_);
v___x_2456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2456_, 0, v_s_2448_);
lean_ctor_set(v___x_2456_, 1, v___x_2453_);
lean_ctor_set(v___x_2456_, 2, v___x_2450_);
v___x_2457_ = l_String_Slice_Pos_nextn(v___x_2456_, v___x_2453_, v___x_2455_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2458_, 0, v_s_2448_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
lean_ctor_set(v___x_2458_, 2, v___x_2450_);
v___x_2459_ = l_String_Slice_isNat(v___x_2458_);
lean_dec_ref(v___x_2458_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object* v_s_2460_){
_start:
{
uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_res_2461_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_2460_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
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
