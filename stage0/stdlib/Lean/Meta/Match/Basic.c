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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Match_Pattern_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 1:
{
lean_object* v_fvarId_7_; lean_object* v___x_8_; 
v_fvarId_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_fvarId_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_fvarId_7_);
return v___x_8_;
}
case 2:
{
lean_object* v_ctorName_9_; lean_object* v_us_10_; lean_object* v_params_11_; lean_object* v_fields_12_; lean_object* v___x_13_; 
v_ctorName_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ctorName_9_);
v_us_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_us_10_);
v_params_11_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_params_11_);
v_fields_12_ = lean_ctor_get(v_t_5_, 3);
lean_inc(v_fields_12_);
lean_dec_ref_known(v_t_5_, 4);
v___x_13_ = lean_apply_4(v_k_6_, v_ctorName_9_, v_us_10_, v_params_11_, v_fields_12_);
return v___x_13_;
}
case 4:
{
lean_object* v_type_14_; lean_object* v_xs_15_; lean_object* v___x_16_; 
v_type_14_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_type_14_);
v_xs_15_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_xs_15_);
lean_dec_ref_known(v_t_5_, 2);
v___x_16_ = lean_apply_2(v_k_6_, v_type_14_, v_xs_15_);
return v___x_16_;
}
case 5:
{
lean_object* v_varId_17_; lean_object* v_p_18_; lean_object* v_hId_19_; lean_object* v___x_20_; 
v_varId_17_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_varId_17_);
v_p_18_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_p_18_);
v_hId_19_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_hId_19_);
lean_dec_ref_known(v_t_5_, 3);
v___x_20_ = lean_apply_3(v_k_6_, v_varId_17_, v_p_18_, v_hId_19_);
return v___x_20_;
}
default: 
{
lean_object* v_e_21_; lean_object* v___x_22_; 
v_e_21_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_21_);
lean_dec_ref(v_t_5_);
v___x_22_ = lean_apply_1(v_k_6_, v_e_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim(lean_object* v_motive__1_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_25_, v_k_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctorElim___boxed(lean_object* v_motive__1_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_Match_Pattern_ctorElim(v_motive__1_29_, v_ctorIdx_30_, v_t_31_, v_h_32_, v_k_33_);
lean_dec(v_ctorIdx_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim___redArg(lean_object* v_t_35_, lean_object* v_inaccessible_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_35_, v_inaccessible_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_inaccessible_elim(lean_object* v_motive__1_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_inaccessible_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_39_, v_inaccessible_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim___redArg(lean_object* v_t_43_, lean_object* v_var_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_43_, v_var_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_var_elim(lean_object* v_motive__1_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_var_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_47_, v_var_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim___redArg(lean_object* v_t_51_, lean_object* v_ctor_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_51_, v_ctor_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_ctor_elim(lean_object* v_motive__1_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_ctor_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_55_, v_ctor_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim___redArg(lean_object* v_t_59_, lean_object* v_val_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_59_, v_val_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_val_elim(lean_object* v_motive__1_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_val_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_63_, v_val_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim___redArg(lean_object* v_t_67_, lean_object* v_arrayLit_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_67_, v_arrayLit_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_arrayLit_elim(lean_object* v_motive__1_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_arrayLit_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_71_, v_arrayLit_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim___redArg(lean_object* v_t_75_, lean_object* v_as_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_75_, v_as_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_as_elim(lean_object* v_motive__1_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_as_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Match_Pattern_ctorElim___redArg(v_t_79_, v_as_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_box(0);
v___x_87_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedPattern_default___closed__1));
v___x_88_ = l_Lean_Expr_const___override(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern_default(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__3, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__3_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__3);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedPattern(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_Match_instInhabitedPattern_default;
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__0));
v___x_95_ = l_Lean_stringToMessageData(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__2));
v___x_98_ = l_Lean_stringToMessageData(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__4));
v___x_101_ = l_Lean_stringToMessageData(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_box(0);
v___x_103_ = l_Lean_MessageData_ofFormat(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__1));
v___x_108_ = l_Lean_MessageData_ofFormat(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
return v_x_109_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_123_; 
v_head_111_ = lean_ctor_get(v_x_110_, 0);
v_tail_112_ = lean_ctor_get(v_x_110_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_110_);
if (v_isSharedCheck_123_ == 0)
{
v___x_114_ = v_x_110_;
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_tail_112_);
lean_inc(v_head_111_);
lean_dec(v_x_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2, &l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2_once, _init_l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__2);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 7);
lean_ctor_set(v___x_114_, 1, v___x_116_);
lean_ctor_set(v___x_114_, 0, v_x_109_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_x_109_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_116_);
v___x_118_ = v_reuseFailAlloc_122_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_111_);
v___x_120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v_x_109_ = v___x_120_;
v_x_110_ = v_tail_112_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__7));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__10));
v___x_131_ = l_Lean_MessageData_ofFormat(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__12));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_toMessageData___closed__14));
v___x_137_ = l_Lean_stringToMessageData(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object* v_x_138_){
_start:
{
switch(lean_obj_tag(v_x_138_))
{
case 0:
{
lean_object* v_e_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_e_139_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_e_139_);
lean_dec_ref_known(v_x_138_, 1);
v___x_140_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__1, &l_Lean_Meta_Match_Pattern_toMessageData___closed__1_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__1);
v___x_141_ = l_Lean_MessageData_ofExpr(v_e_139_);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
return v___x_144_;
}
case 1:
{
lean_object* v_fvarId_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_fvarId_145_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_fvarId_145_);
lean_dec_ref_known(v_x_138_, 1);
v___x_146_ = l_Lean_mkFVar(v_fvarId_145_);
v___x_147_ = l_Lean_MessageData_ofExpr(v___x_146_);
return v___x_147_;
}
case 2:
{
lean_object* v_fields_148_; 
v_fields_148_ = lean_ctor_get(v_x_138_, 3);
if (lean_obj_tag(v_fields_148_) == 0)
{
lean_object* v_ctorName_149_; lean_object* v___x_150_; 
v_ctorName_149_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_ctorName_149_);
lean_dec_ref_known(v_x_138_, 4);
v___x_150_ = l_Lean_MessageData_ofName(v_ctorName_149_);
return v___x_150_;
}
else
{
lean_object* v_ctorName_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc(v_fields_148_);
v_ctorName_151_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_ctorName_151_);
lean_dec_ref_known(v_x_138_, 4);
v___x_152_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_153_ = l_Lean_MessageData_ofName(v_ctorName_151_);
v___x_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_156_ = l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0(v___x_155_, v_fields_148_);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
return v___x_159_;
}
}
case 3:
{
lean_object* v_e_160_; lean_object* v___x_161_; 
v_e_160_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_e_160_);
lean_dec_ref_known(v_x_138_, 1);
v___x_161_ = l_Lean_MessageData_ofExpr(v_e_160_);
return v___x_161_;
}
case 4:
{
lean_object* v_xs_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_176_; 
v_xs_162_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_x_138_, 0);
lean_dec(v_unused_177_);
v___x_164_ = v_x_138_;
v_isShared_165_ = v_isSharedCheck_176_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_xs_162_);
lean_dec(v_x_138_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_176_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_166_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__8, &l_Lean_Meta_Match_Pattern_toMessageData___closed__8_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__8);
v___x_167_ = lean_box(0);
v___x_168_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(v_xs_162_, v___x_167_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_170_ = l_Lean_MessageData_joinSep(v___x_168_, v___x_169_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 7);
lean_ctor_set(v___x_164_, 1, v___x_170_);
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_172_ = v___x_164_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_175_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__13, &l_Lean_Meta_Match_Pattern_toMessageData___closed__13_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__13);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
return v___x_174_;
}
}
}
default: 
{
lean_object* v_varId_178_; lean_object* v_p_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_varId_178_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_varId_178_);
v_p_179_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_p_179_);
lean_dec_ref_known(v_x_138_, 3);
v___x_180_ = l_Lean_mkFVar(v_varId_178_);
v___x_181_ = l_Lean_MessageData_ofExpr(v___x_180_);
v___x_182_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__15, &l_Lean_Meta_Match_Pattern_toMessageData___closed__15_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__15);
v___x_183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_Meta_Match_Pattern_toMessageData(v_p_179_);
v___x_185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
if (lean_obj_tag(v_a_186_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = l_List_reverse___redArg(v_a_187_);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_199_; 
v_head_189_ = lean_ctor_get(v_a_186_, 0);
v_tail_190_ = lean_ctor_get(v_a_186_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_a_186_);
if (v_isSharedCheck_199_ == 0)
{
v___x_192_ = v_a_186_;
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_tail_190_);
lean_inc(v_head_189_);
lean_dec(v_a_186_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_Meta_Match_Pattern_toMessageData(v_head_189_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v_a_187_);
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_187_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
v_a_186_ = v_tail_190_;
v_a_187_ = v___x_196_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(uint8_t v_annotate_200_, lean_object* v_p_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
switch(lean_obj_tag(v_p_201_))
{
case 0:
{
if (v_annotate_200_ == 0)
{
lean_object* v_e_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_e_207_ = lean_ctor_get(v_p_201_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_p_201_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_p_201_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_e_207_);
lean_dec(v_p_201_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_e_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_e_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_e_215_ = lean_ctor_get(v_p_201_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v_p_201_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v_p_201_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_e_215_);
lean_dec(v_p_201_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = l_Lean_mkInaccessible(v_e_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_fvarId_224_ = lean_ctor_get(v_p_201_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_p_201_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v_p_201_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_fvarId_224_);
lean_dec(v_p_201_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = l_Lean_mkFVar(v_fvarId_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 0);
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
case 2:
{
lean_object* v_ctorName_233_; lean_object* v_us_234_; lean_object* v_params_235_; lean_object* v_fields_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_ctorName_233_ = lean_ctor_get(v_p_201_, 0);
lean_inc(v_ctorName_233_);
v_us_234_ = lean_ctor_get(v_p_201_, 1);
lean_inc(v_us_234_);
v_params_235_ = lean_ctor_get(v_p_201_, 2);
lean_inc(v_params_235_);
v_fields_236_ = lean_ctor_get(v_p_201_, 3);
lean_inc(v_fields_236_);
lean_dec_ref_known(v_p_201_, 4);
v___x_237_ = lean_box(0);
v___x_238_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_200_, v_fields_236_, v___x_237_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_250_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_250_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_250_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_250_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_243_ = l_Lean_mkConst(v_ctorName_233_, v_us_234_);
v___x_244_ = l_List_appendTR___redArg(v_params_235_, v_a_239_);
v___x_245_ = lean_array_mk(v___x_244_);
v___x_246_ = l_Lean_mkAppN(v___x_243_, v___x_245_);
lean_dec_ref(v___x_245_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_246_);
v___x_248_ = v___x_241_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_params_235_);
lean_dec(v_us_234_);
lean_dec(v_ctorName_233_);
v_a_251_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_238_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_238_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
case 3:
{
lean_object* v_e_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_e_259_ = lean_ctor_get(v_p_201_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_p_201_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v_p_201_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_e_259_);
lean_dec(v_p_201_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 0);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_e_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
case 4:
{
lean_object* v_type_267_; lean_object* v_xs_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_type_267_ = lean_ctor_get(v_p_201_, 0);
lean_inc_ref(v_type_267_);
v_xs_268_ = lean_ctor_get(v_p_201_, 1);
lean_inc(v_xs_268_);
lean_dec_ref_known(v_p_201_, 2);
v___x_269_ = lean_box(0);
v___x_270_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_200_, v_xs_268_, v___x_269_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l_Lean_Meta_mkArrayLit(v_type_267_, v_a_271_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_272_;
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_type_267_);
v_a_273_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_270_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_270_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
default: 
{
if (v_annotate_200_ == 0)
{
lean_object* v_p_281_; 
v_p_281_ = lean_ctor_get(v_p_201_, 1);
lean_inc_ref(v_p_281_);
lean_dec_ref_known(v_p_201_, 3);
v_p_201_ = v_p_281_;
goto _start;
}
else
{
lean_object* v_varId_283_; lean_object* v_p_284_; lean_object* v_hId_285_; lean_object* v___x_286_; 
v_varId_283_ = lean_ctor_get(v_p_201_, 0);
lean_inc(v_varId_283_);
v_p_284_ = lean_ctor_get(v_p_201_, 1);
lean_inc_ref(v_p_284_);
v_hId_285_ = lean_ctor_get(v_p_201_, 2);
lean_inc(v_hId_285_);
lean_dec_ref_known(v_p_201_, 3);
v___x_286_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_200_, v_p_284_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_mkFVar(v_varId_283_);
v___x_289_ = l_Lean_mkFVar(v_hId_285_);
v___x_290_ = l_Lean_Meta_Match_mkNamedPattern(v___x_288_, v___x_289_, v_a_287_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_290_;
}
else
{
lean_dec(v_hId_285_);
lean_dec(v_varId_283_);
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_0interp(lean_interpreter_value* stack)
{
uint8_t v_annotate_200_ = stack[0].m_num;
lean_object* v_p_201_ = stack[1].m_obj;
lean_object* v_a_202_ = stack[2].m_obj;
lean_object* v_a_203_ = stack[3].m_obj;
lean_object* v_a_204_ = stack[4].m_obj;
lean_object* v_a_205_ = stack[5].m_obj;
lean_object* v_res_291_;
v_res_291_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_200_, v_p_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
stack->m_obj
 = v_res_291_;
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(uint8_t v_annotate_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_List_reverse___redArg(v_x_294_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v_head_302_; lean_object* v_tail_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_321_; 
v_head_302_ = lean_ctor_get(v_x_293_, 0);
v_tail_303_ = lean_ctor_get(v_x_293_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_321_ == 0)
{
v___x_305_ = v_x_293_;
v_isShared_306_ = v_isSharedCheck_321_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_tail_303_);
lean_inc(v_head_302_);
lean_dec(v_x_293_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_321_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_292_, v_head_302_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_x_294_);
lean_ctor_set(v___x_305_, 0, v_a_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_308_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_x_294_);
v___x_310_ = v_reuseFailAlloc_312_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
v_x_293_ = v_tail_303_;
v_x_294_ = v___x_310_;
goto _start;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_del_object(v___x_305_);
lean_dec(v_tail_303_);
lean_dec(v_x_294_);
v_a_313_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_307_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_307_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_annotate_292_ = stack[0].m_num;
lean_object* v_x_293_ = stack[1].m_obj;
lean_object* v_x_294_ = stack[2].m_obj;
lean_object* v___y_295_ = stack[3].m_obj;
lean_object* v___y_296_ = stack[4].m_obj;
lean_object* v___y_297_ = stack[5].m_obj;
lean_object* v___y_298_ = stack[6].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_292_, v_x_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(lean_object* v_annotate_323_, lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v_annotate_boxed_331_; lean_object* v_res_332_; 
v_annotate_boxed_331_ = lean_unbox(v_annotate_323_);
v_res_332_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_boxed_331_, v_x_324_, v_x_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object* v_annotate_333_, lean_object* v_p_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
uint8_t v_annotate_boxed_340_; lean_object* v_res_341_; 
v_annotate_boxed_340_ = lean_unbox(v_annotate_333_);
v_res_341_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_boxed_340_, v_p_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_341_;
}
}
lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object* v_p_342_, uint8_t v_annotate_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_343_, v_p_342_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Pattern_toExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_342_ = stack[0].m_obj;
uint8_t v_annotate_343_ = stack[1].m_num;
lean_object* v_a_344_ = stack[2].m_obj;
lean_object* v_a_345_ = stack[3].m_obj;
lean_object* v_a_346_ = stack[4].m_obj;
lean_object* v_a_347_ = stack[5].m_obj;
lean_object* v_res_350_;
v_res_350_ = l_Lean_Meta_Match_Pattern_toExpr(v_p_342_, v_annotate_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object* v_p_351_, lean_object* v_annotate_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
uint8_t v_annotate_boxed_358_; lean_object* v_res_359_; 
v_annotate_boxed_358_ = lean_unbox(v_annotate_352_);
v_res_359_ = l_Lean_Meta_Match_Pattern_toExpr(v_p_351_, v_annotate_boxed_358_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(lean_object* v_s_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
if (lean_obj_tag(v_a_361_) == 0)
{
lean_object* v___x_363_; 
lean_dec(v_s_360_);
v___x_363_ = l_List_reverse___redArg(v_a_362_);
return v___x_363_;
}
else
{
lean_object* v_head_364_; lean_object* v_tail_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_head_364_ = lean_ctor_get(v_a_361_, 0);
v_tail_365_ = lean_ctor_get(v_a_361_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v_a_361_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_tail_365_);
lean_inc(v_head_364_);
lean_dec(v_a_361_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_inc(v_s_360_);
v___x_369_ = l_Lean_Meta_FVarSubst_apply(v_s_360_, v_head_364_);
lean_dec(v_head_364_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v_a_362_);
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_a_362_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v_a_361_ = v_tail_365_;
v_a_362_ = v___x_371_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object* v_s_375_, lean_object* v_x_376_){
_start:
{
switch(lean_obj_tag(v_x_376_))
{
case 0:
{
lean_object* v_e_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_e_377_ = lean_ctor_get(v_x_376_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v_x_376_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_e_377_);
lean_dec(v_x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = l_Lean_Meta_FVarSubst_apply(v_s_375_, v_e_377_);
lean_dec_ref(v_e_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
case 1:
{
lean_object* v_fvarId_386_; lean_object* v___x_387_; 
v_fvarId_386_ = lean_ctor_get(v_x_376_, 0);
v___x_387_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_375_, v_fvarId_386_);
lean_dec(v_s_375_);
if (lean_obj_tag(v___x_387_) == 0)
{
return v_x_376_;
}
else
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v_isSharedCheck_395_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v_x_376_, 0);
lean_dec(v_unused_396_);
v___x_389_ = v_x_376_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_x_376_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_val_391_; lean_object* v___x_393_; 
v_val_391_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_391_);
lean_dec_ref_known(v___x_387_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 0);
lean_ctor_set(v___x_389_, 0, v_val_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_val_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
case 2:
{
lean_object* v_ctorName_397_; lean_object* v_us_398_; lean_object* v_params_399_; lean_object* v_fields_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_410_; 
v_ctorName_397_ = lean_ctor_get(v_x_376_, 0);
v_us_398_ = lean_ctor_get(v_x_376_, 1);
v_params_399_ = lean_ctor_get(v_x_376_, 2);
v_fields_400_ = lean_ctor_get(v_x_376_, 3);
v_isSharedCheck_410_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_410_ == 0)
{
v___x_402_ = v_x_376_;
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_fields_400_);
lean_inc(v_params_399_);
lean_inc(v_us_398_);
lean_inc(v_ctorName_397_);
lean_dec(v_x_376_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_404_ = lean_box(0);
lean_inc(v_s_375_);
v___x_405_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(v_s_375_, v_params_399_, v___x_404_);
v___x_406_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(v_s_375_, v_fields_400_, v___x_404_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 3, v___x_406_);
lean_ctor_set(v___x_402_, 2, v___x_405_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_ctorName_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_us_398_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
case 3:
{
lean_object* v_e_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_e_411_ = lean_ctor_get(v_x_376_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v_x_376_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_e_411_);
lean_dec(v_x_376_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_Meta_FVarSubst_apply(v_s_375_, v_e_411_);
lean_dec_ref(v_e_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
case 4:
{
lean_object* v_type_420_; lean_object* v_xs_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_type_420_ = lean_ctor_get(v_x_376_, 0);
v_xs_421_ = lean_ctor_get(v_x_376_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v_x_376_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_xs_421_);
lean_inc(v_type_420_);
lean_dec(v_x_376_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc(v_s_375_);
v___x_425_ = l_Lean_Meta_FVarSubst_apply(v_s_375_, v_type_420_);
lean_dec_ref(v_type_420_);
v___x_426_ = lean_box(0);
v___x_427_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(v_s_375_, v_xs_421_, v___x_426_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_427_);
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
default: 
{
lean_object* v_varId_432_; lean_object* v_p_433_; lean_object* v_hId_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_444_; 
v_varId_432_ = lean_ctor_get(v_x_376_, 0);
v_p_433_ = lean_ctor_get(v_x_376_, 1);
v_hId_434_ = lean_ctor_get(v_x_376_, 2);
v_isSharedCheck_444_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_444_ == 0)
{
v___x_436_ = v_x_376_;
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_hId_434_);
lean_inc(v_p_433_);
lean_inc(v_varId_432_);
lean_dec(v_x_376_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_375_, v_varId_432_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_375_, v_p_433_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_varId_432_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_hId_434_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_dec_ref_known(v___x_438_, 1);
lean_del_object(v___x_436_);
lean_dec(v_hId_434_);
lean_dec(v_varId_432_);
v_x_376_ = v_p_433_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(lean_object* v_s_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
if (lean_obj_tag(v_a_446_) == 0)
{
lean_object* v___x_448_; 
lean_dec(v_s_445_);
v___x_448_ = l_List_reverse___redArg(v_a_447_);
return v___x_448_;
}
else
{
lean_object* v_head_449_; lean_object* v_tail_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_459_; 
v_head_449_ = lean_ctor_get(v_a_446_, 0);
v_tail_450_ = lean_ctor_get(v_a_446_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_459_ == 0)
{
v___x_452_ = v_a_446_;
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_tail_450_);
lean_inc(v_head_449_);
lean_dec(v_a_446_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_inc(v_s_445_);
v___x_454_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_445_, v_head_449_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v_a_447_);
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_a_447_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v_a_446_ = v_tail_450_;
v_a_447_ = v___x_456_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object* v_fvarId_460_, lean_object* v_v_461_, lean_object* v_p_462_){
_start:
{
lean_object* v_s_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_s_463_ = lean_box(0);
v___x_464_ = l_Lean_Meta_FVarSubst_insert(v_s_463_, v_fvarId_460_, v_v_461_);
v___x_465_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v___x_464_, v_p_462_);
return v___x_465_;
}
}
uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
else
{
lean_object* v_head_468_; lean_object* v_tail_469_; uint8_t v___x_470_; 
v_head_468_ = lean_ctor_get(v_x_466_, 0);
v_tail_469_ = lean_ctor_get(v_x_466_, 1);
v___x_470_ = l_Lean_Expr_hasExprMVar(v_head_468_);
if (v___x_470_ == 0)
{
v_x_466_ = v_tail_469_;
goto _start;
}
else
{
return v___x_470_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_466_ = stack[0].m_obj;
uint8_t v_res_472_;
v_res_472_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_x_466_);
stack->m_num = v_res_472_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0___boxed(lean_object* v_x_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_x_473_);
lean_dec(v_x_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object* v_x_476_){
_start:
{
switch(lean_obj_tag(v_x_476_))
{
case 0:
{
lean_object* v_e_477_; uint8_t v___x_478_; 
v_e_477_ = lean_ctor_get(v_x_476_, 0);
v___x_478_ = l_Lean_Expr_hasExprMVar(v_e_477_);
return v___x_478_;
}
case 2:
{
lean_object* v_params_479_; lean_object* v_fields_480_; uint8_t v___x_481_; 
v_params_479_ = lean_ctor_get(v_x_476_, 2);
v_fields_480_ = lean_ctor_get(v_x_476_, 3);
v___x_481_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_params_479_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
v___x_482_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_fields_480_);
return v___x_482_;
}
else
{
return v___x_481_;
}
}
case 3:
{
lean_object* v_e_483_; uint8_t v___x_484_; 
v_e_483_ = lean_ctor_get(v_x_476_, 0);
v___x_484_ = l_Lean_Expr_hasExprMVar(v_e_483_);
return v___x_484_;
}
case 5:
{
lean_object* v_p_485_; 
v_p_485_ = lean_ctor_get(v_x_476_, 1);
v_x_476_ = v_p_485_;
goto _start;
}
case 4:
{
lean_object* v_type_487_; lean_object* v_xs_488_; uint8_t v___x_489_; 
v_type_487_ = lean_ctor_get(v_x_476_, 0);
v_xs_488_ = lean_ctor_get(v_x_476_, 1);
v___x_489_ = l_Lean_Expr_hasExprMVar(v_type_487_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_xs_488_);
return v___x_490_;
}
else
{
return v___x_489_;
}
}
default: 
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Pattern_hasExprMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_476_ = stack[0].m_obj;
uint8_t v_res_492_;
v_res_492_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_476_);
stack->m_num = v_res_492_;
}
uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(lean_object* v_x_493_){
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
LEAN_EXPORT void l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_493_ = stack[0].m_obj;
uint8_t v_res_499_;
v_res_499_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_x_493_);
stack->m_num = v_res_499_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1___boxed(lean_object* v_x_500_){
_start:
{
uint8_t v_res_501_; lean_object* v_r_502_; 
v_res_501_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_x_500_);
lean_dec(v_x_500_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object* v_x_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_503_);
lean_dec_ref(v_x_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object* v_as_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
if (lean_obj_tag(v_as_506_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v___x_517_; 
v_head_515_ = lean_ctor_get(v_as_506_, 0);
lean_inc(v_head_515_);
v_tail_516_ = lean_ctor_get(v_as_506_, 1);
lean_inc(v_tail_516_);
lean_dec_ref_known(v_as_506_, 2);
v___x_517_ = l_Lean_Expr_collectFVars(v_head_515_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_dec_ref_known(v___x_517_, 1);
v_as_506_ = v_tail_516_;
goto _start;
}
else
{
lean_dec(v_tail_516_);
return v___x_517_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_506_ = stack[0].m_obj;
lean_object* v___y_507_ = stack[1].m_obj;
lean_object* v___y_508_ = stack[2].m_obj;
lean_object* v___y_509_ = stack[3].m_obj;
lean_object* v___y_510_ = stack[4].m_obj;
lean_object* v___y_511_ = stack[5].m_obj;
lean_object* v_res_519_;
v_res_519_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_as_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object* v_as_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_as_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
return v_res_527_;
}
}
lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object* v_p_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
switch(lean_obj_tag(v_p_528_))
{
case 1:
{
lean_object* v_fvarId_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_546_; 
v_fvarId_535_ = lean_ctor_get(v_p_528_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_p_528_);
if (v_isSharedCheck_546_ == 0)
{
v___x_537_ = v_p_528_;
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_fvarId_535_);
lean_dec(v_p_528_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_546_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_539_ = lean_st_ref_take(v_a_529_);
v___x_540_ = lean_box(0);
v___x_541_ = l_Lean_CollectFVars_State_add(v___x_539_, v_fvarId_535_);
v___x_542_ = lean_st_ref_put(v_a_529_, v___x_541_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 0);
lean_ctor_set(v___x_537_, 0, v___x_540_);
v___x_544_ = v___x_537_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_540_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
case 2:
{
lean_object* v_params_547_; lean_object* v_fields_548_; lean_object* v___x_549_; 
v_params_547_ = lean_ctor_get(v_p_528_, 2);
lean_inc(v_params_547_);
v_fields_548_ = lean_ctor_get(v_p_528_, 3);
lean_inc(v_fields_548_);
lean_dec_ref_known(v_p_528_, 4);
v___x_549_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_params_547_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
lean_dec_ref_known(v___x_549_, 1);
v___x_550_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_fields_548_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
return v___x_550_;
}
else
{
lean_dec(v_fields_548_);
return v___x_549_;
}
}
case 4:
{
lean_object* v_type_551_; lean_object* v_xs_552_; lean_object* v___x_553_; 
v_type_551_ = lean_ctor_get(v_p_528_, 0);
lean_inc_ref(v_type_551_);
v_xs_552_ = lean_ctor_get(v_p_528_, 1);
lean_inc(v_xs_552_);
lean_dec_ref_known(v_p_528_, 2);
v___x_553_ = l_Lean_Expr_collectFVars(v_type_551_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; 
lean_dec_ref_known(v___x_553_, 1);
v___x_554_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_xs_552_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
return v___x_554_;
}
else
{
lean_dec(v_xs_552_);
return v___x_553_;
}
}
case 5:
{
lean_object* v_varId_555_; lean_object* v_p_556_; lean_object* v_hId_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_varId_555_ = lean_ctor_get(v_p_528_, 0);
lean_inc(v_varId_555_);
v_p_556_ = lean_ctor_get(v_p_528_, 1);
lean_inc_ref(v_p_556_);
v_hId_557_ = lean_ctor_get(v_p_528_, 2);
lean_inc(v_hId_557_);
lean_dec_ref_known(v_p_528_, 3);
v___x_558_ = lean_st_ref_take(v_a_529_);
v___x_559_ = l_Lean_CollectFVars_State_add(v___x_558_, v_varId_555_);
v___x_560_ = l_Lean_CollectFVars_State_add(v___x_559_, v_hId_557_);
v___x_561_ = lean_st_ref_put(v_a_529_, v___x_560_);
v_p_528_ = v_p_556_;
goto _start;
}
default: 
{
lean_object* v_e_563_; lean_object* v___x_564_; 
v_e_563_ = lean_ctor_get(v_p_528_, 0);
lean_inc_ref(v_e_563_);
lean_dec_ref(v_p_528_);
v___x_564_ = l_Lean_Expr_collectFVars(v_e_563_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Pattern_collectFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_528_ = stack[0].m_obj;
lean_object* v_a_529_ = stack[1].m_obj;
lean_object* v_a_530_ = stack[2].m_obj;
lean_object* v_a_531_ = stack[3].m_obj;
lean_object* v_a_532_ = stack[4].m_obj;
lean_object* v_a_533_ = stack[5].m_obj;
lean_object* v_res_565_;
v_res_565_ = l_Lean_Meta_Match_Pattern_collectFVars(v_p_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
stack->m_obj
 = v_res_565_;
}
lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object* v_as_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v_as_566_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v_head_575_; lean_object* v_tail_576_; lean_object* v___x_577_; 
v_head_575_ = lean_ctor_get(v_as_566_, 0);
lean_inc(v_head_575_);
v_tail_576_ = lean_ctor_get(v_as_566_, 1);
lean_inc(v_tail_576_);
lean_dec_ref_known(v_as_566_, 2);
v___x_577_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_575_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_dec_ref_known(v___x_577_, 1);
v_as_566_ = v_tail_576_;
goto _start;
}
else
{
lean_dec(v_tail_576_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_566_ = stack[0].m_obj;
lean_object* v___y_567_ = stack[1].m_obj;
lean_object* v___y_568_ = stack[2].m_obj;
lean_object* v___y_569_ = stack[3].m_obj;
lean_object* v___y_570_ = stack[4].m_obj;
lean_object* v___y_571_ = stack[5].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_as_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object* v_as_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_as_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object* v_p_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_Match_Pattern_collectFVars(v_p_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
return v_res_595_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object* v_e_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_Expr_hasMVar(v_e_596_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_e_596_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v_mctx_602_; lean_object* v___x_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; lean_object* v_cache_607_; lean_object* v_zetaDeltaFVarIds_608_; lean_object* v_postponed_609_; lean_object* v_diag_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_619_; 
v___x_601_ = lean_st_ref_get(v___y_597_);
v_mctx_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_mctx_602_);
lean_dec(v___x_601_);
v___x_603_ = l_Lean_instantiateMVarsCore(v_mctx_602_, v_e_596_);
v_fst_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v___x_603_, 1);
lean_inc(v_snd_605_);
lean_dec_ref(v___x_603_);
v___x_606_ = lean_st_ref_take(v___y_597_);
v_cache_607_ = lean_ctor_get(v___x_606_, 1);
v_zetaDeltaFVarIds_608_ = lean_ctor_get(v___x_606_, 2);
v_postponed_609_ = lean_ctor_get(v___x_606_, 3);
v_diag_610_ = lean_ctor_get(v___x_606_, 4);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_606_, 0);
lean_dec(v_unused_620_);
v___x_612_ = v___x_606_;
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_diag_610_);
lean_inc(v_postponed_609_);
lean_inc(v_zetaDeltaFVarIds_608_);
lean_inc(v_cache_607_);
lean_dec(v___x_606_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_snd_605_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_snd_605_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_cache_607_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_zetaDeltaFVarIds_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_postponed_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_diag_610_);
v___x_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_st_ref_put(v___y_597_, v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_fst_604_);
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_596_ = stack[0].m_obj;
lean_object* v___y_597_ = stack[1].m_obj;
lean_object* v_res_621_;
v_res_621_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_596_, v___y_597_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object* v_e_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_622_, v___y_623_);
lean_dec(v___y_623_);
return v_res_625_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object* v_e_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_626_, v___y_628_);
return v___x_632_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_626_ = stack[0].m_obj;
lean_object* v___y_627_ = stack[1].m_obj;
lean_object* v___y_628_ = stack[2].m_obj;
lean_object* v___y_629_ = stack[3].m_obj;
lean_object* v___y_630_ = stack[4].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(v_e_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object* v_e_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(v_e_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_640_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = l_List_reverse___redArg(v_x_642_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v_head_650_; lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_661_; 
v_head_650_ = lean_ctor_get(v_x_641_, 0);
v_tail_651_ = lean_ctor_get(v_x_641_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_661_ == 0)
{
v___x_653_ = v_x_641_;
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_inc(v_head_650_);
lean_dec(v_x_641_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v_a_656_; lean_object* v___x_658_; 
v___x_655_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_650_, v___y_644_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v___x_655_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_x_642_);
lean_ctor_set(v___x_653_, 0, v_a_656_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_656_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_x_642_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v_x_641_ = v_tail_651_;
v_x_642_ = v___x_658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_641_ = stack[0].m_obj;
lean_object* v_x_642_ = stack[1].m_obj;
lean_object* v___y_643_ = stack[2].m_obj;
lean_object* v___y_644_ = stack[3].m_obj;
lean_object* v___y_645_ = stack[4].m_obj;
lean_object* v___y_646_ = stack[5].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_x_641_, v_x_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_x_663_, v_x_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_670_;
}
}
lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* v_x_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
switch(lean_obj_tag(v_x_671_))
{
case 0:
{
lean_object* v_e_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_701_; 
v_e_677_ = lean_ctor_get(v_x_671_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_701_ == 0)
{
v___x_679_ = v_x_671_;
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_e_677_);
lean_dec(v_x_671_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_701_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_677_, v_a_673_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_692_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_a_682_);
v___x_687_ = v___x_679_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_687_);
v___x_689_ = v___x_684_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_679_);
v_a_693_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_681_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_681_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
case 3:
{
lean_object* v_e_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_726_; 
v_e_702_ = lean_ctor_get(v_x_671_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_726_ == 0)
{
v___x_704_ = v_x_671_;
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_e_702_);
lean_dec(v_x_671_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_702_, v_a_673_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_717_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_717_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_717_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_717_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_a_707_);
v___x_712_ = v___x_704_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_714_ = v___x_709_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_del_object(v___x_704_);
v_a_718_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_706_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_706_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
case 2:
{
lean_object* v_ctorName_727_; lean_object* v_us_728_; lean_object* v_params_729_; lean_object* v_fields_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_765_; 
v_ctorName_727_ = lean_ctor_get(v_x_671_, 0);
v_us_728_ = lean_ctor_get(v_x_671_, 1);
v_params_729_ = lean_ctor_get(v_x_671_, 2);
v_fields_730_ = lean_ctor_get(v_x_671_, 3);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_765_ == 0)
{
v___x_732_ = v_x_671_;
v_isShared_733_ = v_isSharedCheck_765_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_fields_730_);
lean_inc(v_params_729_);
lean_inc(v_us_728_);
lean_inc(v_ctorName_727_);
lean_dec(v_x_671_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_765_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_params_729_, v___x_734_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_fields_730_, v___x_734_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_748_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 3, v_a_738_);
lean_ctor_set(v___x_732_, 2, v_a_736_);
v___x_743_ = v___x_732_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_ctorName_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_us_728_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_a_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_a_738_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_736_);
lean_del_object(v___x_732_);
lean_dec(v_us_728_);
lean_dec(v_ctorName_727_);
v_a_749_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_737_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_737_);
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
lean_del_object(v___x_732_);
lean_dec(v_fields_730_);
lean_dec(v_us_728_);
lean_dec(v_ctorName_727_);
v_a_757_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_735_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_735_);
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
}
case 5:
{
lean_object* v_varId_766_; lean_object* v_p_767_; lean_object* v_hId_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_784_; 
v_varId_766_ = lean_ctor_get(v_x_671_, 0);
v_p_767_ = lean_ctor_get(v_x_671_, 1);
v_hId_768_ = lean_ctor_get(v_x_671_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_784_ == 0)
{
v___x_770_ = v_x_671_;
v_isShared_771_ = v_isSharedCheck_784_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_hId_768_);
lean_inc(v_p_767_);
lean_inc(v_varId_766_);
lean_dec(v_x_671_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_784_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Match_instantiatePatternMVars(v_p_767_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_783_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_783_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_a_773_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_varId_766_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_773_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_hId_768_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_778_);
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_del_object(v___x_770_);
lean_dec(v_hId_768_);
lean_dec(v_varId_766_);
return v___x_772_;
}
}
}
case 4:
{
lean_object* v_type_785_; lean_object* v_xs_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_821_; 
v_type_785_ = lean_ctor_get(v_x_671_, 0);
v_xs_786_ = lean_ctor_get(v_x_671_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_821_ == 0)
{
v___x_788_ = v_x_671_;
v_isShared_789_ = v_isSharedCheck_821_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_xs_786_);
lean_inc(v_type_785_);
lean_dec(v_x_671_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_821_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_785_, v_a_673_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = lean_box(0);
v___x_793_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_xs_786_, v___x_792_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_804_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_804_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_a_794_);
lean_ctor_set(v___x_788_, 0, v_a_791_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_791_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_a_794_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_799_);
v___x_801_ = v___x_796_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_a_791_);
lean_del_object(v___x_788_);
v_a_805_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_793_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_793_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_del_object(v___x_788_);
lean_dec(v_xs_786_);
v_a_813_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_790_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_790_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
default: 
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_x_671_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_instantiatePatternMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_671_ = stack[0].m_obj;
lean_object* v_a_672_ = stack[1].m_obj;
lean_object* v_a_673_ = stack[2].m_obj;
lean_object* v_a_674_ = stack[3].m_obj;
lean_object* v_a_675_ = stack[4].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_Meta_Match_instantiatePatternMVars(v_x_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
stack->m_obj
 = v_res_823_;
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = l_List_reverse___redArg(v_x_825_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
else
{
lean_object* v_head_833_; lean_object* v_tail_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_852_; 
v_head_833_ = lean_ctor_get(v_x_824_, 0);
v_tail_834_ = lean_ctor_get(v_x_824_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_824_);
if (v_isSharedCheck_852_ == 0)
{
v___x_836_ = v_x_824_;
v_isShared_837_ = v_isSharedCheck_852_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_tail_834_);
lean_inc(v_head_833_);
lean_dec(v_x_824_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_852_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Match_instantiatePatternMVars(v_head_833_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_x_825_);
lean_ctor_set(v___x_836_, 0, v_a_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_839_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_x_825_);
v___x_841_ = v_reuseFailAlloc_843_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
v_x_824_ = v_tail_834_;
v_x_825_ = v___x_841_;
goto _start;
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_del_object(v___x_836_);
lean_dec(v_tail_834_);
lean_dec(v_x_825_);
v_a_844_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_838_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_838_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_824_ = stack[0].m_obj;
lean_object* v_x_825_ = stack[1].m_obj;
lean_object* v___y_826_ = stack[2].m_obj;
lean_object* v___y_827_ = stack[3].m_obj;
lean_object* v___y_828_ = stack[4].m_obj;
lean_object* v___y_829_ = stack[5].m_obj;
lean_object* v_res_853_;
v_res_853_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_x_824_, v_x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_853_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_x_854_, v_x_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* v_x_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_Match_instantiatePatternMVars(v_x_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
return v_res_868_;
}
}
lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object* v_as_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
if (lean_obj_tag(v_as_874_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; lean_object* v___x_885_; 
v_head_883_ = lean_ctor_get(v_as_874_, 0);
lean_inc(v_head_883_);
v_tail_884_ = lean_ctor_get(v_as_874_, 1);
lean_inc(v_tail_884_);
lean_dec_ref_known(v_as_874_, 2);
v___x_885_ = l_Lean_LocalDecl_collectFVars(v_head_883_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_dec_ref_known(v___x_885_, 1);
v_as_874_ = v_tail_884_;
goto _start;
}
else
{
lean_dec(v_tail_884_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_874_ = stack[0].m_obj;
lean_object* v___y_875_ = stack[1].m_obj;
lean_object* v___y_876_ = stack[2].m_obj;
lean_object* v___y_877_ = stack[3].m_obj;
lean_object* v___y_878_ = stack[4].m_obj;
lean_object* v___y_879_ = stack[5].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_as_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object* v_as_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_as_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
return v_res_895_;
}
}
lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object* v_as_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
if (lean_obj_tag(v_as_896_) == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v_head_905_; lean_object* v_tail_906_; lean_object* v___x_907_; 
v_head_905_ = lean_ctor_get(v_as_896_, 0);
lean_inc(v_head_905_);
v_tail_906_ = lean_ctor_get(v_as_896_, 1);
lean_inc(v_tail_906_);
lean_dec_ref_known(v_as_896_, 2);
v___x_907_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_905_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_dec_ref_known(v___x_907_, 1);
v_as_896_ = v_tail_906_;
goto _start;
}
else
{
lean_dec(v_tail_906_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_896_ = stack[0].m_obj;
lean_object* v___y_897_ = stack[1].m_obj;
lean_object* v___y_898_ = stack[2].m_obj;
lean_object* v___y_899_ = stack[3].m_obj;
lean_object* v___y_900_ = stack[4].m_obj;
lean_object* v___y_901_ = stack[5].m_obj;
lean_object* v_res_909_;
v_res_909_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_as_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
stack->m_obj
 = v_res_909_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object* v_as_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_as_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
return v_res_917_;
}
}
lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* v_altLHS_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_fvarDecls_925_; lean_object* v_patterns_926_; lean_object* v___x_927_; 
v_fvarDecls_925_ = lean_ctor_get(v_altLHS_918_, 1);
lean_inc(v_fvarDecls_925_);
v_patterns_926_ = lean_ctor_get(v_altLHS_918_, 2);
lean_inc(v_patterns_926_);
lean_dec_ref(v_altLHS_918_);
v___x_927_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_fvarDecls_925_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_928_; 
lean_dec_ref_known(v___x_927_, 1);
v___x_928_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_patterns_926_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_928_;
}
else
{
lean_dec(v_patterns_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_AltLHS_collectFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_altLHS_918_ = stack[0].m_obj;
lean_object* v_a_919_ = stack[1].m_obj;
lean_object* v_a_920_ = stack[2].m_obj;
lean_object* v_a_921_ = stack[3].m_obj;
lean_object* v_a_922_ = stack[4].m_obj;
lean_object* v_a_923_ = stack[5].m_obj;
lean_object* v_res_929_;
v_res_929_ = l_Lean_Meta_Match_AltLHS_collectFVars(v_altLHS_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* v_altLHS_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_Match_AltLHS_collectFVars(v_altLHS_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
return v_res_937_;
}
}
lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object* v_localDecl_938_, lean_object* v___y_939_){
_start:
{
if (lean_obj_tag(v_localDecl_938_) == 0)
{
lean_object* v_index_941_; lean_object* v_fvarId_942_; lean_object* v_userName_943_; lean_object* v_type_944_; uint8_t v_bi_945_; uint8_t v_kind_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_962_; 
v_index_941_ = lean_ctor_get(v_localDecl_938_, 0);
v_fvarId_942_ = lean_ctor_get(v_localDecl_938_, 1);
v_userName_943_ = lean_ctor_get(v_localDecl_938_, 2);
v_type_944_ = lean_ctor_get(v_localDecl_938_, 3);
v_bi_945_ = lean_ctor_get_uint8(v_localDecl_938_, sizeof(void*)*4);
v_kind_946_ = lean_ctor_get_uint8(v_localDecl_938_, sizeof(void*)*4 + 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_localDecl_938_);
if (v_isSharedCheck_962_ == 0)
{
v___x_948_ = v_localDecl_938_;
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_type_944_);
lean_inc(v_userName_943_);
lean_inc(v_fvarId_942_);
lean_inc(v_index_941_);
lean_dec(v_localDecl_938_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_962_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_961_; 
v___x_950_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_944_, v___y_939_);
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_961_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 3, v_a_951_);
v___x_956_ = v___x_948_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_index_941_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_fvarId_942_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_userName_943_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_a_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*4, v_bi_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_960_, sizeof(void*)*4 + 1, v_kind_946_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
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
}
else
{
lean_object* v_index_963_; lean_object* v_fvarId_964_; lean_object* v_userName_965_; lean_object* v_type_966_; lean_object* v_value_967_; uint8_t v_nondep_968_; uint8_t v_kind_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_987_; 
v_index_963_ = lean_ctor_get(v_localDecl_938_, 0);
v_fvarId_964_ = lean_ctor_get(v_localDecl_938_, 1);
v_userName_965_ = lean_ctor_get(v_localDecl_938_, 2);
v_type_966_ = lean_ctor_get(v_localDecl_938_, 3);
v_value_967_ = lean_ctor_get(v_localDecl_938_, 4);
v_nondep_968_ = lean_ctor_get_uint8(v_localDecl_938_, sizeof(void*)*5);
v_kind_969_ = lean_ctor_get_uint8(v_localDecl_938_, sizeof(void*)*5 + 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_localDecl_938_);
if (v_isSharedCheck_987_ == 0)
{
v___x_971_ = v_localDecl_938_;
v_isShared_972_ = v_isSharedCheck_987_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_value_967_);
lean_inc(v_type_966_);
lean_inc(v_userName_965_);
lean_inc(v_fvarId_964_);
lean_inc(v_index_963_);
lean_dec(v_localDecl_938_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_987_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_986_; 
v___x_973_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_966_, v___y_939_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_967_, v___y_939_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_986_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v_a_976_);
lean_ctor_set(v___x_971_, 3, v_a_974_);
v___x_981_ = v___x_971_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_index_963_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_fvarId_964_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_userName_965_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_a_974_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_a_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*5, v_nondep_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*5 + 1, v_kind_969_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_938_ = stack[0].m_obj;
lean_object* v___y_939_ = stack[1].m_obj;
lean_object* v_res_988_;
v_res_988_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_938_, v___y_939_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object* v_localDecl_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_989_, v___y_990_);
lean_dec(v___y_990_);
return v_res_992_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l_List_reverse___redArg(v_x_994_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
else
{
lean_object* v_head_1002_; lean_object* v_tail_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1021_; 
v_head_1002_ = lean_ctor_get(v_x_993_, 0);
v_tail_1003_ = lean_ctor_get(v_x_993_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_x_993_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1005_ = v_x_993_;
v_isShared_1006_ = v_isSharedCheck_1021_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_tail_1003_);
lean_inc(v_head_1002_);
lean_dec(v_x_993_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1021_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_1002_, v___y_996_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_x_994_);
lean_ctor_set(v___x_1005_, 0, v_a_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1008_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_x_994_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v_x_993_ = v_tail_1003_;
v_x_994_ = v___x_1010_;
goto _start;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_1005_);
lean_dec(v_tail_1003_);
lean_dec(v_x_994_);
v_a_1013_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1007_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1007_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_993_ = stack[0].m_obj;
lean_object* v_x_994_ = stack[1].m_obj;
lean_object* v___y_995_ = stack[2].m_obj;
lean_object* v___y_996_ = stack[3].m_obj;
lean_object* v___y_997_ = stack[4].m_obj;
lean_object* v___y_998_ = stack[5].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_x_993_, v_x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_x_1023_, v_x_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1030_;
}
}
lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* v_altLHS_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_ref_1037_; lean_object* v_fvarDecls_1038_; lean_object* v_patterns_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1074_; 
v_ref_1037_ = lean_ctor_get(v_altLHS_1031_, 0);
v_fvarDecls_1038_ = lean_ctor_get(v_altLHS_1031_, 1);
v_patterns_1039_ = lean_ctor_get(v_altLHS_1031_, 2);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_altLHS_1031_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1041_ = v_altLHS_1031_;
v_isShared_1042_ = v_isSharedCheck_1074_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_patterns_1039_);
lean_inc(v_fvarDecls_1038_);
lean_inc(v_ref_1037_);
lean_dec(v_altLHS_1031_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1074_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_fvarDecls_1038_, v___x_1043_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_patterns_1039_, v___x_1043_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1057_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1057_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1057_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 2, v_a_1047_);
lean_ctor_set(v___x_1041_, 1, v_a_1045_);
v___x_1052_ = v___x_1041_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_ref_1037_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_a_1045_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1052_);
v___x_1054_ = v___x_1049_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_a_1045_);
lean_del_object(v___x_1041_);
lean_dec(v_ref_1037_);
v_a_1058_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1046_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1046_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_del_object(v___x_1041_);
lean_dec(v_patterns_1039_);
lean_dec(v_ref_1037_);
v_a_1066_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1044_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1044_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_instantiateAltLHSMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_altLHS_1031_ = stack[0].m_obj;
lean_object* v_a_1032_ = stack[1].m_obj;
lean_object* v_a_1033_ = stack[2].m_obj;
lean_object* v_a_1034_ = stack[3].m_obj;
lean_object* v_a_1035_ = stack[4].m_obj;
lean_object* v_res_1075_;
v_res_1075_ = l_Lean_Meta_Match_instantiateAltLHSMVars(v_altLHS_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* v_altLHS_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Meta_Match_instantiateAltLHSMVars(v_altLHS_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1082_;
}
}
lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object* v_localDecl_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_1083_, v___y_1085_);
return v___x_1089_;
}
}
LEAN_EXPORT void l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_1083_ = stack[0].m_obj;
lean_object* v___y_1084_ = stack[1].m_obj;
lean_object* v___y_1085_ = stack[2].m_obj;
lean_object* v___y_1086_ = stack[3].m_obj;
lean_object* v___y_1087_ = stack[4].m_obj;
lean_object* v_res_1090_;
v_res_1090_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(v_localDecl_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
stack->m_obj
 = v_res_1090_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object* v_localDecl_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(v_localDecl_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0));
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1103_);
lean_ctor_set(v___x_1105_, 2, v___x_1102_);
lean_ctor_set(v___x_1105_, 3, v___x_1101_);
lean_ctor_set(v___x_1105_, 4, v___x_1101_);
lean_ctor_set(v___x_1105_, 5, v___x_1101_);
lean_ctor_set(v___x_1105_, 6, v___x_1100_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default(void){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedAlt_default___closed__1, &l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Meta_Match_instInhabitedAlt_default;
return v___x_1107_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object* v_msgData_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; uint8_t v___x_1116_; lean_object* v_env_1117_; lean_object* v___x_1118_; lean_object* v_toCold_1119_; lean_object* v_mctx_1120_; lean_object* v_lctx_1121_; lean_object* v_options_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1114_ = lean_st_ref_get(v___y_1112_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = 0;
v_env_1117_ = l_Lean_Environment_setRecordingDeps(v_env_1115_, v___x_1116_);
v___x_1118_ = lean_st_ref_get(v___y_1110_);
v_toCold_1119_ = lean_ctor_get(v___y_1111_, 0);
v_mctx_1120_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_mctx_1120_);
lean_dec(v___x_1118_);
v_lctx_1121_ = lean_ctor_get(v___y_1109_, 2);
v_options_1122_ = lean_ctor_get(v_toCold_1119_, 2);
lean_inc_ref(v_options_1122_);
lean_inc_ref(v_lctx_1121_);
v___x_1123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1123_, 0, v_env_1117_);
lean_ctor_set(v___x_1123_, 1, v_mctx_1120_);
lean_ctor_set(v___x_1123_, 2, v_lctx_1121_);
lean_ctor_set(v___x_1123_, 3, v_options_1122_);
v___x_1124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_msgData_1108_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1108_ = stack[0].m_obj;
lean_object* v___y_1109_ = stack[1].m_obj;
lean_object* v___y_1110_ = stack[2].m_obj;
lean_object* v___y_1111_ = stack[3].m_obj;
lean_object* v___y_1112_ = stack[4].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msgData_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object* v_msgData_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msgData_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(lean_object* v_decls_1134_, lean_object* v_x_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1134_, v_x_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1134_ = stack[0].m_obj;
lean_object* v_x_1135_ = stack[1].m_obj;
lean_object* v___y_1136_ = stack[2].m_obj;
lean_object* v___y_1137_ = stack[3].m_obj;
lean_object* v___y_1138_ = stack[4].m_obj;
lean_object* v___y_1139_ = stack[5].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1134_, v_x_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(lean_object* v_decls_1159_, lean_object* v_x_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1159_, v_x_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1166_;
}
}
lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object* v_00_u03b1_1167_, lean_object* v_decls_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT void l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1168_ = stack[1].m_obj;
lean_object* v_x_1169_ = stack[2].m_obj;
lean_object* v___y_1170_ = stack[3].m_obj;
lean_object* v___y_1171_ = stack[4].m_obj;
lean_object* v___y_1172_ = stack[5].m_obj;
lean_object* v___y_1173_ = stack[6].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_box(0), v_decls_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_decls_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(v_00_u03b1_1177_, v_decls_1178_, v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1185_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2));
v___x_1191_ = l_Lean_stringToMessageData(v___x_1190_);
return v___x_1191_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(lean_object* v_as_x27_1192_, lean_object* v_b_1193_){
_start:
{
if (lean_obj_tag(v_as_x27_1192_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1193_);
return v___x_1195_;
}
else
{
lean_object* v_head_1196_; lean_object* v_tail_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_head_1196_ = lean_ctor_get(v_as_x27_1192_, 0);
v_tail_1197_ = lean_ctor_get(v_as_x27_1192_, 1);
v_fst_1198_ = lean_ctor_get(v_head_1196_, 0);
v_snd_1199_ = lean_ctor_get(v_head_1196_, 1);
v___x_1200_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_b_1193_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
lean_inc(v_fst_1198_);
v___x_1202_ = l_Lean_MessageData_ofExpr(v_fst_1198_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
lean_inc(v_snd_1199_);
v___x_1206_ = l_Lean_MessageData_ofExpr(v_snd_1199_);
v___x_1207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v_as_x27_1192_ = v_tail_1197_;
v_b_1193_ = v___x_1207_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1192_ = stack[0].m_obj;
lean_object* v_b_1193_ = stack[1].m_obj;
lean_object* v_res_1209_;
v_res_1209_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1192_, v_b_1193_);
stack->m_obj
 = v_res_1209_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(lean_object* v_as_x27_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1210_, v_b_1211_);
lean_dec(v_as_x27_1210_);
return v_res_1213_;
}
}
lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object* v_cnstrs_1214_, lean_object* v_msg_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v_a_1222_; lean_object* v___x_1223_; 
v___x_1221_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_cnstrs_1214_, v_msg_1215_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_a_1222_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v___x_1223_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Alt_toMessageData___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cnstrs_1214_ = stack[0].m_obj;
lean_object* v_msg_1215_ = stack[1].m_obj;
lean_object* v___y_1216_ = stack[2].m_obj;
lean_object* v___y_1217_ = stack[3].m_obj;
lean_object* v___y_1218_ = stack[4].m_obj;
lean_object* v___y_1219_ = stack[5].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(v_cnstrs_1214_, v_msg_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object* v_cnstrs_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(v_cnstrs_1225_, v_msg_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v_cnstrs_1225_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = l_List_reverse___redArg(v_a_1234_);
return v___x_1235_;
}
else
{
lean_object* v_head_1236_; lean_object* v_tail_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_head_1236_ = lean_ctor_get(v_a_1233_, 0);
v_tail_1237_ = lean_ctor_get(v_a_1233_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1239_ = v_a_1233_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tail_1237_);
lean_inc(v_head_1236_);
lean_dec(v_a_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v_a_1234_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_head_1236_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_a_1234_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v_a_1233_ = v_tail_1237_;
v_a_1234_ = v___x_1242_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
if (lean_obj_tag(v_a_1249_) == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = l_List_reverse___redArg(v_a_1250_);
return v___x_1251_;
}
else
{
lean_object* v_head_1252_; lean_object* v_tail_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1270_; 
v_head_1252_ = lean_ctor_get(v_a_1249_, 0);
v_tail_1253_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1255_ = v_a_1249_;
v_isShared_1256_ = v_isSharedCheck_1270_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_tail_1253_);
lean_inc(v_head_1252_);
lean_dec(v_a_1249_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1270_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_inc(v_head_1252_);
v___x_1257_ = l_Lean_LocalDecl_toExpr(v_head_1252_);
v___x_1258_ = l_Lean_MessageData_ofExpr(v___x_1257_);
v___x_1259_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_LocalDecl_type(v_head_1252_);
lean_dec(v_head_1252_);
v___x_1262_ = l_Lean_MessageData_ofExpr(v___x_1261_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1260_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v_a_1250_);
lean_ctor_set(v___x_1255_, 0, v___x_1265_);
v___x_1267_ = v___x_1255_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1250_);
v___x_1267_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v_a_1249_ = v_tail_1253_;
v_a_1250_ = v___x_1267_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__0));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__2));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__4));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__6));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object* v_alt_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_rhs_1289_; lean_object* v_fvarDecls_1290_; lean_object* v_patterns_1291_; lean_object* v_cnstrs_1292_; lean_object* v___y_1294_; uint8_t v___x_1308_; 
v_rhs_1289_ = lean_ctor_get(v_alt_1283_, 2);
lean_inc_ref(v_rhs_1289_);
v_fvarDecls_1290_ = lean_ctor_get(v_alt_1283_, 3);
lean_inc(v_fvarDecls_1290_);
v_patterns_1291_ = lean_ctor_get(v_alt_1283_, 4);
lean_inc(v_patterns_1291_);
v_cnstrs_1292_ = lean_ctor_get(v_alt_1283_, 5);
lean_inc(v_cnstrs_1292_);
lean_dec_ref(v_alt_1283_);
v___x_1308_ = l_List_isEmpty___redArg(v_fvarDecls_1290_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1309_ = lean_box(0);
lean_inc(v_fvarDecls_1290_);
v___x_1310_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(v_fvarDecls_1290_, v___x_1309_);
v___x_1311_ = l_Lean_MessageData_ofList(v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___y_1294_ = v___x_1313_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__7, &l_Lean_Meta_Match_Alt_toMessageData___closed__7_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7);
v___y_1294_ = v___x_1314_;
goto v___jp_1293_;
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_msg_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; 
v___x_1295_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__1, &l_Lean_Meta_Match_Alt_toMessageData___closed__1_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1);
v___x_1296_ = lean_box(0);
v___x_1297_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(v_patterns_1291_, v___x_1296_);
v___x_1298_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v___x_1297_, v___x_1296_);
v___x_1299_ = l_Lean_MessageData_ofList(v___x_1298_);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1295_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__3, &l_Lean_Meta_Match_Alt_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = l_Lean_MessageData_ofExpr(v_rhs_1289_);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v_msg_1305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_1305_, 0, v___y_1294_);
lean_ctor_set(v_msg_1305_, 1, v___x_1304_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1306_, 0, v_cnstrs_1292_);
lean_closure_set(v___f_1306_, 1, v_msg_1305_);
v___x_1307_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_fvarDecls_1290_, v___f_1306_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
return v___x_1307_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Alt_toMessageData_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_1283_ = stack[0].m_obj;
lean_object* v_a_1284_ = stack[1].m_obj;
lean_object* v_a_1285_ = stack[2].m_obj;
lean_object* v_a_1286_ = stack[3].m_obj;
lean_object* v_a_1287_ = stack[4].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Lean_Meta_Match_Alt_toMessageData(v_alt_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object* v_alt_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Meta_Match_Alt_toMessageData(v_alt_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1322_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object* v_as_1323_, lean_object* v_as_x27_1324_, lean_object* v_b_1325_, lean_object* v_a_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1324_, v_b_1325_);
return v___x_1332_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1323_ = stack[0].m_obj;
lean_object* v_as_x27_1324_ = stack[1].m_obj;
lean_object* v_b_1325_ = stack[2].m_obj;
lean_object* v___y_1327_ = stack[4].m_obj;
lean_object* v___y_1328_ = stack[5].m_obj;
lean_object* v___y_1329_ = stack[6].m_obj;
lean_object* v___y_1330_ = stack[7].m_obj;
lean_object* v_res_1333_;
v_res_1333_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(v_as_1323_, v_as_x27_1324_, v_b_1325_, lean_box(0), v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
stack->m_obj
 = v_res_1333_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(lean_object* v_as_1334_, lean_object* v_as_x27_1335_, lean_object* v_b_1336_, lean_object* v_a_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(v_as_1334_, v_as_x27_1335_, v_b_1336_, v_a_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v_as_x27_1335_);
lean_dec(v_as_1334_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object* v_s_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
if (lean_obj_tag(v_a_1345_) == 0)
{
lean_object* v___x_1347_; 
lean_dec(v_s_1344_);
v___x_1347_ = l_List_reverse___redArg(v_a_1346_);
return v___x_1347_;
}
else
{
lean_object* v_head_1348_; lean_object* v_tail_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1358_; 
v_head_1348_ = lean_ctor_get(v_a_1345_, 0);
v_tail_1349_ = lean_ctor_get(v_a_1345_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1351_ = v_a_1345_;
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_tail_1349_);
lean_inc(v_head_1348_);
lean_dec(v_a_1345_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_inc(v_s_1344_);
v___x_1353_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_1344_, v_head_1348_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v_a_1346_);
lean_ctor_set(v___x_1351_, 0, v___x_1353_);
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_a_1346_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
v_a_1345_ = v_tail_1349_;
v_a_1346_ = v___x_1355_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object* v_s_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
if (lean_obj_tag(v_a_1360_) == 0)
{
lean_object* v___x_1362_; 
lean_dec(v_s_1359_);
v___x_1362_ = l_List_reverse___redArg(v_a_1361_);
return v___x_1362_;
}
else
{
lean_object* v_head_1363_; lean_object* v_tail_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1373_; 
v_head_1363_ = lean_ctor_get(v_a_1360_, 0);
v_tail_1364_ = lean_ctor_get(v_a_1360_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1366_ = v_a_1360_;
v_isShared_1367_ = v_isSharedCheck_1373_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_tail_1364_);
lean_inc(v_head_1363_);
lean_dec(v_a_1360_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1373_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_inc(v_s_1359_);
v___x_1368_ = l_Lean_LocalDecl_applyFVarSubst(v_s_1359_, v_head_1363_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_a_1361_);
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_a_1361_);
v___x_1370_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v_a_1360_ = v_tail_1364_;
v_a_1361_ = v___x_1370_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object* v_s_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
if (lean_obj_tag(v_a_1375_) == 0)
{
lean_object* v___x_1377_; 
lean_dec(v_s_1374_);
v___x_1377_ = l_List_reverse___redArg(v_a_1376_);
return v___x_1377_;
}
else
{
lean_object* v_head_1378_; lean_object* v_tail_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1398_; 
v_head_1378_ = lean_ctor_get(v_a_1375_, 0);
v_tail_1379_ = lean_ctor_get(v_a_1375_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_a_1375_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1381_ = v_a_1375_;
v_isShared_1382_ = v_isSharedCheck_1398_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_tail_1379_);
lean_inc(v_head_1378_);
lean_dec(v_a_1375_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1398_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
v_fst_1383_ = lean_ctor_get(v_head_1378_, 0);
v_snd_1384_ = lean_ctor_get(v_head_1378_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_head_1378_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1386_ = v_head_1378_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v_head_1378_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_inc_n(v_s_1374_, 2);
v___x_1388_ = l_Lean_Meta_FVarSubst_apply(v_s_1374_, v_fst_1383_);
lean_dec(v_fst_1383_);
v___x_1389_ = l_Lean_Meta_FVarSubst_apply(v_s_1374_, v_snd_1384_);
lean_dec(v_snd_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1389_);
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v_a_1376_);
lean_ctor_set(v___x_1381_, 0, v___x_1391_);
v___x_1393_ = v___x_1381_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_a_1376_);
v___x_1393_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
v_a_1375_ = v_tail_1379_;
v_a_1376_ = v___x_1393_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object* v_s_1399_, lean_object* v_alt_1400_){
_start:
{
lean_object* v_ref_1401_; lean_object* v_idx_1402_; lean_object* v_rhs_1403_; lean_object* v_fvarDecls_1404_; lean_object* v_patterns_1405_; lean_object* v_cnstrs_1406_; lean_object* v_notAltIdxs_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1419_; 
v_ref_1401_ = lean_ctor_get(v_alt_1400_, 0);
v_idx_1402_ = lean_ctor_get(v_alt_1400_, 1);
v_rhs_1403_ = lean_ctor_get(v_alt_1400_, 2);
v_fvarDecls_1404_ = lean_ctor_get(v_alt_1400_, 3);
v_patterns_1405_ = lean_ctor_get(v_alt_1400_, 4);
v_cnstrs_1406_ = lean_ctor_get(v_alt_1400_, 5);
v_notAltIdxs_1407_ = lean_ctor_get(v_alt_1400_, 6);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_alt_1400_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1409_ = v_alt_1400_;
v_isShared_1410_ = v_isSharedCheck_1419_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_notAltIdxs_1407_);
lean_inc(v_cnstrs_1406_);
lean_inc(v_patterns_1405_);
lean_inc(v_fvarDecls_1404_);
lean_inc(v_rhs_1403_);
lean_inc(v_idx_1402_);
lean_inc(v_ref_1401_);
lean_dec(v_alt_1400_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1419_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_inc_n(v_s_1399_, 3);
v___x_1411_ = l_Lean_Meta_FVarSubst_apply(v_s_1399_, v_rhs_1403_);
lean_dec_ref(v_rhs_1403_);
v___x_1412_ = lean_box(0);
v___x_1413_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(v_s_1399_, v_fvarDecls_1404_, v___x_1412_);
v___x_1414_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(v_s_1399_, v_patterns_1405_, v___x_1412_);
v___x_1415_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(v_s_1399_, v_cnstrs_1406_, v___x_1412_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 5, v___x_1415_);
lean_ctor_set(v___x_1409_, 4, v___x_1414_);
lean_ctor_set(v___x_1409_, 3, v___x_1413_);
lean_ctor_set(v___x_1409_, 2, v___x_1411_);
v___x_1417_ = v___x_1409_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_ref_1401_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_idx_1402_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1418_, 5, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1418_, 6, v_notAltIdxs_1407_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object* v_fvarId_1420_, lean_object* v_v_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v_v_1421_);
lean_dec(v_fvarId_1420_);
v___x_1424_ = l_List_reverse___redArg(v_a_1423_);
return v___x_1424_;
}
else
{
lean_object* v_head_1425_; lean_object* v_tail_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1435_; 
v_head_1425_ = lean_ctor_get(v_a_1422_, 0);
v_tail_1426_ = lean_ctor_get(v_a_1422_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_a_1422_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1428_ = v_a_1422_;
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_tail_1426_);
lean_inc(v_head_1425_);
lean_dec(v_a_1422_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_inc_ref(v_v_1421_);
lean_inc(v_fvarId_1420_);
v___x_1430_ = l_Lean_Meta_Match_Pattern_replaceFVarId(v_fvarId_1420_, v_v_1421_, v_head_1425_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v_a_1423_);
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1423_);
v___x_1432_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v_a_1422_ = v_tail_1426_;
v_a_1423_ = v___x_1432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object* v_fvarId_1436_, lean_object* v_v_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
if (lean_obj_tag(v_a_1438_) == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_fvarId_1436_);
v___x_1440_ = l_List_reverse___redArg(v_a_1439_);
return v___x_1440_;
}
else
{
lean_object* v_head_1441_; lean_object* v_tail_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1451_; 
v_head_1441_ = lean_ctor_get(v_a_1438_, 0);
v_tail_1442_ = lean_ctor_get(v_a_1438_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1444_ = v_a_1438_;
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_tail_1442_);
lean_inc(v_head_1441_);
lean_dec(v_a_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
lean_inc(v_fvarId_1436_);
v___x_1446_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_1436_, v_v_1437_, v_head_1441_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_a_1439_);
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_a_1439_);
v___x_1448_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
v_a_1438_ = v_tail_1442_;
v_a_1439_ = v___x_1448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_1452_, lean_object* v_v_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1452_, v_v_1453_, v_a_1454_, v_a_1455_);
lean_dec_ref(v_v_1453_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object* v_fvarId_1457_, lean_object* v_v_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
if (lean_obj_tag(v_a_1459_) == 0)
{
lean_object* v___x_1461_; 
lean_dec(v_fvarId_1457_);
v___x_1461_ = l_List_reverse___redArg(v_a_1460_);
return v___x_1461_;
}
else
{
lean_object* v_head_1462_; lean_object* v_tail_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1482_; 
v_head_1462_ = lean_ctor_get(v_a_1459_, 0);
v_tail_1463_ = lean_ctor_get(v_a_1459_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1459_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1465_ = v_a_1459_;
v_isShared_1466_ = v_isSharedCheck_1482_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_tail_1463_);
lean_inc(v_head_1462_);
lean_dec(v_a_1459_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1482_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_fst_1467_; lean_object* v_snd_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1481_; 
v_fst_1467_ = lean_ctor_get(v_head_1462_, 0);
v_snd_1468_ = lean_ctor_get(v_head_1462_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_head_1462_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1470_ = v_head_1462_;
v_isShared_1471_ = v_isSharedCheck_1481_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snd_1468_);
lean_inc(v_fst_1467_);
lean_dec(v_head_1462_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1481_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
lean_inc_n(v_fvarId_1457_, 2);
v___x_1472_ = l_Lean_Expr_replaceFVarId(v_fst_1467_, v_fvarId_1457_, v_v_1458_);
lean_dec(v_fst_1467_);
v___x_1473_ = l_Lean_Expr_replaceFVarId(v_snd_1468_, v_fvarId_1457_, v_v_1458_);
lean_dec(v_snd_1468_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1473_);
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1475_ = v___x_1470_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_a_1460_);
lean_ctor_set(v___x_1465_, 0, v___x_1475_);
v___x_1477_ = v___x_1465_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1460_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v_a_1459_ = v_tail_1463_;
v_a_1460_ = v___x_1477_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object* v_fvarId_1483_, lean_object* v_v_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1483_, v_v_1484_, v_a_1485_, v_a_1486_);
lean_dec_ref(v_v_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object* v_fvarId_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
if (lean_obj_tag(v_a_1489_) == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = l_List_reverse___redArg(v_a_1490_);
return v___x_1491_;
}
else
{
lean_object* v_head_1492_; lean_object* v_tail_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1504_; 
v_head_1492_ = lean_ctor_get(v_a_1489_, 0);
v_tail_1493_ = lean_ctor_get(v_a_1489_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_a_1489_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1495_ = v_a_1489_;
v_isShared_1496_ = v_isSharedCheck_1504_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_tail_1493_);
lean_inc(v_head_1492_);
lean_dec(v_a_1489_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1504_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = l_Lean_LocalDecl_fvarId(v_head_1492_);
v___x_1498_ = l_Lean_instBEqFVarId_beq(v___x_1497_, v_fvarId_1488_);
lean_dec(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v_a_1490_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_head_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_a_1490_);
v___x_1500_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
v_a_1489_ = v_tail_1493_;
v_a_1490_ = v___x_1500_;
goto _start;
}
}
else
{
lean_del_object(v___x_1495_);
lean_dec(v_head_1492_);
v_a_1489_ = v_tail_1493_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_fvarId_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object* v_fvarId_1509_, lean_object* v_v_1510_, lean_object* v_alt_1511_){
_start:
{
lean_object* v_ref_1512_; lean_object* v_idx_1513_; lean_object* v_rhs_1514_; lean_object* v_fvarDecls_1515_; lean_object* v_patterns_1516_; lean_object* v_cnstrs_1517_; lean_object* v_notAltIdxs_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1531_; 
v_ref_1512_ = lean_ctor_get(v_alt_1511_, 0);
v_idx_1513_ = lean_ctor_get(v_alt_1511_, 1);
v_rhs_1514_ = lean_ctor_get(v_alt_1511_, 2);
v_fvarDecls_1515_ = lean_ctor_get(v_alt_1511_, 3);
v_patterns_1516_ = lean_ctor_get(v_alt_1511_, 4);
v_cnstrs_1517_ = lean_ctor_get(v_alt_1511_, 5);
v_notAltIdxs_1518_ = lean_ctor_get(v_alt_1511_, 6);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_alt_1511_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1520_ = v_alt_1511_;
v_isShared_1521_ = v_isSharedCheck_1531_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_notAltIdxs_1518_);
lean_inc(v_cnstrs_1517_);
lean_inc(v_patterns_1516_);
lean_inc(v_fvarDecls_1515_);
lean_inc(v_rhs_1514_);
lean_inc(v_idx_1513_);
lean_inc(v_ref_1512_);
lean_dec(v_alt_1511_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1531_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_decls_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_inc_n(v_fvarId_1509_, 3);
v___x_1522_ = l_Lean_Expr_replaceFVarId(v_rhs_1514_, v_fvarId_1509_, v_v_1510_);
lean_dec_ref(v_rhs_1514_);
v___x_1523_ = lean_box(0);
v_decls_1524_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1509_, v_fvarDecls_1515_, v___x_1523_);
v___x_1525_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1509_, v_v_1510_, v_decls_1524_, v___x_1523_);
lean_inc_ref(v_v_1510_);
v___x_1526_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(v_fvarId_1509_, v_v_1510_, v_patterns_1516_, v___x_1523_);
v___x_1527_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1509_, v_v_1510_, v_cnstrs_1517_, v___x_1523_);
lean_dec_ref(v_v_1510_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 5, v___x_1527_);
lean_ctor_set(v___x_1520_, 4, v___x_1526_);
lean_ctor_set(v___x_1520_, 3, v___x_1525_);
lean_ctor_set(v___x_1520_, 2, v___x_1522_);
v___x_1529_ = v___x_1520_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_ref_1512_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_idx_1513_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1530_, 5, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 6, v_notAltIdxs_1518_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
uint8_t l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(lean_object* v_fvarId_1532_, lean_object* v_x_1533_){
_start:
{
if (lean_obj_tag(v_x_1533_) == 0)
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
else
{
lean_object* v_head_1535_; lean_object* v_tail_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_head_1535_ = lean_ctor_get(v_x_1533_, 0);
v_tail_1536_ = lean_ctor_get(v_x_1533_, 1);
v___x_1537_ = l_Lean_LocalDecl_fvarId(v_head_1535_);
v___x_1538_ = l_Lean_instBEqFVarId_beq(v___x_1537_, v_fvarId_1532_);
lean_dec(v___x_1537_);
if (v___x_1538_ == 0)
{
v_x_1533_ = v_tail_1536_;
goto _start;
}
else
{
return v___x_1538_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1532_ = stack[0].m_obj;
lean_object* v_x_1533_ = stack[1].m_obj;
uint8_t v_res_1540_;
v_res_1540_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1532_, v_x_1533_);
stack->m_num = v_res_1540_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(lean_object* v_fvarId_1541_, lean_object* v_x_1542_){
_start:
{
uint8_t v_res_1543_; lean_object* v_r_1544_; 
v_res_1543_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1541_, v_x_1542_);
lean_dec(v_x_1542_);
lean_dec(v_fvarId_1541_);
v_r_1544_ = lean_box(v_res_1543_);
return v_r_1544_;
}
}
uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object* v_fvarId_1545_, lean_object* v_alt_1546_){
_start:
{
lean_object* v_fvarDecls_1547_; uint8_t v___x_1548_; 
v_fvarDecls_1547_ = lean_ctor_get(v_alt_1546_, 3);
v___x_1548_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1545_, v_fvarDecls_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Alt_isLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1545_ = stack[0].m_obj;
lean_object* v_alt_1546_ = stack[1].m_obj;
uint8_t v_res_1549_;
v_res_1549_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_1545_, v_alt_1546_);
stack->m_num = v_res_1549_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object* v_fvarId_1550_, lean_object* v_alt_1551_){
_start:
{
uint8_t v_res_1552_; lean_object* v_r_1553_; 
v_res_1552_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_1550_, v_alt_1551_);
lean_dec_ref(v_alt_1551_);
lean_dec(v_fvarId_1550_);
v_r_1553_ = lean_box(v_res_1552_);
return v_r_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___impl(lean_object* v_x_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_obj_tag_nat(v_x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___impl___boxed(lean_object* v_x_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Meta_Match_Example_ctorIdx___impl(v_x_1556_);
lean_dec(v_x_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object* v_t_1558_, lean_object* v_k_1559_){
_start:
{
switch(lean_obj_tag(v_t_1558_))
{
case 1:
{
return v_k_1559_;
}
case 2:
{
lean_object* v_a_1560_; lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1560_ = lean_ctor_get(v_t_1558_, 0);
lean_inc(v_a_1560_);
v_a_1561_ = lean_ctor_get(v_t_1558_, 1);
lean_inc(v_a_1561_);
lean_dec_ref_known(v_t_1558_, 2);
v___x_1562_ = lean_apply_2(v_k_1559_, v_a_1560_, v_a_1561_);
return v___x_1562_;
}
case 3:
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v_t_1558_, 0);
lean_inc_ref(v_a_1563_);
lean_dec_ref_known(v_t_1558_, 1);
v___x_1564_ = lean_apply_1(v_k_1559_, v_a_1563_);
return v___x_1564_;
}
default: 
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v_t_1558_, 0);
lean_inc(v_a_1565_);
lean_dec(v_t_1558_);
v___x_1566_ = lean_apply_1(v_k_1559_, v_a_1565_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object* v_motive__1_1567_, lean_object* v_ctorIdx_1568_, lean_object* v_t_1569_, lean_object* v_h_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1569_, v_k_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object* v_motive__1_1573_, lean_object* v_ctorIdx_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_k_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Meta_Match_Example_ctorElim(v_motive__1_1573_, v_ctorIdx_1574_, v_t_1575_, v_h_1576_, v_k_1577_);
lean_dec(v_ctorIdx_1574_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object* v_t_1579_, lean_object* v_var_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1579_, v_var_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object* v_motive__1_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_var_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1583_, v_var_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object* v_t_1587_, lean_object* v_underscore_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1587_, v_underscore_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object* v_motive__1_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_underscore_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1591_, v_underscore_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object* v_t_1595_, lean_object* v_ctor_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1595_, v_ctor_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object* v_motive__1_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_ctor_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1599_, v_ctor_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object* v_t_1603_, lean_object* v_val_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1603_, v_val_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object* v_motive__1_1606_, lean_object* v_t_1607_, lean_object* v_h_1608_, lean_object* v_val_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1607_, v_val_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object* v_t_1611_, lean_object* v_arrayLit_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1611_, v_arrayLit_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object* v_motive__1_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_arrayLit_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1615_, v_arrayLit_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object* v_fvarId_1619_, lean_object* v_ex_1620_, lean_object* v_x_1621_){
_start:
{
switch(lean_obj_tag(v_x_1621_))
{
case 0:
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v_x_1621_, 0);
v___x_1623_ = l_Lean_instBEqFVarId_beq(v_a_1622_, v_fvarId_1619_);
if (v___x_1623_ == 0)
{
return v_x_1621_;
}
else
{
lean_dec_ref_known(v_x_1621_, 1);
lean_inc(v_ex_1620_);
return v_ex_1620_;
}
}
case 2:
{
lean_object* v_a_1624_; lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1634_; 
v_a_1624_ = lean_ctor_get(v_x_1621_, 0);
v_a_1625_ = lean_ctor_get(v_x_1621_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1627_ = v_x_1621_;
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_inc(v_a_1624_);
lean_dec(v_x_1621_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1634_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1619_, v_ex_1620_, v_a_1625_, v___x_1629_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1630_);
v___x_1632_ = v___x_1627_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1624_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
case 4:
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1644_; 
v_a_1635_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1637_ = v_x_1621_;
v_isShared_1638_ = v_isSharedCheck_1644_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v_x_1621_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1644_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_box(0);
v___x_1640_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1619_, v_ex_1620_, v_a_1635_, v___x_1639_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
default: 
{
return v_x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object* v_fvarId_1645_, lean_object* v_ex_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
if (lean_obj_tag(v_a_1647_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = l_List_reverse___redArg(v_a_1648_);
return v___x_1649_;
}
else
{
lean_object* v_head_1650_; lean_object* v_tail_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v_head_1650_ = lean_ctor_get(v_a_1647_, 0);
v_tail_1651_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1653_ = v_a_1647_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_tail_1651_);
lean_inc(v_head_1650_);
lean_dec(v_a_1647_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1645_, v_ex_1646_, v_head_1650_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v_a_1648_);
lean_ctor_set(v___x_1653_, 0, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_a_1648_);
v___x_1657_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v_a_1647_ = v_tail_1651_;
v_a_1648_ = v___x_1657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1661_, lean_object* v_ex_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1661_, v_ex_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_ex_1662_);
lean_dec(v_fvarId_1661_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object* v_fvarId_1666_, lean_object* v_ex_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1666_, v_ex_1667_, v_x_1668_);
lean_dec(v_ex_1667_);
lean_dec(v_fvarId_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object* v_s_1670_, lean_object* v_x_1671_){
_start:
{
switch(lean_obj_tag(v_x_1671_))
{
case 0:
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1682_; 
v_a_1672_ = lean_ctor_get(v_x_1671_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_x_1671_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1674_ = v_x_1671_;
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v_x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Meta_FVarSubst_get(v_s_1670_, v_a_1672_);
if (lean_obj_tag(v___x_1676_) == 1)
{
lean_object* v_fvarId_1677_; lean_object* v___x_1679_; 
v_fvarId_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_fvarId_1677_);
lean_dec_ref_known(v___x_1676_, 1);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v_fvarId_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_fvarId_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v___x_1681_; 
lean_dec_ref(v___x_1676_);
lean_del_object(v___x_1674_);
v___x_1681_ = lean_box(1);
return v___x_1681_;
}
}
}
case 2:
{
lean_object* v_a_1683_; lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1693_; 
v_a_1683_ = lean_ctor_get(v_x_1671_, 0);
v_a_1684_ = lean_ctor_get(v_x_1671_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1671_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1686_ = v_x_1671_;
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_inc(v_a_1683_);
lean_dec(v_x_1671_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1670_, v_a_1684_, v___x_1688_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1689_);
v___x_1691_ = v___x_1686_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1683_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
case 4:
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
v_a_1694_ = lean_ctor_get(v_x_1671_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1671_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1696_ = v_x_1671_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_x_1671_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1670_, v_a_1694_, v___x_1698_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
default: 
{
return v_x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object* v_s_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
if (lean_obj_tag(v_a_1705_) == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = l_List_reverse___redArg(v_a_1706_);
return v___x_1707_;
}
else
{
lean_object* v_head_1708_; lean_object* v_tail_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1718_; 
v_head_1708_ = lean_ctor_get(v_a_1705_, 0);
v_tail_1709_ = lean_ctor_get(v_a_1705_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_a_1705_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1711_ = v_a_1705_;
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_tail_1709_);
lean_inc(v_head_1708_);
lean_dec(v_a_1705_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1704_, v_head_1708_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v_a_1706_);
lean_ctor_set(v___x_1711_, 0, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_a_1706_);
v___x_1715_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v_a_1705_ = v_tail_1709_;
v_a_1706_ = v___x_1715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object* v_s_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_s_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object* v_s_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1723_, v_x_1724_);
lean_dec(v_s_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object* v_x_1726_){
_start:
{
switch(lean_obj_tag(v_x_1726_))
{
case 0:
{
lean_object* v___x_1727_; 
lean_dec_ref_known(v_x_1726_, 1);
v___x_1727_ = lean_box(1);
return v___x_1727_;
}
case 2:
{
lean_object* v_a_1728_; lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1738_; 
v_a_1728_ = lean_ctor_get(v_x_1726_, 0);
v_a_1729_ = lean_ctor_get(v_x_1726_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1726_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1731_ = v_x_1726_;
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_inc(v_a_1728_);
lean_dec(v_x_1726_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1733_ = lean_box(0);
v___x_1734_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1729_, v___x_1733_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1734_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1728_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
case 4:
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1748_; 
v_a_1739_ = lean_ctor_get(v_x_1726_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1726_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1741_ = v_x_1726_;
v_isShared_1742_ = v_isSharedCheck_1748_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v_x_1726_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1748_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1743_ = lean_box(0);
v___x_1744_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1739_, v___x_1743_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1744_);
v___x_1746_ = v___x_1741_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
default: 
{
return v_x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
if (lean_obj_tag(v_a_1749_) == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = l_List_reverse___redArg(v_a_1750_);
return v___x_1751_;
}
else
{
lean_object* v_head_1752_; lean_object* v_tail_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1762_; 
v_head_1752_ = lean_ctor_get(v_a_1749_, 0);
v_tail_1753_ = lean_ctor_get(v_a_1749_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1755_ = v_a_1749_;
v_isShared_1756_ = v_isSharedCheck_1762_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_tail_1753_);
lean_inc(v_head_1752_);
lean_dec(v_a_1749_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1762_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1752_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v_a_1750_);
lean_ctor_set(v___x_1755_, 0, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_a_1750_);
v___x_1759_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
v_a_1749_ = v_tail_1753_;
v_a_1750_ = v___x_1759_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__1));
v___x_1767_ = l_Lean_MessageData_ofFormat(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0));
v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1771_) == 0)
{
return v_x_1770_;
}
else
{
lean_object* v_head_1772_; lean_object* v_tail_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1784_; 
v_head_1772_ = lean_ctor_get(v_x_1771_, 0);
v_tail_1773_ = lean_ctor_get(v_x_1771_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_x_1771_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1775_ = v_x_1771_;
v_isShared_1776_ = v_isSharedCheck_1784_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_tail_1773_);
lean_inc(v_head_1772_);
lean_dec(v_x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1784_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0, &l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once, _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 7);
lean_ctor_set(v___x_1775_, 1, v___x_1777_);
lean_ctor_set(v___x_1775_, 0, v_x_1770_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_x_1770_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1772_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v_x_1770_ = v___x_1781_;
v_x_1771_ = v_tail_1773_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__4));
v___x_1789_ = l_Lean_MessageData_ofFormat(v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object* v_x_1790_){
_start:
{
switch(lean_obj_tag(v_x_1790_))
{
case 0:
{
lean_object* v_a_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_a_1791_ = lean_ctor_get(v_x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v_x_1790_, 1);
v___x_1792_ = l_Lean_mkFVar(v_a_1791_);
v___x_1793_ = l_Lean_MessageData_ofExpr(v___x_1792_);
return v___x_1793_;
}
case 1:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__2, &l_Lean_Meta_Match_Example_toMessageData___closed__2_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__2);
return v___x_1794_;
}
case 2:
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v_x_1790_, 1);
if (lean_obj_tag(v_a_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_a_1796_ = lean_ctor_get(v_x_1790_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v_x_1790_, 2);
v___x_1797_ = lean_box(0);
v___x_1798_ = l_Lean_mkConst(v_a_1796_, v___x_1797_);
v___x_1799_ = l_Lean_MessageData_ofExpr(v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1815_; 
lean_inc(v_a_1795_);
v_a_1800_ = lean_ctor_get(v_x_1790_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1790_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_x_1790_, 1);
lean_dec(v_unused_1816_);
v___x_1802_ = v_x_1790_;
v_isShared_1803_ = v_isSharedCheck_1815_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v_x_1790_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1815_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1804_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_1805_ = 0;
v___x_1806_ = l_Lean_MessageData_ofConstName(v_a_1800_, v___x_1805_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 7);
lean_ctor_set(v___x_1802_, 1, v___x_1806_);
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1808_ = v___x_1802_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1809_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_1810_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(v___x_1809_, v_a_1795_);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1808_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
return v___x_1813_;
}
}
}
}
case 3:
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v_x_1790_, 0);
lean_inc_ref(v_a_1817_);
lean_dec_ref_known(v_x_1790_, 1);
v___x_1818_ = l_Lean_MessageData_ofExpr(v_a_1817_);
return v___x_1818_;
}
default: 
{
lean_object* v_a_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_a_1819_ = lean_ctor_get(v_x_1790_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v_x_1790_, 1);
v___x_1820_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__5, &l_Lean_Meta_Match_Example_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__5);
v___x_1821_ = lean_box(0);
v___x_1822_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_1819_, v___x_1821_);
v___x_1823_ = l_Lean_MessageData_ofList(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1820_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
if (lean_obj_tag(v_a_1825_) == 0)
{
lean_object* v___x_1827_; 
v___x_1827_ = l_List_reverse___redArg(v_a_1826_);
return v___x_1827_;
}
else
{
lean_object* v_head_1828_; lean_object* v_tail_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1838_; 
v_head_1828_ = lean_ctor_get(v_a_1825_, 0);
v_tail_1829_ = lean_ctor_get(v_a_1825_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1831_ = v_a_1825_;
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_tail_1829_);
lean_inc(v_head_1828_);
lean_dec(v_a_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1828_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v_a_1826_);
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1826_);
v___x_1835_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v_a_1825_ = v_tail_1829_;
v_a_1826_ = v___x_1835_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
if (lean_obj_tag(v_a_1839_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = l_List_reverse___redArg(v_a_1840_);
return v___x_1841_;
}
else
{
lean_object* v_head_1842_; lean_object* v_tail_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1853_; 
v_head_1842_ = lean_ctor_get(v_a_1839_, 0);
v_tail_1843_ = lean_ctor_get(v_a_1839_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1845_ = v_a_1839_;
v_isShared_1846_ = v_isSharedCheck_1853_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_tail_1843_);
lean_inc(v_head_1842_);
lean_dec(v_a_1839_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1853_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1847_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1842_);
v___x_1848_ = l_Lean_Meta_Match_Example_toMessageData(v___x_1847_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v_a_1840_);
lean_ctor_set(v___x_1845_, 0, v___x_1848_);
v___x_1850_ = v___x_1845_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_a_1840_);
v___x_1850_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
v_a_1839_ = v_tail_1843_;
v_a_1840_ = v___x_1850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object* v_cex_1854_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(v_cex_1854_, v___x_1855_);
v___x_1857_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_1858_ = l_Lean_MessageData_joinSep(v___x_1856_, v___x_1857_);
return v___x_1858_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object* v_mvarId_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1871_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1871_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1864_ = stack[0].m_obj;
lean_object* v_x_1865_ = stack[1].m_obj;
lean_object* v___y_1866_ = stack[2].m_obj;
lean_object* v___y_1867_ = stack[3].m_obj;
lean_object* v___y_1868_ = stack[4].m_obj;
lean_object* v___y_1869_ = stack[5].m_obj;
lean_object* v_res_1888_;
v_res_1888_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
stack->m_obj
 = v_res_1888_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object* v_mvarId_1889_, lean_object* v_x_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1889_, v_x_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1896_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object* v_00_u03b1_1897_, lean_object* v_mvarId_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1898_, v_x_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1898_ = stack[1].m_obj;
lean_object* v_x_1899_ = stack[2].m_obj;
lean_object* v___y_1900_ = stack[3].m_obj;
lean_object* v___y_1901_ = stack[4].m_obj;
lean_object* v___y_1902_ = stack[5].m_obj;
lean_object* v___y_1903_ = stack[6].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_box(0), v_mvarId_1898_, v_x_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object* v_00_u03b1_1907_, lean_object* v_mvarId_1908_, lean_object* v_x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(v_00_u03b1_1907_, v_mvarId_1908_, v_x_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1915_;
}
}
lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object* v_p_1916_, lean_object* v_x_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_mvarId_1923_; lean_object* v___x_1924_; 
v_mvarId_1923_ = lean_ctor_get(v_p_1916_, 0);
lean_inc(v_mvarId_1923_);
lean_dec_ref(v_p_1916_);
v___x_1924_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1923_, v_x_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
return v___x_1924_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_withGoalOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1916_ = stack[0].m_obj;
lean_object* v_x_1917_ = stack[1].m_obj;
lean_object* v_a_1918_ = stack[2].m_obj;
lean_object* v_a_1919_ = stack[3].m_obj;
lean_object* v_a_1920_ = stack[4].m_obj;
lean_object* v_a_1921_ = stack[5].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1916_, v_x_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object* v_p_1926_, lean_object* v_x_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1926_, v_x_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1933_;
}
}
lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* v_00_u03b1_1934_, lean_object* v_p_1935_, lean_object* v_x_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1935_, v_x_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_withGoalOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1935_ = stack[1].m_obj;
lean_object* v_x_1936_ = stack[2].m_obj;
lean_object* v_a_1937_ = stack[3].m_obj;
lean_object* v_a_1938_ = stack[4].m_obj;
lean_object* v_a_1939_ = stack[5].m_obj;
lean_object* v_a_1940_ = stack[6].m_obj;
lean_object* v_res_1943_;
v_res_1943_ = l_Lean_Meta_Match_withGoalOf(lean_box(0), v_p_1935_, v_x_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
stack->m_obj
 = v_res_1943_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_p_1945_, lean_object* v_x_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_Meta_Match_withGoalOf(v_00_u03b1_1944_, v_p_1945_, v_x_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
return v_res_1952_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object* v_x_1953_, lean_object* v_x_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
if (lean_obj_tag(v_x_1953_) == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = l_List_reverse___redArg(v_x_1954_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v_head_1962_; lean_object* v_tail_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1981_; 
v_head_1962_ = lean_ctor_get(v_x_1953_, 0);
v_tail_1963_ = lean_ctor_get(v_x_1953_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_x_1953_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1965_ = v_x_1953_;
v_isShared_1966_ = v_isSharedCheck_1981_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_tail_1963_);
lean_inc(v_head_1962_);
lean_dec(v_x_1953_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1981_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Meta_Match_Alt_toMessageData(v_head_1962_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 1, v_x_1954_);
lean_ctor_set(v___x_1965_, 0, v_a_1968_);
v___x_1970_ = v___x_1965_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1968_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_x_1954_);
v___x_1970_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
v_x_1953_ = v_tail_1963_;
v_x_1954_ = v___x_1970_;
goto _start;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_del_object(v___x_1965_);
lean_dec(v_tail_1963_);
lean_dec(v_x_1954_);
v_a_1973_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1967_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1967_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1953_ = stack[0].m_obj;
lean_object* v_x_1954_ = stack[1].m_obj;
lean_object* v___y_1955_ = stack[2].m_obj;
lean_object* v___y_1956_ = stack[3].m_obj;
lean_object* v___y_1957_ = stack[4].m_obj;
lean_object* v___y_1958_ = stack[5].m_obj;
lean_object* v_res_1982_;
v_res_1982_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_x_1953_, v_x_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
stack->m_obj
 = v_res_1982_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_x_1983_, v_x_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = l_List_reverse___redArg(v_x_1992_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
else
{
lean_object* v_head_2000_; lean_object* v_tail_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2026_; 
v_head_2000_ = lean_ctor_get(v_x_1991_, 0);
v_tail_2001_ = lean_ctor_get(v_x_1991_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_x_1991_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2003_ = v_x_1991_;
v_isShared_2004_ = v_isSharedCheck_2026_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_tail_2001_);
lean_inc(v_head_2000_);
lean_dec(v_x_1991_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2026_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; 
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v_head_2000_);
v___x_2005_ = lean_infer_type(v_head_2000_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v___x_2007_ = l_Lean_MessageData_ofExpr(v_head_2000_);
v___x_2008_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Lean_MessageData_ofExpr(v_a_2006_);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_x_1992_);
lean_ctor_set(v___x_2003_, 0, v___x_2013_);
v___x_2015_ = v___x_2003_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_x_1992_);
v___x_2015_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
v_x_1991_ = v_tail_2001_;
v_x_1992_ = v___x_2015_;
goto _start;
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_del_object(v___x_2003_);
lean_dec(v_tail_2001_);
lean_dec(v_head_2000_);
lean_dec(v_x_1992_);
v_a_2018_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2005_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2005_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1991_ = stack[0].m_obj;
lean_object* v_x_1992_ = stack[1].m_obj;
lean_object* v___y_1993_ = stack[2].m_obj;
lean_object* v___y_1994_ = stack[3].m_obj;
lean_object* v___y_1995_ = stack[4].m_obj;
lean_object* v___y_1996_ = stack[5].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_x_1991_, v_x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_x_2028_, v_x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
return v_res_2035_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_box(1);
v___x_2043_ = l_Lean_MessageData_ofFormat(v___x_2042_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5));
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
return v___x_2046_;
}
}
lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object* v_alts_2047_, lean_object* v___x_2048_, lean_object* v_vars_2049_, lean_object* v_examples_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; 
lean_inc(v___x_2048_);
v___x_2056_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_alts_2047_, v___x_2048_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
lean_inc(v___x_2048_);
v___x_2058_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_vars_2049_, v___x_2048_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2082_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2082_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2082_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2063_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1);
v___x_2064_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v_a_2059_, v___x_2048_);
v___x_2065_ = l_Lean_MessageData_ofList(v___x_2064_);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2063_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2070_ = l_Lean_MessageData_joinSep(v_a_2057_, v___x_2069_);
v___x_2071_ = l_Lean_indentD(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2068_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_2050_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2078_);
v___x_2080_ = v___x_2061_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_2057_);
lean_dec(v_examples_2050_);
lean_dec(v___x_2048_);
v_a_2083_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2058_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2058_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_examples_2050_);
lean_dec(v_vars_2049_);
lean_dec(v___x_2048_);
v_a_2091_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2056_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2056_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Problem_toMessageData___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_2047_ = stack[0].m_obj;
lean_object* v___x_2048_ = stack[1].m_obj;
lean_object* v_vars_2049_ = stack[2].m_obj;
lean_object* v_examples_2050_ = stack[3].m_obj;
lean_object* v___y_2051_ = stack[4].m_obj;
lean_object* v___y_2052_ = stack[5].m_obj;
lean_object* v___y_2053_ = stack[6].m_obj;
lean_object* v___y_2054_ = stack[7].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(v_alts_2047_, v___x_2048_, v_vars_2049_, v_examples_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object* v_alts_2100_, lean_object* v___x_2101_, lean_object* v_vars_2102_, lean_object* v_examples_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(v_alts_2100_, v___x_2101_, v_vars_2102_, v_examples_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2109_;
}
}
lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* v_p_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_vars_2116_; lean_object* v_alts_2117_; lean_object* v_examples_2118_; lean_object* v___x_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; 
v_vars_2116_ = lean_ctor_get(v_p_2110_, 1);
v_alts_2117_ = lean_ctor_get(v_p_2110_, 2);
v_examples_2118_ = lean_ctor_get(v_p_2110_, 3);
v___x_2119_ = lean_box(0);
lean_inc(v_examples_2118_);
lean_inc(v_vars_2116_);
lean_inc(v_alts_2117_);
v___f_2120_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2120_, 0, v_alts_2117_);
lean_closure_set(v___f_2120_, 1, v___x_2119_);
lean_closure_set(v___f_2120_, 2, v_vars_2116_);
lean_closure_set(v___f_2120_, 3, v_examples_2118_);
v___x_2121_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_2110_, v___f_2120_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2121_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Problem_toMessageData_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2110_ = stack[0].m_obj;
lean_object* v_a_2111_ = stack[1].m_obj;
lean_object* v_a_2112_ = stack[2].m_obj;
lean_object* v_a_2113_ = stack[3].m_obj;
lean_object* v_a_2114_ = stack[4].m_obj;
lean_object* v_res_2122_;
v_res_2122_ = l_Lean_Meta_Match_Problem_toMessageData(v_p_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
stack->m_obj
 = v_res_2122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object* v_p_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_Match_Problem_toMessageData(v_p_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object* v_cex_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
if (lean_obj_tag(v_a_2132_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = l_List_reverse___redArg(v_a_2133_);
return v___x_2134_;
}
else
{
lean_object* v_head_2135_; lean_object* v_tail_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2145_; 
v_head_2135_ = lean_ctor_get(v_a_2132_, 0);
v_tail_2136_ = lean_ctor_get(v_a_2132_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_a_2132_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2138_ = v_a_2132_;
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_tail_2136_);
lean_inc(v_head_2135_);
lean_dec(v_a_2132_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l_Lean_Meta_Match_examplesToMessageData(v_head_2135_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v_a_2133_);
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_a_2133_);
v___x_2142_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
v_a_2132_ = v_tail_2136_;
v_a_2133_ = v___x_2142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object* v_cexs_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2147_ = lean_array_to_list(v_cexs_2146_);
v___x_2148_ = lean_box(0);
v___x_2149_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(v___x_2147_, v___x_2148_);
v___x_2150_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2151_ = l_Lean_MessageData_joinSep(v___x_2149_, v___x_2150_);
return v___x_2151_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object* v_msg_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_ref_2158_; lean_object* v___x_2159_; lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
v_ref_2158_ = lean_ctor_get(v___y_2155_, 2);
v___x_2159_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msg_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_inc(v_ref_2158_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_ref_2158_);
lean_ctor_set(v___x_2164_, 1, v_a_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set_tag(v___x_2162_, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2152_ = stack[0].m_obj;
lean_object* v___y_2153_ = stack[1].m_obj;
lean_object* v___y_2154_ = stack[2].m_obj;
lean_object* v___y_2155_ = stack[3].m_obj;
lean_object* v___y_2156_ = stack[4].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2176_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__0));
v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__2));
v___x_2182_ = l_Lean_stringToMessageData(v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4(void){
_start:
{
lean_object* v___x_2183_; lean_object* v_dummy_2184_; 
v___x_2183_ = lean_box(0);
v_dummy_2184_ = l_Lean_Expr_sort___override(v___x_2183_);
return v_dummy_2184_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t v_sz_2185_, size_t v_i_2186_, lean_object* v_bs_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v___x_2193_; 
v___x_2193_ = lean_usize_dec_lt(v_i_2186_, v_sz_2185_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_bs_2187_);
return v___x_2194_;
}
else
{
lean_object* v_v_2195_; lean_object* v___x_2196_; lean_object* v_bs_x27_2197_; lean_object* v___x_2198_; 
v_v_2195_ = lean_array_uget(v_bs_2187_, v_i_2186_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v_bs_x27_2197_ = lean_array_uset(v_bs_2187_, v_i_2186_, v___x_2196_);
v___x_2198_ = l_Lean_Meta_Match_toPattern(v_v_2195_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_add(v_i_2186_, v___x_2200_);
v___x_2202_ = lean_array_uset(v_bs_x27_2197_, v_i_2186_, v_a_2199_);
v_i_2186_ = v___x_2201_;
v_bs_2187_ = v___x_2202_;
goto _start;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v_bs_x27_2197_);
v_a_2204_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2198_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2198_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2185_ = stack[0].m_num;
size_t v_i_2186_ = stack[1].m_num;
lean_object* v_bs_2187_ = stack[2].m_obj;
lean_object* v___y_2188_ = stack[3].m_obj;
lean_object* v___y_2189_ = stack[4].m_obj;
lean_object* v___y_2190_ = stack[5].m_obj;
lean_object* v___y_2191_ = stack[6].m_obj;
lean_object* v_res_2212_;
v_res_2212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_2185_, v_i_2186_, v_bs_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
stack->m_obj
 = v_res_2212_;
}
lean_object* l_Lean_Meta_Match_toPattern(lean_object* v_e_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_inaccessible_x3f(v_e_2213_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Expr_arrayLit_x3f(v_e_2213_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_2213_);
if (lean_obj_tag(v___x_2237_) == 1)
{
lean_object* v_val_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec_ref(v_e_2213_);
v_val_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2239_ = lean_unsigned_to_nat(2u);
v___x_2240_ = l_Lean_Expr_getAppNumArgs(v_val_2238_);
v___x_2241_ = lean_nat_sub(v___x_2240_, v___x_2239_);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_sub(v___x_2241_, v___x_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = l_Lean_Expr_getRevArg_x21(v_val_2238_, v___x_2243_);
v___x_2245_ = l_Lean_Meta_Match_toPattern(v___x_2244_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2263_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2263_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2263_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_nat_sub(v___x_2240_, v___x_2242_);
v___x_2251_ = lean_nat_sub(v___x_2250_, v___x_2242_);
lean_dec(v___x_2250_);
v___x_2252_ = l_Lean_Expr_getRevArg_x21(v_val_2238_, v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 1)
{
lean_object* v_fvarId_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_fvarId_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_fvarId_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = lean_unsigned_to_nat(3u);
v___x_2255_ = lean_nat_sub(v___x_2240_, v___x_2254_);
lean_dec(v___x_2240_);
v___x_2256_ = lean_nat_sub(v___x_2255_, v___x_2242_);
lean_dec(v___x_2255_);
v___x_2257_ = l_Lean_Expr_getRevArg_x21(v_val_2238_, v___x_2256_);
lean_dec(v_val_2238_);
if (lean_obj_tag(v___x_2257_) == 1)
{
lean_object* v_fvarId_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v_fvarId_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_fvarId_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___x_2259_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_2259_, 0, v_fvarId_2253_);
lean_ctor_set(v___x_2259_, 1, v_a_2246_);
lean_ctor_set(v___x_2259_, 2, v_fvarId_2258_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2259_);
v___x_2261_ = v___x_2248_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
else
{
lean_dec_ref(v___x_2257_);
lean_dec(v_fvarId_2253_);
lean_del_object(v___x_2248_);
lean_dec(v_a_2246_);
v___y_2229_ = v_a_2214_;
v___y_2230_ = v_a_2215_;
v___y_2231_ = v_a_2216_;
v___y_2232_ = v_a_2217_;
goto v___jp_2228_;
}
}
else
{
lean_dec_ref(v___x_2252_);
lean_del_object(v___x_2248_);
lean_dec(v_a_2246_);
lean_dec(v___x_2240_);
lean_dec(v_val_2238_);
v___y_2229_ = v_a_2214_;
v___y_2230_ = v_a_2215_;
v___y_2231_ = v_a_2216_;
v___y_2232_ = v_a_2217_;
goto v___jp_2228_;
}
}
}
else
{
lean_dec(v___x_2240_);
lean_dec(v_val_2238_);
return v___x_2245_;
}
}
else
{
lean_object* v___x_2264_; 
lean_dec(v___x_2237_);
lean_inc_ref(v_e_2213_);
v___x_2264_ = l_Lean_Meta_isMatchValue(v_e_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2357_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2357_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2357_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
uint8_t v___x_2269_; 
v___x_2269_ = lean_unbox(v_a_2265_);
lean_dec(v_a_2265_);
if (v___x_2269_ == 0)
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Expr_isFVar(v_e_2213_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_del_object(v___x_2267_);
lean_inc(v_a_2217_);
lean_inc_ref(v_a_2216_);
lean_inc(v_a_2215_);
lean_inc_ref(v_a_2214_);
lean_inc_ref(v_e_2213_);
v___x_2271_ = lean_whnf(v_e_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; uint8_t v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = lean_expr_eqv(v_a_2272_, v_e_2213_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v_e_2213_);
v_e_2213_ = v_a_2272_;
goto _start;
}
else
{
if (v___x_2270_ == 0)
{
lean_object* v___x_2275_; 
lean_dec(v_a_2272_);
v___x_2275_ = l_Lean_Expr_getAppFn(v_e_2213_);
if (lean_obj_tag(v___x_2275_) == 4)
{
lean_object* v_declName_2276_; lean_object* v_us_2277_; lean_object* v___x_2278_; lean_object* v_env_2279_; lean_object* v___x_2280_; 
v_declName_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_declName_2276_);
v_us_2277_ = lean_ctor_get(v___x_2275_, 1);
lean_inc(v_us_2277_);
lean_dec_ref_known(v___x_2275_, 2);
v___x_2278_ = lean_st_ref_get(v_a_2217_);
v_env_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref(v_env_2279_);
lean_dec(v___x_2278_);
v___x_2280_ = l_Lean_Environment_find_x3f(v_env_2279_, v_declName_2276_, v___x_2270_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_dec(v_us_2277_);
v___y_2220_ = v_a_2214_;
v___y_2221_ = v_a_2215_;
v___y_2222_ = v_a_2216_;
v___y_2223_ = v_a_2217_;
goto v___jp_2219_;
}
else
{
lean_object* v_val_2281_; 
v_val_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___x_2280_, 1);
if (lean_obj_tag(v_val_2281_) == 6)
{
lean_object* v_val_2282_; lean_object* v_toConstantVal_2283_; lean_object* v_numParams_2284_; lean_object* v_numFields_2285_; lean_object* v_nargs_2286_; lean_object* v_dummy_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_val_2282_ = lean_ctor_get(v_val_2281_, 0);
lean_inc_ref(v_val_2282_);
lean_dec_ref_known(v_val_2281_, 1);
v_toConstantVal_2283_ = lean_ctor_get(v_val_2282_, 0);
lean_inc_ref(v_toConstantVal_2283_);
v_numParams_2284_ = lean_ctor_get(v_val_2282_, 3);
lean_inc(v_numParams_2284_);
v_numFields_2285_ = lean_ctor_get(v_val_2282_, 4);
lean_inc(v_numFields_2285_);
lean_dec_ref(v_val_2282_);
v_nargs_2286_ = l_Lean_Expr_getAppNumArgs(v_e_2213_);
v_dummy_2287_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__4, &l_Lean_Meta_Match_toPattern___closed__4_once, _init_l_Lean_Meta_Match_toPattern___closed__4);
lean_inc(v_nargs_2286_);
v___x_2288_ = lean_mk_array(v_nargs_2286_, v_dummy_2287_);
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = lean_nat_sub(v_nargs_2286_, v___x_2289_);
lean_dec(v_nargs_2286_);
lean_inc_ref(v_e_2213_);
v___x_2291_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2213_, v___x_2288_, v___x_2290_);
v___x_2324_ = lean_array_get_size(v___x_2291_);
v___x_2325_ = lean_nat_add(v_numParams_2284_, v_numFields_2285_);
lean_dec(v_numFields_2285_);
v___x_2326_ = lean_nat_dec_eq(v___x_2324_, v___x_2325_);
lean_dec(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2327_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2328_ = l_Lean_indentExpr(v_e_2213_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2329_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_dec_ref_known(v___x_2330_, 1);
v___y_2293_ = v_a_2214_;
v___y_2294_ = v_a_2215_;
v___y_2295_ = v_a_2216_;
v___y_2296_ = v_a_2217_;
goto v___jp_2292_;
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec_ref(v___x_2291_);
lean_dec(v_numParams_2284_);
lean_dec_ref(v_toConstantVal_2283_);
lean_dec(v_us_2277_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_dec_ref(v_e_2213_);
v___y_2293_ = v_a_2214_;
v___y_2294_ = v_a_2215_;
v___y_2295_ = v_a_2216_;
v___y_2296_ = v_a_2217_;
goto v___jp_2292_;
}
v___jp_2292_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2297_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2284_);
v___x_2298_ = l_Array_extract___redArg(v___x_2291_, v___x_2297_, v_numParams_2284_);
v___x_2299_ = lean_array_get_size(v___x_2291_);
v___x_2300_ = l_Array_extract___redArg(v___x_2291_, v_numParams_2284_, v___x_2299_);
lean_dec_ref(v___x_2291_);
v_sz_2301_ = lean_array_size(v___x_2300_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_2301_, v___x_2302_, v___x_2300_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2315_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_name_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v_name_2308_ = lean_ctor_get(v_toConstantVal_2283_, 0);
lean_inc(v_name_2308_);
lean_dec_ref(v_toConstantVal_2283_);
v___x_2309_ = lean_array_to_list(v___x_2298_);
v___x_2310_ = lean_array_to_list(v_a_2304_);
v___x_2311_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2311_, 0, v_name_2308_);
lean_ctor_set(v___x_2311_, 1, v_us_2277_);
lean_ctor_set(v___x_2311_, 2, v___x_2309_);
lean_ctor_set(v___x_2311_, 3, v___x_2310_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2311_);
v___x_2313_ = v___x_2306_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v___x_2298_);
lean_dec_ref(v_toConstantVal_2283_);
lean_dec(v_us_2277_);
v_a_2316_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2303_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2303_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
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
}
else
{
lean_dec(v_val_2281_);
lean_dec(v_us_2277_);
v___y_2220_ = v_a_2214_;
v___y_2221_ = v_a_2215_;
v___y_2222_ = v_a_2216_;
v___y_2223_ = v_a_2217_;
goto v___jp_2219_;
}
}
}
else
{
lean_dec_ref(v___x_2275_);
v___y_2220_ = v_a_2214_;
v___y_2221_ = v_a_2215_;
v___y_2222_ = v_a_2216_;
v___y_2223_ = v_a_2217_;
goto v___jp_2219_;
}
}
else
{
lean_dec_ref(v_e_2213_);
v_e_2213_ = v_a_2272_;
goto _start;
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_e_2213_);
v_a_2340_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2271_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2271_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2348_ = l_Lean_Expr_fvarId_x21(v_e_2213_);
lean_dec_ref(v_e_2213_);
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2349_);
v___x_2351_ = v___x_2267_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_e_2213_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2353_);
v___x_2355_ = v___x_2267_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_e_2213_);
v_a_2358_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2264_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2264_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v_val_2366_; lean_object* v_fst_2367_; lean_object* v_snd_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v_e_2213_);
v_val_2366_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v___x_2236_, 1);
v_fst_2367_ = lean_ctor_get(v_val_2366_, 0);
v_snd_2368_ = lean_ctor_get(v_val_2366_, 1);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_val_2366_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2370_ = v_val_2366_;
v_isShared_2371_ = v_isSharedCheck_2393_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snd_2368_);
lean_inc(v_fst_2367_);
lean_dec(v_val_2366_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2393_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_snd_2368_, v___x_2372_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2384_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2384_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2384_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 4);
lean_ctor_set(v___x_2370_, 1, v_a_2374_);
v___x_2379_ = v___x_2370_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_fst_2367_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2379_);
v___x_2381_ = v___x_2376_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_del_object(v___x_2370_);
lean_dec(v_fst_2367_);
v_a_2385_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2373_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2373_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
else
{
lean_object* v_val_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
lean_dec_ref(v_e_2213_);
v_val_2394_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v___x_2235_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_val_2394_);
lean_dec(v___x_2235_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 0);
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_val_2394_);
v___x_2399_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
v___jp_2219_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2224_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2225_ = l_Lean_indentExpr(v_e_2213_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2224_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2226_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2227_;
}
v___jp_2228_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__3, &l_Lean_Meta_Match_toPattern___closed__3_once, _init_l_Lean_Meta_Match_toPattern___closed__3);
v___x_2234_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2233_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2234_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_toPattern_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2213_ = stack[0].m_obj;
lean_object* v_a_2214_ = stack[1].m_obj;
lean_object* v_a_2215_ = stack[2].m_obj;
lean_object* v_a_2216_ = stack[3].m_obj;
lean_object* v_a_2217_ = stack[4].m_obj;
lean_object* v_res_2403_;
v_res_2403_ = l_Lean_Meta_Match_toPattern(v_e_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
stack->m_obj
 = v_res_2403_;
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
if (lean_obj_tag(v_x_2404_) == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = l_List_reverse___redArg(v_x_2405_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
else
{
lean_object* v_head_2413_; lean_object* v_tail_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2432_; 
v_head_2413_ = lean_ctor_get(v_x_2404_, 0);
v_tail_2414_ = lean_ctor_get(v_x_2404_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_x_2404_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2416_ = v_x_2404_;
v_isShared_2417_ = v_isSharedCheck_2432_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_tail_2414_);
lean_inc(v_head_2413_);
lean_dec(v_x_2404_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2432_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_Match_toPattern(v_head_2413_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_x_2405_);
lean_ctor_set(v___x_2416_, 0, v_a_2419_);
v___x_2421_ = v___x_2416_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2419_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_x_2405_);
v___x_2421_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
v_x_2404_ = v_tail_2414_;
v_x_2405_ = v___x_2421_;
goto _start;
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_del_object(v___x_2416_);
lean_dec(v_tail_2414_);
lean_dec(v_x_2405_);
v_a_2424_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2418_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2418_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2404_ = stack[0].m_obj;
lean_object* v_x_2405_ = stack[1].m_obj;
lean_object* v___y_2406_ = stack[2].m_obj;
lean_object* v___y_2407_ = stack[3].m_obj;
lean_object* v___y_2408_ = stack[4].m_obj;
lean_object* v___y_2409_ = stack[5].m_obj;
lean_object* v_res_2433_;
v_res_2433_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_x_2404_, v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
stack->m_obj
 = v_res_2433_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object* v_x_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_x_2434_, v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object* v_sz_2442_, lean_object* v_i_2443_, lean_object* v_bs_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
size_t v_sz_boxed_2450_; size_t v_i_boxed_2451_; lean_object* v_res_2452_; 
v_sz_boxed_2450_ = lean_unbox_usize(v_sz_2442_);
lean_dec(v_sz_2442_);
v_i_boxed_2451_ = lean_unbox_usize(v_i_2443_);
lean_dec(v_i_2443_);
v_res_2452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_2450_, v_i_boxed_2451_, v_bs_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object* v_e_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_Match_toPattern(v_e_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
return v_res_2459_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object* v_00_u03b1_2460_, lean_object* v_msg_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2461_ = stack[1].m_obj;
lean_object* v___y_2462_ = stack[2].m_obj;
lean_object* v___y_2463_ = stack[3].m_obj;
lean_object* v___y_2464_ = stack[4].m_obj;
lean_object* v___y_2465_ = stack[5].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_box(0), v_msg_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_msg_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(v_00_u03b1_2469_, v_msg_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(lean_object* v_s_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2484_ = lean_string_utf8_byte_size(v_s_2483_);
v___x_2485_ = lean_unsigned_to_nat(9u);
v___x_2486_ = lean_nat_dec_le(v___x_2485_, v___x_2484_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec_ref(v_s_2483_);
v___x_2487_ = lean_box(0);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2488_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = lean_string_memcmp(v_s_2483_, v___x_2488_, v___x_2489_, v___x_2489_, v___x_2485_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref(v_s_2483_);
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_inc_ref(v_s_2483_);
v___x_2492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2492_, 0, v_s_2483_);
lean_ctor_set(v___x_2492_, 1, v___x_2489_);
lean_ctor_set(v___x_2492_, 2, v___x_2484_);
v___x_2493_ = l_String_Slice_pos_x21(v___x_2492_, v___x_2485_);
lean_dec_ref_known(v___x_2492_, 3);
v___x_2494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2494_, 0, v_s_2483_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
lean_ctor_set(v___x_2494_, 2, v___x_2484_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
return v___x_2495_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(lean_object* v_s_2496_, lean_object* v_pat_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object* v_s_2499_, lean_object* v_pat_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(v_s_2499_, v_pat_2500_);
lean_dec_ref(v_pat_2500_);
return v_res_2501_;
}
}
uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object* v_s_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_2502_);
if (lean_obj_tag(v___x_2503_) == 0)
{
uint8_t v___x_2504_; 
v___x_2504_ = 0;
return v___x_2504_;
}
else
{
lean_object* v_val_2505_; uint8_t v___x_2506_; 
v_val_2505_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_val_2505_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2506_ = l_String_Slice_isNat(v_val_2505_);
lean_dec(v_val_2505_);
return v___x_2506_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_isCongrEqnReservedNameSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2502_ = stack[0].m_obj;
uint8_t v_res_2507_;
v_res_2507_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_2502_);
stack->m_num = v_res_2507_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object* v_s_2508_){
_start:
{
uint8_t v_res_2509_; lean_object* v_r_2510_; 
v_res_2509_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_2508_);
v_r_2510_ = lean_box(v_res_2509_);
return v_r_2510_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Value(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
