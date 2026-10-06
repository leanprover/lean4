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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(uint8_t v_annotate_200_, lean_object* v_p_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(uint8_t v_annotate_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_List_reverse___redArg(v_x_293_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v_head_301_; lean_object* v_tail_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_320_; 
v_head_301_ = lean_ctor_get(v_x_292_, 0);
v_tail_302_ = lean_ctor_get(v_x_292_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_292_);
if (v_isSharedCheck_320_ == 0)
{
v___x_304_ = v_x_292_;
v_isShared_305_ = v_isSharedCheck_320_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_tail_302_);
lean_inc(v_head_301_);
lean_dec(v_x_292_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_320_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_291_, v_head_301_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v_x_293_);
lean_ctor_set(v___x_304_, 0, v_a_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_307_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_x_293_);
v___x_309_ = v_reuseFailAlloc_311_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
v_x_292_ = v_tail_302_;
v_x_293_ = v___x_309_;
goto _start;
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_del_object(v___x_304_);
lean_dec(v_tail_302_);
lean_dec(v_x_293_);
v_a_312_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_306_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0___boxed(lean_object* v_annotate_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v_annotate_boxed_329_; lean_object* v_res_330_; 
v_annotate_boxed_329_ = lean_unbox(v_annotate_321_);
v_res_330_ = l_List_mapM_loop___at___00__private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit_spec__0(v_annotate_boxed_329_, v_x_322_, v_x_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit___boxed(lean_object* v_annotate_331_, lean_object* v_p_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
uint8_t v_annotate_boxed_338_; lean_object* v_res_339_; 
v_annotate_boxed_338_ = lean_unbox(v_annotate_331_);
v_res_339_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_boxed_338_, v_p_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr(lean_object* v_p_340_, uint8_t v_annotate_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Lean_Meta_Match_Basic_0__Lean_Meta_Match_Pattern_toExpr_visit(v_annotate_341_, v_p_340_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_toExpr___boxed(lean_object* v_p_348_, lean_object* v_annotate_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
uint8_t v_annotate_boxed_355_; lean_object* v_res_356_; 
v_annotate_boxed_355_ = lean_unbox(v_annotate_349_);
v_res_356_ = l_Lean_Meta_Match_Pattern_toExpr(v_p_348_, v_annotate_boxed_355_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(lean_object* v_s_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
if (lean_obj_tag(v_a_358_) == 0)
{
lean_object* v___x_360_; 
lean_dec(v_s_357_);
v___x_360_ = l_List_reverse___redArg(v_a_359_);
return v___x_360_;
}
else
{
lean_object* v_head_361_; lean_object* v_tail_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_371_; 
v_head_361_ = lean_ctor_get(v_a_358_, 0);
v_tail_362_ = lean_ctor_get(v_a_358_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_a_358_);
if (v_isSharedCheck_371_ == 0)
{
v___x_364_ = v_a_358_;
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_tail_362_);
lean_inc(v_head_361_);
lean_dec(v_a_358_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_371_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_inc(v_s_357_);
v___x_366_ = l_Lean_Meta_FVarSubst_apply(v_s_357_, v_head_361_);
lean_dec(v_head_361_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_a_359_);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_359_);
v___x_368_ = v_reuseFailAlloc_370_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
v_a_358_ = v_tail_362_;
v_a_359_ = v___x_368_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object* v_s_372_, lean_object* v_x_373_){
_start:
{
switch(lean_obj_tag(v_x_373_))
{
case 0:
{
lean_object* v_e_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_e_374_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v_x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_e_374_);
lean_dec(v_x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = l_Lean_Meta_FVarSubst_apply(v_s_372_, v_e_374_);
lean_dec_ref(v_e_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
case 1:
{
lean_object* v_fvarId_383_; lean_object* v___x_384_; 
v_fvarId_383_ = lean_ctor_get(v_x_373_, 0);
v___x_384_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_372_, v_fvarId_383_);
lean_dec(v_s_372_);
if (lean_obj_tag(v___x_384_) == 0)
{
return v_x_373_;
}
else
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_isSharedCheck_392_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v_x_373_, 0);
lean_dec(v_unused_393_);
v___x_386_ = v_x_373_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_x_373_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_val_388_; lean_object* v___x_390_; 
v_val_388_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___x_384_, 1);
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 0);
lean_ctor_set(v___x_386_, 0, v_val_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_val_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
case 2:
{
lean_object* v_ctorName_394_; lean_object* v_us_395_; lean_object* v_params_396_; lean_object* v_fields_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_407_; 
v_ctorName_394_ = lean_ctor_get(v_x_373_, 0);
v_us_395_ = lean_ctor_get(v_x_373_, 1);
v_params_396_ = lean_ctor_get(v_x_373_, 2);
v_fields_397_ = lean_ctor_get(v_x_373_, 3);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_407_ == 0)
{
v___x_399_ = v_x_373_;
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_fields_397_);
lean_inc(v_params_396_);
lean_inc(v_us_395_);
lean_inc(v_ctorName_394_);
lean_dec(v_x_373_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_401_ = lean_box(0);
lean_inc(v_s_372_);
v___x_402_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__0(v_s_372_, v_params_396_, v___x_401_);
v___x_403_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(v_s_372_, v_fields_397_, v___x_401_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 3, v___x_403_);
lean_ctor_set(v___x_399_, 2, v___x_402_);
v___x_405_ = v___x_399_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_ctorName_394_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_us_395_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
case 3:
{
lean_object* v_e_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_416_; 
v_e_408_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_416_ == 0)
{
v___x_410_ = v_x_373_;
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_e_408_);
lean_dec(v_x_373_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = l_Lean_Meta_FVarSubst_apply(v_s_372_, v_e_408_);
lean_dec_ref(v_e_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
case 4:
{
lean_object* v_type_417_; lean_object* v_xs_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_type_417_ = lean_ctor_get(v_x_373_, 0);
v_xs_418_ = lean_ctor_get(v_x_373_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v_x_373_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_xs_418_);
lean_inc(v_type_417_);
lean_dec(v_x_373_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_inc(v_s_372_);
v___x_422_ = l_Lean_Meta_FVarSubst_apply(v_s_372_, v_type_417_);
lean_dec_ref(v_type_417_);
v___x_423_ = lean_box(0);
v___x_424_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(v_s_372_, v_xs_418_, v___x_423_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_424_);
lean_ctor_set(v___x_420_, 0, v___x_422_);
v___x_426_ = v___x_420_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
default: 
{
lean_object* v_varId_429_; lean_object* v_p_430_; lean_object* v_hId_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_441_; 
v_varId_429_ = lean_ctor_get(v_x_373_, 0);
v_p_430_ = lean_ctor_get(v_x_373_, 1);
v_hId_431_ = lean_ctor_get(v_x_373_, 2);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_441_ == 0)
{
v___x_433_ = v_x_373_;
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_hId_431_);
lean_inc(v_p_430_);
lean_inc(v_varId_429_);
lean_dec(v_x_373_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_FVarSubst_find_x3f(v_s_372_, v_varId_429_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_372_, v_p_430_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_varId_429_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_hId_431_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_dec_ref_known(v___x_435_, 1);
lean_del_object(v___x_433_);
lean_dec(v_hId_431_);
lean_dec(v_varId_429_);
v_x_373_ = v_p_430_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_applyFVarSubst_spec__1(lean_object* v_s_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
if (lean_obj_tag(v_a_443_) == 0)
{
lean_object* v___x_445_; 
lean_dec(v_s_442_);
v___x_445_ = l_List_reverse___redArg(v_a_444_);
return v___x_445_;
}
else
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v_head_446_ = lean_ctor_get(v_a_443_, 0);
v_tail_447_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_456_ == 0)
{
v___x_449_ = v_a_443_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_tail_447_);
lean_inc(v_head_446_);
lean_dec(v_a_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_inc(v_s_442_);
v___x_451_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_442_, v_head_446_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_a_444_);
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_444_);
v___x_453_ = v_reuseFailAlloc_455_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v_a_443_ = v_tail_447_;
v_a_444_ = v___x_453_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_replaceFVarId(lean_object* v_fvarId_457_, lean_object* v_v_458_, lean_object* v_p_459_){
_start:
{
lean_object* v_s_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_s_460_ = lean_box(0);
v___x_461_ = l_Lean_Meta_FVarSubst_insert(v_s_460_, v_fvarId_457_, v_v_458_);
v___x_462_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v___x_461_, v_p_459_);
return v___x_462_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(lean_object* v_x_463_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
uint8_t v___x_464_; 
v___x_464_ = 0;
return v___x_464_;
}
else
{
lean_object* v_head_465_; lean_object* v_tail_466_; uint8_t v___x_467_; 
v_head_465_ = lean_ctor_get(v_x_463_, 0);
v_tail_466_ = lean_ctor_get(v_x_463_, 1);
v___x_467_ = l_Lean_Expr_hasExprMVar(v_head_465_);
if (v___x_467_ == 0)
{
v_x_463_ = v_tail_466_;
goto _start;
}
else
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0___boxed(lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_x_469_);
lean_dec(v_x_469_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object* v_x_472_){
_start:
{
switch(lean_obj_tag(v_x_472_))
{
case 0:
{
lean_object* v_e_473_; uint8_t v___x_474_; 
v_e_473_ = lean_ctor_get(v_x_472_, 0);
v___x_474_ = l_Lean_Expr_hasExprMVar(v_e_473_);
return v___x_474_;
}
case 2:
{
lean_object* v_params_475_; lean_object* v_fields_476_; uint8_t v___x_477_; 
v_params_475_ = lean_ctor_get(v_x_472_, 2);
v_fields_476_ = lean_ctor_get(v_x_472_, 3);
v___x_477_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__0(v_params_475_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; 
v___x_478_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_fields_476_);
return v___x_478_;
}
else
{
return v___x_477_;
}
}
case 3:
{
lean_object* v_e_479_; uint8_t v___x_480_; 
v_e_479_ = lean_ctor_get(v_x_472_, 0);
v___x_480_ = l_Lean_Expr_hasExprMVar(v_e_479_);
return v___x_480_;
}
case 5:
{
lean_object* v_p_481_; 
v_p_481_ = lean_ctor_get(v_x_472_, 1);
v_x_472_ = v_p_481_;
goto _start;
}
case 4:
{
lean_object* v_type_483_; lean_object* v_xs_484_; uint8_t v___x_485_; 
v_type_483_ = lean_ctor_get(v_x_472_, 0);
v_xs_484_ = lean_ctor_get(v_x_472_, 1);
v___x_485_ = l_Lean_Expr_hasExprMVar(v_type_483_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_xs_484_);
return v___x_486_;
}
else
{
return v___x_485_;
}
}
default: 
{
uint8_t v___x_487_; 
v___x_487_ = 0;
return v___x_487_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
else
{
lean_object* v_head_490_; lean_object* v_tail_491_; uint8_t v___x_492_; 
v_head_490_ = lean_ctor_get(v_x_488_, 0);
v_tail_491_ = lean_ctor_get(v_x_488_, 1);
v___x_492_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_head_490_);
if (v___x_492_ == 0)
{
v_x_488_ = v_tail_491_;
goto _start;
}
else
{
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1___boxed(lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_List_any___at___00Lean_Meta_Match_Pattern_hasExprMVar_spec__1(v_x_494_);
lean_dec(v_x_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_497_);
lean_dec_ref(v_x_497_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object* v_as_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
if (lean_obj_tag(v_as_500_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v_head_509_; lean_object* v_tail_510_; lean_object* v___x_511_; 
v_head_509_ = lean_ctor_get(v_as_500_, 0);
lean_inc(v_head_509_);
v_tail_510_ = lean_ctor_get(v_as_500_, 1);
lean_inc(v_tail_510_);
lean_dec_ref_known(v_as_500_, 2);
v___x_511_ = l_Lean_Expr_collectFVars(v_head_509_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_dec_ref_known(v___x_511_, 1);
v_as_500_ = v_tail_510_;
goto _start;
}
else
{
lean_dec(v_tail_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object* v_as_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_as_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object* v_p_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
switch(lean_obj_tag(v_p_521_))
{
case 1:
{
lean_object* v_fvarId_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_539_; 
v_fvarId_528_ = lean_ctor_get(v_p_521_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_p_521_);
if (v_isSharedCheck_539_ == 0)
{
v___x_530_ = v_p_521_;
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_fvarId_528_);
lean_dec(v_p_521_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_532_ = lean_st_ref_take(v_a_522_);
v___x_533_ = lean_box(0);
v___x_534_ = l_Lean_CollectFVars_State_add(v___x_532_, v_fvarId_528_);
v___x_535_ = lean_st_ref_put(v_a_522_, v___x_534_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 0);
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_537_ = v___x_530_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_533_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
case 2:
{
lean_object* v_params_540_; lean_object* v_fields_541_; lean_object* v___x_542_; 
v_params_540_ = lean_ctor_get(v_p_521_, 2);
lean_inc(v_params_540_);
v_fields_541_ = lean_ctor_get(v_p_521_, 3);
lean_inc(v_fields_541_);
lean_dec_ref_known(v_p_521_, 4);
v___x_542_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_params_540_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v___x_543_; 
lean_dec_ref_known(v___x_542_, 1);
v___x_543_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_fields_541_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
return v___x_543_;
}
else
{
lean_dec(v_fields_541_);
return v___x_542_;
}
}
case 4:
{
lean_object* v_type_544_; lean_object* v_xs_545_; lean_object* v___x_546_; 
v_type_544_ = lean_ctor_get(v_p_521_, 0);
lean_inc_ref(v_type_544_);
v_xs_545_ = lean_ctor_get(v_p_521_, 1);
lean_inc(v_xs_545_);
lean_dec_ref_known(v_p_521_, 2);
v___x_546_ = l_Lean_Expr_collectFVars(v_type_544_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_547_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_xs_545_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
return v___x_547_;
}
else
{
lean_dec(v_xs_545_);
return v___x_546_;
}
}
case 5:
{
lean_object* v_varId_548_; lean_object* v_p_549_; lean_object* v_hId_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_varId_548_ = lean_ctor_get(v_p_521_, 0);
lean_inc(v_varId_548_);
v_p_549_ = lean_ctor_get(v_p_521_, 1);
lean_inc_ref(v_p_549_);
v_hId_550_ = lean_ctor_get(v_p_521_, 2);
lean_inc(v_hId_550_);
lean_dec_ref_known(v_p_521_, 3);
v___x_551_ = lean_st_ref_take(v_a_522_);
v___x_552_ = l_Lean_CollectFVars_State_add(v___x_551_, v_varId_548_);
v___x_553_ = l_Lean_CollectFVars_State_add(v___x_552_, v_hId_550_);
v___x_554_ = lean_st_ref_put(v_a_522_, v___x_553_);
v_p_521_ = v_p_549_;
goto _start;
}
default: 
{
lean_object* v_e_556_; lean_object* v___x_557_; 
v_e_556_ = lean_ctor_get(v_p_521_, 0);
lean_inc_ref(v_e_556_);
lean_dec_ref(v_p_521_);
v___x_557_ = l_Lean_Expr_collectFVars(v_e_556_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object* v_as_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
if (lean_obj_tag(v_as_558_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
else
{
lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___x_569_; 
v_head_567_ = lean_ctor_get(v_as_558_, 0);
lean_inc(v_head_567_);
v_tail_568_ = lean_ctor_get(v_as_558_, 1);
lean_inc(v_tail_568_);
lean_dec_ref_known(v_as_558_, 2);
v___x_569_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_567_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_dec_ref_known(v___x_569_, 1);
v_as_558_ = v_tail_568_;
goto _start;
}
else
{
lean_dec(v_tail_568_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object* v_as_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_as_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object* v_p_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Match_Pattern_collectFVars(v_p_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object* v_e_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_Expr_hasMVar(v_e_587_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v_e_587_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v_mctx_593_; lean_object* v___x_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_597_; lean_object* v_cache_598_; lean_object* v_zetaDeltaFVarIds_599_; lean_object* v_postponed_600_; lean_object* v_diag_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_610_; 
v___x_592_ = lean_st_ref_get(v___y_588_);
v_mctx_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_ref(v_mctx_593_);
lean_dec(v___x_592_);
v___x_594_ = l_Lean_instantiateMVarsCore(v_mctx_593_, v_e_587_);
v_fst_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_fst_595_);
v_snd_596_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_snd_596_);
lean_dec_ref(v___x_594_);
v___x_597_ = lean_st_ref_take(v___y_588_);
v_cache_598_ = lean_ctor_get(v___x_597_, 1);
v_zetaDeltaFVarIds_599_ = lean_ctor_get(v___x_597_, 2);
v_postponed_600_ = lean_ctor_get(v___x_597_, 3);
v_diag_601_ = lean_ctor_get(v___x_597_, 4);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_611_);
v___x_603_ = v___x_597_;
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_diag_601_);
lean_inc(v_postponed_600_);
lean_inc(v_zetaDeltaFVarIds_599_);
lean_inc(v_cache_598_);
lean_dec(v___x_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_610_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_snd_596_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_snd_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_cache_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_zetaDeltaFVarIds_599_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_postponed_600_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_diag_601_);
v___x_606_ = v_reuseFailAlloc_609_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_st_ref_put(v___y_588_, v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_fst_595_);
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object* v_e_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_612_, v___y_613_);
lean_dec(v___y_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object* v_e_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_616_, v___y_618_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object* v_e_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(v_e_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = l_List_reverse___redArg(v_x_631_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v_head_639_; lean_object* v_tail_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_650_; 
v_head_639_ = lean_ctor_get(v_x_630_, 0);
v_tail_640_ = lean_ctor_get(v_x_630_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_650_ == 0)
{
v___x_642_ = v_x_630_;
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_tail_640_);
lean_inc(v_head_639_);
lean_dec(v_x_630_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v_a_645_; lean_object* v___x_647_; 
v___x_644_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_639_, v___y_633_);
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_644_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_x_631_);
lean_ctor_set(v___x_642_, 0, v_a_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_645_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_x_631_);
v___x_647_ = v_reuseFailAlloc_649_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v_x_630_ = v_tail_640_;
v_x_631_ = v___x_647_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_x_651_, v_x_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* v_x_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
switch(lean_obj_tag(v_x_659_))
{
case 0:
{
lean_object* v_e_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_689_; 
v_e_665_ = lean_ctor_get(v_x_659_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_689_ == 0)
{
v___x_667_ = v_x_659_;
v_isShared_668_ = v_isSharedCheck_689_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_e_665_);
lean_dec(v_x_659_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_689_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_665_, v_a_661_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_680_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_680_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_680_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_680_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_a_670_);
v___x_675_ = v___x_667_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_del_object(v___x_667_);
v_a_681_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_669_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_669_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
case 3:
{
lean_object* v_e_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_714_; 
v_e_690_ = lean_ctor_get(v_x_659_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_714_ == 0)
{
v___x_692_ = v_x_659_;
v_isShared_693_ = v_isSharedCheck_714_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_e_690_);
lean_dec(v_x_659_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_714_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_690_, v_a_661_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_705_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_a_695_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_692_);
v_a_706_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_694_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_694_);
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
case 2:
{
lean_object* v_ctorName_715_; lean_object* v_us_716_; lean_object* v_params_717_; lean_object* v_fields_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_753_; 
v_ctorName_715_ = lean_ctor_get(v_x_659_, 0);
v_us_716_ = lean_ctor_get(v_x_659_, 1);
v_params_717_ = lean_ctor_get(v_x_659_, 2);
v_fields_718_ = lean_ctor_get(v_x_659_, 3);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_753_ == 0)
{
v___x_720_ = v_x_659_;
v_isShared_721_ = v_isSharedCheck_753_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_fields_718_);
lean_inc(v_params_717_);
lean_inc(v_us_716_);
lean_inc(v_ctorName_715_);
lean_dec(v_x_659_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_753_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_box(0);
v___x_723_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_params_717_, v___x_722_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_fields_718_, v___x_722_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_736_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_736_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 3, v_a_726_);
lean_ctor_set(v___x_720_, 2, v_a_724_);
v___x_731_ = v___x_720_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_ctorName_715_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_us_716_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_a_724_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_a_726_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_a_724_);
lean_del_object(v___x_720_);
lean_dec(v_us_716_);
lean_dec(v_ctorName_715_);
v_a_737_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_725_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_725_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_720_);
lean_dec(v_fields_718_);
lean_dec(v_us_716_);
lean_dec(v_ctorName_715_);
v_a_745_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_723_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_723_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
case 5:
{
lean_object* v_varId_754_; lean_object* v_p_755_; lean_object* v_hId_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_772_; 
v_varId_754_ = lean_ctor_get(v_x_659_, 0);
v_p_755_ = lean_ctor_get(v_x_659_, 1);
v_hId_756_ = lean_ctor_get(v_x_659_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_772_ == 0)
{
v___x_758_ = v_x_659_;
v_isShared_759_ = v_isSharedCheck_772_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_hId_756_);
lean_inc(v_p_755_);
lean_inc(v_varId_754_);
lean_dec(v_x_659_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_772_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Match_instantiatePatternMVars(v_p_755_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_771_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_771_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_a_761_);
v___x_766_ = v___x_758_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_varId_754_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_hId_756_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_del_object(v___x_758_);
lean_dec(v_hId_756_);
lean_dec(v_varId_754_);
return v___x_760_;
}
}
}
case 4:
{
lean_object* v_type_773_; lean_object* v_xs_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_809_; 
v_type_773_ = lean_ctor_get(v_x_659_, 0);
v_xs_774_ = lean_ctor_get(v_x_659_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_809_ == 0)
{
v___x_776_ = v_x_659_;
v_isShared_777_ = v_isSharedCheck_809_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_xs_774_);
lean_inc(v_type_773_);
lean_dec(v_x_659_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_809_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_773_, v_a_661_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = lean_box(0);
v___x_781_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_xs_774_, v___x_780_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_792_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_792_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v_a_782_);
lean_ctor_set(v___x_776_, 0, v_a_779_);
v___x_787_ = v___x_776_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_779_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_a_782_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec(v_a_779_);
lean_del_object(v___x_776_);
v_a_793_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_781_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_781_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_del_object(v___x_776_);
lean_dec(v_xs_774_);
v_a_801_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_778_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_778_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
default: 
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_x_659_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = l_List_reverse___redArg(v_x_812_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v_head_820_; lean_object* v_tail_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_839_; 
v_head_820_ = lean_ctor_get(v_x_811_, 0);
v_tail_821_ = lean_ctor_get(v_x_811_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_839_ == 0)
{
v___x_823_ = v_x_811_;
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_tail_821_);
lean_inc(v_head_820_);
lean_dec(v_x_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_Match_instantiatePatternMVars(v_head_820_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_x_812_);
lean_ctor_set(v___x_823_, 0, v_a_826_);
v___x_828_ = v___x_823_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_x_812_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_x_811_ = v_tail_821_;
v_x_812_ = v___x_828_;
goto _start;
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_823_);
lean_dec(v_tail_821_);
lean_dec(v_x_812_);
v_a_831_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_825_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_825_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_x_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* v_x_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_Match_instantiatePatternMVars(v_x_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object* v_as_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
if (lean_obj_tag(v_as_860_) == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
else
{
lean_object* v_head_869_; lean_object* v_tail_870_; lean_object* v___x_871_; 
v_head_869_ = lean_ctor_get(v_as_860_, 0);
lean_inc(v_head_869_);
v_tail_870_ = lean_ctor_get(v_as_860_, 1);
lean_inc(v_tail_870_);
lean_dec_ref_known(v_as_860_, 2);
v___x_871_ = l_Lean_LocalDecl_collectFVars(v_head_869_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_dec_ref_known(v___x_871_, 1);
v_as_860_ = v_tail_870_;
goto _start;
}
else
{
lean_dec(v_tail_870_);
return v___x_871_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object* v_as_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_as_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object* v_as_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (lean_obj_tag(v_as_881_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v_head_890_; lean_object* v_tail_891_; lean_object* v___x_892_; 
v_head_890_ = lean_ctor_get(v_as_881_, 0);
lean_inc(v_head_890_);
v_tail_891_ = lean_ctor_get(v_as_881_, 1);
lean_inc(v_tail_891_);
lean_dec_ref_known(v_as_881_, 2);
v___x_892_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_890_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v_as_881_ = v_tail_891_;
goto _start;
}
else
{
lean_dec(v_tail_891_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object* v_as_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_as_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* v_altLHS_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_fvarDecls_909_; lean_object* v_patterns_910_; lean_object* v___x_911_; 
v_fvarDecls_909_ = lean_ctor_get(v_altLHS_902_, 1);
lean_inc(v_fvarDecls_909_);
v_patterns_910_ = lean_ctor_get(v_altLHS_902_, 2);
lean_inc(v_patterns_910_);
lean_dec_ref(v_altLHS_902_);
v___x_911_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_fvarDecls_909_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; 
lean_dec_ref_known(v___x_911_, 1);
v___x_912_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_patterns_910_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_912_;
}
else
{
lean_dec(v_patterns_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* v_altLHS_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Meta_Match_AltLHS_collectFVars(v_altLHS_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object* v_localDecl_921_, lean_object* v___y_922_){
_start:
{
if (lean_obj_tag(v_localDecl_921_) == 0)
{
lean_object* v_index_924_; lean_object* v_fvarId_925_; lean_object* v_userName_926_; lean_object* v_type_927_; uint8_t v_bi_928_; uint8_t v_kind_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_945_; 
v_index_924_ = lean_ctor_get(v_localDecl_921_, 0);
v_fvarId_925_ = lean_ctor_get(v_localDecl_921_, 1);
v_userName_926_ = lean_ctor_get(v_localDecl_921_, 2);
v_type_927_ = lean_ctor_get(v_localDecl_921_, 3);
v_bi_928_ = lean_ctor_get_uint8(v_localDecl_921_, sizeof(void*)*4);
v_kind_929_ = lean_ctor_get_uint8(v_localDecl_921_, sizeof(void*)*4 + 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_localDecl_921_);
if (v_isSharedCheck_945_ == 0)
{
v___x_931_ = v_localDecl_921_;
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_type_927_);
lean_inc(v_userName_926_);
lean_inc(v_fvarId_925_);
lean_inc(v_index_924_);
lean_dec(v_localDecl_921_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_944_; 
v___x_933_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_927_, v___y_922_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_944_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_944_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_944_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 3, v_a_934_);
v___x_939_ = v___x_931_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_index_924_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_fvarId_925_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_userName_926_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_a_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*4, v_bi_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*4 + 1, v_kind_929_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_939_);
v___x_941_ = v___x_936_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
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
}
else
{
lean_object* v_index_946_; lean_object* v_fvarId_947_; lean_object* v_userName_948_; lean_object* v_type_949_; lean_object* v_value_950_; uint8_t v_nondep_951_; uint8_t v_kind_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_970_; 
v_index_946_ = lean_ctor_get(v_localDecl_921_, 0);
v_fvarId_947_ = lean_ctor_get(v_localDecl_921_, 1);
v_userName_948_ = lean_ctor_get(v_localDecl_921_, 2);
v_type_949_ = lean_ctor_get(v_localDecl_921_, 3);
v_value_950_ = lean_ctor_get(v_localDecl_921_, 4);
v_nondep_951_ = lean_ctor_get_uint8(v_localDecl_921_, sizeof(void*)*5);
v_kind_952_ = lean_ctor_get_uint8(v_localDecl_921_, sizeof(void*)*5 + 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_localDecl_921_);
if (v_isSharedCheck_970_ == 0)
{
v___x_954_ = v_localDecl_921_;
v_isShared_955_ = v_isSharedCheck_970_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_value_950_);
lean_inc(v_type_949_);
lean_inc(v_userName_948_);
lean_inc(v_fvarId_947_);
lean_inc(v_index_946_);
lean_dec(v_localDecl_921_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_970_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_969_; 
v___x_956_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_949_, v___y_922_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_950_, v___y_922_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_969_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 4, v_a_959_);
lean_ctor_set(v___x_954_, 3, v_a_957_);
v___x_964_ = v___x_954_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_index_946_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_fvarId_947_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_userName_948_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_a_957_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_a_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*5, v_nondep_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*5 + 1, v_kind_952_);
v___x_964_ = v_reuseFailAlloc_968_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_964_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object* v_localDecl_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_971_, v___y_972_);
lean_dec(v___y_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = l_List_reverse___redArg(v_x_976_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
else
{
lean_object* v_head_984_; lean_object* v_tail_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1003_; 
v_head_984_ = lean_ctor_get(v_x_975_, 0);
v_tail_985_ = lean_ctor_get(v_x_975_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_987_ = v_x_975_;
v_isShared_988_ = v_isSharedCheck_1003_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_tail_985_);
lean_inc(v_head_984_);
lean_dec(v_x_975_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1003_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_984_, v___y_978_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_x_976_);
lean_ctor_set(v___x_987_, 0, v_a_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_x_976_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_x_975_ = v_tail_985_;
v_x_976_ = v___x_992_;
goto _start;
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_del_object(v___x_987_);
lean_dec(v_tail_985_);
lean_dec(v_x_976_);
v_a_995_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_989_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_989_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_x_1004_, v_x_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* v_altLHS_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_ref_1018_; lean_object* v_fvarDecls_1019_; lean_object* v_patterns_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1055_; 
v_ref_1018_ = lean_ctor_get(v_altLHS_1012_, 0);
v_fvarDecls_1019_ = lean_ctor_get(v_altLHS_1012_, 1);
v_patterns_1020_ = lean_ctor_get(v_altLHS_1012_, 2);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_altLHS_1012_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1022_ = v_altLHS_1012_;
v_isShared_1023_ = v_isSharedCheck_1055_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_patterns_1020_);
lean_inc(v_fvarDecls_1019_);
lean_inc(v_ref_1018_);
lean_dec(v_altLHS_1012_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1055_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_fvarDecls_1019_, v___x_1024_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_patterns_1020_, v___x_1024_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 2, v_a_1028_);
lean_ctor_set(v___x_1022_, 1, v_a_1026_);
v___x_1033_ = v___x_1022_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_ref_1018_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_a_1026_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1026_);
lean_del_object(v___x_1022_);
lean_dec(v_ref_1018_);
v_a_1039_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1027_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1027_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1022_);
lean_dec(v_patterns_1020_);
lean_dec(v_ref_1018_);
v_a_1047_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1025_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1025_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* v_altLHS_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_Match_instantiateAltLHSMVars(v_altLHS_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object* v_localDecl_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_1063_, v___y_1065_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object* v_localDecl_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(v_localDecl_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1079_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0));
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
lean_ctor_set(v___x_1084_, 2, v___x_1081_);
lean_ctor_set(v___x_1084_, 3, v___x_1080_);
lean_ctor_set(v___x_1084_, 4, v___x_1080_);
lean_ctor_set(v___x_1084_, 5, v___x_1080_);
lean_ctor_set(v___x_1084_, 6, v___x_1079_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default(void){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedAlt_default___closed__1, &l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt(void){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_Match_instInhabitedAlt_default;
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object* v_msgData_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v_env_1094_; uint8_t v___x_1095_; lean_object* v_env_1096_; lean_object* v___x_1097_; lean_object* v_toCold_1098_; lean_object* v_mctx_1099_; lean_object* v_lctx_1100_; lean_object* v_options_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1093_ = lean_st_ref_get(v___y_1091_);
v_env_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_env_1094_);
lean_dec(v___x_1093_);
v___x_1095_ = 0;
v_env_1096_ = l_Lean_Environment_setRecordingDeps(v_env_1094_, v___x_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1089_);
v_toCold_1098_ = lean_ctor_get(v___y_1090_, 0);
v_mctx_1099_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_mctx_1099_);
lean_dec(v___x_1097_);
v_lctx_1100_ = lean_ctor_get(v___y_1088_, 2);
v_options_1101_ = lean_ctor_get(v_toCold_1098_, 2);
lean_inc_ref(v_options_1101_);
lean_inc_ref(v_lctx_1100_);
v___x_1102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1102_, 0, v_env_1096_);
lean_ctor_set(v___x_1102_, 1, v_mctx_1099_);
lean_ctor_set(v___x_1102_, 2, v_lctx_1100_);
lean_ctor_set(v___x_1102_, 3, v_options_1101_);
v___x_1103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_msgData_1087_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object* v_msgData_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msgData_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(lean_object* v_decls_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1112_, v_x_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
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
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(lean_object* v_decls_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1136_, v_x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object* v_00_u03b1_1144_, lean_object* v_decls_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1145_, v_x_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_decls_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(v_00_u03b1_1153_, v_decls_1154_, v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(lean_object* v_as_x27_1168_, lean_object* v_b_1169_){
_start:
{
if (lean_obj_tag(v_as_x27_1168_) == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_b_1169_);
return v___x_1171_;
}
else
{
lean_object* v_head_1172_; lean_object* v_tail_1173_; lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_head_1172_ = lean_ctor_get(v_as_x27_1168_, 0);
v_tail_1173_ = lean_ctor_get(v_as_x27_1168_, 1);
v_fst_1174_ = lean_ctor_get(v_head_1172_, 0);
v_snd_1175_ = lean_ctor_get(v_head_1172_, 1);
v___x_1176_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1169_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
lean_inc(v_fst_1174_);
v___x_1178_ = l_Lean_MessageData_ofExpr(v_fst_1174_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
lean_inc(v_snd_1175_);
v___x_1182_ = l_Lean_MessageData_ofExpr(v_snd_1175_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v_as_x27_1168_ = v_tail_1173_;
v_b_1169_ = v___x_1183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(lean_object* v_as_x27_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1185_, v_b_1186_);
lean_dec(v_as_x27_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0(lean_object* v_cnstrs_1189_, lean_object* v_msg_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v_a_1197_; lean_object* v___x_1198_; 
v___x_1196_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_cnstrs_1189_, v_msg_1190_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_a_1197_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed(lean_object* v_cnstrs_1199_, lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_Match_Alt_toMessageData___lam__0(v_cnstrs_1199_, v_msg_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v_cnstrs_1199_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
if (lean_obj_tag(v_a_1207_) == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = l_List_reverse___redArg(v_a_1208_);
return v___x_1209_;
}
else
{
lean_object* v_head_1210_; lean_object* v_tail_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_head_1210_ = lean_ctor_get(v_a_1207_, 0);
v_tail_1211_ = lean_ctor_get(v_a_1207_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_a_1207_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v_a_1207_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_tail_1211_);
lean_inc(v_head_1210_);
lean_dec(v_a_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_a_1208_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_head_1210_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_a_1208_);
v___x_1216_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v_a_1207_ = v_tail_1211_;
v_a_1208_ = v___x_1216_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__0));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
if (lean_obj_tag(v_a_1223_) == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = l_List_reverse___redArg(v_a_1224_);
return v___x_1225_;
}
else
{
lean_object* v_head_1226_; lean_object* v_tail_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1244_; 
v_head_1226_ = lean_ctor_get(v_a_1223_, 0);
v_tail_1227_ = lean_ctor_get(v_a_1223_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_a_1223_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1229_ = v_a_1223_;
v_isShared_1230_ = v_isSharedCheck_1244_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_tail_1227_);
lean_inc(v_head_1226_);
lean_dec(v_a_1223_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1244_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
lean_inc(v_head_1226_);
v___x_1231_ = l_Lean_LocalDecl_toExpr(v_head_1226_);
v___x_1232_ = l_Lean_MessageData_ofExpr(v___x_1231_);
v___x_1233_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_LocalDecl_type(v_head_1226_);
lean_dec(v_head_1226_);
v___x_1236_ = l_Lean_MessageData_ofExpr(v___x_1235_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1234_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_a_1224_);
lean_ctor_set(v___x_1229_, 0, v___x_1239_);
v___x_1241_ = v___x_1229_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_a_1224_);
v___x_1241_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
v_a_1223_ = v_tail_1227_;
v_a_1224_ = v___x_1241_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__0));
v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__2));
v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__4));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Meta_Match_Alt_toMessageData___closed__6));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData(lean_object* v_alt_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_rhs_1263_; lean_object* v_fvarDecls_1264_; lean_object* v_patterns_1265_; lean_object* v_cnstrs_1266_; lean_object* v___y_1268_; uint8_t v___x_1282_; 
v_rhs_1263_ = lean_ctor_get(v_alt_1257_, 2);
lean_inc_ref(v_rhs_1263_);
v_fvarDecls_1264_ = lean_ctor_get(v_alt_1257_, 3);
lean_inc(v_fvarDecls_1264_);
v_patterns_1265_ = lean_ctor_get(v_alt_1257_, 4);
lean_inc(v_patterns_1265_);
v_cnstrs_1266_ = lean_ctor_get(v_alt_1257_, 5);
lean_inc(v_cnstrs_1266_);
lean_dec_ref(v_alt_1257_);
v___x_1282_ = l_List_isEmpty___redArg(v_fvarDecls_1264_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1283_ = lean_box(0);
lean_inc(v_fvarDecls_1264_);
v___x_1284_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4(v_fvarDecls_1264_, v___x_1283_);
v___x_1285_ = l_Lean_MessageData_ofList(v___x_1284_);
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___y_1268_ = v___x_1287_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__7, &l_Lean_Meta_Match_Alt_toMessageData___closed__7_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__7);
v___y_1268_ = v___x_1288_;
goto v___jp_1267_;
}
v___jp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_msg_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___x_1269_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__1, &l_Lean_Meta_Match_Alt_toMessageData___closed__1_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__1);
v___x_1270_ = lean_box(0);
v___x_1271_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Pattern_toMessageData_spec__1(v_patterns_1265_, v___x_1270_);
v___x_1272_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v___x_1271_, v___x_1270_);
v___x_1273_ = l_Lean_MessageData_ofList(v___x_1272_);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1269_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__3, &l_Lean_Meta_Match_Alt_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__3);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Lean_MessageData_ofExpr(v_rhs_1263_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v_msg_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_1279_, 0, v___y_1268_);
lean_ctor_set(v_msg_1279_, 1, v___x_1278_);
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_toMessageData___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1280_, 0, v_cnstrs_1266_);
lean_closure_set(v___f_1280_, 1, v_msg_1279_);
v___x_1281_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_fvarDecls_1264_, v___f_1280_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_toMessageData___boxed(lean_object* v_alt_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_Match_Alt_toMessageData(v_alt_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(lean_object* v_as_1296_, lean_object* v_as_x27_1297_, lean_object* v_b_1298_, lean_object* v_a_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1297_, v_b_1298_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___boxed(lean_object* v_as_1306_, lean_object* v_as_x27_1307_, lean_object* v_b_1308_, lean_object* v_a_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1(v_as_1306_, v_as_x27_1307_, v_b_1308_, v_a_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_as_x27_1307_);
lean_dec(v_as_1306_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(lean_object* v_s_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
if (lean_obj_tag(v_a_1317_) == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_s_1316_);
v___x_1319_ = l_List_reverse___redArg(v_a_1318_);
return v___x_1319_;
}
else
{
lean_object* v_head_1320_; lean_object* v_tail_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1330_; 
v_head_1320_ = lean_ctor_get(v_a_1317_, 0);
v_tail_1321_ = lean_ctor_get(v_a_1317_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_a_1317_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1323_ = v_a_1317_;
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_tail_1321_);
lean_inc(v_head_1320_);
lean_dec(v_a_1317_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_inc(v_s_1316_);
v___x_1325_ = l_Lean_Meta_Match_Pattern_applyFVarSubst(v_s_1316_, v_head_1320_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v_a_1318_);
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_a_1318_);
v___x_1327_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
v_a_1317_ = v_tail_1321_;
v_a_1318_ = v___x_1327_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(lean_object* v_s_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
if (lean_obj_tag(v_a_1332_) == 0)
{
lean_object* v___x_1334_; 
lean_dec(v_s_1331_);
v___x_1334_ = l_List_reverse___redArg(v_a_1333_);
return v___x_1334_;
}
else
{
lean_object* v_head_1335_; lean_object* v_tail_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1345_; 
v_head_1335_ = lean_ctor_get(v_a_1332_, 0);
v_tail_1336_ = lean_ctor_get(v_a_1332_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_a_1332_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1338_ = v_a_1332_;
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_tail_1336_);
lean_inc(v_head_1335_);
lean_dec(v_a_1332_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_inc(v_s_1331_);
v___x_1340_ = l_Lean_LocalDecl_applyFVarSubst(v_s_1331_, v_head_1335_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_a_1333_);
lean_ctor_set(v___x_1338_, 0, v___x_1340_);
v___x_1342_ = v___x_1338_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_a_1333_);
v___x_1342_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
v_a_1332_ = v_tail_1336_;
v_a_1333_ = v___x_1342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(lean_object* v_s_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v___x_1349_; 
lean_dec(v_s_1346_);
v___x_1349_ = l_List_reverse___redArg(v_a_1348_);
return v___x_1349_;
}
else
{
lean_object* v_head_1350_; lean_object* v_tail_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1370_; 
v_head_1350_ = lean_ctor_get(v_a_1347_, 0);
v_tail_1351_ = lean_ctor_get(v_a_1347_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_a_1347_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1353_ = v_a_1347_;
v_isShared_1354_ = v_isSharedCheck_1370_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_tail_1351_);
lean_inc(v_head_1350_);
lean_dec(v_a_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1370_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1369_; 
v_fst_1355_ = lean_ctor_get(v_head_1350_, 0);
v_snd_1356_ = lean_ctor_get(v_head_1350_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_head_1350_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1358_ = v_head_1350_;
v_isShared_1359_ = v_isSharedCheck_1369_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_inc(v_fst_1355_);
lean_dec(v_head_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1369_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_inc_n(v_s_1346_, 2);
v___x_1360_ = l_Lean_Meta_FVarSubst_apply(v_s_1346_, v_fst_1355_);
lean_dec(v_fst_1355_);
v___x_1361_ = l_Lean_Meta_FVarSubst_apply(v_s_1346_, v_snd_1356_);
lean_dec(v_snd_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1361_);
lean_ctor_set(v___x_1358_, 0, v___x_1360_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_a_1348_);
lean_ctor_set(v___x_1353_, 0, v___x_1363_);
v___x_1365_ = v___x_1353_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1348_);
v___x_1365_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v_a_1347_ = v_tail_1351_;
v_a_1348_ = v___x_1365_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object* v_s_1371_, lean_object* v_alt_1372_){
_start:
{
lean_object* v_ref_1373_; lean_object* v_idx_1374_; lean_object* v_rhs_1375_; lean_object* v_fvarDecls_1376_; lean_object* v_patterns_1377_; lean_object* v_cnstrs_1378_; lean_object* v_notAltIdxs_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1391_; 
v_ref_1373_ = lean_ctor_get(v_alt_1372_, 0);
v_idx_1374_ = lean_ctor_get(v_alt_1372_, 1);
v_rhs_1375_ = lean_ctor_get(v_alt_1372_, 2);
v_fvarDecls_1376_ = lean_ctor_get(v_alt_1372_, 3);
v_patterns_1377_ = lean_ctor_get(v_alt_1372_, 4);
v_cnstrs_1378_ = lean_ctor_get(v_alt_1372_, 5);
v_notAltIdxs_1379_ = lean_ctor_get(v_alt_1372_, 6);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_alt_1372_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1381_ = v_alt_1372_;
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_notAltIdxs_1379_);
lean_inc(v_cnstrs_1378_);
lean_inc(v_patterns_1377_);
lean_inc(v_fvarDecls_1376_);
lean_inc(v_rhs_1375_);
lean_inc(v_idx_1374_);
lean_inc(v_ref_1373_);
lean_dec(v_alt_1372_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_inc_n(v_s_1371_, 3);
v___x_1383_ = l_Lean_Meta_FVarSubst_apply(v_s_1371_, v_rhs_1375_);
lean_dec_ref(v_rhs_1375_);
v___x_1384_ = lean_box(0);
v___x_1385_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__0(v_s_1371_, v_fvarDecls_1376_, v___x_1384_);
v___x_1386_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__1(v_s_1371_, v_patterns_1377_, v___x_1384_);
v___x_1387_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_applyFVarSubst_spec__2(v_s_1371_, v_cnstrs_1378_, v___x_1384_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 5, v___x_1387_);
lean_ctor_set(v___x_1381_, 4, v___x_1386_);
lean_ctor_set(v___x_1381_, 3, v___x_1385_);
lean_ctor_set(v___x_1381_, 2, v___x_1383_);
v___x_1389_ = v___x_1381_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_ref_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_idx_1374_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_notAltIdxs_1379_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(lean_object* v_fvarId_1392_, lean_object* v_v_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
if (lean_obj_tag(v_a_1394_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v_v_1393_);
lean_dec(v_fvarId_1392_);
v___x_1396_ = l_List_reverse___redArg(v_a_1395_);
return v___x_1396_;
}
else
{
lean_object* v_head_1397_; lean_object* v_tail_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1407_; 
v_head_1397_ = lean_ctor_get(v_a_1394_, 0);
v_tail_1398_ = lean_ctor_get(v_a_1394_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1394_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1400_ = v_a_1394_;
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_tail_1398_);
lean_inc(v_head_1397_);
lean_dec(v_a_1394_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_inc_ref(v_v_1393_);
lean_inc(v_fvarId_1392_);
v___x_1402_ = l_Lean_Meta_Match_Pattern_replaceFVarId(v_fvarId_1392_, v_v_1393_, v_head_1397_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_a_1395_);
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_a_1395_);
v___x_1404_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
v_a_1394_ = v_tail_1398_;
v_a_1395_ = v___x_1404_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(lean_object* v_fvarId_1408_, lean_object* v_v_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
if (lean_obj_tag(v_a_1410_) == 0)
{
lean_object* v___x_1412_; 
lean_dec(v_fvarId_1408_);
v___x_1412_ = l_List_reverse___redArg(v_a_1411_);
return v___x_1412_;
}
else
{
lean_object* v_head_1413_; lean_object* v_tail_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1423_; 
v_head_1413_ = lean_ctor_get(v_a_1410_, 0);
v_tail_1414_ = lean_ctor_get(v_a_1410_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_a_1410_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1416_ = v_a_1410_;
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_tail_1414_);
lean_inc(v_head_1413_);
lean_dec(v_a_1410_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_inc(v_fvarId_1408_);
v___x_1418_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_1408_, v_v_1409_, v_head_1413_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v_a_1411_);
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_a_1411_);
v___x_1420_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
v_a_1410_ = v_tail_1414_;
v_a_1411_ = v___x_1420_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_1424_, lean_object* v_v_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1424_, v_v_1425_, v_a_1426_, v_a_1427_);
lean_dec_ref(v_v_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(lean_object* v_fvarId_1429_, lean_object* v_v_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
if (lean_obj_tag(v_a_1431_) == 0)
{
lean_object* v___x_1433_; 
lean_dec(v_fvarId_1429_);
v___x_1433_ = l_List_reverse___redArg(v_a_1432_);
return v___x_1433_;
}
else
{
lean_object* v_head_1434_; lean_object* v_tail_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1454_; 
v_head_1434_ = lean_ctor_get(v_a_1431_, 0);
v_tail_1435_ = lean_ctor_get(v_a_1431_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1437_ = v_a_1431_;
v_isShared_1438_ = v_isSharedCheck_1454_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_tail_1435_);
lean_inc(v_head_1434_);
lean_dec(v_a_1431_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1454_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_fst_1439_; lean_object* v_snd_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1453_; 
v_fst_1439_ = lean_ctor_get(v_head_1434_, 0);
v_snd_1440_ = lean_ctor_get(v_head_1434_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_head_1434_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1442_ = v_head_1434_;
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snd_1440_);
lean_inc(v_fst_1439_);
lean_dec(v_head_1434_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_inc_n(v_fvarId_1429_, 2);
v___x_1444_ = l_Lean_Expr_replaceFVarId(v_fst_1439_, v_fvarId_1429_, v_v_1430_);
lean_dec(v_fst_1439_);
v___x_1445_ = l_Lean_Expr_replaceFVarId(v_snd_1440_, v_fvarId_1429_, v_v_1430_);
lean_dec(v_snd_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1445_);
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1447_ = v___x_1442_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_a_1432_);
lean_ctor_set(v___x_1437_, 0, v___x_1447_);
v___x_1449_ = v___x_1437_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_a_1432_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
v_a_1431_ = v_tail_1435_;
v_a_1432_ = v___x_1449_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3___boxed(lean_object* v_fvarId_1455_, lean_object* v_v_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1455_, v_v_1456_, v_a_1457_, v_a_1458_);
lean_dec_ref(v_v_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(lean_object* v_fvarId_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
if (lean_obj_tag(v_a_1461_) == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = l_List_reverse___redArg(v_a_1462_);
return v___x_1463_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1476_; 
v_head_1464_ = lean_ctor_get(v_a_1461_, 0);
v_tail_1465_ = lean_ctor_get(v_a_1461_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_a_1461_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1467_ = v_a_1461_;
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_head_1464_);
lean_dec(v_a_1461_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = l_Lean_LocalDecl_fvarId(v_head_1464_);
v___x_1470_ = l_Lean_instBEqFVarId_beq(v___x_1469_, v_fvarId_1460_);
lean_dec(v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1472_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v_a_1462_);
v___x_1472_ = v___x_1467_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_head_1464_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_a_1462_);
v___x_1472_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
v_a_1461_ = v_tail_1465_;
v_a_1462_ = v___x_1472_;
goto _start;
}
}
else
{
lean_del_object(v___x_1467_);
lean_dec(v_head_1464_);
v_a_1461_ = v_tail_1465_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_fvarId_1477_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object* v_fvarId_1481_, lean_object* v_v_1482_, lean_object* v_alt_1483_){
_start:
{
lean_object* v_ref_1484_; lean_object* v_idx_1485_; lean_object* v_rhs_1486_; lean_object* v_fvarDecls_1487_; lean_object* v_patterns_1488_; lean_object* v_cnstrs_1489_; lean_object* v_notAltIdxs_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1503_; 
v_ref_1484_ = lean_ctor_get(v_alt_1483_, 0);
v_idx_1485_ = lean_ctor_get(v_alt_1483_, 1);
v_rhs_1486_ = lean_ctor_get(v_alt_1483_, 2);
v_fvarDecls_1487_ = lean_ctor_get(v_alt_1483_, 3);
v_patterns_1488_ = lean_ctor_get(v_alt_1483_, 4);
v_cnstrs_1489_ = lean_ctor_get(v_alt_1483_, 5);
v_notAltIdxs_1490_ = lean_ctor_get(v_alt_1483_, 6);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_alt_1483_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1492_ = v_alt_1483_;
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_notAltIdxs_1490_);
lean_inc(v_cnstrs_1489_);
lean_inc(v_patterns_1488_);
lean_inc(v_fvarDecls_1487_);
lean_inc(v_rhs_1486_);
lean_inc(v_idx_1485_);
lean_inc(v_ref_1484_);
lean_dec(v_alt_1483_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_decls_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_inc_n(v_fvarId_1481_, 3);
v___x_1494_ = l_Lean_Expr_replaceFVarId(v_rhs_1486_, v_fvarId_1481_, v_v_1482_);
lean_dec_ref(v_rhs_1486_);
v___x_1495_ = lean_box(0);
v_decls_1496_ = l_List_filterTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__0(v_fvarId_1481_, v_fvarDecls_1487_, v___x_1495_);
v___x_1497_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__1(v_fvarId_1481_, v_v_1482_, v_decls_1496_, v___x_1495_);
lean_inc_ref(v_v_1482_);
v___x_1498_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__2(v_fvarId_1481_, v_v_1482_, v_patterns_1488_, v___x_1495_);
v___x_1499_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_replaceFVarId_spec__3(v_fvarId_1481_, v_v_1482_, v_cnstrs_1489_, v___x_1495_);
lean_dec_ref(v_v_1482_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 5, v___x_1499_);
lean_ctor_set(v___x_1492_, 4, v___x_1498_);
lean_ctor_set(v___x_1492_, 3, v___x_1497_);
lean_ctor_set(v___x_1492_, 2, v___x_1494_);
v___x_1501_ = v___x_1492_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_ref_1484_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_idx_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1502_, 5, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1502_, 6, v_notAltIdxs_1490_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(lean_object* v_fvarId_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = 0;
return v___x_1506_;
}
else
{
lean_object* v_head_1507_; lean_object* v_tail_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_head_1507_ = lean_ctor_get(v_x_1505_, 0);
v_tail_1508_ = lean_ctor_get(v_x_1505_, 1);
v___x_1509_ = l_Lean_LocalDecl_fvarId(v_head_1507_);
v___x_1510_ = l_Lean_instBEqFVarId_beq(v___x_1509_, v_fvarId_1504_);
lean_dec(v___x_1509_);
if (v___x_1510_ == 0)
{
v_x_1505_ = v_tail_1508_;
goto _start;
}
else
{
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0___boxed(lean_object* v_fvarId_1512_, lean_object* v_x_1513_){
_start:
{
uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_res_1514_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1512_, v_x_1513_);
lean_dec(v_x_1513_);
lean_dec(v_fvarId_1512_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object* v_fvarId_1516_, lean_object* v_alt_1517_){
_start:
{
lean_object* v_fvarDecls_1518_; uint8_t v___x_1519_; 
v_fvarDecls_1518_ = lean_ctor_get(v_alt_1517_, 3);
v___x_1519_ = l_List_any___at___00Lean_Meta_Match_Alt_isLocalDecl_spec__0(v_fvarId_1516_, v_fvarDecls_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object* v_fvarId_1520_, lean_object* v_alt_1521_){
_start:
{
uint8_t v_res_1522_; lean_object* v_r_1523_; 
v_res_1522_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_1520_, v_alt_1521_);
lean_dec_ref(v_alt_1521_);
lean_dec(v_fvarId_1520_);
v_r_1523_ = lean_box(v_res_1522_);
return v_r_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___impl(lean_object* v_x_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_obj_tag_nat(v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___impl___boxed(lean_object* v_x_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Meta_Match_Example_ctorIdx___impl(v_x_1526_);
lean_dec(v_x_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object* v_t_1528_, lean_object* v_k_1529_){
_start:
{
switch(lean_obj_tag(v_t_1528_))
{
case 1:
{
return v_k_1529_;
}
case 2:
{
lean_object* v_a_1530_; lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v_t_1528_, 0);
lean_inc(v_a_1530_);
v_a_1531_ = lean_ctor_get(v_t_1528_, 1);
lean_inc(v_a_1531_);
lean_dec_ref_known(v_t_1528_, 2);
v___x_1532_ = lean_apply_2(v_k_1529_, v_a_1530_, v_a_1531_);
return v___x_1532_;
}
case 3:
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v_t_1528_, 0);
lean_inc_ref(v_a_1533_);
lean_dec_ref_known(v_t_1528_, 1);
v___x_1534_ = lean_apply_1(v_k_1529_, v_a_1533_);
return v___x_1534_;
}
default: 
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v_t_1528_, 0);
lean_inc(v_a_1535_);
lean_dec(v_t_1528_);
v___x_1536_ = lean_apply_1(v_k_1529_, v_a_1535_);
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object* v_motive__1_1537_, lean_object* v_ctorIdx_1538_, lean_object* v_t_1539_, lean_object* v_h_1540_, lean_object* v_k_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1539_, v_k_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object* v_motive__1_1543_, lean_object* v_ctorIdx_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Meta_Match_Example_ctorElim(v_motive__1_1543_, v_ctorIdx_1544_, v_t_1545_, v_h_1546_, v_k_1547_);
lean_dec(v_ctorIdx_1544_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object* v_t_1549_, lean_object* v_var_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1549_, v_var_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object* v_motive__1_1552_, lean_object* v_t_1553_, lean_object* v_h_1554_, lean_object* v_var_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1553_, v_var_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object* v_t_1557_, lean_object* v_underscore_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1557_, v_underscore_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object* v_motive__1_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_underscore_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1561_, v_underscore_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object* v_t_1565_, lean_object* v_ctor_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1565_, v_ctor_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object* v_motive__1_1568_, lean_object* v_t_1569_, lean_object* v_h_1570_, lean_object* v_ctor_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1569_, v_ctor_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object* v_t_1573_, lean_object* v_val_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1573_, v_val_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object* v_motive__1_1576_, lean_object* v_t_1577_, lean_object* v_h_1578_, lean_object* v_val_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1577_, v_val_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object* v_t_1581_, lean_object* v_arrayLit_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1581_, v_arrayLit_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object* v_motive__1_1584_, lean_object* v_t_1585_, lean_object* v_h_1586_, lean_object* v_arrayLit_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1585_, v_arrayLit_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object* v_fvarId_1589_, lean_object* v_ex_1590_, lean_object* v_x_1591_){
_start:
{
switch(lean_obj_tag(v_x_1591_))
{
case 0:
{
lean_object* v_a_1592_; uint8_t v___x_1593_; 
v_a_1592_ = lean_ctor_get(v_x_1591_, 0);
v___x_1593_ = l_Lean_instBEqFVarId_beq(v_a_1592_, v_fvarId_1589_);
if (v___x_1593_ == 0)
{
return v_x_1591_;
}
else
{
lean_dec_ref_known(v_x_1591_, 1);
lean_inc(v_ex_1590_);
return v_ex_1590_;
}
}
case 2:
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1604_; 
v_a_1594_ = lean_ctor_get(v_x_1591_, 0);
v_a_1595_ = lean_ctor_get(v_x_1591_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1597_ = v_x_1591_;
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_inc(v_a_1594_);
lean_dec(v_x_1591_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1589_, v_ex_1590_, v_a_1595_, v___x_1599_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1594_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
case 4:
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1614_; 
v_a_1605_ = lean_ctor_get(v_x_1591_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1607_ = v_x_1591_;
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v_x_1591_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1589_, v_ex_1590_, v_a_1605_, v___x_1609_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
default: 
{
return v_x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object* v_fvarId_1615_, lean_object* v_ex_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
if (lean_obj_tag(v_a_1617_) == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = l_List_reverse___redArg(v_a_1618_);
return v___x_1619_;
}
else
{
lean_object* v_head_1620_; lean_object* v_tail_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1630_; 
v_head_1620_ = lean_ctor_get(v_a_1617_, 0);
v_tail_1621_ = lean_ctor_get(v_a_1617_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_a_1617_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1623_ = v_a_1617_;
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_tail_1621_);
lean_inc(v_head_1620_);
lean_dec(v_a_1617_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1615_, v_ex_1616_, v_head_1620_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 1, v_a_1618_);
lean_ctor_set(v___x_1623_, 0, v___x_1625_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_a_1618_);
v___x_1627_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
v_a_1617_ = v_tail_1621_;
v_a_1618_ = v___x_1627_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1631_, lean_object* v_ex_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1631_, v_ex_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_ex_1632_);
lean_dec(v_fvarId_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object* v_fvarId_1636_, lean_object* v_ex_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1636_, v_ex_1637_, v_x_1638_);
lean_dec(v_ex_1637_);
lean_dec(v_fvarId_1636_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object* v_s_1640_, lean_object* v_x_1641_){
_start:
{
switch(lean_obj_tag(v_x_1641_))
{
case 0:
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1652_; 
v_a_1642_ = lean_ctor_get(v_x_1641_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1641_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1644_ = v_x_1641_;
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v_x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_FVarSubst_get(v_s_1640_, v_a_1642_);
if (lean_obj_tag(v___x_1646_) == 1)
{
lean_object* v_fvarId_1647_; lean_object* v___x_1649_; 
v_fvarId_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_fvarId_1647_);
lean_dec_ref_known(v___x_1646_, 1);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_fvarId_1647_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_fvarId_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
else
{
lean_object* v___x_1651_; 
lean_dec_ref(v___x_1646_);
lean_del_object(v___x_1644_);
v___x_1651_ = lean_box(1);
return v___x_1651_;
}
}
}
case 2:
{
lean_object* v_a_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1663_; 
v_a_1653_ = lean_ctor_get(v_x_1641_, 0);
v_a_1654_ = lean_ctor_get(v_x_1641_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_x_1641_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1656_ = v_x_1641_;
v_isShared_1657_ = v_isSharedCheck_1663_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_inc(v_a_1653_);
lean_dec(v_x_1641_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1663_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1640_, v_a_1654_, v___x_1658_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 1, v___x_1659_);
v___x_1661_ = v___x_1656_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1653_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
case 4:
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v_a_1664_ = lean_ctor_get(v_x_1641_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1641_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1666_ = v_x_1641_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v_x_1641_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_box(0);
v___x_1669_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1640_, v_a_1664_, v___x_1668_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
default: 
{
return v_x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object* v_s_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
if (lean_obj_tag(v_a_1675_) == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = l_List_reverse___redArg(v_a_1676_);
return v___x_1677_;
}
else
{
lean_object* v_head_1678_; lean_object* v_tail_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1688_; 
v_head_1678_ = lean_ctor_get(v_a_1675_, 0);
v_tail_1679_ = lean_ctor_get(v_a_1675_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_a_1675_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1681_ = v_a_1675_;
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_tail_1679_);
lean_inc(v_head_1678_);
lean_dec(v_a_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1674_, v_head_1678_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_a_1676_);
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1676_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v_a_1675_ = v_tail_1679_;
v_a_1676_ = v___x_1685_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object* v_s_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_s_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object* v_s_1693_, lean_object* v_x_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1693_, v_x_1694_);
lean_dec(v_s_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object* v_x_1696_){
_start:
{
switch(lean_obj_tag(v_x_1696_))
{
case 0:
{
lean_object* v___x_1697_; 
lean_dec_ref_known(v_x_1696_, 1);
v___x_1697_ = lean_box(1);
return v___x_1697_;
}
case 2:
{
lean_object* v_a_1698_; lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
v_a_1698_ = lean_ctor_get(v_x_1696_, 0);
v_a_1699_ = lean_ctor_get(v_x_1696_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v_x_1696_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_inc(v_a_1698_);
lean_dec(v_x_1696_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1699_, v___x_1703_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1698_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
case 4:
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1718_; 
v_a_1709_ = lean_ctor_get(v_x_1696_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1711_ = v_x_1696_;
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v_x_1696_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1709_, v___x_1713_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
default: 
{
return v_x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
if (lean_obj_tag(v_a_1719_) == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = l_List_reverse___redArg(v_a_1720_);
return v___x_1721_;
}
else
{
lean_object* v_head_1722_; lean_object* v_tail_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
v_head_1722_ = lean_ctor_get(v_a_1719_, 0);
v_tail_1723_ = lean_ctor_get(v_a_1719_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_a_1719_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1725_ = v_a_1719_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_tail_1723_);
lean_inc(v_head_1722_);
lean_dec(v_a_1719_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1722_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_a_1720_);
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_a_1720_);
v___x_1729_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v_a_1719_ = v_tail_1723_;
v_a_1720_ = v___x_1729_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__1));
v___x_1737_ = l_Lean_MessageData_ofFormat(v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0));
v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
if (lean_obj_tag(v_x_1741_) == 0)
{
return v_x_1740_;
}
else
{
lean_object* v_head_1742_; lean_object* v_tail_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1754_; 
v_head_1742_ = lean_ctor_get(v_x_1741_, 0);
v_tail_1743_ = lean_ctor_get(v_x_1741_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_x_1741_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1745_ = v_x_1741_;
v_isShared_1746_ = v_isSharedCheck_1754_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_tail_1743_);
lean_inc(v_head_1742_);
lean_dec(v_x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1754_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0, &l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once, _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 7);
lean_ctor_set(v___x_1745_, 1, v___x_1747_);
lean_ctor_set(v___x_1745_, 0, v_x_1740_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_x_1740_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1742_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v_x_1740_ = v___x_1751_;
v_x_1741_ = v_tail_1743_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__4));
v___x_1759_ = l_Lean_MessageData_ofFormat(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object* v_x_1760_){
_start:
{
switch(lean_obj_tag(v_x_1760_))
{
case 0:
{
lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_a_1761_ = lean_ctor_get(v_x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v_x_1760_, 1);
v___x_1762_ = l_Lean_mkFVar(v_a_1761_);
v___x_1763_ = l_Lean_MessageData_ofExpr(v___x_1762_);
return v___x_1763_;
}
case 1:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__2, &l_Lean_Meta_Match_Example_toMessageData___closed__2_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__2);
return v___x_1764_;
}
case 2:
{
lean_object* v_a_1765_; 
v_a_1765_ = lean_ctor_get(v_x_1760_, 1);
if (lean_obj_tag(v_a_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1766_ = lean_ctor_get(v_x_1760_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v_x_1760_, 2);
v___x_1767_ = lean_box(0);
v___x_1768_ = l_Lean_mkConst(v_a_1766_, v___x_1767_);
v___x_1769_ = l_Lean_MessageData_ofExpr(v___x_1768_);
return v___x_1769_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1785_; 
lean_inc(v_a_1765_);
v_a_1770_ = lean_ctor_get(v_x_1760_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_x_1760_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_x_1760_, 1);
lean_dec(v_unused_1786_);
v___x_1772_ = v_x_1760_;
v_isShared_1773_ = v_isSharedCheck_1785_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v_x_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1785_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1774_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_1775_ = 0;
v___x_1776_ = l_Lean_MessageData_ofConstName(v_a_1770_, v___x_1775_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 7);
lean_ctor_set(v___x_1772_, 1, v___x_1776_);
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1778_ = v___x_1772_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1779_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_1780_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(v___x_1779_, v_a_1765_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1778_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
return v___x_1783_;
}
}
}
}
case 3:
{
lean_object* v_a_1787_; lean_object* v___x_1788_; 
v_a_1787_ = lean_ctor_get(v_x_1760_, 0);
lean_inc_ref(v_a_1787_);
lean_dec_ref_known(v_x_1760_, 1);
v___x_1788_ = l_Lean_MessageData_ofExpr(v_a_1787_);
return v___x_1788_;
}
default: 
{
lean_object* v_a_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_a_1789_ = lean_ctor_get(v_x_1760_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v_x_1760_, 1);
v___x_1790_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__5, &l_Lean_Meta_Match_Example_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__5);
v___x_1791_ = lean_box(0);
v___x_1792_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_1789_, v___x_1791_);
v___x_1793_ = l_Lean_MessageData_ofList(v___x_1792_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1790_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
if (lean_obj_tag(v_a_1795_) == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = l_List_reverse___redArg(v_a_1796_);
return v___x_1797_;
}
else
{
lean_object* v_head_1798_; lean_object* v_tail_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1808_; 
v_head_1798_ = lean_ctor_get(v_a_1795_, 0);
v_tail_1799_ = lean_ctor_get(v_a_1795_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1801_ = v_a_1795_;
v_isShared_1802_ = v_isSharedCheck_1808_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_tail_1799_);
lean_inc(v_head_1798_);
lean_dec(v_a_1795_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1808_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1798_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_a_1796_);
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_a_1796_);
v___x_1805_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
v_a_1795_ = v_tail_1799_;
v_a_1796_ = v___x_1805_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
if (lean_obj_tag(v_a_1809_) == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = l_List_reverse___redArg(v_a_1810_);
return v___x_1811_;
}
else
{
lean_object* v_head_1812_; lean_object* v_tail_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_head_1812_ = lean_ctor_get(v_a_1809_, 0);
v_tail_1813_ = lean_ctor_get(v_a_1809_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1809_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v_a_1809_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_tail_1813_);
lean_inc(v_head_1812_);
lean_dec(v_a_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1817_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1812_);
v___x_1818_ = l_Lean_Meta_Match_Example_toMessageData(v___x_1817_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v_a_1810_);
lean_ctor_set(v___x_1815_, 0, v___x_1818_);
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_a_1810_);
v___x_1820_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
v_a_1809_ = v_tail_1813_;
v_a_1810_ = v___x_1820_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object* v_cex_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(v_cex_1824_, v___x_1825_);
v___x_1827_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_1828_ = l_Lean_MessageData_joinSep(v___x_1826_, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object* v_mvarId_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1834_, v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1841_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1841_);
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
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object* v_mvarId_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1858_, v_x_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object* v_00_u03b1_1866_, lean_object* v_mvarId_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1867_, v_x_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_mvarId_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(v_00_u03b1_1875_, v_mvarId_1876_, v_x_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object* v_p_1884_, lean_object* v_x_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_mvarId_1891_; lean_object* v___x_1892_; 
v_mvarId_1891_ = lean_ctor_get(v_p_1884_, 0);
lean_inc(v_mvarId_1891_);
lean_dec_ref(v_p_1884_);
v___x_1892_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1891_, v_x_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object* v_p_1893_, lean_object* v_x_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1893_, v_x_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* v_00_u03b1_1901_, lean_object* v_p_1902_, lean_object* v_x_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1902_, v_x_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object* v_00_u03b1_1910_, lean_object* v_p_1911_, lean_object* v_x_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Meta_Match_withGoalOf(v_00_u03b1_1910_, v_p_1911_, v_x_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = l_List_reverse___redArg(v_x_1920_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v_head_1928_; lean_object* v_tail_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1947_; 
v_head_1928_ = lean_ctor_get(v_x_1919_, 0);
v_tail_1929_ = lean_ctor_get(v_x_1919_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1931_ = v_x_1919_;
v_isShared_1932_ = v_isSharedCheck_1947_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_tail_1929_);
lean_inc(v_head_1928_);
lean_dec(v_x_1919_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1947_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_Meta_Match_Alt_toMessageData(v_head_1928_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v_x_1920_);
lean_ctor_set(v___x_1931_, 0, v_a_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_x_1920_);
v___x_1936_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v_x_1919_ = v_tail_1929_;
v_x_1920_ = v___x_1936_;
goto _start;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_del_object(v___x_1931_);
lean_dec(v_tail_1929_);
lean_dec(v_x_1920_);
v_a_1939_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1933_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1933_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_x_1948_, v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
if (lean_obj_tag(v_x_1956_) == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = l_List_reverse___redArg(v_x_1957_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
else
{
lean_object* v_head_1965_; lean_object* v_tail_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1991_; 
v_head_1965_ = lean_ctor_get(v_x_1956_, 0);
v_tail_1966_ = lean_ctor_get(v_x_1956_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1968_ = v_x_1956_;
v_isShared_1969_ = v_isSharedCheck_1991_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_tail_1966_);
lean_inc(v_head_1965_);
lean_dec(v_x_1956_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1991_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; 
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v_head_1965_);
v___x_1970_ = lean_infer_type(v_head_1965_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l_Lean_MessageData_ofExpr(v_head_1965_);
v___x_1973_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_MessageData_ofExpr(v_a_1971_);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v_x_1957_);
lean_ctor_set(v___x_1968_, 0, v___x_1978_);
v___x_1980_ = v___x_1968_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_x_1957_);
v___x_1980_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v_x_1956_ = v_tail_1966_;
v_x_1957_ = v___x_1980_;
goto _start;
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_del_object(v___x_1968_);
lean_dec(v_tail_1966_);
lean_dec(v_head_1965_);
lean_dec(v_x_1957_);
v_a_1983_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1970_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1970_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_x_1992_, v_x_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1999_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2));
v___x_2005_ = l_Lean_stringToMessageData(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_box(1);
v___x_2007_ = l_Lean_MessageData_ofFormat(v___x_2006_);
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object* v_alts_2011_, lean_object* v___x_2012_, lean_object* v_vars_2013_, lean_object* v_examples_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
lean_inc(v___x_2012_);
v___x_2020_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_alts_2011_, v___x_2012_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
lean_inc(v___x_2012_);
v___x_2022_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_vars_2013_, v___x_2012_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2046_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2046_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2046_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2027_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1);
v___x_2028_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v_a_2023_, v___x_2012_);
v___x_2029_ = l_Lean_MessageData_ofList(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2034_ = l_Lean_MessageData_joinSep(v_a_2021_, v___x_2033_);
v___x_2035_ = l_Lean_indentD(v___x_2034_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2032_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_2014_);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2042_);
v___x_2044_ = v___x_2025_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_2021_);
lean_dec(v_examples_2014_);
lean_dec(v___x_2012_);
v_a_2047_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2022_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2022_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_examples_2014_);
lean_dec(v_vars_2013_);
lean_dec(v___x_2012_);
v_a_2055_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2020_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2020_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object* v_alts_2063_, lean_object* v___x_2064_, lean_object* v_vars_2065_, lean_object* v_examples_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(v_alts_2063_, v___x_2064_, v_vars_2065_, v_examples_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* v_p_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v_vars_2079_; lean_object* v_alts_2080_; lean_object* v_examples_2081_; lean_object* v___x_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; 
v_vars_2079_ = lean_ctor_get(v_p_2073_, 1);
v_alts_2080_ = lean_ctor_get(v_p_2073_, 2);
v_examples_2081_ = lean_ctor_get(v_p_2073_, 3);
v___x_2082_ = lean_box(0);
lean_inc(v_examples_2081_);
lean_inc(v_vars_2079_);
lean_inc(v_alts_2080_);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2083_, 0, v_alts_2080_);
lean_closure_set(v___f_2083_, 1, v___x_2082_);
lean_closure_set(v___f_2083_, 2, v_vars_2079_);
lean_closure_set(v___f_2083_, 3, v_examples_2081_);
v___x_2084_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_2073_, v___f_2083_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object* v_p_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Meta_Match_Problem_toMessageData(v_p_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object* v_cex_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
if (lean_obj_tag(v_a_2094_) == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l_List_reverse___redArg(v_a_2095_);
return v___x_2096_;
}
else
{
lean_object* v_head_2097_; lean_object* v_tail_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2107_; 
v_head_2097_ = lean_ctor_get(v_a_2094_, 0);
v_tail_2098_ = lean_ctor_get(v_a_2094_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_a_2094_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2100_ = v_a_2094_;
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_tail_2098_);
lean_inc(v_head_2097_);
lean_dec(v_a_2094_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = l_Lean_Meta_Match_examplesToMessageData(v_head_2097_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v_a_2095_);
lean_ctor_set(v___x_2100_, 0, v___x_2102_);
v___x_2104_ = v___x_2100_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_a_2095_);
v___x_2104_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v_a_2094_ = v_tail_2098_;
v_a_2095_ = v___x_2104_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object* v_cexs_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2109_ = lean_array_to_list(v_cexs_2108_);
v___x_2110_ = lean_box(0);
v___x_2111_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(v___x_2109_, v___x_2110_);
v___x_2112_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2113_ = l_Lean_MessageData_joinSep(v___x_2111_, v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object* v_msg_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_ref_2120_; lean_object* v___x_2121_; lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_ref_2120_ = lean_ctor_get(v___y_2117_, 2);
v___x_2121_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msg_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_inc(v_ref_2120_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_ref_2120_);
lean_ctor_set(v___x_2126_, 1, v_a_2122_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 1);
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object* v_msg_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2137_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__0));
v___x_2140_ = l_Lean_stringToMessageData(v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__2));
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4(void){
_start:
{
lean_object* v___x_2144_; lean_object* v_dummy_2145_; 
v___x_2144_ = lean_box(0);
v_dummy_2145_ = l_Lean_Expr_sort___override(v___x_2144_);
return v_dummy_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t v_sz_2146_, size_t v_i_2147_, lean_object* v_bs_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_usize_dec_lt(v_i_2147_, v_sz_2146_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_bs_2148_);
return v___x_2155_;
}
else
{
lean_object* v_v_2156_; lean_object* v___x_2157_; lean_object* v_bs_x27_2158_; lean_object* v___x_2159_; 
v_v_2156_ = lean_array_uget(v_bs_2148_, v_i_2147_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v_bs_x27_2158_ = lean_array_uset(v_bs_2148_, v_i_2147_, v___x_2157_);
v___x_2159_ = l_Lean_Meta_Match_toPattern(v_v_2156_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; size_t v___x_2161_; size_t v___x_2162_; lean_object* v___x_2163_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = ((size_t)1ULL);
v___x_2162_ = lean_usize_add(v_i_2147_, v___x_2161_);
v___x_2163_ = lean_array_uset(v_bs_x27_2158_, v_i_2147_, v_a_2160_);
v_i_2147_ = v___x_2162_;
v_bs_2148_ = v___x_2163_;
goto _start;
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_bs_x27_2158_);
v_a_2165_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2159_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2159_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object* v_e_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_inaccessible_x3f(v_e_2173_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Expr_arrayLit_x3f(v_e_2173_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_2173_);
if (lean_obj_tag(v___x_2197_) == 1)
{
lean_object* v_val_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref(v_e_2173_);
v_val_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v___x_2199_ = lean_unsigned_to_nat(2u);
v___x_2200_ = l_Lean_Expr_getAppNumArgs(v_val_2198_);
v___x_2201_ = lean_nat_sub(v___x_2200_, v___x_2199_);
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_sub(v___x_2201_, v___x_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = l_Lean_Expr_getRevArg_x21(v_val_2198_, v___x_2203_);
v___x_2205_ = l_Lean_Meta_Match_toPattern(v___x_2204_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2223_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2223_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2223_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_nat_sub(v___x_2200_, v___x_2202_);
v___x_2211_ = lean_nat_sub(v___x_2210_, v___x_2202_);
lean_dec(v___x_2210_);
v___x_2212_ = l_Lean_Expr_getRevArg_x21(v_val_2198_, v___x_2211_);
if (lean_obj_tag(v___x_2212_) == 1)
{
lean_object* v_fvarId_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_fvarId_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_fvarId_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = lean_unsigned_to_nat(3u);
v___x_2215_ = lean_nat_sub(v___x_2200_, v___x_2214_);
lean_dec(v___x_2200_);
v___x_2216_ = lean_nat_sub(v___x_2215_, v___x_2202_);
lean_dec(v___x_2215_);
v___x_2217_ = l_Lean_Expr_getRevArg_x21(v_val_2198_, v___x_2216_);
lean_dec(v_val_2198_);
if (lean_obj_tag(v___x_2217_) == 1)
{
lean_object* v_fvarId_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v_fvarId_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_fvarId_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_2219_, 0, v_fvarId_2213_);
lean_ctor_set(v___x_2219_, 1, v_a_2206_);
lean_ctor_set(v___x_2219_, 2, v_fvarId_2218_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2219_);
v___x_2221_ = v___x_2208_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
else
{
lean_dec_ref(v___x_2217_);
lean_dec(v_fvarId_2213_);
lean_del_object(v___x_2208_);
lean_dec(v_a_2206_);
v___y_2189_ = v_a_2174_;
v___y_2190_ = v_a_2175_;
v___y_2191_ = v_a_2176_;
v___y_2192_ = v_a_2177_;
goto v___jp_2188_;
}
}
else
{
lean_dec_ref(v___x_2212_);
lean_del_object(v___x_2208_);
lean_dec(v_a_2206_);
lean_dec(v___x_2200_);
lean_dec(v_val_2198_);
v___y_2189_ = v_a_2174_;
v___y_2190_ = v_a_2175_;
v___y_2191_ = v_a_2176_;
v___y_2192_ = v_a_2177_;
goto v___jp_2188_;
}
}
}
else
{
lean_dec(v___x_2200_);
lean_dec(v_val_2198_);
return v___x_2205_;
}
}
else
{
lean_object* v___x_2224_; 
lean_dec(v___x_2197_);
lean_inc_ref(v_e_2173_);
v___x_2224_ = l_Lean_Meta_isMatchValue(v_e_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2317_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2317_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2317_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
uint8_t v___x_2229_; 
v___x_2229_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
if (v___x_2229_ == 0)
{
uint8_t v___x_2230_; 
v___x_2230_ = l_Lean_Expr_isFVar(v_e_2173_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_del_object(v___x_2227_);
lean_inc(v_a_2177_);
lean_inc_ref(v_a_2176_);
lean_inc(v_a_2175_);
lean_inc_ref(v_a_2174_);
lean_inc_ref(v_e_2173_);
v___x_2231_ = lean_whnf(v_e_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; uint8_t v___x_2233_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = lean_expr_eqv(v_a_2232_, v_e_2173_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v_e_2173_);
v_e_2173_ = v_a_2232_;
goto _start;
}
else
{
if (v___x_2230_ == 0)
{
lean_object* v___x_2235_; 
lean_dec(v_a_2232_);
v___x_2235_ = l_Lean_Expr_getAppFn(v_e_2173_);
if (lean_obj_tag(v___x_2235_) == 4)
{
lean_object* v_declName_2236_; lean_object* v_us_2237_; lean_object* v___x_2238_; lean_object* v_env_2239_; lean_object* v___x_2240_; 
v_declName_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_declName_2236_);
v_us_2237_ = lean_ctor_get(v___x_2235_, 1);
lean_inc(v_us_2237_);
lean_dec_ref_known(v___x_2235_, 2);
v___x_2238_ = lean_st_ref_get(v_a_2177_);
v_env_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_ref(v_env_2239_);
lean_dec(v___x_2238_);
v___x_2240_ = l_Lean_Environment_find_x3f(v_env_2239_, v_declName_2236_, v___x_2230_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_dec(v_us_2237_);
v___y_2180_ = v_a_2174_;
v___y_2181_ = v_a_2175_;
v___y_2182_ = v_a_2176_;
v___y_2183_ = v_a_2177_;
goto v___jp_2179_;
}
else
{
lean_object* v_val_2241_; 
v_val_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v___x_2240_, 1);
if (lean_obj_tag(v_val_2241_) == 6)
{
lean_object* v_val_2242_; lean_object* v_toConstantVal_2243_; lean_object* v_numParams_2244_; lean_object* v_numFields_2245_; lean_object* v_nargs_2246_; lean_object* v_dummy_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_val_2242_ = lean_ctor_get(v_val_2241_, 0);
lean_inc_ref(v_val_2242_);
lean_dec_ref_known(v_val_2241_, 1);
v_toConstantVal_2243_ = lean_ctor_get(v_val_2242_, 0);
lean_inc_ref(v_toConstantVal_2243_);
v_numParams_2244_ = lean_ctor_get(v_val_2242_, 3);
lean_inc(v_numParams_2244_);
v_numFields_2245_ = lean_ctor_get(v_val_2242_, 4);
lean_inc(v_numFields_2245_);
lean_dec_ref(v_val_2242_);
v_nargs_2246_ = l_Lean_Expr_getAppNumArgs(v_e_2173_);
v_dummy_2247_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__4, &l_Lean_Meta_Match_toPattern___closed__4_once, _init_l_Lean_Meta_Match_toPattern___closed__4);
lean_inc(v_nargs_2246_);
v___x_2248_ = lean_mk_array(v_nargs_2246_, v_dummy_2247_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_sub(v_nargs_2246_, v___x_2249_);
lean_dec(v_nargs_2246_);
lean_inc_ref(v_e_2173_);
v___x_2251_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2173_, v___x_2248_, v___x_2250_);
v___x_2284_ = lean_array_get_size(v___x_2251_);
v___x_2285_ = lean_nat_add(v_numParams_2244_, v_numFields_2245_);
lean_dec(v_numFields_2245_);
v___x_2286_ = lean_nat_dec_eq(v___x_2284_, v___x_2285_);
lean_dec(v___x_2285_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2287_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2288_ = l_Lean_indentExpr(v_e_2173_);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2289_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_dec_ref_known(v___x_2290_, 1);
v___y_2253_ = v_a_2174_;
v___y_2254_ = v_a_2175_;
v___y_2255_ = v_a_2176_;
v___y_2256_ = v_a_2177_;
goto v___jp_2252_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v___x_2251_);
lean_dec(v_numParams_2244_);
lean_dec_ref(v_toConstantVal_2243_);
lean_dec(v_us_2237_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_dec_ref(v_e_2173_);
v___y_2253_ = v_a_2174_;
v___y_2254_ = v_a_2175_;
v___y_2255_ = v_a_2176_;
v___y_2256_ = v_a_2177_;
goto v___jp_2252_;
}
v___jp_2252_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; size_t v_sz_2261_; size_t v___x_2262_; lean_object* v___x_2263_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2244_);
v___x_2258_ = l_Array_extract___redArg(v___x_2251_, v___x_2257_, v_numParams_2244_);
v___x_2259_ = lean_array_get_size(v___x_2251_);
v___x_2260_ = l_Array_extract___redArg(v___x_2251_, v_numParams_2244_, v___x_2259_);
lean_dec_ref(v___x_2251_);
v_sz_2261_ = lean_array_size(v___x_2260_);
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_2261_, v___x_2262_, v___x_2260_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2275_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_name_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v_name_2268_ = lean_ctor_get(v_toConstantVal_2243_, 0);
lean_inc(v_name_2268_);
lean_dec_ref(v_toConstantVal_2243_);
v___x_2269_ = lean_array_to_list(v___x_2258_);
v___x_2270_ = lean_array_to_list(v_a_2264_);
v___x_2271_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2271_, 0, v_name_2268_);
lean_ctor_set(v___x_2271_, 1, v_us_2237_);
lean_ctor_set(v___x_2271_, 2, v___x_2269_);
lean_ctor_set(v___x_2271_, 3, v___x_2270_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2271_);
v___x_2273_ = v___x_2266_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v___x_2258_);
lean_dec_ref(v_toConstantVal_2243_);
lean_dec(v_us_2237_);
v_a_2276_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2263_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2263_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_dec(v_val_2241_);
lean_dec(v_us_2237_);
v___y_2180_ = v_a_2174_;
v___y_2181_ = v_a_2175_;
v___y_2182_ = v_a_2176_;
v___y_2183_ = v_a_2177_;
goto v___jp_2179_;
}
}
}
else
{
lean_dec_ref(v___x_2235_);
v___y_2180_ = v_a_2174_;
v___y_2181_ = v_a_2175_;
v___y_2182_ = v_a_2176_;
v___y_2183_ = v_a_2177_;
goto v___jp_2179_;
}
}
else
{
lean_dec_ref(v_e_2173_);
v_e_2173_ = v_a_2232_;
goto _start;
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v_e_2173_);
v_a_2300_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2231_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2231_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2308_ = l_Lean_Expr_fvarId_x21(v_e_2173_);
lean_dec_ref(v_e_2173_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2309_);
v___x_2311_ = v___x_2227_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_e_2173_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2313_);
v___x_2315_ = v___x_2227_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_e_2173_);
v_a_2318_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2224_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2224_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
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
}
else
{
lean_object* v_val_2326_; lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v_e_2173_);
v_val_2326_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2326_);
lean_dec_ref_known(v___x_2196_, 1);
v_fst_2327_ = lean_ctor_get(v_val_2326_, 0);
v_snd_2328_ = lean_ctor_get(v_val_2326_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_val_2326_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2330_ = v_val_2326_;
v_isShared_2331_ = v_isSharedCheck_2353_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_inc(v_fst_2327_);
lean_dec(v_val_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2353_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_box(0);
v___x_2333_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_snd_2328_, v___x_2332_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2344_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2344_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2344_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 4);
lean_ctor_set(v___x_2330_, 1, v_a_2334_);
v___x_2339_ = v___x_2330_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_fst_2327_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2339_);
v___x_2341_ = v___x_2336_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_del_object(v___x_2330_);
lean_dec(v_fst_2327_);
v_a_2345_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2333_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2333_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_e_2173_);
v_val_2354_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2356_ = v___x_2195_;
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_val_2354_);
lean_dec(v___x_2195_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 0);
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_val_2354_);
v___x_2359_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
}
v___jp_2179_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2185_ = l_Lean_indentExpr(v_e_2173_);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2186_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2187_;
}
v___jp_2188_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__3, &l_Lean_Meta_Match_toPattern___closed__3_once, _init_l_Lean_Meta_Match_toPattern___closed__3);
v___x_2194_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2193_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
if (lean_obj_tag(v_x_2363_) == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_List_reverse___redArg(v_x_2364_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
return v___x_2371_;
}
else
{
lean_object* v_head_2372_; lean_object* v_tail_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2391_; 
v_head_2372_ = lean_ctor_get(v_x_2363_, 0);
v_tail_2373_ = lean_ctor_get(v_x_2363_, 1);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_x_2363_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2375_ = v_x_2363_;
v_isShared_2376_ = v_isSharedCheck_2391_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_tail_2373_);
lean_inc(v_head_2372_);
lean_dec(v_x_2363_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2391_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_Meta_Match_toPattern(v_head_2372_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 1, v_x_2364_);
lean_ctor_set(v___x_2375_, 0, v_a_2378_);
v___x_2380_ = v___x_2375_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2378_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_x_2364_);
v___x_2380_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
v_x_2363_ = v_tail_2373_;
v_x_2364_ = v___x_2380_;
goto _start;
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_del_object(v___x_2375_);
lean_dec(v_tail_2373_);
lean_dec(v_x_2364_);
v_a_2383_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2377_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2377_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_x_2392_, v_x_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object* v_sz_2400_, lean_object* v_i_2401_, lean_object* v_bs_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
size_t v_sz_boxed_2408_; size_t v_i_boxed_2409_; lean_object* v_res_2410_; 
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2400_);
lean_dec(v_sz_2400_);
v_i_boxed_2409_ = lean_unbox_usize(v_i_2401_);
lean_dec(v_i_2401_);
v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_2408_, v_i_boxed_2409_, v_bs_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object* v_e_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_Meta_Match_toPattern(v_e_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object* v_00_u03b1_2418_, lean_object* v_msg_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(v_00_u03b1_2426_, v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(lean_object* v_s_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2441_ = lean_string_utf8_byte_size(v_s_2440_);
v___x_2442_ = lean_unsigned_to_nat(9u);
v___x_2443_ = lean_nat_dec_le(v___x_2442_, v___x_2441_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
lean_dec_ref(v_s_2440_);
v___x_2444_ = lean_box(0);
return v___x_2444_;
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2445_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2446_ = lean_unsigned_to_nat(0u);
v___x_2447_ = lean_string_memcmp(v_s_2440_, v___x_2445_, v___x_2446_, v___x_2446_, v___x_2442_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v_s_2440_);
v___x_2448_ = lean_box(0);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_inc_ref(v_s_2440_);
v___x_2449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2449_, 0, v_s_2440_);
lean_ctor_set(v___x_2449_, 1, v___x_2446_);
lean_ctor_set(v___x_2449_, 2, v___x_2441_);
v___x_2450_ = l_String_Slice_pos_x21(v___x_2449_, v___x_2442_);
lean_dec_ref_known(v___x_2449_, 3);
v___x_2451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2451_, 0, v_s_2440_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
lean_ctor_set(v___x_2451_, 2, v___x_2441_);
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(lean_object* v_s_2453_, lean_object* v_pat_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___boxed(lean_object* v_s_2456_, lean_object* v_pat_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0(v_s_2456_, v_pat_2457_);
lean_dec_ref(v_pat_2457_);
return v_res_2458_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object* v_s_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_String_dropPrefix_x3f___at___00Lean_Meta_Match_isCongrEqnReservedNameSuffix_spec__0___redArg(v_s_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
uint8_t v___x_2461_; 
v___x_2461_ = 0;
return v___x_2461_;
}
else
{
lean_object* v_val_2462_; uint8_t v___x_2463_; 
v_val_2462_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2463_ = l_String_Slice_isNat(v_val_2462_);
lean_dec(v_val_2462_);
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object* v_s_2464_){
_start:
{
uint8_t v_res_2465_; lean_object* v_r_2466_; 
v_res_2465_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_2464_);
v_r_2466_ = lean_box(v_res_2465_);
return v_r_2466_;
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
