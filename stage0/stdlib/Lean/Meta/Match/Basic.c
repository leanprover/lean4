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
lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Match_Pattern_hasExprMVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hasExprMVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Pattern_hasExprMVar___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Pattern_hasExprMVar(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_hasExprMVar___boxed(lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Lean_Meta_Match_Pattern_hasExprMVar(v_x_469_);
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
lean_inc_ref(v_e_473_);
lean_dec_ref(v_x_472_);
v___x_474_ = l_Lean_Expr_hasExprMVar(v_e_473_);
lean_dec_ref(v_e_473_);
return v___x_474_;
}
case 2:
{
lean_object* v_params_475_; lean_object* v_fields_476_; lean_object* v___f_477_; uint8_t v___x_478_; 
v_params_475_ = lean_ctor_get(v_x_472_, 2);
lean_inc(v_params_475_);
v_fields_476_ = lean_ctor_get(v_x_472_, 3);
lean_inc(v_fields_476_);
lean_dec_ref(v_x_472_);
v___f_477_ = ((lean_object*)(l_Lean_Meta_Match_Pattern_hasExprMVar___closed__0));
v___x_478_ = l_List_any___redArg(v_params_475_, v___f_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Pattern_hasExprMVar___boxed), 1, 0);
v___x_480_ = l_List_any___redArg(v_fields_476_, v___x_479_);
return v___x_480_;
}
else
{
lean_dec(v_fields_476_);
return v___x_478_;
}
}
case 3:
{
lean_object* v_e_481_; uint8_t v___x_482_; 
v_e_481_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_e_481_);
lean_dec_ref(v_x_472_);
v___x_482_ = l_Lean_Expr_hasExprMVar(v_e_481_);
lean_dec_ref(v_e_481_);
return v___x_482_;
}
case 5:
{
lean_object* v_p_483_; 
v_p_483_ = lean_ctor_get(v_x_472_, 1);
lean_inc_ref(v_p_483_);
lean_dec_ref(v_x_472_);
v_x_472_ = v_p_483_;
goto _start;
}
case 4:
{
lean_object* v_type_485_; lean_object* v_xs_486_; uint8_t v___x_487_; 
v_type_485_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_type_485_);
v_xs_486_ = lean_ctor_get(v_x_472_, 1);
lean_inc(v_xs_486_);
lean_dec_ref(v_x_472_);
v___x_487_ = l_Lean_Expr_hasExprMVar(v_type_485_);
lean_dec_ref(v_type_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Pattern_hasExprMVar___boxed), 1, 0);
v___x_489_ = l_List_any___redArg(v_xs_486_, v___x_488_);
return v___x_489_;
}
else
{
lean_dec(v_xs_486_);
return v___x_487_;
}
}
default: 
{
uint8_t v___x_490_; 
lean_dec_ref(v_x_472_);
v___x_490_ = 0;
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(lean_object* v_as_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
if (lean_obj_tag(v_as_491_) == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_box(0);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_head_500_; lean_object* v_tail_501_; lean_object* v___x_502_; 
v_head_500_ = lean_ctor_get(v_as_491_, 0);
lean_inc(v_head_500_);
v_tail_501_ = lean_ctor_get(v_as_491_, 1);
lean_inc(v_tail_501_);
lean_dec_ref(v_as_491_);
v___x_502_ = l_Lean_Expr_collectFVars(v_head_500_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_dec_ref(v___x_502_);
v_as_491_ = v_tail_501_;
goto _start;
}
else
{
lean_dec(v_tail_501_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0___boxed(lean_object* v_as_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_as_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars(lean_object* v_p_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
switch(lean_obj_tag(v_p_512_))
{
case 1:
{
lean_object* v_fvarId_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_530_; 
v_fvarId_519_ = lean_ctor_get(v_p_512_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_p_512_);
if (v_isSharedCheck_530_ == 0)
{
v___x_521_ = v_p_512_;
v_isShared_522_ = v_isSharedCheck_530_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_fvarId_519_);
lean_dec(v_p_512_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_530_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_523_ = lean_st_ref_take(v_a_513_);
v___x_524_ = l_Lean_CollectFVars_State_add(v___x_523_, v_fvarId_519_);
v___x_525_ = lean_st_ref_set(v_a_513_, v___x_524_);
v___x_526_ = lean_box(0);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 0);
lean_ctor_set(v___x_521_, 0, v___x_526_);
v___x_528_ = v___x_521_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
case 2:
{
lean_object* v_params_531_; lean_object* v_fields_532_; lean_object* v___x_533_; 
v_params_531_ = lean_ctor_get(v_p_512_, 2);
lean_inc(v_params_531_);
v_fields_532_ = lean_ctor_get(v_p_512_, 3);
lean_inc(v_fields_532_);
lean_dec_ref(v_p_512_);
v___x_533_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__0(v_params_531_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v___x_534_; 
lean_dec_ref(v___x_533_);
v___x_534_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_fields_532_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
return v___x_534_;
}
else
{
lean_dec(v_fields_532_);
return v___x_533_;
}
}
case 4:
{
lean_object* v_type_535_; lean_object* v_xs_536_; lean_object* v___x_537_; 
v_type_535_ = lean_ctor_get(v_p_512_, 0);
lean_inc_ref(v_type_535_);
v_xs_536_ = lean_ctor_get(v_p_512_, 1);
lean_inc(v_xs_536_);
lean_dec_ref(v_p_512_);
v___x_537_ = l_Lean_Expr_collectFVars(v_type_535_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; 
lean_dec_ref(v___x_537_);
v___x_538_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_xs_536_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
return v___x_538_;
}
else
{
lean_dec(v_xs_536_);
return v___x_537_;
}
}
case 5:
{
lean_object* v_varId_539_; lean_object* v_p_540_; lean_object* v_hId_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_varId_539_ = lean_ctor_get(v_p_512_, 0);
lean_inc(v_varId_539_);
v_p_540_ = lean_ctor_get(v_p_512_, 1);
lean_inc_ref(v_p_540_);
v_hId_541_ = lean_ctor_get(v_p_512_, 2);
lean_inc(v_hId_541_);
lean_dec_ref(v_p_512_);
v___x_542_ = lean_st_ref_take(v_a_513_);
v___x_543_ = l_Lean_CollectFVars_State_add(v___x_542_, v_varId_539_);
v___x_544_ = l_Lean_CollectFVars_State_add(v___x_543_, v_hId_541_);
v___x_545_ = lean_st_ref_set(v_a_513_, v___x_544_);
v_p_512_ = v_p_540_;
goto _start;
}
default: 
{
lean_object* v_e_547_; lean_object* v___x_548_; 
v_e_547_ = lean_ctor_get(v_p_512_, 0);
lean_inc_ref(v_e_547_);
lean_dec_ref(v_p_512_);
v___x_548_ = l_Lean_Expr_collectFVars(v_e_547_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(lean_object* v_as_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
if (lean_obj_tag(v_as_549_) == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v_head_558_; lean_object* v_tail_559_; lean_object* v___x_560_; 
v_head_558_ = lean_ctor_get(v_as_549_, 0);
lean_inc(v_head_558_);
v_tail_559_ = lean_ctor_get(v_as_549_, 1);
lean_inc(v_tail_559_);
lean_dec_ref(v_as_549_);
v___x_560_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_558_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_dec_ref(v___x_560_);
v_as_549_ = v_tail_559_;
goto _start;
}
else
{
lean_dec(v_tail_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1___boxed(lean_object* v_as_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_List_forM___at___00Lean_Meta_Match_Pattern_collectFVars_spec__1(v_as_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Pattern_collectFVars___boxed(lean_object* v_p_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_Match_Pattern_collectFVars(v_p_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(lean_object* v_e_578_, lean_object* v___y_579_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = l_Lean_Expr_hasMVar(v_e_578_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_e_578_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v_mctx_584_; lean_object* v___x_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; lean_object* v___x_588_; lean_object* v_cache_589_; lean_object* v_zetaDeltaFVarIds_590_; lean_object* v_postponed_591_; lean_object* v_diag_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_601_; 
v___x_583_ = lean_st_ref_get(v___y_579_);
v_mctx_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_mctx_584_);
lean_dec(v___x_583_);
v___x_585_ = l_Lean_instantiateMVarsCore(v_mctx_584_, v_e_578_);
v_fst_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_fst_586_);
v_snd_587_ = lean_ctor_get(v___x_585_, 1);
lean_inc(v_snd_587_);
lean_dec_ref(v___x_585_);
v___x_588_ = lean_st_ref_take(v___y_579_);
v_cache_589_ = lean_ctor_get(v___x_588_, 1);
v_zetaDeltaFVarIds_590_ = lean_ctor_get(v___x_588_, 2);
v_postponed_591_ = lean_ctor_get(v___x_588_, 3);
v_diag_592_ = lean_ctor_get(v___x_588_, 4);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_602_);
v___x_594_ = v___x_588_;
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_diag_592_);
lean_inc(v_postponed_591_);
lean_inc(v_zetaDeltaFVarIds_590_);
lean_inc(v_cache_589_);
lean_dec(v___x_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_snd_587_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_snd_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_cache_589_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_zetaDeltaFVarIds_590_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_postponed_591_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_diag_592_);
v___x_597_ = v_reuseFailAlloc_600_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_st_ref_set(v___y_579_, v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v_fst_586_);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg___boxed(lean_object* v_e_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_603_, v___y_604_);
lean_dec(v___y_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(lean_object* v_e_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_607_, v___y_609_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___boxed(lean_object* v_e_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0(v_e_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = l_List_reverse___redArg(v_x_622_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_641_; 
v_head_630_ = lean_ctor_get(v_x_621_, 0);
v_tail_631_ = lean_ctor_get(v_x_621_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_641_ == 0)
{
v___x_633_ = v_x_621_;
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_tail_631_);
lean_inc(v_head_630_);
lean_dec(v_x_621_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v_a_636_; lean_object* v___x_638_; 
v___x_635_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_head_630_, v___y_624_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_x_622_);
lean_ctor_set(v___x_633_, 0, v_a_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_636_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_x_622_);
v___x_638_ = v_reuseFailAlloc_640_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v_x_621_ = v_tail_631_;
v_x_622_ = v___x_638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1___boxed(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_x_642_, v_x_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars(lean_object* v_x_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
switch(lean_obj_tag(v_x_650_))
{
case 0:
{
lean_object* v_e_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_680_; 
v_e_656_ = lean_ctor_get(v_x_650_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_680_ == 0)
{
v___x_658_ = v_x_650_;
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_e_656_);
lean_dec(v_x_650_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_656_, v_a_652_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_671_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_671_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_671_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_671_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_a_661_);
v___x_666_ = v___x_658_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_del_object(v___x_658_);
v_a_672_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_660_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_660_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
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
}
case 3:
{
lean_object* v_e_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_705_; 
v_e_681_ = lean_ctor_get(v_x_650_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_705_ == 0)
{
v___x_683_ = v_x_650_;
v_isShared_684_ = v_isSharedCheck_705_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_e_681_);
lean_dec(v_x_650_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_705_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_e_681_, v_a_652_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_696_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_696_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_a_686_);
v___x_691_ = v___x_683_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_683_);
v_a_697_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_685_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_685_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
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
}
case 2:
{
lean_object* v_ctorName_706_; lean_object* v_us_707_; lean_object* v_params_708_; lean_object* v_fields_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_744_; 
v_ctorName_706_ = lean_ctor_get(v_x_650_, 0);
v_us_707_ = lean_ctor_get(v_x_650_, 1);
v_params_708_ = lean_ctor_get(v_x_650_, 2);
v_fields_709_ = lean_ctor_get(v_x_650_, 3);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_744_ == 0)
{
v___x_711_ = v_x_650_;
v_isShared_712_ = v_isSharedCheck_744_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_fields_709_);
lean_inc(v_params_708_);
lean_inc(v_us_707_);
lean_inc(v_ctorName_706_);
lean_dec(v_x_650_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_744_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__1(v_params_708_, v___x_713_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v___x_716_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_fields_709_, v___x_713_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_727_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_727_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_727_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 3, v_a_717_);
lean_ctor_set(v___x_711_, 2, v_a_715_);
v___x_722_ = v___x_711_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_ctorName_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_us_707_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_a_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_a_717_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_a_715_);
lean_del_object(v___x_711_);
lean_dec(v_us_707_);
lean_dec(v_ctorName_706_);
v_a_728_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_716_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_716_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
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
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_del_object(v___x_711_);
lean_dec(v_fields_709_);
lean_dec(v_us_707_);
lean_dec(v_ctorName_706_);
v_a_736_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_714_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_714_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
case 5:
{
lean_object* v_varId_745_; lean_object* v_p_746_; lean_object* v_hId_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_763_; 
v_varId_745_ = lean_ctor_get(v_x_650_, 0);
v_p_746_ = lean_ctor_get(v_x_650_, 1);
v_hId_747_ = lean_ctor_get(v_x_650_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_763_ == 0)
{
v___x_749_ = v_x_650_;
v_isShared_750_ = v_isSharedCheck_763_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_hId_747_);
lean_inc(v_p_746_);
lean_inc(v_varId_745_);
lean_dec(v_x_650_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_763_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Match_instantiatePatternMVars(v_p_746_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_762_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_762_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_762_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_a_752_);
v___x_757_ = v___x_749_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_varId_745_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_a_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_hId_747_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_757_);
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_del_object(v___x_749_);
lean_dec(v_hId_747_);
lean_dec(v_varId_745_);
return v___x_751_;
}
}
}
case 4:
{
lean_object* v_type_764_; lean_object* v_xs_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_800_; 
v_type_764_ = lean_ctor_get(v_x_650_, 0);
v_xs_765_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_800_ == 0)
{
v___x_767_ = v_x_650_;
v_isShared_768_ = v_isSharedCheck_800_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_xs_765_);
lean_inc(v_type_764_);
lean_dec(v_x_650_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_800_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_764_, v_a_652_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v___x_771_ = lean_box(0);
v___x_772_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_xs_765_, v___x_771_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
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
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_a_773_);
lean_ctor_set(v___x_767_, 0, v_a_770_);
v___x_778_ = v___x_767_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_773_);
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
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_a_770_);
lean_del_object(v___x_767_);
v_a_784_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_772_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
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
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_del_object(v___x_767_);
lean_dec(v_xs_765_);
v_a_792_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_769_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_769_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
default: 
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_x_650_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_List_reverse___redArg(v_x_803_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_830_; 
v_head_811_ = lean_ctor_get(v_x_802_, 0);
v_tail_812_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_830_ == 0)
{
v___x_814_ = v_x_802_;
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_head_811_);
lean_dec(v_x_802_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_Match_instantiatePatternMVars(v_head_811_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_x_803_);
lean_ctor_set(v___x_814_, 0, v_a_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_817_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_x_803_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_x_802_ = v_tail_812_;
v_x_803_ = v___x_819_;
goto _start;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_del_object(v___x_814_);
lean_dec(v_tail_812_);
lean_dec(v_x_803_);
v_a_822_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_816_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_816_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2___boxed(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_x_831_, v_x_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiatePatternMVars___boxed(lean_object* v_x_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_Match_instantiatePatternMVars(v_x_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(lean_object* v_as_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
if (lean_obj_tag(v_as_851_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
else
{
lean_object* v_head_860_; lean_object* v_tail_861_; lean_object* v___x_862_; 
v_head_860_ = lean_ctor_get(v_as_851_, 0);
lean_inc(v_head_860_);
v_tail_861_ = lean_ctor_get(v_as_851_, 1);
lean_inc(v_tail_861_);
lean_dec_ref(v_as_851_);
v___x_862_ = l_Lean_LocalDecl_collectFVars(v_head_860_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_dec_ref(v___x_862_);
v_as_851_ = v_tail_861_;
goto _start;
}
else
{
lean_dec(v_tail_861_);
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0___boxed(lean_object* v_as_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_as_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(lean_object* v_as_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
if (lean_obj_tag(v_as_872_) == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
else
{
lean_object* v_head_881_; lean_object* v_tail_882_; lean_object* v___x_883_; 
v_head_881_ = lean_ctor_get(v_as_872_, 0);
lean_inc(v_head_881_);
v_tail_882_ = lean_ctor_get(v_as_872_, 1);
lean_inc(v_tail_882_);
lean_dec_ref(v_as_872_);
v___x_883_ = l_Lean_Meta_Match_Pattern_collectFVars(v_head_881_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_dec_ref(v___x_883_);
v_as_872_ = v_tail_882_;
goto _start;
}
else
{
lean_dec(v_tail_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1___boxed(lean_object* v_as_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_as_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars(lean_object* v_altLHS_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_fvarDecls_900_; lean_object* v_patterns_901_; lean_object* v___x_902_; 
v_fvarDecls_900_ = lean_ctor_get(v_altLHS_893_, 1);
lean_inc(v_fvarDecls_900_);
v_patterns_901_ = lean_ctor_get(v_altLHS_893_, 2);
lean_inc(v_patterns_901_);
lean_dec_ref(v_altLHS_893_);
v___x_902_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__0(v_fvarDecls_900_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_903_; 
lean_dec_ref(v___x_902_);
v___x_903_ = l_List_forM___at___00Lean_Meta_Match_AltLHS_collectFVars_spec__1(v_patterns_901_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_903_;
}
else
{
lean_dec(v_patterns_901_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_AltLHS_collectFVars___boxed(lean_object* v_altLHS_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Meta_Match_AltLHS_collectFVars(v_altLHS_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(lean_object* v_localDecl_912_, lean_object* v___y_913_){
_start:
{
if (lean_obj_tag(v_localDecl_912_) == 0)
{
lean_object* v_index_915_; lean_object* v_fvarId_916_; lean_object* v_userName_917_; lean_object* v_type_918_; uint8_t v_bi_919_; uint8_t v_kind_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_936_; 
v_index_915_ = lean_ctor_get(v_localDecl_912_, 0);
v_fvarId_916_ = lean_ctor_get(v_localDecl_912_, 1);
v_userName_917_ = lean_ctor_get(v_localDecl_912_, 2);
v_type_918_ = lean_ctor_get(v_localDecl_912_, 3);
v_bi_919_ = lean_ctor_get_uint8(v_localDecl_912_, sizeof(void*)*4);
v_kind_920_ = lean_ctor_get_uint8(v_localDecl_912_, sizeof(void*)*4 + 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_localDecl_912_);
if (v_isSharedCheck_936_ == 0)
{
v___x_922_ = v_localDecl_912_;
v_isShared_923_ = v_isSharedCheck_936_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_type_918_);
lean_inc(v_userName_917_);
lean_inc(v_fvarId_916_);
lean_inc(v_index_915_);
lean_dec(v_localDecl_912_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_936_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_935_; 
v___x_924_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_918_, v___y_913_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_935_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_935_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_935_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 3, v_a_925_);
v___x_930_ = v___x_922_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_index_915_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_fvarId_916_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_userName_917_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_a_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*4, v_bi_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*4 + 1, v_kind_920_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_930_);
v___x_932_ = v___x_927_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
else
{
lean_object* v_index_937_; lean_object* v_fvarId_938_; lean_object* v_userName_939_; lean_object* v_type_940_; lean_object* v_value_941_; uint8_t v_nondep_942_; uint8_t v_kind_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_961_; 
v_index_937_ = lean_ctor_get(v_localDecl_912_, 0);
v_fvarId_938_ = lean_ctor_get(v_localDecl_912_, 1);
v_userName_939_ = lean_ctor_get(v_localDecl_912_, 2);
v_type_940_ = lean_ctor_get(v_localDecl_912_, 3);
v_value_941_ = lean_ctor_get(v_localDecl_912_, 4);
v_nondep_942_ = lean_ctor_get_uint8(v_localDecl_912_, sizeof(void*)*5);
v_kind_943_ = lean_ctor_get_uint8(v_localDecl_912_, sizeof(void*)*5 + 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_localDecl_912_);
if (v_isSharedCheck_961_ == 0)
{
v___x_945_ = v_localDecl_912_;
v_isShared_946_ = v_isSharedCheck_961_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_value_941_);
lean_inc(v_type_940_);
lean_inc(v_userName_939_);
lean_inc(v_fvarId_938_);
lean_inc(v_index_937_);
lean_dec(v_localDecl_912_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_961_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_960_; 
v___x_947_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_type_940_, v___y_913_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref(v___x_947_);
v___x_949_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_instantiatePatternMVars_spec__0___redArg(v_value_941_, v___y_913_);
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_960_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 4, v_a_950_);
lean_ctor_set(v___x_945_, 3, v_a_948_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_index_937_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_fvarId_938_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_userName_939_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_a_948_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_a_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*5, v_nondep_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*5 + 1, v_kind_943_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg___boxed(lean_object* v_localDecl_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_962_, v___y_963_);
lean_dec(v___y_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(lean_object* v_x_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = l_List_reverse___redArg(v_x_967_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
else
{
lean_object* v_head_975_; lean_object* v_tail_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_994_; 
v_head_975_ = lean_ctor_get(v_x_966_, 0);
v_tail_976_ = lean_ctor_get(v_x_966_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_994_ == 0)
{
v___x_978_ = v_x_966_;
v_isShared_979_ = v_isSharedCheck_994_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_tail_976_);
lean_inc(v_head_975_);
lean_dec(v_x_966_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_994_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_head_975_, v___y_969_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_x_967_);
lean_ctor_set(v___x_978_, 0, v_a_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_981_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_x_967_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_x_966_ = v_tail_976_;
v_x_967_ = v___x_983_;
goto _start;
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_del_object(v___x_978_);
lean_dec(v_tail_976_);
lean_dec(v_x_967_);
v_a_986_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_980_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_980_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1___boxed(lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_x_995_, v_x_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars(lean_object* v_altLHS_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_ref_1009_; lean_object* v_fvarDecls_1010_; lean_object* v_patterns_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1046_; 
v_ref_1009_ = lean_ctor_get(v_altLHS_1003_, 0);
v_fvarDecls_1010_ = lean_ctor_get(v_altLHS_1003_, 1);
v_patterns_1011_ = lean_ctor_get(v_altLHS_1003_, 2);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_altLHS_1003_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1013_ = v_altLHS_1003_;
v_isShared_1014_ = v_isSharedCheck_1046_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_patterns_1011_);
lean_inc(v_fvarDecls_1010_);
lean_inc(v_ref_1009_);
lean_dec(v_altLHS_1003_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1046_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__1(v_fvarDecls_1010_, v___x_1015_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = l_List_mapM_loop___at___00Lean_Meta_Match_instantiatePatternMVars_spec__2(v_patterns_1011_, v___x_1015_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 2, v_a_1019_);
lean_ctor_set(v___x_1013_, 1, v_a_1017_);
v___x_1024_ = v___x_1013_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_ref_1009_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1017_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1024_);
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_a_1017_);
lean_del_object(v___x_1013_);
lean_dec(v_ref_1009_);
v_a_1030_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1018_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1018_);
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
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_del_object(v___x_1013_);
lean_dec(v_patterns_1011_);
lean_dec(v_ref_1009_);
v_a_1038_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1016_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1016_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instantiateAltLHSMVars___boxed(lean_object* v_altLHS_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_Match_instantiateAltLHSMVars(v_altLHS_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(lean_object* v_localDecl_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___redArg(v_localDecl_1054_, v___y_1056_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0___boxed(lean_object* v_localDecl_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_instantiateLocalDeclMVars___at___00Lean_Meta_Match_instantiateAltLHSMVars_spec__0(v_localDecl_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1070_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedAlt_default___closed__0));
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedPattern_default___closed__2, &l_Lean_Meta_Match_instInhabitedPattern_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedPattern_default___closed__2);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
lean_ctor_set(v___x_1075_, 2, v___x_1072_);
lean_ctor_set(v___x_1075_, 3, v___x_1071_);
lean_ctor_set(v___x_1075_, 4, v___x_1071_);
lean_ctor_set(v___x_1075_, 5, v___x_1071_);
lean_ctor_set(v___x_1075_, 6, v___x_1070_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt_default(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedAlt_default___closed__1, &l_Lean_Meta_Match_instInhabitedAlt_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedAlt_default___closed__1);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedAlt(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_Match_instInhabitedAlt_default;
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(lean_object* v_msgData_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; lean_object* v_env_1085_; lean_object* v___x_1086_; lean_object* v_mctx_1087_; lean_object* v_lctx_1088_; lean_object* v_options_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1084_ = lean_st_ref_get(v___y_1082_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1086_ = lean_st_ref_get(v___y_1080_);
v_mctx_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_mctx_1087_);
lean_dec(v___x_1086_);
v_lctx_1088_ = lean_ctor_get(v___y_1079_, 2);
v_options_1089_ = lean_ctor_get(v___y_1081_, 2);
lean_inc_ref(v_options_1089_);
lean_inc_ref(v_lctx_1088_);
v___x_1090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1090_, 0, v_env_1085_);
lean_ctor_set(v___x_1090_, 1, v_mctx_1087_);
lean_ctor_set(v___x_1090_, 2, v_lctx_1088_);
lean_ctor_set(v___x_1090_, 3, v_options_1089_);
v___x_1091_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_msgData_1078_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2___boxed(lean_object* v_msgData_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msgData_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(lean_object* v_decls_1100_, lean_object* v_x_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withExistingLocalDeclsImp(lean_box(0), v_decls_1100_, v_x_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1107_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg___boxed(lean_object* v_decls_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1124_, v_x_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(lean_object* v_00_u03b1_1132_, lean_object* v_decls_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___redArg(v_decls_1133_, v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_decls_1142_, lean_object* v_x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Meta_withExistingLocalDecls___at___00Lean_Meta_Match_Alt_toMessageData_spec__3(v_00_u03b1_1141_, v_decls_1142_, v_x_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__2));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(lean_object* v_as_x27_1156_, lean_object* v_b_1157_){
_start:
{
if (lean_obj_tag(v_as_x27_1156_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_b_1157_);
return v___x_1159_;
}
else
{
lean_object* v_head_1160_; lean_object* v_tail_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1184_; 
v_head_1160_ = lean_ctor_get(v_as_x27_1156_, 0);
v_tail_1161_ = lean_ctor_get(v_as_x27_1156_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_as_x27_1156_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1163_ = v_as_x27_1156_;
v_isShared_1164_ = v_isSharedCheck_1184_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_tail_1161_);
lean_inc(v_head_1160_);
lean_dec(v_as_x27_1156_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1184_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_fst_1165_; lean_object* v_snd_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1183_; 
v_fst_1165_ = lean_ctor_get(v_head_1160_, 0);
v_snd_1166_ = lean_ctor_get(v_head_1160_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_head_1160_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1168_ = v_head_1160_;
v_isShared_1169_ = v_isSharedCheck_1183_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1166_);
lean_inc(v_fst_1165_);
lean_dec(v_head_1160_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1183_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__1);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 7);
lean_ctor_set(v___x_1168_, 1, v___x_1170_);
lean_ctor_set(v___x_1168_, 0, v_b_1157_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_b_1157_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = l_Lean_MessageData_ofExpr(v_fst_1165_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 7);
lean_ctor_set(v___x_1163_, 1, v___x_1173_);
lean_ctor_set(v___x_1163_, 0, v___x_1172_);
v___x_1175_ = v___x_1163_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___closed__3);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_MessageData_ofExpr(v_snd_1166_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v_as_x27_1156_ = v_tail_1161_;
v_b_1157_ = v___x_1179_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg___boxed(lean_object* v_as_x27_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_List_forIn_x27_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__1___redArg(v_as_x27_1185_, v_b_1186_);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl___lam__0(lean_object* v_fvarId_1504_, lean_object* v_d_1505_){
_start:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = l_Lean_LocalDecl_fvarId(v_d_1505_);
v___x_1507_ = l_Lean_instBEqFVarId_beq(v___x_1506_, v_fvarId_1504_);
lean_dec(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___lam__0___boxed(lean_object* v_fvarId_1508_, lean_object* v_d_1509_){
_start:
{
uint8_t v_res_1510_; lean_object* v_r_1511_; 
v_res_1510_ = l_Lean_Meta_Match_Alt_isLocalDecl___lam__0(v_fvarId_1508_, v_d_1509_);
lean_dec_ref(v_d_1509_);
lean_dec(v_fvarId_1508_);
v_r_1511_ = lean_box(v_res_1510_);
return v_r_1511_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Alt_isLocalDecl(lean_object* v_fvarId_1512_, lean_object* v_alt_1513_){
_start:
{
lean_object* v_fvarDecls_1514_; lean_object* v___f_1515_; uint8_t v___x_1516_; 
v_fvarDecls_1514_ = lean_ctor_get(v_alt_1513_, 3);
lean_inc(v_fvarDecls_1514_);
lean_dec_ref(v_alt_1513_);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Alt_isLocalDecl___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1515_, 0, v_fvarId_1512_);
v___x_1516_ = l_List_any___redArg(v_fvarDecls_1514_, v___f_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Alt_isLocalDecl___boxed(lean_object* v_fvarId_1517_, lean_object* v_alt_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l_Lean_Meta_Match_Alt_isLocalDecl(v_fvarId_1517_, v_alt_1518_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx(lean_object* v_x_1521_){
_start:
{
switch(lean_obj_tag(v_x_1521_))
{
case 0:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(0u);
return v___x_1522_;
}
case 1:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
return v___x_1523_;
}
case 2:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_unsigned_to_nat(2u);
return v___x_1524_;
}
case 3:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(3u);
return v___x_1525_;
}
default: 
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_unsigned_to_nat(4u);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorIdx___boxed(lean_object* v_x_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_Match_Example_ctorIdx(v_x_1527_);
lean_dec(v_x_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___redArg(lean_object* v_t_1529_, lean_object* v_k_1530_){
_start:
{
switch(lean_obj_tag(v_t_1529_))
{
case 1:
{
return v_k_1530_;
}
case 2:
{
lean_object* v_a_1531_; lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1531_ = lean_ctor_get(v_t_1529_, 0);
lean_inc(v_a_1531_);
v_a_1532_ = lean_ctor_get(v_t_1529_, 1);
lean_inc(v_a_1532_);
lean_dec_ref(v_t_1529_);
v___x_1533_ = lean_apply_2(v_k_1530_, v_a_1531_, v_a_1532_);
return v___x_1533_;
}
case 3:
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v_t_1529_, 0);
lean_inc_ref(v_a_1534_);
lean_dec_ref(v_t_1529_);
v___x_1535_ = lean_apply_1(v_k_1530_, v_a_1534_);
return v___x_1535_;
}
default: 
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v_t_1529_, 0);
lean_inc(v_a_1536_);
lean_dec(v_t_1529_);
v___x_1537_ = lean_apply_1(v_k_1530_, v_a_1536_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim(lean_object* v_motive__1_1538_, lean_object* v_ctorIdx_1539_, lean_object* v_t_1540_, lean_object* v_h_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1540_, v_k_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctorElim___boxed(lean_object* v_motive__1_1544_, lean_object* v_ctorIdx_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Meta_Match_Example_ctorElim(v_motive__1_1544_, v_ctorIdx_1545_, v_t_1546_, v_h_1547_, v_k_1548_);
lean_dec(v_ctorIdx_1545_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim___redArg(lean_object* v_t_1550_, lean_object* v_var_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1550_, v_var_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_var_elim(lean_object* v_motive__1_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_var_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1554_, v_var_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim___redArg(lean_object* v_t_1558_, lean_object* v_underscore_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1558_, v_underscore_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_underscore_elim(lean_object* v_motive__1_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_underscore_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1562_, v_underscore_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim___redArg(lean_object* v_t_1566_, lean_object* v_ctor_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1566_, v_ctor_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_ctor_elim(lean_object* v_motive__1_1569_, lean_object* v_t_1570_, lean_object* v_h_1571_, lean_object* v_ctor_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1570_, v_ctor_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim___redArg(lean_object* v_t_1574_, lean_object* v_val_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1574_, v_val_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_val_elim(lean_object* v_motive__1_1577_, lean_object* v_t_1578_, lean_object* v_h_1579_, lean_object* v_val_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1578_, v_val_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim___redArg(lean_object* v_t_1582_, lean_object* v_arrayLit_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1582_, v_arrayLit_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_arrayLit_elim(lean_object* v_motive__1_1585_, lean_object* v_t_1586_, lean_object* v_h_1587_, lean_object* v_arrayLit_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Match_Example_ctorElim___redArg(v_t_1586_, v_arrayLit_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object* v_fvarId_1590_, lean_object* v_ex_1591_, lean_object* v_x_1592_){
_start:
{
switch(lean_obj_tag(v_x_1592_))
{
case 0:
{
lean_object* v_a_1593_; uint8_t v___x_1594_; 
v_a_1593_ = lean_ctor_get(v_x_1592_, 0);
v___x_1594_ = l_Lean_instBEqFVarId_beq(v_a_1593_, v_fvarId_1590_);
if (v___x_1594_ == 0)
{
return v_x_1592_;
}
else
{
lean_dec_ref(v_x_1592_);
lean_inc(v_ex_1591_);
return v_ex_1591_;
}
}
case 2:
{
lean_object* v_a_1595_; lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1605_; 
v_a_1595_ = lean_ctor_get(v_x_1592_, 0);
v_a_1596_ = lean_ctor_get(v_x_1592_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1598_ = v_x_1592_;
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_inc(v_a_1595_);
lean_dec(v_x_1592_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1590_, v_ex_1591_, v_a_1596_, v___x_1600_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1601_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1595_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
case 4:
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1615_; 
v_a_1606_ = lean_ctor_get(v_x_1592_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1608_ = v_x_1592_;
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v_x_1592_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1610_ = lean_box(0);
v___x_1611_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1590_, v_ex_1591_, v_a_1606_, v___x_1610_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1611_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
default: 
{
return v_x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(lean_object* v_fvarId_1616_, lean_object* v_ex_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
if (lean_obj_tag(v_a_1618_) == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = l_List_reverse___redArg(v_a_1619_);
return v___x_1620_;
}
else
{
lean_object* v_head_1621_; lean_object* v_tail_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1631_; 
v_head_1621_ = lean_ctor_get(v_a_1618_, 0);
v_tail_1622_ = lean_ctor_get(v_a_1618_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1624_ = v_a_1618_;
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_tail_1622_);
lean_inc(v_head_1621_);
lean_dec(v_a_1618_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1616_, v_ex_1617_, v_head_1621_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v_a_1619_);
lean_ctor_set(v___x_1624_, 0, v___x_1626_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_a_1619_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v_a_1618_ = v_tail_1622_;
v_a_1619_ = v___x_1628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0___boxed(lean_object* v_fvarId_1632_, lean_object* v_ex_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_replaceFVarId_spec__0(v_fvarId_1632_, v_ex_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_ex_1633_);
lean_dec(v_fvarId_1632_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_replaceFVarId___boxed(lean_object* v_fvarId_1637_, lean_object* v_ex_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Meta_Match_Example_replaceFVarId(v_fvarId_1637_, v_ex_1638_, v_x_1639_);
lean_dec(v_ex_1638_);
lean_dec(v_fvarId_1637_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object* v_s_1641_, lean_object* v_x_1642_){
_start:
{
switch(lean_obj_tag(v_x_1642_))
{
case 0:
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1653_; 
v_a_1643_ = lean_ctor_get(v_x_1642_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1645_ = v_x_1642_;
v_isShared_1646_ = v_isSharedCheck_1653_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v_x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1653_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_FVarSubst_get(v_s_1641_, v_a_1643_);
if (lean_obj_tag(v___x_1647_) == 1)
{
lean_object* v_fvarId_1648_; lean_object* v___x_1650_; 
v_fvarId_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_fvarId_1648_);
lean_dec_ref(v___x_1647_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_fvarId_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_fvarId_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
else
{
lean_object* v___x_1652_; 
lean_dec_ref(v___x_1647_);
lean_del_object(v___x_1645_);
v___x_1652_ = lean_box(1);
return v___x_1652_;
}
}
}
case 2:
{
lean_object* v_a_1654_; lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1664_; 
v_a_1654_ = lean_ctor_get(v_x_1642_, 0);
v_a_1655_ = lean_ctor_get(v_x_1642_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1657_ = v_x_1642_;
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_inc(v_a_1654_);
lean_dec(v_x_1642_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1659_ = lean_box(0);
v___x_1660_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1641_, v_a_1655_, v___x_1659_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___x_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1654_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
case 4:
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1674_; 
v_a_1665_ = lean_ctor_get(v_x_1642_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1667_ = v_x_1642_;
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v_x_1642_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1641_, v_a_1665_, v___x_1669_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
default: 
{
return v_x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(lean_object* v_s_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
if (lean_obj_tag(v_a_1676_) == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = l_List_reverse___redArg(v_a_1677_);
return v___x_1678_;
}
else
{
lean_object* v_head_1679_; lean_object* v_tail_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1689_; 
v_head_1679_ = lean_ctor_get(v_a_1676_, 0);
v_tail_1680_ = lean_ctor_get(v_a_1676_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_a_1676_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1682_ = v_a_1676_;
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_tail_1680_);
lean_inc(v_head_1679_);
lean_dec(v_a_1676_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1689_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1675_, v_head_1679_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v_a_1677_);
lean_ctor_set(v___x_1682_, 0, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_a_1677_);
v___x_1686_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_a_1676_ = v_tail_1680_;
v_a_1677_ = v___x_1686_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0___boxed(lean_object* v_s_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_applyFVarSubst_spec__0(v_s_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_s_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_applyFVarSubst___boxed(lean_object* v_s_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_Match_Example_applyFVarSubst(v_s_1694_, v_x_1695_);
lean_dec(v_s_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_varsToUnderscore(lean_object* v_x_1697_){
_start:
{
switch(lean_obj_tag(v_x_1697_))
{
case 0:
{
lean_object* v___x_1698_; 
lean_dec_ref(v_x_1697_);
v___x_1698_ = lean_box(1);
return v___x_1698_;
}
case 2:
{
lean_object* v_a_1699_; lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1709_; 
v_a_1699_ = lean_ctor_get(v_x_1697_, 0);
v_a_1700_ = lean_ctor_get(v_x_1697_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1702_ = v_x_1697_;
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_inc(v_a_1699_);
lean_dec(v_x_1697_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1704_ = lean_box(0);
v___x_1705_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1700_, v___x_1704_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1705_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1699_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
case 4:
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1719_; 
v_a_1710_ = lean_ctor_get(v_x_1697_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_x_1697_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1712_ = v_x_1697_;
v_isShared_1713_ = v_isSharedCheck_1719_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v_x_1697_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1719_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1714_ = lean_box(0);
v___x_1715_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(v_a_1710_, v___x_1714_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
default: 
{
return v_x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_varsToUnderscore_spec__0(lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
if (lean_obj_tag(v_a_1720_) == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = l_List_reverse___redArg(v_a_1721_);
return v___x_1722_;
}
else
{
lean_object* v_head_1723_; lean_object* v_tail_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
v_head_1723_ = lean_ctor_get(v_a_1720_, 0);
v_tail_1724_ = lean_ctor_get(v_a_1720_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_a_1720_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1726_ = v_a_1720_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_tail_1724_);
lean_inc(v_head_1723_);
lean_dec(v_a_1720_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1723_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_a_1721_);
lean_ctor_set(v___x_1726_, 0, v___x_1728_);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1721_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v_a_1720_ = v_tail_1724_;
v_a_1721_ = v___x_1730_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__1));
v___x_1738_ = l_Lean_MessageData_ofFormat(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_List_foldl___at___00Lean_Meta_Match_Pattern_toMessageData_spec__0___closed__0));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
if (lean_obj_tag(v_x_1742_) == 0)
{
return v_x_1741_;
}
else
{
lean_object* v_head_1743_; lean_object* v_tail_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1755_; 
v_head_1743_ = lean_ctor_get(v_x_1742_, 0);
v_tail_1744_ = lean_ctor_get(v_x_1742_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_x_1742_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1746_ = v_x_1742_;
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_tail_1744_);
lean_inc(v_head_1743_);
lean_dec(v_x_1742_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_obj_once(&l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0, &l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0_once, _init_l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0___closed__0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 7);
lean_ctor_set(v___x_1746_, 1, v___x_1748_);
lean_ctor_set(v___x_1746_, 0, v_x_1741_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_x_1741_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1743_);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v_x_1741_ = v___x_1752_;
v_x_1742_ = v_tail_1744_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Example_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lean_Meta_Match_Example_toMessageData___closed__4));
v___x_1760_ = l_Lean_MessageData_ofFormat(v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Example_toMessageData(lean_object* v_x_1761_){
_start:
{
switch(lean_obj_tag(v_x_1761_))
{
case 0:
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_a_1762_ = lean_ctor_get(v_x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v_x_1761_);
v___x_1763_ = l_Lean_mkFVar(v_a_1762_);
v___x_1764_ = l_Lean_MessageData_ofExpr(v___x_1763_);
return v___x_1764_;
}
case 1:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__2, &l_Lean_Meta_Match_Example_toMessageData___closed__2_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__2);
return v___x_1765_;
}
case 2:
{
lean_object* v_a_1766_; 
v_a_1766_ = lean_ctor_get(v_x_1761_, 1);
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1767_ = lean_ctor_get(v_x_1761_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v_x_1761_);
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_mkConst(v_a_1767_, v___x_1768_);
v___x_1770_ = l_Lean_MessageData_ofExpr(v___x_1769_);
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1786_; 
lean_inc(v_a_1766_);
v_a_1771_ = lean_ctor_get(v_x_1761_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1761_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_x_1761_, 1);
lean_dec(v_unused_1787_);
v___x_1773_ = v_x_1761_;
v_isShared_1774_ = v_isSharedCheck_1786_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v_x_1761_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1786_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1775_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__5, &l_Lean_Meta_Match_Pattern_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__5);
v___x_1776_ = 0;
v___x_1777_ = l_Lean_MessageData_ofConstName(v_a_1771_, v___x_1776_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 7);
lean_ctor_set(v___x_1773_, 1, v___x_1777_);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1779_ = v___x_1773_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__6, &l_Lean_Meta_Match_Pattern_toMessageData___closed__6_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__6);
v___x_1781_ = l_List_foldl___at___00Lean_Meta_Match_Example_toMessageData_spec__0(v___x_1780_, v_a_1766_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1779_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
return v___x_1784_;
}
}
}
}
case 3:
{
lean_object* v_a_1788_; lean_object* v___x_1789_; 
v_a_1788_ = lean_ctor_get(v_x_1761_, 0);
lean_inc_ref(v_a_1788_);
lean_dec_ref(v_x_1761_);
v___x_1789_ = l_Lean_MessageData_ofExpr(v_a_1788_);
return v___x_1789_;
}
default: 
{
lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_a_1790_ = lean_ctor_get(v_x_1761_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v_x_1761_);
v___x_1791_ = lean_obj_once(&l_Lean_Meta_Match_Example_toMessageData___closed__5, &l_Lean_Meta_Match_Example_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Example_toMessageData___closed__5);
v___x_1792_ = lean_box(0);
v___x_1793_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(v_a_1790_, v___x_1792_);
v___x_1794_ = l_Lean_MessageData_ofList(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1791_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_Example_toMessageData_spec__1(lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
if (lean_obj_tag(v_a_1796_) == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = l_List_reverse___redArg(v_a_1797_);
return v___x_1798_;
}
else
{
lean_object* v_head_1799_; lean_object* v_tail_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1809_; 
v_head_1799_ = lean_ctor_get(v_a_1796_, 0);
v_tail_1800_ = lean_ctor_get(v_a_1796_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_a_1796_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1802_ = v_a_1796_;
v_isShared_1803_ = v_isSharedCheck_1809_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_tail_1800_);
lean_inc(v_head_1799_);
lean_dec(v_a_1796_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1809_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = l_Lean_Meta_Match_Example_toMessageData(v_head_1799_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v_a_1797_);
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_a_1797_);
v___x_1806_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
v_a_1796_ = v_tail_1800_;
v_a_1797_ = v___x_1806_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
if (lean_obj_tag(v_a_1810_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = l_List_reverse___redArg(v_a_1811_);
return v___x_1812_;
}
else
{
lean_object* v_head_1813_; lean_object* v_tail_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1824_; 
v_head_1813_ = lean_ctor_get(v_a_1810_, 0);
v_tail_1814_ = lean_ctor_get(v_a_1810_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_a_1810_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1816_ = v_a_1810_;
v_isShared_1817_ = v_isSharedCheck_1824_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_tail_1814_);
lean_inc(v_head_1813_);
lean_dec(v_a_1810_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1824_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = l_Lean_Meta_Match_Example_varsToUnderscore(v_head_1813_);
v___x_1819_ = l_Lean_Meta_Match_Example_toMessageData(v___x_1818_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v_a_1811_);
lean_ctor_set(v___x_1816_, 0, v___x_1819_);
v___x_1821_ = v___x_1816_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_a_1811_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
v_a_1810_ = v_tail_1814_;
v_a_1811_ = v___x_1821_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object* v_cex_1825_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = l_List_mapTR_loop___at___00Lean_Meta_Match_examplesToMessageData_spec__0(v_cex_1825_, v___x_1826_);
v___x_1828_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__11, &l_Lean_Meta_Match_Pattern_toMessageData___closed__11_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__11);
v___x_1829_ = l_Lean_MessageData_joinSep(v___x_1827_, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(lean_object* v_mvarId_1835_, lean_object* v_x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1835_, v_x_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1842_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg___boxed(lean_object* v_mvarId_1859_, lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1859_, v_x_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(lean_object* v_00_u03b1_1867_, lean_object* v_mvarId_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1868_, v_x_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___boxed(lean_object* v_00_u03b1_1876_, lean_object* v_mvarId_1877_, lean_object* v_x_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0(v_00_u03b1_1876_, v_mvarId_1877_, v_x_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg(lean_object* v_p_1885_, lean_object* v_x_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_mvarId_1892_; lean_object* v___x_1893_; 
v_mvarId_1892_ = lean_ctor_get(v_p_1885_, 0);
lean_inc(v_mvarId_1892_);
lean_dec_ref(v_p_1885_);
v___x_1893_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_withGoalOf_spec__0___redArg(v_mvarId_1892_, v_x_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___redArg___boxed(lean_object* v_p_1894_, lean_object* v_x_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1894_, v_x_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf(lean_object* v_00_u03b1_1902_, lean_object* v_p_1903_, lean_object* v_x_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_1903_, v_x_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withGoalOf___boxed(lean_object* v_00_u03b1_1911_, lean_object* v_p_1912_, lean_object* v_x_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Meta_Match_withGoalOf(v_00_u03b1_1911_, v_p_1912_, v_x_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = l_List_reverse___redArg(v_x_1921_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
else
{
lean_object* v_head_1929_; lean_object* v_tail_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1948_; 
v_head_1929_ = lean_ctor_get(v_x_1920_, 0);
v_tail_1930_ = lean_ctor_get(v_x_1920_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_x_1920_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1932_ = v_x_1920_;
v_isShared_1933_ = v_isSharedCheck_1948_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_tail_1930_);
lean_inc(v_head_1929_);
lean_dec(v_x_1920_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1948_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Meta_Match_Alt_toMessageData(v_head_1929_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_x_1921_);
lean_ctor_set(v___x_1932_, 0, v_a_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1935_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_x_1921_);
v___x_1937_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v_x_1920_ = v_tail_1930_;
v_x_1921_ = v___x_1937_;
goto _start;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1932_);
lean_dec(v_tail_1930_);
lean_dec(v_x_1921_);
v_a_1940_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1934_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1934_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0___boxed(lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_x_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
if (lean_obj_tag(v_x_1957_) == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = l_List_reverse___redArg(v_x_1958_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
else
{
lean_object* v_head_1966_; lean_object* v_tail_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1992_; 
v_head_1966_ = lean_ctor_get(v_x_1957_, 0);
v_tail_1967_ = lean_ctor_get(v_x_1957_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1957_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1969_ = v_x_1957_;
v_isShared_1970_ = v_isSharedCheck_1992_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_tail_1967_);
lean_inc(v_head_1966_);
lean_dec(v_x_1957_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1992_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; 
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v_head_1966_);
v___x_1971_ = lean_infer_type(v_head_1966_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = l_Lean_MessageData_ofExpr(v_head_1966_);
v___x_1974_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__4___closed__1);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_MessageData_ofExpr(v_a_1972_);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_obj_once(&l_Lean_Meta_Match_Pattern_toMessageData___closed__3, &l_Lean_Meta_Match_Pattern_toMessageData___closed__3_once, _init_l_Lean_Meta_Match_Pattern_toMessageData___closed__3);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v_x_1958_);
lean_ctor_set(v___x_1969_, 0, v___x_1979_);
v___x_1981_ = v___x_1969_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_x_1958_);
v___x_1981_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
v_x_1957_ = v_tail_1967_;
v_x_1958_ = v___x_1981_;
goto _start;
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_del_object(v___x_1969_);
lean_dec(v_tail_1967_);
lean_dec(v_head_1966_);
lean_dec(v_x_1958_);
v_a_1984_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1971_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1971_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1___boxed(lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_x_1993_, v_x_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2000_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__0));
v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__2));
v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
return v___x_2006_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(1);
v___x_2008_ = l_Lean_MessageData_ofFormat(v___x_2007_);
return v___x_2008_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__5));
v___x_2011_ = l_Lean_stringToMessageData(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0(lean_object* v_alts_2012_, lean_object* v___x_2013_, lean_object* v_vars_2014_, lean_object* v_examples_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
lean_inc(v___x_2013_);
v___x_2021_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__0(v_alts_2012_, v___x_2013_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
lean_inc(v___x_2013_);
v___x_2023_ = l_List_mapM_loop___at___00Lean_Meta_Match_Problem_toMessageData_spec__1(v_vars_2014_, v___x_2013_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2047_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2047_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2047_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2028_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__1);
v___x_2029_ = l_List_mapTR_loop___at___00Lean_Meta_Match_Alt_toMessageData_spec__0(v_a_2024_, v___x_2013_);
v___x_2030_ = l_Lean_MessageData_ofList(v___x_2029_);
v___x_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2028_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__3);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2035_ = l_Lean_MessageData_joinSep(v_a_2022_, v___x_2034_);
v___x_2036_ = l_Lean_indentD(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2033_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__6);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = l_Lean_Meta_Match_examplesToMessageData(v_examples_2015_);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_obj_once(&l_Lean_Meta_Match_Alt_toMessageData___closed__5, &l_Lean_Meta_Match_Alt_toMessageData___closed__5_once, _init_l_Lean_Meta_Match_Alt_toMessageData___closed__5);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2043_);
v___x_2045_ = v___x_2026_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_2022_);
lean_dec(v_examples_2015_);
lean_dec(v___x_2013_);
v_a_2048_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2023_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2023_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_examples_2015_);
lean_dec(v_vars_2014_);
lean_dec(v___x_2013_);
v_a_2056_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2021_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2021_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed(lean_object* v_alts_2064_, lean_object* v___x_2065_, lean_object* v_vars_2066_, lean_object* v_examples_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Meta_Match_Problem_toMessageData___lam__0(v_alts_2064_, v___x_2065_, v_vars_2066_, v_examples_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object* v_p_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_vars_2080_; lean_object* v_alts_2081_; lean_object* v_examples_2082_; lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; 
v_vars_2080_ = lean_ctor_get(v_p_2074_, 1);
v_alts_2081_ = lean_ctor_get(v_p_2074_, 2);
v_examples_2082_ = lean_ctor_get(v_p_2074_, 3);
v___x_2083_ = lean_box(0);
lean_inc(v_examples_2082_);
lean_inc(v_vars_2080_);
lean_inc(v_alts_2081_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2084_, 0, v_alts_2081_);
lean_closure_set(v___f_2084_, 1, v___x_2083_);
lean_closure_set(v___f_2084_, 2, v_vars_2080_);
lean_closure_set(v___f_2084_, 3, v_examples_2082_);
v___x_2085_ = l_Lean_Meta_Match_withGoalOf___redArg(v_p_2074_, v___f_2084_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Problem_toMessageData___boxed(lean_object* v_p_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_Match_Problem_toMessageData(v_p_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExampleToMessageData(lean_object* v_cex_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Meta_Match_examplesToMessageData(v_cex_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
if (lean_obj_tag(v_a_2095_) == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = l_List_reverse___redArg(v_a_2096_);
return v___x_2097_;
}
else
{
lean_object* v_head_2098_; lean_object* v_tail_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2108_; 
v_head_2098_ = lean_ctor_get(v_a_2095_, 0);
v_tail_2099_ = lean_ctor_get(v_a_2095_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_a_2095_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2101_ = v_a_2095_;
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_tail_2099_);
lean_inc(v_head_2098_);
lean_dec(v_a_2095_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = l_Lean_Meta_Match_examplesToMessageData(v_head_2098_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v_a_2096_);
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_a_2096_);
v___x_2105_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
v_a_2095_ = v_tail_2099_;
v_a_2096_ = v___x_2105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_counterExamplesToMessageData(lean_object* v_cexs_2109_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2110_ = lean_array_to_list(v_cexs_2109_);
v___x_2111_ = lean_box(0);
v___x_2112_ = l_List_mapTR_loop___at___00Lean_Meta_Match_counterExamplesToMessageData_spec__0(v___x_2110_, v___x_2111_);
v___x_2113_ = lean_obj_once(&l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4, &l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4_once, _init_l_Lean_Meta_Match_Problem_toMessageData___lam__0___closed__4);
v___x_2114_ = l_Lean_MessageData_joinSep(v___x_2112_, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_ref_2121_; lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_ref_2121_ = lean_ctor_get(v___y_2118_, 5);
v___x_2122_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Match_Alt_toMessageData_spec__2(v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_inc(v_ref_2121_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v_ref_2121_);
lean_ctor_set(v___x_2127_, 1, v_a_2123_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg___boxed(lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2138_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__1(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__0));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__3(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_Meta_Match_toPattern___closed__2));
v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_Meta_Match_toPattern___closed__4(void){
_start:
{
lean_object* v___x_2145_; lean_object* v_dummy_2146_; 
v___x_2145_ = lean_box(0);
v_dummy_2146_ = l_Lean_Expr_sort___override(v___x_2145_);
return v_dummy_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_bs_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_bs_2149_);
return v___x_2156_;
}
else
{
lean_object* v_v_2157_; lean_object* v___x_2158_; 
v_v_2157_ = lean_array_uget_borrowed(v_bs_2149_, v_i_2148_);
lean_inc(v_v_2157_);
v___x_2158_ = l_Lean_Meta_Match_toPattern(v_v_2157_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; lean_object* v_bs_x27_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2158_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v_bs_x27_2161_ = lean_array_uset(v_bs_2149_, v_i_2148_, v___x_2160_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2148_, v___x_2162_);
v___x_2164_ = lean_array_uset(v_bs_x27_2161_, v_i_2148_, v_a_2159_);
v_i_2148_ = v___x_2163_;
v_bs_2149_ = v___x_2164_;
goto _start;
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_bs_2149_);
v_a_2166_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2158_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2158_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern(lean_object* v_e_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_inaccessible_x3f(v_e_2174_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Expr_arrayLit_x3f(v_e_2174_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_2174_);
if (lean_obj_tag(v___x_2191_) == 1)
{
lean_object* v_val_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref(v_e_2174_);
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = lean_unsigned_to_nat(2u);
v___x_2194_ = l_Lean_Expr_getAppNumArgs(v_val_2192_);
v___x_2195_ = lean_nat_sub(v___x_2194_, v___x_2193_);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_sub(v___x_2195_, v___x_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = l_Lean_Expr_getRevArg_x21(v_val_2192_, v___x_2197_);
v___x_2199_ = l_Lean_Meta_Match_toPattern(v___x_2198_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2224_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2224_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2224_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_nat_sub(v___x_2194_, v___x_2196_);
v___x_2212_ = lean_nat_sub(v___x_2211_, v___x_2196_);
lean_dec(v___x_2211_);
v___x_2213_ = l_Lean_Expr_getRevArg_x21(v_val_2192_, v___x_2212_);
if (lean_obj_tag(v___x_2213_) == 1)
{
lean_object* v_fvarId_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_fvarId_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_fvarId_2214_);
lean_dec_ref(v___x_2213_);
v___x_2215_ = lean_unsigned_to_nat(3u);
v___x_2216_ = lean_nat_sub(v___x_2194_, v___x_2215_);
lean_dec(v___x_2194_);
v___x_2217_ = lean_nat_sub(v___x_2216_, v___x_2196_);
lean_dec(v___x_2216_);
v___x_2218_ = l_Lean_Expr_getRevArg_x21(v_val_2192_, v___x_2217_);
lean_dec(v_val_2192_);
if (lean_obj_tag(v___x_2218_) == 1)
{
lean_object* v_fvarId_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v_fvarId_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_fvarId_2219_);
lean_dec_ref(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_2220_, 0, v_fvarId_2214_);
lean_ctor_set(v___x_2220_, 1, v_a_2200_);
lean_ctor_set(v___x_2220_, 2, v_fvarId_2219_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2220_);
v___x_2222_ = v___x_2202_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
lean_dec_ref(v___x_2218_);
lean_dec(v_fvarId_2214_);
lean_del_object(v___x_2202_);
lean_dec(v_a_2200_);
v___y_2205_ = v_a_2175_;
v___y_2206_ = v_a_2176_;
v___y_2207_ = v_a_2177_;
v___y_2208_ = v_a_2178_;
goto v___jp_2204_;
}
}
else
{
lean_dec_ref(v___x_2213_);
lean_del_object(v___x_2202_);
lean_dec(v_a_2200_);
lean_dec(v___x_2194_);
lean_dec(v_val_2192_);
v___y_2205_ = v_a_2175_;
v___y_2206_ = v_a_2176_;
v___y_2207_ = v_a_2177_;
v___y_2208_ = v_a_2178_;
goto v___jp_2204_;
}
v___jp_2204_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__3, &l_Lean_Meta_Match_toPattern___closed__3_once, _init_l_Lean_Meta_Match_toPattern___closed__3);
v___x_2210_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2209_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v___x_2210_;
}
}
}
else
{
lean_dec(v___x_2194_);
lean_dec(v_val_2192_);
return v___x_2199_;
}
}
else
{
lean_object* v___x_2225_; 
lean_dec(v___x_2191_);
lean_inc_ref(v_e_2174_);
v___x_2225_ = l_Lean_Meta_isMatchValue(v_e_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2318_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2318_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2318_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_unbox(v_a_2226_);
lean_dec(v_a_2226_);
if (v___x_2230_ == 0)
{
uint8_t v___x_2231_; 
v___x_2231_ = l_Lean_Expr_isFVar(v_e_2174_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
lean_del_object(v___x_2228_);
lean_inc(v_a_2178_);
lean_inc_ref(v_a_2177_);
lean_inc(v_a_2176_);
lean_inc_ref(v_a_2175_);
lean_inc_ref(v_e_2174_);
v___x_2232_ = lean_whnf(v_e_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; uint8_t v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = lean_expr_eqv(v_a_2233_, v_e_2174_);
if (v___x_2234_ == 0)
{
lean_dec_ref(v_e_2174_);
v_e_2174_ = v_a_2233_;
goto _start;
}
else
{
if (v___x_2231_ == 0)
{
lean_object* v___x_2236_; 
lean_dec(v_a_2233_);
v___x_2236_ = l_Lean_Expr_getAppFn(v_e_2174_);
if (lean_obj_tag(v___x_2236_) == 4)
{
lean_object* v_declName_2237_; lean_object* v_us_2238_; lean_object* v___x_2239_; lean_object* v_env_2240_; lean_object* v___x_2241_; 
v_declName_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_declName_2237_);
v_us_2238_ = lean_ctor_get(v___x_2236_, 1);
lean_inc(v_us_2238_);
lean_dec_ref(v___x_2236_);
v___x_2239_ = lean_st_ref_get(v_a_2178_);
v_env_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc_ref(v_env_2240_);
lean_dec(v___x_2239_);
v___x_2241_ = l_Lean_Environment_find_x3f(v_env_2240_, v_declName_2237_, v___x_2231_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_dec(v_us_2238_);
v___y_2181_ = v_a_2175_;
v___y_2182_ = v_a_2176_;
v___y_2183_ = v_a_2177_;
v___y_2184_ = v_a_2178_;
goto v___jp_2180_;
}
else
{
lean_object* v_val_2242_; 
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref(v___x_2241_);
if (lean_obj_tag(v_val_2242_) == 6)
{
lean_object* v_val_2243_; lean_object* v_toConstantVal_2244_; lean_object* v_numParams_2245_; lean_object* v_numFields_2246_; lean_object* v_nargs_2247_; lean_object* v_dummy_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v_val_2243_ = lean_ctor_get(v_val_2242_, 0);
lean_inc_ref(v_val_2243_);
lean_dec_ref(v_val_2242_);
v_toConstantVal_2244_ = lean_ctor_get(v_val_2243_, 0);
lean_inc_ref(v_toConstantVal_2244_);
v_numParams_2245_ = lean_ctor_get(v_val_2243_, 3);
lean_inc(v_numParams_2245_);
v_numFields_2246_ = lean_ctor_get(v_val_2243_, 4);
lean_inc(v_numFields_2246_);
lean_dec_ref(v_val_2243_);
v_nargs_2247_ = l_Lean_Expr_getAppNumArgs(v_e_2174_);
v_dummy_2248_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__4, &l_Lean_Meta_Match_toPattern___closed__4_once, _init_l_Lean_Meta_Match_toPattern___closed__4);
lean_inc(v_nargs_2247_);
v___x_2249_ = lean_mk_array(v_nargs_2247_, v_dummy_2248_);
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_sub(v_nargs_2247_, v___x_2250_);
lean_dec(v_nargs_2247_);
lean_inc_ref(v_e_2174_);
v___x_2252_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2174_, v___x_2249_, v___x_2251_);
v___x_2285_ = lean_array_get_size(v___x_2252_);
v___x_2286_ = lean_nat_add(v_numParams_2245_, v_numFields_2246_);
lean_dec(v_numFields_2246_);
v___x_2287_ = lean_nat_dec_eq(v___x_2285_, v___x_2286_);
lean_dec(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2288_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2289_ = l_Lean_indentExpr(v_e_2174_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2290_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_dec_ref(v___x_2291_);
v___y_2254_ = v_a_2175_;
v___y_2255_ = v_a_2176_;
v___y_2256_ = v_a_2177_;
v___y_2257_ = v_a_2178_;
goto v___jp_2253_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v___x_2252_);
lean_dec(v_numParams_2245_);
lean_dec_ref(v_toConstantVal_2244_);
lean_dec(v_us_2238_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_dec_ref(v_e_2174_);
v___y_2254_ = v_a_2175_;
v___y_2255_ = v_a_2176_;
v___y_2256_ = v_a_2177_;
v___y_2257_ = v_a_2178_;
goto v___jp_2253_;
}
v___jp_2253_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; size_t v_sz_2262_; size_t v___x_2263_; lean_object* v___x_2264_; 
v___x_2258_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2245_);
v___x_2259_ = l_Array_extract___redArg(v___x_2252_, v___x_2258_, v_numParams_2245_);
v___x_2260_ = lean_array_get_size(v___x_2252_);
v___x_2261_ = l_Array_extract___redArg(v___x_2252_, v_numParams_2245_, v___x_2260_);
lean_dec_ref(v___x_2252_);
v_sz_2262_ = lean_array_size(v___x_2261_);
v___x_2263_ = ((size_t)0ULL);
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_2262_, v___x_2263_, v___x_2261_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2276_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2276_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2276_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_name_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v_name_2269_ = lean_ctor_get(v_toConstantVal_2244_, 0);
lean_inc(v_name_2269_);
lean_dec_ref(v_toConstantVal_2244_);
v___x_2270_ = lean_array_to_list(v___x_2259_);
v___x_2271_ = lean_array_to_list(v_a_2265_);
v___x_2272_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2272_, 0, v_name_2269_);
lean_ctor_set(v___x_2272_, 1, v_us_2238_);
lean_ctor_set(v___x_2272_, 2, v___x_2270_);
lean_ctor_set(v___x_2272_, 3, v___x_2271_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2272_);
v___x_2274_ = v___x_2267_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v___x_2259_);
lean_dec_ref(v_toConstantVal_2244_);
lean_dec(v_us_2238_);
v_a_2277_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2264_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2264_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
else
{
lean_dec(v_val_2242_);
lean_dec(v_us_2238_);
v___y_2181_ = v_a_2175_;
v___y_2182_ = v_a_2176_;
v___y_2183_ = v_a_2177_;
v___y_2184_ = v_a_2178_;
goto v___jp_2180_;
}
}
}
else
{
lean_dec_ref(v___x_2236_);
v___y_2181_ = v_a_2175_;
v___y_2182_ = v_a_2176_;
v___y_2183_ = v_a_2177_;
v___y_2184_ = v_a_2178_;
goto v___jp_2180_;
}
}
else
{
lean_dec_ref(v_e_2174_);
v_e_2174_ = v_a_2233_;
goto _start;
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_e_2174_);
v_a_2301_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2232_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2232_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2309_ = l_Lean_Expr_fvarId_x21(v_e_2174_);
lean_dec_ref(v_e_2174_);
v___x_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2310_);
v___x_2312_ = v___x_2228_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_e_2174_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2314_);
v___x_2316_ = v___x_2228_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_e_2174_);
v_a_2319_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2225_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2225_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
else
{
lean_object* v_val_2327_; lean_object* v_fst_2328_; lean_object* v_snd_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v_e_2174_);
v_val_2327_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_val_2327_);
lean_dec_ref(v___x_2190_);
v_fst_2328_ = lean_ctor_get(v_val_2327_, 0);
v_snd_2329_ = lean_ctor_get(v_val_2327_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_val_2327_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2331_ = v_val_2327_;
v_isShared_2332_ = v_isSharedCheck_2354_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_snd_2329_);
lean_inc(v_fst_2328_);
lean_dec(v_val_2327_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2354_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_snd_2329_, v___x_2333_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2345_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2345_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2345_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set_tag(v___x_2331_, 4);
lean_ctor_set(v___x_2331_, 1, v_a_2335_);
v___x_2340_ = v___x_2331_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_fst_2328_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2340_);
v___x_2342_ = v___x_2337_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_del_object(v___x_2331_);
lean_dec(v_fst_2328_);
v_a_2346_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2334_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2334_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
else
{
lean_object* v_val_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v_e_2174_);
v_val_2355_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2357_ = v___x_2189_;
v_isShared_2358_ = v_isSharedCheck_2363_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_val_2355_);
lean_dec(v___x_2189_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2363_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 0);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_val_2355_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
v___jp_2180_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2185_ = lean_obj_once(&l_Lean_Meta_Match_toPattern___closed__1, &l_Lean_Meta_Match_toPattern___closed__1_once, _init_l_Lean_Meta_Match_toPattern___closed__1);
v___x_2186_ = l_Lean_indentExpr(v_e_2174_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v___x_2187_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
if (lean_obj_tag(v_x_2364_) == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = l_List_reverse___redArg(v_x_2365_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v_head_2373_; lean_object* v_tail_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2392_; 
v_head_2373_ = lean_ctor_get(v_x_2364_, 0);
v_tail_2374_ = lean_ctor_get(v_x_2364_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_x_2364_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2376_ = v_x_2364_;
v_isShared_2377_ = v_isSharedCheck_2392_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_tail_2374_);
lean_inc(v_head_2373_);
lean_dec(v_x_2364_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2392_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Meta_Match_toPattern(v_head_2373_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2378_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v_x_2365_);
lean_ctor_set(v___x_2376_, 0, v_a_2379_);
v___x_2381_ = v___x_2376_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2379_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_x_2365_);
v___x_2381_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
v_x_2364_ = v_tail_2374_;
v_x_2365_ = v___x_2381_;
goto _start;
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2376_);
lean_dec(v_tail_2374_);
lean_dec(v_x_2365_);
v_a_2384_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2378_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2378_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2___boxed(lean_object* v_x_2393_, lean_object* v_x_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_List_mapM_loop___at___00Lean_Meta_Match_toPattern_spec__2(v_x_2393_, v_x_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1___boxed(lean_object* v_sz_2401_, lean_object* v_i_2402_, lean_object* v_bs_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
size_t v_sz_boxed_2409_; size_t v_i_boxed_2410_; lean_object* v_res_2411_; 
v_sz_boxed_2409_ = lean_unbox_usize(v_sz_2401_);
lean_dec(v_sz_2401_);
v_i_boxed_2410_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_toPattern_spec__1(v_sz_boxed_2409_, v_i_boxed_2410_, v_bs_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_toPattern___boxed(lean_object* v_e_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Meta_Match_toPattern(v_e_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(lean_object* v_00_u03b1_2419_, lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___redArg(v_msg_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_msg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_throwError___at___00Lean_Meta_Match_toPattern_spec__0(v_00_u03b1_2427_, v_msg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2434_;
}
}
static lean_object* _init_l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2442_ = lean_string_utf8_byte_size(v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object* v_s_2443_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2444_ = ((lean_object*)(l_Lean_Meta_Match_congrEqnThmSuffixBasePrefix___closed__0));
v___x_2445_ = lean_string_utf8_byte_size(v_s_2443_);
v___x_2446_ = lean_obj_once(&l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0, &l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0_once, _init_l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___closed__0);
v___x_2447_ = lean_nat_dec_le(v___x_2446_, v___x_2445_);
if (v___x_2447_ == 0)
{
lean_dec_ref(v_s_2443_);
return v___x_2447_;
}
else
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
v___x_2449_ = lean_string_memcmp(v_s_2443_, v___x_2444_, v___x_2448_, v___x_2448_, v___x_2446_);
if (v___x_2449_ == 0)
{
lean_dec_ref(v_s_2443_);
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2450_ = lean_unsigned_to_nat(9u);
lean_inc_ref(v_s_2443_);
v___x_2451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2451_, 0, v_s_2443_);
lean_ctor_set(v___x_2451_, 1, v___x_2448_);
lean_ctor_set(v___x_2451_, 2, v___x_2445_);
v___x_2452_ = l_String_Slice_Pos_nextn(v___x_2451_, v___x_2448_, v___x_2450_);
lean_dec_ref(v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2453_, 0, v_s_2443_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_ctor_set(v___x_2453_, 2, v___x_2445_);
v___x_2454_ = l_String_Slice_isNat(v___x_2453_);
lean_dec_ref(v___x_2453_);
return v___x_2454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCongrEqnReservedNameSuffix___boxed(lean_object* v_s_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_s_2455_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
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
