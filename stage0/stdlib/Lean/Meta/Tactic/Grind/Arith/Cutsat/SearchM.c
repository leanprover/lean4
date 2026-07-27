// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7;
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_d_8_; lean_object* v___x_9_; 
v_d_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_d_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_d_8_);
return v___x_9_;
}
else
{
lean_object* v_s_10_; lean_object* v_hs_11_; lean_object* v_decVars_12_; lean_object* v___x_13_; 
v_s_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_s_10_);
v_hs_11_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_hs_11_);
v_decVars_12_ = lean_ctor_get(v_t_6_, 2);
lean_inc(v_decVars_12_);
lean_dec_ref_known(v_t_6_, 3);
v___x_13_ = lean_apply_3(v_k_7_, v_s_10_, v_hs_11_, v_decVars_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object* v_t_26_, lean_object* v_diseq_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_26_, v_diseq_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_diseq_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_30_, v_diseq_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object* v_t_34_, lean_object* v_cooper_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_34_, v_cooper_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_cooper_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_38_, v_cooper_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_box(0);
v___x_50_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3));
v___x_51_ = l_Lean_Expr_const___override(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5);
v___x_55_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6);
v___x_59_ = 0;
v___x_60_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*3, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_box(1);
v___x_64_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8));
v___x_65_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
v___x_70_ = lean_box(0);
v___x_71_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(uint8_t v_x_75_){
_start:
{
if (v_x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(0u);
return v___x_76_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(1u);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___boxed(lean_object* v_x_78_){
_start:
{
uint8_t v_x_boxed_79_; lean_object* v_res_80_; 
v_x_boxed_79_ = lean_unbox(v_x_78_);
v_res_80_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_boxed_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(uint8_t v_x_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx___boxed(lean_object* v_x_83_){
_start:
{
uint8_t v_x_4__boxed_84_; lean_object* v_res_85_; 
v_x_4__boxed_84_ = lean_unbox(v_x_83_);
v_res_85_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(v_x_4__boxed_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object* v_k_86_){
_start:
{
lean_inc(v_k_86_);
return v_k_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object* v_k_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(v_k_87_);
lean_dec(v_k_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object* v_motive_89_, lean_object* v_ctorIdx_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_k_93_){
_start:
{
lean_inc(v_k_93_);
return v_k_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object* v_motive_94_, lean_object* v_ctorIdx_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_k_98_){
_start:
{
uint8_t v_t_boxed_99_; lean_object* v_res_100_; 
v_t_boxed_99_ = lean_unbox(v_t_96_);
v_res_100_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(v_motive_94_, v_ctorIdx_95_, v_t_boxed_99_, v_h_97_, v_k_98_);
lean_dec(v_k_98_);
lean_dec(v_ctorIdx_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object* v_rat_101_){
_start:
{
lean_inc(v_rat_101_);
return v_rat_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object* v_rat_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(v_rat_102_);
lean_dec(v_rat_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object* v_motive_104_, uint8_t v_t_105_, lean_object* v_h_106_, lean_object* v_rat_107_){
_start:
{
lean_inc(v_rat_107_);
return v_rat_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_rat_111_){
_start:
{
uint8_t v_t_boxed_112_; lean_object* v_res_113_; 
v_t_boxed_112_ = lean_unbox(v_t_109_);
v_res_113_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(v_motive_108_, v_t_boxed_112_, v_h_110_, v_rat_111_);
lean_dec(v_rat_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object* v_int_114_){
_start:
{
lean_inc(v_int_114_);
return v_int_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object* v_int_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(v_int_115_);
lean_dec(v_int_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object* v_motive_117_, uint8_t v_t_118_, lean_object* v_h_119_, lean_object* v_int_120_){
_start:
{
lean_inc(v_int_120_);
return v_int_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_int_124_){
_start:
{
uint8_t v_t_boxed_125_; lean_object* v_res_126_; 
v_t_boxed_125_ = lean_unbox(v_t_122_);
v_res_126_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(v_motive_121_, v_t_boxed_125_, v_h_123_, v_int_124_);
lean_dec(v_int_124_);
return v_res_126_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind(void){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t v_x_129_, uint8_t v_y_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_129_);
v___x_132_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_y_130_);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_x_17__boxed_136_; uint8_t v_y_18__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_17__boxed_136_ = lean_unbox(v_x_134_);
v_y_18__boxed_137_ = lean_unbox(v_y_135_);
v_res_138_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_x_17__boxed_136_, v_y_18__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t v_a_142_){
_start:
{
uint8_t v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = 0;
v___x_145_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_a_142_, v___x_144_);
v___x_146_ = lean_box(v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
uint8_t v_a_boxed_150_; lean_object* v_res_151_; 
v_a_boxed_150_ = lean_unbox(v_a_148_);
v_res_151_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_152_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
uint8_t v_a_boxed_179_; lean_object* v_res_180_; 
v_a_boxed_179_ = lean_unbox(v_a_166_);
v_res_180_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(v_a_boxed_179_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec(v_a_168_);
lean_dec(v_a_167_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v_cases_184_; lean_object* v_decVars_185_; lean_object* v_steps_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_197_; 
v___x_183_ = lean_st_ref_take(v_a_181_);
v_cases_184_ = lean_ctor_get(v___x_183_, 0);
v_decVars_185_ = lean_ctor_get(v___x_183_, 1);
v_steps_186_ = lean_ctor_get(v___x_183_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_197_ == 0)
{
v___x_188_ = v___x_183_;
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_steps_186_);
lean_inc(v_decVars_185_);
lean_inc(v_cases_184_);
lean_dec(v___x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
uint8_t v___x_190_; lean_object* v___x_192_; 
v___x_190_ = 0;
if (v_isShared_189_ == 0)
{
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_cases_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_decVars_185_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_steps_186_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*3, v___x_190_);
v___x_193_ = lean_st_ref_set(v_a_181_, v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_198_);
lean_dec(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_202_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
uint8_t v_a_boxed_228_; lean_object* v_res_229_; 
v_a_boxed_228_ = lean_unbox(v_a_215_);
v_res_229_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(v_a_boxed_228_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec(v_a_217_);
lean_dec(v_a_216_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; lean_object* v_cases_236_; uint8_t v_precise_237_; lean_object* v_decVars_238_; lean_object* v_steps_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_283_; 
v___x_235_ = lean_st_ref_take(v_a_230_);
v_cases_236_ = lean_ctor_get(v___x_235_, 0);
v_precise_237_ = lean_ctor_get_uint8(v___x_235_, sizeof(void*)*3);
v_decVars_238_ = lean_ctor_get(v___x_235_, 1);
v_steps_239_ = lean_ctor_get(v___x_235_, 2);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_283_ == 0)
{
v___x_241_ = v___x_235_;
v_isShared_242_ = v_isSharedCheck_283_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_steps_239_);
lean_inc(v_decVars_238_);
lean_inc(v_cases_236_);
lean_dec(v___x_235_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_283_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_steps_239_, v___x_243_);
lean_dec(v_steps_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 2, v___x_244_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_cases_236_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_decVars_238_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v___x_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*3, v_precise_237_);
v___x_246_ = v_reuseFailAlloc_282_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_st_ref_set(v_a_230_, v___x_246_);
v___x_248_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_231_, v_a_233_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = lean_st_ref_get(v_a_230_);
v___x_251_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_232_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_265_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_265_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_265_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_265_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_liaSteps_256_; lean_object* v_steps_257_; lean_object* v_steps_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v_liaSteps_256_ = lean_ctor_get(v_a_252_, 8);
lean_inc(v_liaSteps_256_);
lean_dec(v_a_252_);
v_steps_257_ = lean_ctor_get(v_a_249_, 15);
lean_inc(v_steps_257_);
lean_dec(v_a_249_);
v_steps_258_ = lean_ctor_get(v___x_250_, 2);
lean_inc(v_steps_258_);
lean_dec(v___x_250_);
v___x_259_ = lean_nat_add(v_steps_257_, v_steps_258_);
lean_dec(v_steps_258_);
lean_dec(v_steps_257_);
v___x_260_ = lean_nat_dec_lt(v_liaSteps_256_, v___x_259_);
lean_dec(v___x_259_);
lean_dec(v_liaSteps_256_);
v___x_261_ = lean_box(v___x_260_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_261_);
v___x_263_ = v___x_254_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec(v___x_250_);
lean_dec(v_a_249_);
v_a_266_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_251_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_251_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_248_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_248_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec_ref(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec(v_a_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_291_, v_a_292_, v_a_294_, v_a_300_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
uint8_t v_a_boxed_317_; lean_object* v_res_318_; 
v_a_boxed_317_ = lean_unbox(v_a_304_);
v_res_318_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(v_a_boxed_317_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec(v_a_306_);
lean_dec(v_a_305_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object* v_steps_319_, lean_object* v_s_320_){
_start:
{
lean_object* v_vars_321_; lean_object* v_varMap_322_; lean_object* v_vars_x27_323_; lean_object* v_varMap_x27_324_; lean_object* v_natToIntMap_325_; lean_object* v_natDef_326_; lean_object* v_dvds_327_; lean_object* v_lowers_328_; lean_object* v_uppers_329_; lean_object* v_diseqs_330_; lean_object* v_elimEqs_331_; lean_object* v_elimStack_332_; lean_object* v_occurs_333_; lean_object* v_assignment_334_; lean_object* v_nextCnstrId_335_; uint8_t v_caseSplits_336_; lean_object* v_steps_337_; lean_object* v_conflict_x3f_338_; lean_object* v_diseqSplits_339_; lean_object* v_divMod_340_; lean_object* v_toIntIds_341_; lean_object* v_toIntInfos_342_; lean_object* v_toIntTermMap_343_; lean_object* v_toIntVarMap_344_; uint8_t v_usedCommRing_345_; lean_object* v_nonlinearOccs_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
v_vars_321_ = lean_ctor_get(v_s_320_, 0);
v_varMap_322_ = lean_ctor_get(v_s_320_, 1);
v_vars_x27_323_ = lean_ctor_get(v_s_320_, 2);
v_varMap_x27_324_ = lean_ctor_get(v_s_320_, 3);
v_natToIntMap_325_ = lean_ctor_get(v_s_320_, 4);
v_natDef_326_ = lean_ctor_get(v_s_320_, 5);
v_dvds_327_ = lean_ctor_get(v_s_320_, 6);
v_lowers_328_ = lean_ctor_get(v_s_320_, 7);
v_uppers_329_ = lean_ctor_get(v_s_320_, 8);
v_diseqs_330_ = lean_ctor_get(v_s_320_, 9);
v_elimEqs_331_ = lean_ctor_get(v_s_320_, 10);
v_elimStack_332_ = lean_ctor_get(v_s_320_, 11);
v_occurs_333_ = lean_ctor_get(v_s_320_, 12);
v_assignment_334_ = lean_ctor_get(v_s_320_, 13);
v_nextCnstrId_335_ = lean_ctor_get(v_s_320_, 14);
v_caseSplits_336_ = lean_ctor_get_uint8(v_s_320_, sizeof(void*)*24);
v_steps_337_ = lean_ctor_get(v_s_320_, 15);
v_conflict_x3f_338_ = lean_ctor_get(v_s_320_, 16);
v_diseqSplits_339_ = lean_ctor_get(v_s_320_, 17);
v_divMod_340_ = lean_ctor_get(v_s_320_, 18);
v_toIntIds_341_ = lean_ctor_get(v_s_320_, 19);
v_toIntInfos_342_ = lean_ctor_get(v_s_320_, 20);
v_toIntTermMap_343_ = lean_ctor_get(v_s_320_, 21);
v_toIntVarMap_344_ = lean_ctor_get(v_s_320_, 22);
v_usedCommRing_345_ = lean_ctor_get_uint8(v_s_320_, sizeof(void*)*24 + 1);
v_nonlinearOccs_346_ = lean_ctor_get(v_s_320_, 23);
v_isSharedCheck_354_ = !lean_is_exclusive(v_s_320_);
if (v_isSharedCheck_354_ == 0)
{
v___x_348_ = v_s_320_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_nonlinearOccs_346_);
lean_inc(v_toIntVarMap_344_);
lean_inc(v_toIntTermMap_343_);
lean_inc(v_toIntInfos_342_);
lean_inc(v_toIntIds_341_);
lean_inc(v_divMod_340_);
lean_inc(v_diseqSplits_339_);
lean_inc(v_conflict_x3f_338_);
lean_inc(v_steps_337_);
lean_inc(v_nextCnstrId_335_);
lean_inc(v_assignment_334_);
lean_inc(v_occurs_333_);
lean_inc(v_elimStack_332_);
lean_inc(v_elimEqs_331_);
lean_inc(v_diseqs_330_);
lean_inc(v_uppers_329_);
lean_inc(v_lowers_328_);
lean_inc(v_dvds_327_);
lean_inc(v_natDef_326_);
lean_inc(v_natToIntMap_325_);
lean_inc(v_varMap_x27_324_);
lean_inc(v_vars_x27_323_);
lean_inc(v_varMap_322_);
lean_inc(v_vars_321_);
lean_dec(v_s_320_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_nat_add(v_steps_337_, v_steps_319_);
lean_dec(v_steps_337_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 15, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_vars_321_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_varMap_322_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_vars_x27_323_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_varMap_x27_324_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_natToIntMap_325_);
lean_ctor_set(v_reuseFailAlloc_353_, 5, v_natDef_326_);
lean_ctor_set(v_reuseFailAlloc_353_, 6, v_dvds_327_);
lean_ctor_set(v_reuseFailAlloc_353_, 7, v_lowers_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 8, v_uppers_329_);
lean_ctor_set(v_reuseFailAlloc_353_, 9, v_diseqs_330_);
lean_ctor_set(v_reuseFailAlloc_353_, 10, v_elimEqs_331_);
lean_ctor_set(v_reuseFailAlloc_353_, 11, v_elimStack_332_);
lean_ctor_set(v_reuseFailAlloc_353_, 12, v_occurs_333_);
lean_ctor_set(v_reuseFailAlloc_353_, 13, v_assignment_334_);
lean_ctor_set(v_reuseFailAlloc_353_, 14, v_nextCnstrId_335_);
lean_ctor_set(v_reuseFailAlloc_353_, 15, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 16, v_conflict_x3f_338_);
lean_ctor_set(v_reuseFailAlloc_353_, 17, v_diseqSplits_339_);
lean_ctor_set(v_reuseFailAlloc_353_, 18, v_divMod_340_);
lean_ctor_set(v_reuseFailAlloc_353_, 19, v_toIntIds_341_);
lean_ctor_set(v_reuseFailAlloc_353_, 20, v_toIntInfos_342_);
lean_ctor_set(v_reuseFailAlloc_353_, 21, v_toIntTermMap_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 22, v_toIntVarMap_344_);
lean_ctor_set(v_reuseFailAlloc_353_, 23, v_nonlinearOccs_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_353_, sizeof(void*)*24, v_caseSplits_336_);
lean_ctor_set_uint8(v_reuseFailAlloc_353_, sizeof(void*)*24 + 1, v_usedCommRing_345_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object* v_steps_355_, lean_object* v_s_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(v_steps_355_, v_s_356_);
lean_dec(v_steps_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_steps_362_; lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = lean_st_ref_get(v_a_358_);
v_steps_362_ = lean_ctor_get(v___x_361_, 2);
lean_inc(v_steps_362_);
lean_dec(v___x_361_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_363_, 0, v_steps_362_);
v___x_364_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_365_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_364_, v___f_363_, v_a_359_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec(v_a_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_371_, v_a_372_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
uint8_t v_a_boxed_397_; lean_object* v_res_398_; 
v_a_boxed_397_ = lean_unbox(v_a_384_);
v_res_398_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_boxed_397_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec(v_a_386_);
lean_dec(v_a_385_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* v_s_399_){
_start:
{
lean_object* v_vars_400_; lean_object* v_varMap_401_; lean_object* v_vars_x27_402_; lean_object* v_varMap_x27_403_; lean_object* v_natToIntMap_404_; lean_object* v_natDef_405_; lean_object* v_dvds_406_; lean_object* v_lowers_407_; lean_object* v_uppers_408_; lean_object* v_diseqs_409_; lean_object* v_elimEqs_410_; lean_object* v_elimStack_411_; lean_object* v_occurs_412_; lean_object* v_assignment_413_; lean_object* v_nextCnstrId_414_; lean_object* v_steps_415_; lean_object* v_conflict_x3f_416_; lean_object* v_diseqSplits_417_; lean_object* v_divMod_418_; lean_object* v_toIntIds_419_; lean_object* v_toIntInfos_420_; lean_object* v_toIntTermMap_421_; lean_object* v_toIntVarMap_422_; uint8_t v_usedCommRing_423_; lean_object* v_nonlinearOccs_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_432_; 
v_vars_400_ = lean_ctor_get(v_s_399_, 0);
v_varMap_401_ = lean_ctor_get(v_s_399_, 1);
v_vars_x27_402_ = lean_ctor_get(v_s_399_, 2);
v_varMap_x27_403_ = lean_ctor_get(v_s_399_, 3);
v_natToIntMap_404_ = lean_ctor_get(v_s_399_, 4);
v_natDef_405_ = lean_ctor_get(v_s_399_, 5);
v_dvds_406_ = lean_ctor_get(v_s_399_, 6);
v_lowers_407_ = lean_ctor_get(v_s_399_, 7);
v_uppers_408_ = lean_ctor_get(v_s_399_, 8);
v_diseqs_409_ = lean_ctor_get(v_s_399_, 9);
v_elimEqs_410_ = lean_ctor_get(v_s_399_, 10);
v_elimStack_411_ = lean_ctor_get(v_s_399_, 11);
v_occurs_412_ = lean_ctor_get(v_s_399_, 12);
v_assignment_413_ = lean_ctor_get(v_s_399_, 13);
v_nextCnstrId_414_ = lean_ctor_get(v_s_399_, 14);
v_steps_415_ = lean_ctor_get(v_s_399_, 15);
v_conflict_x3f_416_ = lean_ctor_get(v_s_399_, 16);
v_diseqSplits_417_ = lean_ctor_get(v_s_399_, 17);
v_divMod_418_ = lean_ctor_get(v_s_399_, 18);
v_toIntIds_419_ = lean_ctor_get(v_s_399_, 19);
v_toIntInfos_420_ = lean_ctor_get(v_s_399_, 20);
v_toIntTermMap_421_ = lean_ctor_get(v_s_399_, 21);
v_toIntVarMap_422_ = lean_ctor_get(v_s_399_, 22);
v_usedCommRing_423_ = lean_ctor_get_uint8(v_s_399_, sizeof(void*)*24 + 1);
v_nonlinearOccs_424_ = lean_ctor_get(v_s_399_, 23);
v_isSharedCheck_432_ = !lean_is_exclusive(v_s_399_);
if (v_isSharedCheck_432_ == 0)
{
v___x_426_ = v_s_399_;
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_nonlinearOccs_424_);
lean_inc(v_toIntVarMap_422_);
lean_inc(v_toIntTermMap_421_);
lean_inc(v_toIntInfos_420_);
lean_inc(v_toIntIds_419_);
lean_inc(v_divMod_418_);
lean_inc(v_diseqSplits_417_);
lean_inc(v_conflict_x3f_416_);
lean_inc(v_steps_415_);
lean_inc(v_nextCnstrId_414_);
lean_inc(v_assignment_413_);
lean_inc(v_occurs_412_);
lean_inc(v_elimStack_411_);
lean_inc(v_elimEqs_410_);
lean_inc(v_diseqs_409_);
lean_inc(v_uppers_408_);
lean_inc(v_lowers_407_);
lean_inc(v_dvds_406_);
lean_inc(v_natDef_405_);
lean_inc(v_natToIntMap_404_);
lean_inc(v_varMap_x27_403_);
lean_inc(v_vars_x27_402_);
lean_inc(v_varMap_401_);
lean_inc(v_vars_400_);
lean_dec(v_s_399_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; lean_object* v___x_430_; 
v___x_428_ = 1;
if (v_isShared_427_ == 0)
{
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_vars_400_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_varMap_401_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_vars_x27_402_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_varMap_x27_403_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_natToIntMap_404_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_natDef_405_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_dvds_406_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_lowers_407_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_uppers_408_);
lean_ctor_set(v_reuseFailAlloc_431_, 9, v_diseqs_409_);
lean_ctor_set(v_reuseFailAlloc_431_, 10, v_elimEqs_410_);
lean_ctor_set(v_reuseFailAlloc_431_, 11, v_elimStack_411_);
lean_ctor_set(v_reuseFailAlloc_431_, 12, v_occurs_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 13, v_assignment_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 14, v_nextCnstrId_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 15, v_steps_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 16, v_conflict_x3f_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 17, v_diseqSplits_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 18, v_divMod_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 19, v_toIntIds_419_);
lean_ctor_set(v_reuseFailAlloc_431_, 20, v_toIntInfos_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 21, v_toIntTermMap_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 22, v_toIntVarMap_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 23, v_nonlinearOccs_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*24 + 1, v_usedCommRing_423_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*24, v___x_428_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v_ngen_436_; lean_object* v_namePrefix_437_; lean_object* v_idx_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_467_; 
v___x_435_ = lean_st_ref_get(v___y_433_);
v_ngen_436_ = lean_ctor_get(v___x_435_, 2);
lean_inc_ref(v_ngen_436_);
lean_dec(v___x_435_);
v_namePrefix_437_ = lean_ctor_get(v_ngen_436_, 0);
v_idx_438_ = lean_ctor_get(v_ngen_436_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_ngen_436_);
if (v_isSharedCheck_467_ == 0)
{
v___x_440_ = v_ngen_436_;
v_isShared_441_ = v_isSharedCheck_467_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_idx_438_);
lean_inc(v_namePrefix_437_);
lean_dec(v_ngen_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_467_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_env_443_; lean_object* v_nextMacroScope_444_; lean_object* v_auxDeclNGen_445_; lean_object* v_traceState_446_; lean_object* v_cache_447_; lean_object* v_messages_448_; lean_object* v_infoState_449_; lean_object* v_snapshotTasks_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_465_; 
v___x_442_ = lean_st_ref_take(v___y_433_);
v_env_443_ = lean_ctor_get(v___x_442_, 0);
v_nextMacroScope_444_ = lean_ctor_get(v___x_442_, 1);
v_auxDeclNGen_445_ = lean_ctor_get(v___x_442_, 3);
v_traceState_446_ = lean_ctor_get(v___x_442_, 4);
v_cache_447_ = lean_ctor_get(v___x_442_, 5);
v_messages_448_ = lean_ctor_get(v___x_442_, 6);
v_infoState_449_ = lean_ctor_get(v___x_442_, 7);
v_snapshotTasks_450_ = lean_ctor_get(v___x_442_, 8);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___x_442_, 2);
lean_dec(v_unused_466_);
v___x_452_ = v___x_442_;
v_isShared_453_ = v_isSharedCheck_465_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snapshotTasks_450_);
lean_inc(v_infoState_449_);
lean_inc(v_messages_448_);
lean_inc(v_cache_447_);
lean_inc(v_traceState_446_);
lean_inc(v_auxDeclNGen_445_);
lean_inc(v_nextMacroScope_444_);
lean_inc(v_env_443_);
lean_dec(v___x_442_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_465_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_r_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_idx_438_);
lean_inc(v_namePrefix_437_);
v_r_454_ = l_Lean_Name_num___override(v_namePrefix_437_, v_idx_438_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v_idx_438_, v___x_455_);
lean_dec(v_idx_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_456_);
v___x_458_ = v___x_440_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_namePrefix_437_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_464_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 2, v___x_458_);
v___x_460_ = v___x_452_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_env_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_nextMacroScope_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_auxDeclNGen_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_traceState_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_cache_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_messages_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_infoState_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_snapshotTasks_450_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_set(v___y_433_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_r_454_);
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_468_);
lean_dec(v___y_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v___x_484_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_482_);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___y_12375__boxed_506_; lean_object* v_res_507_; 
v___y_12375__boxed_506_ = lean_unbox(v___y_493_);
v_res_507_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_12375__boxed_506_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* v_kind_509_, uint8_t v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_512_, v_a_520_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v_cases_528_; uint8_t v_precise_529_; lean_object* v_decVars_530_; lean_object* v_steps_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_561_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_st_ref_take(v_a_511_);
v_cases_528_ = lean_ctor_get(v___x_527_, 0);
v_precise_529_ = lean_ctor_get_uint8(v___x_527_, sizeof(void*)*3);
v_decVars_530_ = lean_ctor_get(v___x_527_, 1);
v_steps_531_ = lean_ctor_get(v___x_527_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_561_ == 0)
{
v___x_533_ = v___x_527_;
v_isShared_534_ = v_isSharedCheck_561_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_steps_531_);
lean_inc(v_decVars_530_);
lean_inc(v_cases_528_);
lean_dec(v___x_527_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_561_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
lean_inc_n(v_a_524_, 2);
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v_kind_509_);
lean_ctor_set(v___x_535_, 1, v_a_524_);
lean_ctor_set(v___x_535_, 2, v_a_526_);
v___x_536_ = l_Lean_PersistentArray_push___redArg(v_cases_528_, v___x_535_);
v___x_537_ = l_Lean_FVarIdSet_insert(v_decVars_530_, v_a_524_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_537_);
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_539_ = v___x_533_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_steps_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, sizeof(void*)*3, v_precise_529_);
v___x_539_ = v_reuseFailAlloc_560_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_st_ref_set(v_a_511_, v___x_539_);
v___f_541_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0));
v___x_542_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_543_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_542_, v___f_541_, v_a_512_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___x_543_, 0);
lean_dec(v_unused_551_);
v___x_545_ = v___x_543_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_dec(v___x_543_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_a_524_);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_524_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_a_524_);
v_a_552_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_543_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_543_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_524_);
lean_dec_ref(v_kind_509_);
v_a_562_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_525_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_525_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_dec_ref(v_kind_509_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* v_kind_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
uint8_t v_a_boxed_584_; lean_object* v_res_585_; 
v_a_boxed_584_ = lean_unbox(v_a_571_);
v_res_585_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_570_, v_a_boxed_584_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec(v_a_573_);
lean_dec(v_a_572_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
uint8_t v___y_12527__boxed_613_; lean_object* v_res_614_; 
v___y_12527__boxed_613_ = lean_unbox(v___y_600_);
v_res_614_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12527__boxed_613_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
lean_dec(v___y_601_);
return v_res_614_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase);
l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default();
l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
}
#ifdef __cplusplus
}
#endif
