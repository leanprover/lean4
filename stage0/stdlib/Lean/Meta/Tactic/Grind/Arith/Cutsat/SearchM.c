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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_d_7_; lean_object* v___x_8_; 
v_d_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_d_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_d_7_);
return v___x_8_;
}
else
{
lean_object* v_s_9_; lean_object* v_hs_10_; lean_object* v_decVars_11_; lean_object* v___x_12_; 
v_s_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_s_9_);
v_hs_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_hs_10_);
v_decVars_11_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_decVars_11_);
lean_dec_ref_known(v_t_5_, 3);
v___x_12_ = lean_apply_3(v_k_6_, v_s_9_, v_hs_10_, v_decVars_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(lean_object* v_t_25_, lean_object* v_diseq_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_25_, v_diseq_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_diseq_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_29_, v_diseq_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(lean_object* v_t_33_, lean_object* v_cooper_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_33_, v_cooper_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_cooper_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_37_, v_cooper_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_box(0);
v___x_49_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3));
v___x_50_ = l_Lean_Expr_const___override(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5);
v___x_54_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_box(0);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6);
v___x_58_ = 0;
v___x_59_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*3, v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_box(1);
v___x_63_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8));
v___x_64_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7);
v___x_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
v___x_69_ = lean_box(0);
v___x_70_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
return v___x_73_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(uint8_t v_x_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(v_x_74_);
v___x_76_ = lean_obj_tag_nat(v___x_75_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_74_ = stack[0].m_num;
lean_object* v_res_77_;
v_res_77_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(v_x_74_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl___boxed(lean_object* v_x_78_){
_start:
{
uint8_t v_x_4__boxed_79_; lean_object* v_res_80_; 
v_x_4__boxed_79_ = lean_unbox(v_x_78_);
v_res_80_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___impl(v_x_4__boxed_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(lean_object* v_k_81_){
_start:
{
lean_inc(v_k_81_);
return v_k_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(lean_object* v_k_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(v_k_82_);
lean_dec(v_k_82_);
return v_res_83_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object* v_motive_84_, lean_object* v_ctorIdx_85_, uint8_t v_t_86_, lean_object* v_h_87_, lean_object* v_k_88_){
_start:
{
lean_inc(v_k_88_);
return v_k_88_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_85_ = stack[1].m_obj;
uint8_t v_t_86_ = stack[2].m_num;
lean_object* v_k_88_ = stack[4].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_box(0), v_ctorIdx_85_, v_t_86_, lean_box(0), v_k_88_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object* v_motive_90_, lean_object* v_ctorIdx_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_k_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(v_motive_90_, v_ctorIdx_91_, v_t_boxed_95_, v_h_93_, v_k_94_);
lean_dec(v_k_94_);
lean_dec(v_ctorIdx_91_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object* v_rat_97_){
_start:
{
lean_inc(v_rat_97_);
return v_rat_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object* v_rat_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(v_rat_98_);
lean_dec(v_rat_98_);
return v_res_99_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object* v_motive_100_, uint8_t v_t_101_, lean_object* v_h_102_, lean_object* v_rat_103_){
_start:
{
lean_inc(v_rat_103_);
return v_rat_103_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_101_ = stack[1].m_num;
lean_object* v_rat_103_ = stack[3].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_box(0), v_t_101_, lean_box(0), v_rat_103_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_rat_108_){
_start:
{
uint8_t v_t_boxed_109_; lean_object* v_res_110_; 
v_t_boxed_109_ = lean_unbox(v_t_106_);
v_res_110_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(v_motive_105_, v_t_boxed_109_, v_h_107_, v_rat_108_);
lean_dec(v_rat_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object* v_int_111_){
_start:
{
lean_inc(v_int_111_);
return v_int_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object* v_int_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(v_int_112_);
lean_dec(v_int_112_);
return v_res_113_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object* v_motive_114_, uint8_t v_t_115_, lean_object* v_h_116_, lean_object* v_int_117_){
_start:
{
lean_inc(v_int_117_);
return v_int_117_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_115_ = stack[1].m_num;
lean_object* v_int_117_ = stack[3].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_box(0), v_t_115_, lean_box(0), v_int_117_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_int_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_int_122_);
lean_dec(v_int_122_);
return v_res_124_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind(void){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t v_x_127_, uint8_t v_y_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_129_ = lean_box(v_x_127_);
v___x_130_ = lean_obj_tag_nat(v___x_129_);
lean_dec(v___x_129_);
v___x_131_ = lean_box(v_y_128_);
v___x_132_ = lean_obj_tag_nat(v___x_131_);
lean_dec(v___x_131_);
v___x_133_ = lean_nat_dec_eq(v___x_130_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_127_ = stack[0].m_num;
uint8_t v_y_128_ = stack[1].m_num;
uint8_t v_res_134_;
v_res_134_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_x_127_, v_y_128_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object* v_x_135_, lean_object* v_y_136_){
_start:
{
uint8_t v_x_24__boxed_137_; uint8_t v_y_25__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_x_24__boxed_137_ = lean_unbox(v_x_135_);
v_y_25__boxed_138_ = lean_unbox(v_y_136_);
v_res_139_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_x_24__boxed_137_, v_y_25__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t v_a_143_){
_start:
{
uint8_t v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = 0;
v___x_146_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_a_143_, v___x_145_);
v___x_147_ = lean_box(v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_143_ = stack[0].m_num;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_143_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
uint8_t v_a_boxed_152_; lean_object* v_res_153_; 
v_a_boxed_152_ = lean_unbox(v_a_150_);
v_res_153_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_boxed_152_);
return v_res_153_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_154_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isApprox_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_154_ = stack[0].m_num;
lean_object* v_a_155_ = stack[1].m_obj;
lean_object* v_a_156_ = stack[2].m_obj;
lean_object* v_a_157_ = stack[3].m_obj;
lean_object* v_a_158_ = stack[4].m_obj;
lean_object* v_a_159_ = stack[5].m_obj;
lean_object* v_a_160_ = stack[6].m_obj;
lean_object* v_a_161_ = stack[7].m_obj;
lean_object* v_a_162_ = stack[8].m_obj;
lean_object* v_a_163_ = stack[9].m_obj;
lean_object* v_a_164_ = stack[10].m_obj;
lean_object* v_a_165_ = stack[11].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
uint8_t v_a_boxed_182_; lean_object* v_res_183_; 
v_a_boxed_182_ = lean_unbox(v_a_169_);
v_res_183_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(v_a_boxed_182_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_a_171_);
lean_dec(v_a_170_);
return v_res_183_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object* v_a_184_){
_start:
{
lean_object* v___x_186_; lean_object* v_cases_187_; lean_object* v_decVars_188_; lean_object* v_steps_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_200_; 
v___x_186_ = lean_st_ref_take(v_a_184_);
v_cases_187_ = lean_ctor_get(v___x_186_, 0);
v_decVars_188_ = lean_ctor_get(v___x_186_, 1);
v_steps_189_ = lean_ctor_get(v___x_186_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_200_ == 0)
{
v___x_191_ = v___x_186_;
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_steps_189_);
lean_inc(v_decVars_188_);
lean_inc(v_cases_187_);
lean_dec(v___x_186_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_200_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_196_; 
v___x_193_ = lean_box(0);
v___x_194_ = 0;
if (v_isShared_192_ == 0)
{
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_cases_187_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_decVars_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_steps_189_);
v___x_196_ = v_reuseFailAlloc_199_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3, v___x_194_);
v___x_197_ = lean_st_ref_put(v_a_184_, v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_193_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_184_ = stack[0].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_184_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_202_);
lean_dec(v_a_202_);
return v_res_204_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_206_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_setImprecise_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_205_ = stack[0].m_num;
lean_object* v_a_206_ = stack[1].m_obj;
lean_object* v_a_207_ = stack[2].m_obj;
lean_object* v_a_208_ = stack[3].m_obj;
lean_object* v_a_209_ = stack[4].m_obj;
lean_object* v_a_210_ = stack[5].m_obj;
lean_object* v_a_211_ = stack[6].m_obj;
lean_object* v_a_212_ = stack[7].m_obj;
lean_object* v_a_213_ = stack[8].m_obj;
lean_object* v_a_214_ = stack[9].m_obj;
lean_object* v_a_215_ = stack[10].m_obj;
lean_object* v_a_216_ = stack[11].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
uint8_t v_a_boxed_233_; lean_object* v_res_234_; 
v_a_boxed_233_ = lean_unbox(v_a_220_);
v_res_234_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(v_a_boxed_233_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
return v_res_234_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_cases_241_; uint8_t v_precise_242_; lean_object* v_decVars_243_; lean_object* v_steps_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_288_; 
v___x_240_ = lean_st_ref_take(v_a_235_);
v_cases_241_ = lean_ctor_get(v___x_240_, 0);
v_precise_242_ = lean_ctor_get_uint8(v___x_240_, sizeof(void*)*3);
v_decVars_243_ = lean_ctor_get(v___x_240_, 1);
v_steps_244_ = lean_ctor_get(v___x_240_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_288_ == 0)
{
v___x_246_ = v___x_240_;
v_isShared_247_ = v_isSharedCheck_288_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_steps_244_);
lean_inc(v_decVars_243_);
lean_inc(v_cases_241_);
lean_dec(v___x_240_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_288_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_add(v_steps_244_, v___x_248_);
lean_dec(v_steps_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 2, v___x_249_);
v___x_251_ = v___x_246_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_cases_241_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_decVars_243_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v___x_249_);
lean_ctor_set_uint8(v_reuseFailAlloc_287_, sizeof(void*)*3, v_precise_242_);
v___x_251_ = v_reuseFailAlloc_287_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_st_ref_put(v_a_235_, v___x_251_);
v___x_253_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_236_, v_a_238_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v___x_255_ = lean_st_ref_get(v_a_235_);
v___x_256_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_237_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_270_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_270_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_270_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_270_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_liaSteps_261_; lean_object* v_steps_262_; lean_object* v_steps_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v_liaSteps_261_ = lean_ctor_get(v_a_257_, 8);
lean_inc(v_liaSteps_261_);
lean_dec(v_a_257_);
v_steps_262_ = lean_ctor_get(v_a_254_, 14);
lean_inc(v_steps_262_);
lean_dec(v_a_254_);
v_steps_263_ = lean_ctor_get(v___x_255_, 2);
lean_inc(v_steps_263_);
lean_dec(v___x_255_);
v___x_264_ = lean_nat_add(v_steps_262_, v_steps_263_);
lean_dec(v_steps_263_);
lean_dec(v_steps_262_);
v___x_265_ = lean_nat_dec_lt(v_liaSteps_261_, v___x_264_);
lean_dec(v___x_264_);
lean_dec(v_liaSteps_261_);
v___x_266_ = lean_box(v___x_265_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_266_);
v___x_268_ = v___x_259_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec(v___x_255_);
lean_dec(v_a_254_);
v_a_271_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_256_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_256_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_253_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_253_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_235_ = stack[0].m_obj;
lean_object* v_a_236_ = stack[1].m_obj;
lean_object* v_a_237_ = stack[2].m_obj;
lean_object* v_a_238_ = stack[3].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_235_, v_a_236_, v_a_237_, v_a_238_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec_ref(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec(v_a_290_);
return v_res_295_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_297_, v_a_298_, v_a_300_, v_a_306_);
return v___x_309_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_296_ = stack[0].m_num;
lean_object* v_a_297_ = stack[1].m_obj;
lean_object* v_a_298_ = stack[2].m_obj;
lean_object* v_a_299_ = stack[3].m_obj;
lean_object* v_a_300_ = stack[4].m_obj;
lean_object* v_a_301_ = stack[5].m_obj;
lean_object* v_a_302_ = stack[6].m_obj;
lean_object* v_a_303_ = stack[7].m_obj;
lean_object* v_a_304_ = stack[8].m_obj;
lean_object* v_a_305_ = stack[9].m_obj;
lean_object* v_a_306_ = stack[10].m_obj;
lean_object* v_a_307_ = stack[11].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
uint8_t v_a_boxed_324_; lean_object* v_res_325_; 
v_a_boxed_324_ = lean_unbox(v_a_311_);
v_res_325_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(v_a_boxed_324_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec(v_a_313_);
lean_dec(v_a_312_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object* v_steps_326_, lean_object* v_s_327_){
_start:
{
lean_object* v_vars_328_; lean_object* v_varMap_329_; lean_object* v_varsHistory_330_; lean_object* v_natToIntMap_331_; lean_object* v_natDef_332_; lean_object* v_dvds_333_; lean_object* v_lowers_334_; lean_object* v_uppers_335_; lean_object* v_diseqs_336_; lean_object* v_elimEqs_337_; lean_object* v_elimStack_338_; lean_object* v_occurs_339_; lean_object* v_assignment_340_; lean_object* v_nextCnstrId_341_; uint8_t v_caseSplits_342_; lean_object* v_steps_343_; lean_object* v_conflict_x3f_344_; lean_object* v_diseqSplits_345_; lean_object* v_divMod_346_; uint8_t v_usedCommRing_347_; lean_object* v_nonlinearOccs_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_vars_328_ = lean_ctor_get(v_s_327_, 0);
v_varMap_329_ = lean_ctor_get(v_s_327_, 1);
v_varsHistory_330_ = lean_ctor_get(v_s_327_, 2);
v_natToIntMap_331_ = lean_ctor_get(v_s_327_, 3);
v_natDef_332_ = lean_ctor_get(v_s_327_, 4);
v_dvds_333_ = lean_ctor_get(v_s_327_, 5);
v_lowers_334_ = lean_ctor_get(v_s_327_, 6);
v_uppers_335_ = lean_ctor_get(v_s_327_, 7);
v_diseqs_336_ = lean_ctor_get(v_s_327_, 8);
v_elimEqs_337_ = lean_ctor_get(v_s_327_, 9);
v_elimStack_338_ = lean_ctor_get(v_s_327_, 10);
v_occurs_339_ = lean_ctor_get(v_s_327_, 11);
v_assignment_340_ = lean_ctor_get(v_s_327_, 12);
v_nextCnstrId_341_ = lean_ctor_get(v_s_327_, 13);
v_caseSplits_342_ = lean_ctor_get_uint8(v_s_327_, sizeof(void*)*19);
v_steps_343_ = lean_ctor_get(v_s_327_, 14);
v_conflict_x3f_344_ = lean_ctor_get(v_s_327_, 15);
v_diseqSplits_345_ = lean_ctor_get(v_s_327_, 16);
v_divMod_346_ = lean_ctor_get(v_s_327_, 17);
v_usedCommRing_347_ = lean_ctor_get_uint8(v_s_327_, sizeof(void*)*19 + 1);
v_nonlinearOccs_348_ = lean_ctor_get(v_s_327_, 18);
v_isSharedCheck_356_ = !lean_is_exclusive(v_s_327_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v_s_327_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_nonlinearOccs_348_);
lean_inc(v_divMod_346_);
lean_inc(v_diseqSplits_345_);
lean_inc(v_conflict_x3f_344_);
lean_inc(v_steps_343_);
lean_inc(v_nextCnstrId_341_);
lean_inc(v_assignment_340_);
lean_inc(v_occurs_339_);
lean_inc(v_elimStack_338_);
lean_inc(v_elimEqs_337_);
lean_inc(v_diseqs_336_);
lean_inc(v_uppers_335_);
lean_inc(v_lowers_334_);
lean_inc(v_dvds_333_);
lean_inc(v_natDef_332_);
lean_inc(v_natToIntMap_331_);
lean_inc(v_varsHistory_330_);
lean_inc(v_varMap_329_);
lean_inc(v_vars_328_);
lean_dec(v_s_327_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_nat_add(v_steps_343_, v_steps_326_);
lean_dec(v_steps_343_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 14, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_vars_328_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_varMap_329_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_varsHistory_330_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_natToIntMap_331_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_natDef_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_dvds_333_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_lowers_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_uppers_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v_diseqs_336_);
lean_ctor_set(v_reuseFailAlloc_355_, 9, v_elimEqs_337_);
lean_ctor_set(v_reuseFailAlloc_355_, 10, v_elimStack_338_);
lean_ctor_set(v_reuseFailAlloc_355_, 11, v_occurs_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 12, v_assignment_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 13, v_nextCnstrId_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 14, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 15, v_conflict_x3f_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 16, v_diseqSplits_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 17, v_divMod_346_);
lean_ctor_set(v_reuseFailAlloc_355_, 18, v_nonlinearOccs_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*19, v_caseSplits_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*19 + 1, v_usedCommRing_347_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object* v_steps_357_, lean_object* v_s_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(v_steps_357_, v_s_358_);
lean_dec(v_steps_357_);
return v_res_359_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; lean_object* v_steps_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_363_ = lean_st_ref_get(v_a_360_);
v_steps_364_ = lean_ctor_get(v___x_363_, 2);
lean_inc(v_steps_364_);
lean_dec(v___x_363_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_365_, 0, v_steps_364_);
v___x_366_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_367_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_366_, v___f_365_, v_a_361_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_360_ = stack[0].m_obj;
lean_object* v_a_361_ = stack[1].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_360_, v_a_361_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec(v_a_369_);
return v_res_372_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_374_, v_a_375_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_saveSteps_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_373_ = stack[0].m_num;
lean_object* v_a_374_ = stack[1].m_obj;
lean_object* v_a_375_ = stack[2].m_obj;
lean_object* v_a_376_ = stack[3].m_obj;
lean_object* v_a_377_ = stack[4].m_obj;
lean_object* v_a_378_ = stack[5].m_obj;
lean_object* v_a_379_ = stack[6].m_obj;
lean_object* v_a_380_ = stack[7].m_obj;
lean_object* v_a_381_ = stack[8].m_obj;
lean_object* v_a_382_ = stack[9].m_obj;
lean_object* v_a_383_ = stack[10].m_obj;
lean_object* v_a_384_ = stack[11].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_a_boxed_401_; lean_object* v_res_402_; 
v_a_boxed_401_ = lean_unbox(v_a_388_);
v_res_402_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_boxed_401_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec(v_a_390_);
lean_dec(v_a_389_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* v_s_403_){
_start:
{
lean_object* v_vars_404_; lean_object* v_varMap_405_; lean_object* v_varsHistory_406_; lean_object* v_natToIntMap_407_; lean_object* v_natDef_408_; lean_object* v_dvds_409_; lean_object* v_lowers_410_; lean_object* v_uppers_411_; lean_object* v_diseqs_412_; lean_object* v_elimEqs_413_; lean_object* v_elimStack_414_; lean_object* v_occurs_415_; lean_object* v_assignment_416_; lean_object* v_nextCnstrId_417_; lean_object* v_steps_418_; lean_object* v_conflict_x3f_419_; lean_object* v_diseqSplits_420_; lean_object* v_divMod_421_; uint8_t v_usedCommRing_422_; lean_object* v_nonlinearOccs_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
v_vars_404_ = lean_ctor_get(v_s_403_, 0);
v_varMap_405_ = lean_ctor_get(v_s_403_, 1);
v_varsHistory_406_ = lean_ctor_get(v_s_403_, 2);
v_natToIntMap_407_ = lean_ctor_get(v_s_403_, 3);
v_natDef_408_ = lean_ctor_get(v_s_403_, 4);
v_dvds_409_ = lean_ctor_get(v_s_403_, 5);
v_lowers_410_ = lean_ctor_get(v_s_403_, 6);
v_uppers_411_ = lean_ctor_get(v_s_403_, 7);
v_diseqs_412_ = lean_ctor_get(v_s_403_, 8);
v_elimEqs_413_ = lean_ctor_get(v_s_403_, 9);
v_elimStack_414_ = lean_ctor_get(v_s_403_, 10);
v_occurs_415_ = lean_ctor_get(v_s_403_, 11);
v_assignment_416_ = lean_ctor_get(v_s_403_, 12);
v_nextCnstrId_417_ = lean_ctor_get(v_s_403_, 13);
v_steps_418_ = lean_ctor_get(v_s_403_, 14);
v_conflict_x3f_419_ = lean_ctor_get(v_s_403_, 15);
v_diseqSplits_420_ = lean_ctor_get(v_s_403_, 16);
v_divMod_421_ = lean_ctor_get(v_s_403_, 17);
v_usedCommRing_422_ = lean_ctor_get_uint8(v_s_403_, sizeof(void*)*19 + 1);
v_nonlinearOccs_423_ = lean_ctor_get(v_s_403_, 18);
v_isSharedCheck_431_ = !lean_is_exclusive(v_s_403_);
if (v_isSharedCheck_431_ == 0)
{
v___x_425_ = v_s_403_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_nonlinearOccs_423_);
lean_inc(v_divMod_421_);
lean_inc(v_diseqSplits_420_);
lean_inc(v_conflict_x3f_419_);
lean_inc(v_steps_418_);
lean_inc(v_nextCnstrId_417_);
lean_inc(v_assignment_416_);
lean_inc(v_occurs_415_);
lean_inc(v_elimStack_414_);
lean_inc(v_elimEqs_413_);
lean_inc(v_diseqs_412_);
lean_inc(v_uppers_411_);
lean_inc(v_lowers_410_);
lean_inc(v_dvds_409_);
lean_inc(v_natDef_408_);
lean_inc(v_natToIntMap_407_);
lean_inc(v_varsHistory_406_);
lean_inc(v_varMap_405_);
lean_inc(v_vars_404_);
lean_dec(v_s_403_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
uint8_t v___x_427_; lean_object* v___x_429_; 
v___x_427_ = 1;
if (v_isShared_426_ == 0)
{
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_vars_404_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_varMap_405_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_varsHistory_406_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_natToIntMap_407_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_natDef_408_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_dvds_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v_lowers_410_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_uppers_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_diseqs_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 9, v_elimEqs_413_);
lean_ctor_set(v_reuseFailAlloc_430_, 10, v_elimStack_414_);
lean_ctor_set(v_reuseFailAlloc_430_, 11, v_occurs_415_);
lean_ctor_set(v_reuseFailAlloc_430_, 12, v_assignment_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 13, v_nextCnstrId_417_);
lean_ctor_set(v_reuseFailAlloc_430_, 14, v_steps_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 15, v_conflict_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 16, v_diseqSplits_420_);
lean_ctor_set(v_reuseFailAlloc_430_, 17, v_divMod_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 18, v_nonlinearOccs_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_430_, sizeof(void*)*19 + 1, v_usedCommRing_422_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*19, v___x_427_);
return v___x_429_;
}
}
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; lean_object* v_ngen_435_; lean_object* v_namePrefix_436_; lean_object* v_idx_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v___x_434_ = lean_st_ref_get(v___y_432_);
v_ngen_435_ = lean_ctor_get(v___x_434_, 2);
lean_inc_ref(v_ngen_435_);
lean_dec(v___x_434_);
v_namePrefix_436_ = lean_ctor_get(v_ngen_435_, 0);
v_idx_437_ = lean_ctor_get(v_ngen_435_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_ngen_435_);
if (v_isSharedCheck_467_ == 0)
{
v___x_439_ = v_ngen_435_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_idx_437_);
lean_inc(v_namePrefix_436_);
lean_dec(v_ngen_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_r_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
lean_inc(v_idx_437_);
lean_inc(v_namePrefix_436_);
v_r_441_ = l_Lean_Name_num___override(v_namePrefix_436_, v_idx_437_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_idx_437_, v___x_442_);
lean_dec(v_idx_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_443_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_namePrefix_436_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_466_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v_env_447_; lean_object* v_nextMacroScope_448_; lean_object* v_auxDeclNGen_449_; lean_object* v_traceState_450_; lean_object* v_cache_451_; lean_object* v_recordedDeps_452_; lean_object* v_messages_453_; lean_object* v_infoState_454_; lean_object* v_snapshotTasks_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v___x_446_ = lean_st_ref_take(v___y_432_);
v_env_447_ = lean_ctor_get(v___x_446_, 0);
v_nextMacroScope_448_ = lean_ctor_get(v___x_446_, 1);
v_auxDeclNGen_449_ = lean_ctor_get(v___x_446_, 3);
v_traceState_450_ = lean_ctor_get(v___x_446_, 4);
v_cache_451_ = lean_ctor_get(v___x_446_, 5);
v_recordedDeps_452_ = lean_ctor_get(v___x_446_, 6);
v_messages_453_ = lean_ctor_get(v___x_446_, 7);
v_infoState_454_ = lean_ctor_get(v___x_446_, 8);
v_snapshotTasks_455_ = lean_ctor_get(v___x_446_, 9);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_446_, 2);
lean_dec(v_unused_465_);
v___x_457_ = v___x_446_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snapshotTasks_455_);
lean_inc(v_infoState_454_);
lean_inc(v_messages_453_);
lean_inc(v_recordedDeps_452_);
lean_inc(v_cache_451_);
lean_inc(v_traceState_450_);
lean_inc(v_auxDeclNGen_449_);
lean_inc(v_nextMacroScope_448_);
lean_inc(v_env_447_);
lean_dec(v___x_446_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 2, v___x_445_);
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_env_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_nextMacroScope_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_auxDeclNGen_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_traceState_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_recordedDeps_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_messages_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_infoState_454_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_snapshotTasks_455_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_put(v___y_432_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_r_441_);
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_432_ = stack[0].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_432_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_469_);
lean_dec(v___y_469_);
return v_res_471_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v___x_485_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_483_);
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_472_ = stack[0].m_num;
lean_object* v___y_473_ = stack[1].m_obj;
lean_object* v___y_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v___y_479_ = stack[7].m_obj;
lean_object* v___y_480_ = stack[8].m_obj;
lean_object* v___y_481_ = stack[9].m_obj;
lean_object* v___y_482_ = stack[10].m_obj;
lean_object* v___y_483_ = stack[11].m_obj;
lean_object* v_res_494_;
v_res_494_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___y_12020__boxed_508_; lean_object* v_res_509_; 
v___y_12020__boxed_508_ = lean_unbox(v___y_495_);
v_res_509_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_12020__boxed_508_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec(v___y_497_);
lean_dec(v___y_496_);
return v_res_509_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* v_kind_511_, uint8_t v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___f_525_; lean_object* v___x_526_; 
v___f_525_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0));
v___x_526_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_514_, v_a_522_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v_cases_531_; uint8_t v_precise_532_; lean_object* v_decVars_533_; lean_object* v_steps_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_563_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = lean_st_ref_take(v_a_513_);
v_cases_531_ = lean_ctor_get(v___x_530_, 0);
v_precise_532_ = lean_ctor_get_uint8(v___x_530_, sizeof(void*)*3);
v_decVars_533_ = lean_ctor_get(v___x_530_, 1);
v_steps_534_ = lean_ctor_get(v___x_530_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_563_ == 0)
{
v___x_536_ = v___x_530_;
v_isShared_537_ = v_isSharedCheck_563_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_steps_534_);
lean_inc(v_decVars_533_);
lean_inc(v_cases_531_);
lean_dec(v___x_530_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_563_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_inc_n(v_a_527_, 2);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v_kind_511_);
lean_ctor_set(v___x_538_, 1, v_a_527_);
lean_ctor_set(v___x_538_, 2, v_a_529_);
v___x_539_ = l_Lean_PersistentArray_push___redArg(v_cases_531_, v___x_538_);
v___x_540_ = l_Lean_FVarIdSet_insert(v_decVars_533_, v_a_527_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_540_);
lean_ctor_set(v___x_536_, 0, v___x_539_);
v___x_542_ = v___x_536_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_steps_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3, v_precise_532_);
v___x_542_ = v_reuseFailAlloc_562_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_st_ref_put(v_a_513_, v___x_542_);
v___x_544_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_545_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_544_, v___f_525_, v_a_514_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v___x_545_, 0);
lean_dec(v_unused_553_);
v___x_547_ = v___x_545_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_dec(v___x_545_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v_a_527_);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_527_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_527_);
v_a_554_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_545_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_545_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_a_527_);
lean_dec_ref(v_kind_511_);
v_a_564_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_528_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_528_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_dec_ref(v_kind_511_);
return v___x_526_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_mkCase_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_511_ = stack[0].m_obj;
uint8_t v_a_512_ = stack[1].m_num;
lean_object* v_a_513_ = stack[2].m_obj;
lean_object* v_a_514_ = stack[3].m_obj;
lean_object* v_a_515_ = stack[4].m_obj;
lean_object* v_a_516_ = stack[5].m_obj;
lean_object* v_a_517_ = stack[6].m_obj;
lean_object* v_a_518_ = stack[7].m_obj;
lean_object* v_a_519_ = stack[8].m_obj;
lean_object* v_a_520_ = stack[9].m_obj;
lean_object* v_a_521_ = stack[10].m_obj;
lean_object* v_a_522_ = stack[11].m_obj;
lean_object* v_a_523_ = stack[12].m_obj;
lean_object* v_res_572_;
v_res_572_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* v_kind_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
uint8_t v_a_boxed_587_; lean_object* v_res_588_; 
v_a_boxed_587_ = lean_unbox(v_a_574_);
v_res_588_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_573_, v_a_boxed_587_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
return v_res_588_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_600_);
return v___x_602_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_589_ = stack[0].m_num;
lean_object* v___y_590_ = stack[1].m_obj;
lean_object* v___y_591_ = stack[2].m_obj;
lean_object* v___y_592_ = stack[3].m_obj;
lean_object* v___y_593_ = stack[4].m_obj;
lean_object* v___y_594_ = stack[5].m_obj;
lean_object* v___y_595_ = stack[6].m_obj;
lean_object* v___y_596_ = stack[7].m_obj;
lean_object* v___y_597_ = stack[8].m_obj;
lean_object* v___y_598_ = stack[9].m_obj;
lean_object* v___y_599_ = stack[10].m_obj;
lean_object* v___y_600_ = stack[11].m_obj;
lean_object* v_res_603_;
v_res_603_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___y_12253__boxed_617_; lean_object* v_res_618_; 
v___y_12253__boxed_617_ = lean_unbox(v___y_604_);
v_res_618_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12253__boxed_617_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
return v_res_618_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
