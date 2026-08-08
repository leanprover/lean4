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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(lean_object* v_motive_84_, lean_object* v_ctorIdx_85_, uint8_t v_t_86_, lean_object* v_h_87_, lean_object* v_k_88_){
_start:
{
lean_inc(v_k_88_);
return v_k_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(lean_object* v_motive_89_, lean_object* v_ctorIdx_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_k_93_){
_start:
{
uint8_t v_t_boxed_94_; lean_object* v_res_95_; 
v_t_boxed_94_ = lean_unbox(v_t_91_);
v_res_95_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(v_motive_89_, v_ctorIdx_90_, v_t_boxed_94_, v_h_92_, v_k_93_);
lean_dec(v_k_93_);
lean_dec(v_ctorIdx_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(lean_object* v_rat_96_){
_start:
{
lean_inc(v_rat_96_);
return v_rat_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(lean_object* v_rat_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(v_rat_97_);
lean_dec(v_rat_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(lean_object* v_motive_99_, uint8_t v_t_100_, lean_object* v_h_101_, lean_object* v_rat_102_){
_start:
{
lean_inc(v_rat_102_);
return v_rat_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(lean_object* v_motive_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_rat_106_){
_start:
{
uint8_t v_t_boxed_107_; lean_object* v_res_108_; 
v_t_boxed_107_ = lean_unbox(v_t_104_);
v_res_108_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(v_motive_103_, v_t_boxed_107_, v_h_105_, v_rat_106_);
lean_dec(v_rat_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(lean_object* v_int_109_){
_start:
{
lean_inc(v_int_109_);
return v_int_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(lean_object* v_int_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(v_int_110_);
lean_dec(v_int_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(lean_object* v_motive_112_, uint8_t v_t_113_, lean_object* v_h_114_, lean_object* v_int_115_){
_start:
{
lean_inc(v_int_115_);
return v_int_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_int_119_){
_start:
{
uint8_t v_t_boxed_120_; lean_object* v_res_121_; 
v_t_boxed_120_ = lean_unbox(v_t_117_);
v_res_121_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(v_motive_116_, v_t_boxed_120_, v_h_118_, v_int_119_);
lean_dec(v_int_119_);
return v_res_121_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default(void){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind(void){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(uint8_t v_x_124_, uint8_t v_y_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_124_);
v___x_127_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_y_125_);
v___x_128_ = lean_nat_dec_eq(v___x_126_, v___x_127_);
lean_dec(v___x_127_);
lean_dec(v___x_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(lean_object* v_x_129_, lean_object* v_y_130_){
_start:
{
uint8_t v_x_17__boxed_131_; uint8_t v_y_18__boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_x_17__boxed_131_ = lean_unbox(v_x_129_);
v_y_18__boxed_132_ = lean_unbox(v_y_130_);
v_res_133_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_x_17__boxed_131_, v_y_18__boxed_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(uint8_t v_a_137_){
_start:
{
uint8_t v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_139_ = 0;
v___x_140_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_a_137_, v___x_139_);
v___x_141_ = lean_box(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
uint8_t v_a_boxed_145_; lean_object* v_res_146_; 
v_a_boxed_145_ = lean_unbox(v_a_143_);
v_res_146_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_boxed_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_147_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_a_boxed_174_; lean_object* v_res_175_; 
v_a_boxed_174_ = lean_unbox(v_a_161_);
v_res_175_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(v_a_boxed_174_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec(v_a_163_);
lean_dec(v_a_162_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; lean_object* v_cases_179_; lean_object* v_decVars_180_; lean_object* v_steps_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_192_; 
v___x_178_ = lean_st_ref_take(v_a_176_);
v_cases_179_ = lean_ctor_get(v___x_178_, 0);
v_decVars_180_ = lean_ctor_get(v___x_178_, 1);
v_steps_181_ = lean_ctor_get(v___x_178_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_192_ == 0)
{
v___x_183_ = v___x_178_;
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_steps_181_);
lean_inc(v_decVars_180_);
lean_inc(v_cases_179_);
lean_dec(v___x_178_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
uint8_t v___x_185_; lean_object* v___x_187_; 
v___x_185_ = 0;
if (v_isShared_184_ == 0)
{
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_cases_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_decVars_180_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_steps_181_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*3, v___x_185_);
v___x_188_ = lean_st_ref_set(v_a_176_, v___x_187_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_193_);
lean_dec(v_a_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(uint8_t v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_197_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
uint8_t v_a_boxed_223_; lean_object* v_res_224_; 
v_a_boxed_223_ = lean_unbox(v_a_210_);
v_res_224_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(v_a_boxed_223_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
lean_dec(v_a_211_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; lean_object* v_cases_231_; uint8_t v_precise_232_; lean_object* v_decVars_233_; lean_object* v_steps_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_278_; 
v___x_230_ = lean_st_ref_take(v_a_225_);
v_cases_231_ = lean_ctor_get(v___x_230_, 0);
v_precise_232_ = lean_ctor_get_uint8(v___x_230_, sizeof(void*)*3);
v_decVars_233_ = lean_ctor_get(v___x_230_, 1);
v_steps_234_ = lean_ctor_get(v___x_230_, 2);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_278_ == 0)
{
v___x_236_ = v___x_230_;
v_isShared_237_ = v_isSharedCheck_278_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_steps_234_);
lean_inc(v_decVars_233_);
lean_inc(v_cases_231_);
lean_dec(v___x_230_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_278_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_add(v_steps_234_, v___x_238_);
lean_dec(v_steps_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 2, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_cases_231_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_decVars_233_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v___x_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*3, v_precise_232_);
v___x_241_ = v_reuseFailAlloc_277_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_st_ref_set(v_a_225_, v___x_241_);
v___x_243_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_226_, v_a_228_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
v___x_245_ = lean_st_ref_get(v_a_225_);
v___x_246_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_227_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_260_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_260_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_liaSteps_251_; lean_object* v_steps_252_; lean_object* v_steps_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v_liaSteps_251_ = lean_ctor_get(v_a_247_, 8);
lean_inc(v_liaSteps_251_);
lean_dec(v_a_247_);
v_steps_252_ = lean_ctor_get(v_a_244_, 15);
lean_inc(v_steps_252_);
lean_dec(v_a_244_);
v_steps_253_ = lean_ctor_get(v___x_245_, 2);
lean_inc(v_steps_253_);
lean_dec(v___x_245_);
v___x_254_ = lean_nat_add(v_steps_252_, v_steps_253_);
lean_dec(v_steps_253_);
lean_dec(v_steps_252_);
v___x_255_ = lean_nat_dec_lt(v_liaSteps_251_, v___x_254_);
lean_dec(v___x_254_);
lean_dec(v_liaSteps_251_);
v___x_256_ = lean_box(v___x_255_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_256_);
v___x_258_ = v___x_249_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v___x_245_);
lean_dec(v_a_244_);
v_a_261_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_246_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_246_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_243_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_243_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec(v_a_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(uint8_t v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___redArg(v_a_286_, v_a_287_, v_a_289_, v_a_295_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps___boxed(lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_a_boxed_312_; lean_object* v_res_313_; 
v_a_boxed_312_ = lean_unbox(v_a_299_);
v_res_313_ = l_Lean_Meta_Grind_Arith_Cutsat_checkMaxSteps(v_a_boxed_312_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_a_300_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(lean_object* v_steps_314_, lean_object* v_s_315_){
_start:
{
lean_object* v_vars_316_; lean_object* v_varMap_317_; lean_object* v_vars_x27_318_; lean_object* v_varMap_x27_319_; lean_object* v_natToIntMap_320_; lean_object* v_natDef_321_; lean_object* v_dvds_322_; lean_object* v_lowers_323_; lean_object* v_uppers_324_; lean_object* v_diseqs_325_; lean_object* v_elimEqs_326_; lean_object* v_elimStack_327_; lean_object* v_occurs_328_; lean_object* v_assignment_329_; lean_object* v_nextCnstrId_330_; uint8_t v_caseSplits_331_; lean_object* v_steps_332_; lean_object* v_conflict_x3f_333_; lean_object* v_diseqSplits_334_; lean_object* v_divMod_335_; lean_object* v_toIntIds_336_; lean_object* v_toIntInfos_337_; lean_object* v_toIntTermMap_338_; lean_object* v_toIntVarMap_339_; uint8_t v_usedCommRing_340_; lean_object* v_nonlinearOccs_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v_vars_316_ = lean_ctor_get(v_s_315_, 0);
v_varMap_317_ = lean_ctor_get(v_s_315_, 1);
v_vars_x27_318_ = lean_ctor_get(v_s_315_, 2);
v_varMap_x27_319_ = lean_ctor_get(v_s_315_, 3);
v_natToIntMap_320_ = lean_ctor_get(v_s_315_, 4);
v_natDef_321_ = lean_ctor_get(v_s_315_, 5);
v_dvds_322_ = lean_ctor_get(v_s_315_, 6);
v_lowers_323_ = lean_ctor_get(v_s_315_, 7);
v_uppers_324_ = lean_ctor_get(v_s_315_, 8);
v_diseqs_325_ = lean_ctor_get(v_s_315_, 9);
v_elimEqs_326_ = lean_ctor_get(v_s_315_, 10);
v_elimStack_327_ = lean_ctor_get(v_s_315_, 11);
v_occurs_328_ = lean_ctor_get(v_s_315_, 12);
v_assignment_329_ = lean_ctor_get(v_s_315_, 13);
v_nextCnstrId_330_ = lean_ctor_get(v_s_315_, 14);
v_caseSplits_331_ = lean_ctor_get_uint8(v_s_315_, sizeof(void*)*24);
v_steps_332_ = lean_ctor_get(v_s_315_, 15);
v_conflict_x3f_333_ = lean_ctor_get(v_s_315_, 16);
v_diseqSplits_334_ = lean_ctor_get(v_s_315_, 17);
v_divMod_335_ = lean_ctor_get(v_s_315_, 18);
v_toIntIds_336_ = lean_ctor_get(v_s_315_, 19);
v_toIntInfos_337_ = lean_ctor_get(v_s_315_, 20);
v_toIntTermMap_338_ = lean_ctor_get(v_s_315_, 21);
v_toIntVarMap_339_ = lean_ctor_get(v_s_315_, 22);
v_usedCommRing_340_ = lean_ctor_get_uint8(v_s_315_, sizeof(void*)*24 + 1);
v_nonlinearOccs_341_ = lean_ctor_get(v_s_315_, 23);
v_isSharedCheck_349_ = !lean_is_exclusive(v_s_315_);
if (v_isSharedCheck_349_ == 0)
{
v___x_343_ = v_s_315_;
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_nonlinearOccs_341_);
lean_inc(v_toIntVarMap_339_);
lean_inc(v_toIntTermMap_338_);
lean_inc(v_toIntInfos_337_);
lean_inc(v_toIntIds_336_);
lean_inc(v_divMod_335_);
lean_inc(v_diseqSplits_334_);
lean_inc(v_conflict_x3f_333_);
lean_inc(v_steps_332_);
lean_inc(v_nextCnstrId_330_);
lean_inc(v_assignment_329_);
lean_inc(v_occurs_328_);
lean_inc(v_elimStack_327_);
lean_inc(v_elimEqs_326_);
lean_inc(v_diseqs_325_);
lean_inc(v_uppers_324_);
lean_inc(v_lowers_323_);
lean_inc(v_dvds_322_);
lean_inc(v_natDef_321_);
lean_inc(v_natToIntMap_320_);
lean_inc(v_varMap_x27_319_);
lean_inc(v_vars_x27_318_);
lean_inc(v_varMap_317_);
lean_inc(v_vars_316_);
lean_dec(v_s_315_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_nat_add(v_steps_332_, v_steps_314_);
lean_dec(v_steps_332_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 15, v___x_345_);
v___x_347_ = v___x_343_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_vars_316_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_varMap_317_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_vars_x27_318_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_varMap_x27_319_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_natToIntMap_320_);
lean_ctor_set(v_reuseFailAlloc_348_, 5, v_natDef_321_);
lean_ctor_set(v_reuseFailAlloc_348_, 6, v_dvds_322_);
lean_ctor_set(v_reuseFailAlloc_348_, 7, v_lowers_323_);
lean_ctor_set(v_reuseFailAlloc_348_, 8, v_uppers_324_);
lean_ctor_set(v_reuseFailAlloc_348_, 9, v_diseqs_325_);
lean_ctor_set(v_reuseFailAlloc_348_, 10, v_elimEqs_326_);
lean_ctor_set(v_reuseFailAlloc_348_, 11, v_elimStack_327_);
lean_ctor_set(v_reuseFailAlloc_348_, 12, v_occurs_328_);
lean_ctor_set(v_reuseFailAlloc_348_, 13, v_assignment_329_);
lean_ctor_set(v_reuseFailAlloc_348_, 14, v_nextCnstrId_330_);
lean_ctor_set(v_reuseFailAlloc_348_, 15, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_348_, 16, v_conflict_x3f_333_);
lean_ctor_set(v_reuseFailAlloc_348_, 17, v_diseqSplits_334_);
lean_ctor_set(v_reuseFailAlloc_348_, 18, v_divMod_335_);
lean_ctor_set(v_reuseFailAlloc_348_, 19, v_toIntIds_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 20, v_toIntInfos_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 21, v_toIntTermMap_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 22, v_toIntVarMap_339_);
lean_ctor_set(v_reuseFailAlloc_348_, 23, v_nonlinearOccs_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*24, v_caseSplits_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_348_, sizeof(void*)*24 + 1, v_usedCommRing_340_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed(lean_object* v_steps_350_, lean_object* v_s_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0(v_steps_350_, v_s_351_);
lean_dec(v_steps_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_steps_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_356_ = lean_st_ref_get(v_a_353_);
v_steps_357_ = lean_ctor_get(v___x_356_, 2);
lean_inc(v_steps_357_);
lean_dec(v___x_356_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_358_, 0, v_steps_357_);
v___x_359_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_360_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_359_, v___f_358_, v_a_354_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg___boxed(lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec(v_a_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(uint8_t v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___redArg(v_a_366_, v_a_367_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_saveSteps___boxed(lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
uint8_t v_a_boxed_392_; lean_object* v_res_393_; 
v_a_boxed_392_ = lean_unbox(v_a_379_);
v_res_393_ = l_Lean_Meta_Grind_Arith_Cutsat_saveSteps(v_a_boxed_392_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
lean_dec(v_a_380_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(lean_object* v_s_394_){
_start:
{
lean_object* v_vars_395_; lean_object* v_varMap_396_; lean_object* v_vars_x27_397_; lean_object* v_varMap_x27_398_; lean_object* v_natToIntMap_399_; lean_object* v_natDef_400_; lean_object* v_dvds_401_; lean_object* v_lowers_402_; lean_object* v_uppers_403_; lean_object* v_diseqs_404_; lean_object* v_elimEqs_405_; lean_object* v_elimStack_406_; lean_object* v_occurs_407_; lean_object* v_assignment_408_; lean_object* v_nextCnstrId_409_; lean_object* v_steps_410_; lean_object* v_conflict_x3f_411_; lean_object* v_diseqSplits_412_; lean_object* v_divMod_413_; lean_object* v_toIntIds_414_; lean_object* v_toIntInfos_415_; lean_object* v_toIntTermMap_416_; lean_object* v_toIntVarMap_417_; uint8_t v_usedCommRing_418_; lean_object* v_nonlinearOccs_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_vars_395_ = lean_ctor_get(v_s_394_, 0);
v_varMap_396_ = lean_ctor_get(v_s_394_, 1);
v_vars_x27_397_ = lean_ctor_get(v_s_394_, 2);
v_varMap_x27_398_ = lean_ctor_get(v_s_394_, 3);
v_natToIntMap_399_ = lean_ctor_get(v_s_394_, 4);
v_natDef_400_ = lean_ctor_get(v_s_394_, 5);
v_dvds_401_ = lean_ctor_get(v_s_394_, 6);
v_lowers_402_ = lean_ctor_get(v_s_394_, 7);
v_uppers_403_ = lean_ctor_get(v_s_394_, 8);
v_diseqs_404_ = lean_ctor_get(v_s_394_, 9);
v_elimEqs_405_ = lean_ctor_get(v_s_394_, 10);
v_elimStack_406_ = lean_ctor_get(v_s_394_, 11);
v_occurs_407_ = lean_ctor_get(v_s_394_, 12);
v_assignment_408_ = lean_ctor_get(v_s_394_, 13);
v_nextCnstrId_409_ = lean_ctor_get(v_s_394_, 14);
v_steps_410_ = lean_ctor_get(v_s_394_, 15);
v_conflict_x3f_411_ = lean_ctor_get(v_s_394_, 16);
v_diseqSplits_412_ = lean_ctor_get(v_s_394_, 17);
v_divMod_413_ = lean_ctor_get(v_s_394_, 18);
v_toIntIds_414_ = lean_ctor_get(v_s_394_, 19);
v_toIntInfos_415_ = lean_ctor_get(v_s_394_, 20);
v_toIntTermMap_416_ = lean_ctor_get(v_s_394_, 21);
v_toIntVarMap_417_ = lean_ctor_get(v_s_394_, 22);
v_usedCommRing_418_ = lean_ctor_get_uint8(v_s_394_, sizeof(void*)*24 + 1);
v_nonlinearOccs_419_ = lean_ctor_get(v_s_394_, 23);
v_isSharedCheck_427_ = !lean_is_exclusive(v_s_394_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v_s_394_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_nonlinearOccs_419_);
lean_inc(v_toIntVarMap_417_);
lean_inc(v_toIntTermMap_416_);
lean_inc(v_toIntInfos_415_);
lean_inc(v_toIntIds_414_);
lean_inc(v_divMod_413_);
lean_inc(v_diseqSplits_412_);
lean_inc(v_conflict_x3f_411_);
lean_inc(v_steps_410_);
lean_inc(v_nextCnstrId_409_);
lean_inc(v_assignment_408_);
lean_inc(v_occurs_407_);
lean_inc(v_elimStack_406_);
lean_inc(v_elimEqs_405_);
lean_inc(v_diseqs_404_);
lean_inc(v_uppers_403_);
lean_inc(v_lowers_402_);
lean_inc(v_dvds_401_);
lean_inc(v_natDef_400_);
lean_inc(v_natToIntMap_399_);
lean_inc(v_varMap_x27_398_);
lean_inc(v_vars_x27_397_);
lean_inc(v_varMap_396_);
lean_inc(v_vars_395_);
lean_dec(v_s_394_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint8_t v___x_423_; lean_object* v___x_425_; 
v___x_423_ = 1;
if (v_isShared_422_ == 0)
{
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_vars_395_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_varMap_396_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_vars_x27_397_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_varMap_x27_398_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_natToIntMap_399_);
lean_ctor_set(v_reuseFailAlloc_426_, 5, v_natDef_400_);
lean_ctor_set(v_reuseFailAlloc_426_, 6, v_dvds_401_);
lean_ctor_set(v_reuseFailAlloc_426_, 7, v_lowers_402_);
lean_ctor_set(v_reuseFailAlloc_426_, 8, v_uppers_403_);
lean_ctor_set(v_reuseFailAlloc_426_, 9, v_diseqs_404_);
lean_ctor_set(v_reuseFailAlloc_426_, 10, v_elimEqs_405_);
lean_ctor_set(v_reuseFailAlloc_426_, 11, v_elimStack_406_);
lean_ctor_set(v_reuseFailAlloc_426_, 12, v_occurs_407_);
lean_ctor_set(v_reuseFailAlloc_426_, 13, v_assignment_408_);
lean_ctor_set(v_reuseFailAlloc_426_, 14, v_nextCnstrId_409_);
lean_ctor_set(v_reuseFailAlloc_426_, 15, v_steps_410_);
lean_ctor_set(v_reuseFailAlloc_426_, 16, v_conflict_x3f_411_);
lean_ctor_set(v_reuseFailAlloc_426_, 17, v_diseqSplits_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 18, v_divMod_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 19, v_toIntIds_414_);
lean_ctor_set(v_reuseFailAlloc_426_, 20, v_toIntInfos_415_);
lean_ctor_set(v_reuseFailAlloc_426_, 21, v_toIntTermMap_416_);
lean_ctor_set(v_reuseFailAlloc_426_, 22, v_toIntVarMap_417_);
lean_ctor_set(v_reuseFailAlloc_426_, 23, v_nonlinearOccs_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*24 + 1, v_usedCommRing_418_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*24, v___x_423_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_ngen_431_; lean_object* v_namePrefix_432_; lean_object* v_idx_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_462_; 
v___x_430_ = lean_st_ref_get(v___y_428_);
v_ngen_431_ = lean_ctor_get(v___x_430_, 2);
lean_inc_ref(v_ngen_431_);
lean_dec(v___x_430_);
v_namePrefix_432_ = lean_ctor_get(v_ngen_431_, 0);
v_idx_433_ = lean_ctor_get(v_ngen_431_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_ngen_431_);
if (v_isSharedCheck_462_ == 0)
{
v___x_435_ = v_ngen_431_;
v_isShared_436_ = v_isSharedCheck_462_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_idx_433_);
lean_inc(v_namePrefix_432_);
lean_dec(v_ngen_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_462_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v_env_438_; lean_object* v_nextMacroScope_439_; lean_object* v_auxDeclNGen_440_; lean_object* v_traceState_441_; lean_object* v_cache_442_; lean_object* v_messages_443_; lean_object* v_infoState_444_; lean_object* v_snapshotTasks_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_460_; 
v___x_437_ = lean_st_ref_take(v___y_428_);
v_env_438_ = lean_ctor_get(v___x_437_, 0);
v_nextMacroScope_439_ = lean_ctor_get(v___x_437_, 1);
v_auxDeclNGen_440_ = lean_ctor_get(v___x_437_, 3);
v_traceState_441_ = lean_ctor_get(v___x_437_, 4);
v_cache_442_ = lean_ctor_get(v___x_437_, 5);
v_messages_443_ = lean_ctor_get(v___x_437_, 6);
v_infoState_444_ = lean_ctor_get(v___x_437_, 7);
v_snapshotTasks_445_ = lean_ctor_get(v___x_437_, 8);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v___x_437_, 2);
lean_dec(v_unused_461_);
v___x_447_ = v___x_437_;
v_isShared_448_ = v_isSharedCheck_460_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snapshotTasks_445_);
lean_inc(v_infoState_444_);
lean_inc(v_messages_443_);
lean_inc(v_cache_442_);
lean_inc(v_traceState_441_);
lean_inc(v_auxDeclNGen_440_);
lean_inc(v_nextMacroScope_439_);
lean_inc(v_env_438_);
lean_dec(v___x_437_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_460_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_r_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
lean_inc(v_idx_433_);
lean_inc(v_namePrefix_432_);
v_r_449_ = l_Lean_Name_num___override(v_namePrefix_432_, v_idx_433_);
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_add(v_idx_433_, v___x_450_);
lean_dec(v_idx_433_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_451_);
v___x_453_ = v___x_435_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_namePrefix_432_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_459_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_453_);
v___x_455_ = v___x_447_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_env_438_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_nextMacroScope_439_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_auxDeclNGen_440_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_traceState_441_);
lean_ctor_set(v_reuseFailAlloc_458_, 5, v_cache_442_);
lean_ctor_set(v_reuseFailAlloc_458_, 6, v_messages_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 7, v_infoState_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 8, v_snapshotTasks_445_);
v___x_455_ = v_reuseFailAlloc_458_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_st_ref_set(v___y_428_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_r_449_);
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_463_);
lean_dec(v___y_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(uint8_t v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v___x_479_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_477_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
uint8_t v___y_12375__boxed_501_; lean_object* v_res_502_; 
v___y_12375__boxed_501_ = lean_unbox(v___y_488_);
v_res_502_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v___y_12375__boxed_501_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec(v___y_490_);
lean_dec(v___y_489_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object* v_kind_504_, uint8_t v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_507_, v_a_515_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v_cases_523_; uint8_t v_precise_524_; lean_object* v_decVars_525_; lean_object* v_steps_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_556_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = lean_st_ref_take(v_a_506_);
v_cases_523_ = lean_ctor_get(v___x_522_, 0);
v_precise_524_ = lean_ctor_get_uint8(v___x_522_, sizeof(void*)*3);
v_decVars_525_ = lean_ctor_get(v___x_522_, 1);
v_steps_526_ = lean_ctor_get(v___x_522_, 2);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_556_ == 0)
{
v___x_528_ = v___x_522_;
v_isShared_529_ = v_isSharedCheck_556_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_steps_526_);
lean_inc(v_decVars_525_);
lean_inc(v_cases_523_);
lean_dec(v___x_522_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_556_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_inc_n(v_a_519_, 2);
v___x_530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_530_, 0, v_kind_504_);
lean_ctor_set(v___x_530_, 1, v_a_519_);
lean_ctor_set(v___x_530_, 2, v_a_521_);
v___x_531_ = l_Lean_PersistentArray_push___redArg(v_cases_523_, v___x_530_);
v___x_532_ = l_Lean_FVarIdSet_insert(v_decVars_525_, v_a_519_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v___x_532_);
lean_ctor_set(v___x_528_, 0, v___x_531_);
v___x_534_ = v___x_528_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_steps_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*3, v_precise_524_);
v___x_534_ = v_reuseFailAlloc_555_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = lean_st_ref_set(v_a_506_, v___x_534_);
v___f_536_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0));
v___x_537_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_538_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_537_, v___f_536_, v_a_507_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v___x_538_, 0);
lean_dec(v_unused_546_);
v___x_540_ = v___x_538_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_dec(v___x_538_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_a_519_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_519_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_519_);
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_a_519_);
lean_dec_ref(v_kind_504_);
v_a_557_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_520_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_520_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_dec_ref(v_kind_504_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(lean_object* v_kind_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
uint8_t v_a_boxed_579_; lean_object* v_res_580_; 
v_a_boxed_579_ = lean_unbox(v_a_566_);
v_res_580_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(v_kind_565_, v_a_boxed_579_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec(v_a_568_);
lean_dec(v_a_567_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(uint8_t v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
uint8_t v___y_12527__boxed_608_; lean_object* v_res_609_; 
v___y_12527__boxed_608_ = lean_unbox(v___y_595_);
v_res_609_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12527__boxed_608_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec(v___y_597_);
lean_dec(v___y_596_);
return v_res_609_;
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
