// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.Types public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`grind` internal error, invalid structure id"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "`grind linarith` internal error, structure is not a ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`grind linarith` internal error, structure is not a commutative ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_4_, v_a_1_, v_a_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_6_, v_a_7_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27(lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_10_, v_a_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_Grind_Arith_Linear_get_x27(v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec(v_a_22_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(lean_object* v_f_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_38_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_37_, v_f_34_, v_a_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(lean_object* v_f_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(v_f_39_, v_a_40_);
lean_dec(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27(lean_object* v_f_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_55_, v_f_43_, v_a_44_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(lean_object* v_f_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27(v_f_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec(v_a_58_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_apply_2(v_inst_70_, lean_box(0), v_inst_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(lean_object* v_m_73_, lean_object* v_n_74_, lean_object* v_inst_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_apply_2(v_inst_75_, lean_box(0), v_inst_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(lean_object* v_structId_78_, lean_object* v_x_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc(v_a_80_);
v___x_91_ = lean_apply_12(v_x_79_, v_structId_78_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(lean_object* v_structId_92_, lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(v_structId_92_, v_x_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run(lean_object* v_00_u03b1_106_, lean_object* v_structId_107_, lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; 
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc(v_a_109_);
v___x_120_ = lean_apply_12(v_x_108_, v_structId_107_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, lean_box(0));
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(lean_object* v_00_u03b1_121_, lean_object* v_structId_122_, lean_object* v_x_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run(v_00_u03b1_121_, v_structId_122_, v_x_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec(v_a_124_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v_a_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_a_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(v_a_139_);
lean_dec(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
lean_inc(v_a_142_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v_a_142_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Meta_Grind_Arith_Linear_getStructId(v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec(v_a_156_);
lean_dec(v_a_155_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(lean_object* v_msgData_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_env_175_; lean_object* v___x_176_; lean_object* v_mctx_177_; lean_object* v_lctx_178_; lean_object* v_options_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = lean_st_ref_get(v___y_170_);
v_mctx_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_mctx_177_);
lean_dec(v___x_176_);
v_lctx_178_ = lean_ctor_get(v___y_169_, 2);
v_options_179_ = lean_ctor_get(v___y_171_, 2);
lean_inc_ref(v_options_179_);
lean_inc_ref(v_lctx_178_);
v___x_180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_180_, 0, v_env_175_);
lean_ctor_set(v___x_180_, 1, v_mctx_177_);
lean_ctor_set(v___x_180_, 2, v_lctx_178_);
lean_ctor_set(v___x_180_, 3, v_options_179_);
v___x_181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_msgData_168_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_ref_196_; lean_object* v___x_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
v_ref_196_ = lean_ctor_get(v___y_193_, 5);
v___x_197_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_206_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc(v_ref_196_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_ref_196_);
lean_ctor_set(v___x_202_, 1, v_a_198_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 1);
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_218_, v_a_226_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_243_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_243_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_243_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_243_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_structs_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_structs_234_ = lean_ctor_get(v_a_230_, 0);
lean_inc_ref(v_structs_234_);
lean_dec(v_a_230_);
v___x_235_ = lean_array_get_size(v_structs_234_);
v___x_236_ = lean_nat_dec_lt(v_a_217_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_structs_234_);
lean_del_object(v___x_232_);
v___x_237_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1);
v___x_238_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_237_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_array_fget(v_structs_234_, v_a_217_);
lean_dec_ref(v_structs_234_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_239_);
v___x_241_ = v___x_232_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_229_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_229_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
lean_dec(v_a_252_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object* v_00_u03b1_265_, lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_266_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_280_, lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(v_00_u03b1_280_, v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object* v_ringId_x3f_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_296_) == 1)
{
lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_335_; 
v_val_308_ = lean_ctor_get(v_ringId_x3f_296_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_ringId_x3f_296_);
if (v_isSharedCheck_335_ == 0)
{
v___x_310_ = v_ringId_x3f_296_;
v_isShared_311_ = v_isSharedCheck_335_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_dec(v_ringId_x3f_296_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_335_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = 0;
v___x_313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_313_, 0, v_val_308_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_312_);
v___x_314_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_313_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_326_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_326_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_326_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_326_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_toRing_319_; lean_object* v___x_321_; 
v_toRing_319_ = lean_ctor_get(v_a_315_, 0);
lean_inc_ref(v_toRing_319_);
lean_dec(v_a_315_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v_toRing_319_);
v___x_321_ = v___x_310_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_toRing_319_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_321_);
v___x_323_ = v___x_317_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_del_object(v___x_310_);
v_a_327_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_314_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_314_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_ringId_x3f_296_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object* v_ringId_x3f_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
return v_res_350_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1);
v___x_360_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_359_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object* v_00_u03b1_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_375_, v_a_376_, v_a_377_, v_a_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object* v_00_u03b1_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(v_00_u03b1_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
return v_res_394_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1);
v___x_404_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_403_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object* v_00_u03b1_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_419_, v_a_420_, v_a_421_, v_a_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object* v_00_u03b1_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(v_00_u03b1_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v_ringId_x3f_453_; lean_object* v___x_454_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_451_);
v_ringId_x3f_453_ = lean_ctor_get(v_a_452_, 1);
lean_inc(v_ringId_x3f_453_);
lean_dec(v_a_452_);
v___x_454_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_453_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
return v___x_454_;
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_451_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_451_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object* v_e_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Sym_canon(v_e_476_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref(v___x_489_);
v___x_491_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_490_, v___y_483_);
return v___x_491_;
}
else
{
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object* v_e_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(v_e_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
lean_dec(v___y_493_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object* v_e_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_e_506_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object* v_e_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(v_e_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
if (lean_obj_tag(v_a_553_) == 1)
{
lean_object* v_val_557_; lean_object* v___x_559_; 
v_val_557_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v_a_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_val_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_val_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; 
lean_del_object(v___x_555_);
lean_dec(v_a_553_);
v___x_561_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_561_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_552_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_552_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec(v_a_572_);
lean_dec(v_a_571_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object* v_f_584_, lean_object* v_s_585_){
_start:
{
lean_object* v_toRing_586_; lean_object* v_invFn_x3f_587_; lean_object* v_semiringId_x3f_588_; lean_object* v_commSemiringInst_589_; lean_object* v_commRingInst_590_; lean_object* v_noZeroDivInst_x3f_591_; lean_object* v_fieldInst_x3f_592_; lean_object* v_powIdentityInst_x3f_593_; lean_object* v_denoteEntries_594_; lean_object* v_nextId_595_; lean_object* v_steps_596_; lean_object* v_queue_597_; lean_object* v_basis_598_; lean_object* v_diseqs_599_; uint8_t v_recheck_600_; lean_object* v_invSet_601_; lean_object* v_powIdentityVarCount_602_; lean_object* v_numEq0_x3f_603_; uint8_t v_numEq0Updated_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_toRing_586_ = lean_ctor_get(v_s_585_, 0);
v_invFn_x3f_587_ = lean_ctor_get(v_s_585_, 1);
v_semiringId_x3f_588_ = lean_ctor_get(v_s_585_, 2);
v_commSemiringInst_589_ = lean_ctor_get(v_s_585_, 3);
v_commRingInst_590_ = lean_ctor_get(v_s_585_, 4);
v_noZeroDivInst_x3f_591_ = lean_ctor_get(v_s_585_, 5);
v_fieldInst_x3f_592_ = lean_ctor_get(v_s_585_, 6);
v_powIdentityInst_x3f_593_ = lean_ctor_get(v_s_585_, 7);
v_denoteEntries_594_ = lean_ctor_get(v_s_585_, 8);
v_nextId_595_ = lean_ctor_get(v_s_585_, 9);
v_steps_596_ = lean_ctor_get(v_s_585_, 10);
v_queue_597_ = lean_ctor_get(v_s_585_, 11);
v_basis_598_ = lean_ctor_get(v_s_585_, 12);
v_diseqs_599_ = lean_ctor_get(v_s_585_, 13);
v_recheck_600_ = lean_ctor_get_uint8(v_s_585_, sizeof(void*)*17);
v_invSet_601_ = lean_ctor_get(v_s_585_, 14);
v_powIdentityVarCount_602_ = lean_ctor_get(v_s_585_, 15);
v_numEq0_x3f_603_ = lean_ctor_get(v_s_585_, 16);
v_numEq0Updated_604_ = lean_ctor_get_uint8(v_s_585_, sizeof(void*)*17 + 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_s_585_);
if (v_isSharedCheck_612_ == 0)
{
v___x_606_ = v_s_585_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_numEq0_x3f_603_);
lean_inc(v_powIdentityVarCount_602_);
lean_inc(v_invSet_601_);
lean_inc(v_diseqs_599_);
lean_inc(v_basis_598_);
lean_inc(v_queue_597_);
lean_inc(v_steps_596_);
lean_inc(v_nextId_595_);
lean_inc(v_denoteEntries_594_);
lean_inc(v_powIdentityInst_x3f_593_);
lean_inc(v_fieldInst_x3f_592_);
lean_inc(v_noZeroDivInst_x3f_591_);
lean_inc(v_commRingInst_590_);
lean_inc(v_commSemiringInst_589_);
lean_inc(v_semiringId_x3f_588_);
lean_inc(v_invFn_x3f_587_);
lean_inc(v_toRing_586_);
lean_dec(v_s_585_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_apply_1(v_f_584_, v_toRing_586_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_invFn_x3f_587_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_semiringId_x3f_588_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_commSemiringInst_589_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_commRingInst_590_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v_noZeroDivInst_x3f_591_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_fieldInst_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_powIdentityInst_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v_denoteEntries_594_);
lean_ctor_set(v_reuseFailAlloc_611_, 9, v_nextId_595_);
lean_ctor_set(v_reuseFailAlloc_611_, 10, v_steps_596_);
lean_ctor_set(v_reuseFailAlloc_611_, 11, v_queue_597_);
lean_ctor_set(v_reuseFailAlloc_611_, 12, v_basis_598_);
lean_ctor_set(v_reuseFailAlloc_611_, 13, v_diseqs_599_);
lean_ctor_set(v_reuseFailAlloc_611_, 14, v_invSet_601_);
lean_ctor_set(v_reuseFailAlloc_611_, 15, v_powIdentityVarCount_602_);
lean_ctor_set(v_reuseFailAlloc_611_, 16, v_numEq0_x3f_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*17, v_recheck_600_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*17 + 1, v_numEq0Updated_604_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object* v_f_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_ringId_x3f_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref(v___x_626_);
v_ringId_x3f_628_ = lean_ctor_get(v_a_627_, 1);
lean_inc(v_ringId_x3f_628_);
lean_dec(v_a_627_);
if (lean_obj_tag(v_ringId_x3f_628_) == 1)
{
lean_object* v_val_629_; lean_object* v___f_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_val_629_ = lean_ctor_get(v_ringId_x3f_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref(v_ringId_x3f_628_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0), 2, 1);
lean_closure_set(v___f_630_, 0, v_f_613_);
v___x_631_ = 0;
v___x_632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_632_, 0, v_val_629_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_631_);
v___x_633_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_630_, v___x_632_, v___y_615_);
lean_dec_ref(v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; 
lean_dec(v_ringId_x3f_628_);
lean_dec_ref(v_f_613_);
v___x_634_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v___x_634_;
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_f_613_);
v_a_635_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_626_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object* v_f_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(v_f_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec(v___y_645_);
lean_dec(v___y_644_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1(void){
_start:
{
lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___f_658_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0));
v___x_659_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed), 12, 0);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___f_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM(void){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object* v_x_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v_ringId_x3f_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
v_ringId_x3f_677_ = lean_ctor_get(v_a_676_, 1);
lean_inc(v_ringId_x3f_677_);
lean_dec(v_a_676_);
if (lean_obj_tag(v_ringId_x3f_677_) == 1)
{
lean_object* v_val_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_val_678_ = lean_ctor_get(v_ringId_x3f_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref(v_ringId_x3f_677_);
v___x_679_ = 0;
v___x_680_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_680_, 0, v_val_678_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1, v___x_679_);
lean_inc(v_a_673_);
lean_inc_ref(v_a_672_);
lean_inc(v_a_671_);
lean_inc_ref(v_a_670_);
lean_inc(v_a_669_);
lean_inc_ref(v_a_668_);
lean_inc(v_a_667_);
lean_inc_ref(v_a_666_);
lean_inc(v_a_665_);
lean_inc(v_a_664_);
v___x_681_ = lean_apply_12(v_x_662_, v___x_680_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, lean_box(0));
return v___x_681_;
}
else
{
lean_object* v___x_682_; 
lean_dec(v_ringId_x3f_677_);
lean_dec_ref(v_x_662_);
v___x_682_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_682_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_x_662_);
v_a_683_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_675_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_675_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object* v_x_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec(v_a_693_);
lean_dec(v_a_692_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object* v_00_u03b1_705_, lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object* v_00_u03b1_720_, lean_object* v_x_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(v_00_u03b1_720_, v_x_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec(v_a_723_);
lean_dec(v_a_722_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object* v_a_735_, lean_object* v_f_736_, lean_object* v_s_737_){
_start:
{
lean_object* v_structs_738_; lean_object* v_typeIdOf_739_; lean_object* v_exprToStructId_740_; lean_object* v_exprToStructIdEntries_741_; lean_object* v_forbiddenNatModules_742_; lean_object* v_natStructs_743_; lean_object* v_natTypeIdOf_744_; lean_object* v_exprToNatStructId_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_structs_738_ = lean_ctor_get(v_s_737_, 0);
v_typeIdOf_739_ = lean_ctor_get(v_s_737_, 1);
v_exprToStructId_740_ = lean_ctor_get(v_s_737_, 2);
v_exprToStructIdEntries_741_ = lean_ctor_get(v_s_737_, 3);
v_forbiddenNatModules_742_ = lean_ctor_get(v_s_737_, 4);
v_natStructs_743_ = lean_ctor_get(v_s_737_, 5);
v_natTypeIdOf_744_ = lean_ctor_get(v_s_737_, 6);
v_exprToNatStructId_745_ = lean_ctor_get(v_s_737_, 7);
v___x_746_ = lean_array_get_size(v_structs_738_);
v___x_747_ = lean_nat_dec_lt(v_a_735_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec_ref(v_f_736_);
return v_s_737_;
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_759_; 
lean_inc_ref(v_exprToNatStructId_745_);
lean_inc_ref(v_natTypeIdOf_744_);
lean_inc_ref(v_natStructs_743_);
lean_inc_ref(v_forbiddenNatModules_742_);
lean_inc_ref(v_exprToStructIdEntries_741_);
lean_inc_ref(v_exprToStructId_740_);
lean_inc_ref(v_typeIdOf_739_);
lean_inc_ref(v_structs_738_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_s_737_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_760_ = lean_ctor_get(v_s_737_, 7);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_s_737_, 6);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_s_737_, 5);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_s_737_, 4);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_s_737_, 3);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_s_737_, 2);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_s_737_, 1);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_s_737_, 0);
lean_dec(v_unused_767_);
v___x_749_ = v_s_737_;
v_isShared_750_ = v_isSharedCheck_759_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_s_737_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_759_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_v_751_; lean_object* v___x_752_; lean_object* v_xs_x27_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v_v_751_ = lean_array_fget(v_structs_738_, v_a_735_);
v___x_752_ = lean_box(0);
v_xs_x27_753_ = lean_array_fset(v_structs_738_, v_a_735_, v___x_752_);
v___x_754_ = lean_apply_1(v_f_736_, v_v_751_);
v___x_755_ = lean_array_fset(v_xs_x27_753_, v_a_735_, v___x_754_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_755_);
v___x_757_ = v___x_749_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_typeIdOf_739_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_exprToStructId_740_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_exprToStructIdEntries_741_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_forbiddenNatModules_742_);
lean_ctor_set(v_reuseFailAlloc_758_, 5, v_natStructs_743_);
lean_ctor_set(v_reuseFailAlloc_758_, 6, v_natTypeIdOf_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 7, v_exprToNatStructId_745_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_768_, lean_object* v_f_769_, lean_object* v_s_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(v_a_768_, v_f_769_, v_s_770_);
lean_dec(v_a_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object* v_f_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc(v_a_773_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_776_, 0, v_a_773_);
lean_closure_set(v___f_776_, 1, v_f_772_);
v___x_777_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_778_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_777_, v___f_776_, v_a_774_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object* v_f_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec(v_a_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object* v_f_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_inc(v_a_785_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_797_, 0, v_a_785_);
lean_closure_set(v___f_797_, 1, v_f_784_);
v___x_798_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_798_, v___f_797_, v_a_786_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object* v_f_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(v_f_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec(v_a_802_);
lean_dec(v_a_801_);
return v_res_813_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM = _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
}
#ifdef __cplusplus
}
#endif
