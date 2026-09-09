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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_174_; lean_object* v_env_175_; lean_object* v___x_176_; lean_object* v_toCold_177_; lean_object* v_mctx_178_; lean_object* v_lctx_179_; lean_object* v_options_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = lean_st_ref_get(v___y_170_);
v_toCold_177_ = lean_ctor_get(v___y_171_, 0);
v_mctx_178_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_mctx_178_);
lean_dec(v___x_176_);
v_lctx_179_ = lean_ctor_get(v___y_169_, 2);
v_options_180_ = lean_ctor_get(v_toCold_177_, 2);
lean_inc_ref(v_options_180_);
lean_inc_ref(v_lctx_179_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_175_);
lean_ctor_set(v___x_181_, 1, v_mctx_178_);
lean_ctor_set(v___x_181_, 2, v_lctx_179_);
lean_ctor_set(v___x_181_, 3, v_options_180_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_168_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_ref_197_ = lean_ctor_get(v___y_194_, 2);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_ref_197_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_ref_197_);
lean_ctor_set(v___x_203_, 1, v_a_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 1);
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_219_, v_a_227_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_244_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_244_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_structs_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_structs_235_ = lean_ctor_get(v_a_231_, 0);
lean_inc_ref(v_structs_235_);
lean_dec(v_a_231_);
v___x_236_ = lean_array_get_size(v_structs_235_);
v___x_237_ = lean_nat_dec_lt(v_a_218_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_structs_235_);
lean_del_object(v___x_233_);
v___x_238_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1);
v___x_239_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_238_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_array_fget(v_structs_235_, v_a_218_);
lean_dec_ref(v_structs_235_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_240_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_230_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_230_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object* v_00_u03b1_266_, lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_267_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_281_, lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(v_00_u03b1_281_, v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object* v_ringId_x3f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_297_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_336_; 
v_val_309_ = lean_ctor_get(v_ringId_x3f_297_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_ringId_x3f_297_);
if (v_isSharedCheck_336_ == 0)
{
v___x_311_ = v_ringId_x3f_297_;
v_isShared_312_ = v_isSharedCheck_336_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v_ringId_x3f_297_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_336_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = 0;
v___x_314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_314_, 0, v_val_309_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*1, v___x_313_);
v___x_315_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_314_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec_ref_known(v___x_314_, 1);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_327_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_327_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_toRing_320_; lean_object* v___x_322_; 
v_toRing_320_ = lean_ctor_get(v_a_316_, 0);
lean_inc_ref(v_toRing_320_);
lean_dec(v_a_316_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v_toRing_320_);
v___x_322_ = v___x_311_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_toRing_320_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_322_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_del_object(v___x_311_);
v_a_328_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_315_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_315_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_ringId_x3f_297_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object* v_ringId_x3f_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec(v_a_340_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1);
v___x_361_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_360_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object* v_00_u03b1_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object* v_00_u03b1_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(v_00_u03b1_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec(v_a_384_);
lean_dec(v_a_383_);
return v_res_395_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0));
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1);
v___x_405_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_404_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object* v_00_u03b1_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_420_, v_a_421_, v_a_422_, v_a_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object* v_00_u03b1_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(v_00_u03b1_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v_ringId_x3f_454_; lean_object* v___x_455_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v_ringId_x3f_454_ = lean_ctor_get(v_a_453_, 1);
lean_inc(v_ringId_x3f_454_);
lean_dec(v_a_453_);
v___x_455_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_454_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_452_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object* v_e_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Sym_canon(v_e_477_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = l_Lean_Meta_Sym_shareCommon(v_a_491_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
return v___x_492_;
}
else
{
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object* v_e_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(v_e_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
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
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object* v_e_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_507_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object* v_e_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(v_e_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec(v___y_523_);
lean_dec(v___y_522_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_563_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_563_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
if (lean_obj_tag(v_a_554_) == 1)
{
lean_object* v_val_558_; lean_object* v___x_560_; 
v_val_558_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v_a_554_, 1);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_val_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_val_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v___x_562_; 
lean_del_object(v___x_556_);
lean_dec(v_a_554_);
v___x_562_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_548_, v_a_549_, v_a_550_, v_a_551_);
return v___x_562_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_553_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_553_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
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
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object* v_f_585_, lean_object* v_s_586_){
_start:
{
lean_object* v_toRing_587_; lean_object* v_invFn_x3f_588_; lean_object* v_semiringId_x3f_589_; lean_object* v_commSemiringInst_590_; lean_object* v_commRingInst_591_; lean_object* v_noZeroDivInst_x3f_592_; lean_object* v_fieldInst_x3f_593_; lean_object* v_powIdentityInst_x3f_594_; lean_object* v_denoteEntries_595_; lean_object* v_nextId_596_; lean_object* v_steps_597_; lean_object* v_queue_598_; lean_object* v_basis_599_; lean_object* v_diseqs_600_; uint8_t v_recheck_601_; lean_object* v_invSet_602_; lean_object* v_powIdentityVarCount_603_; lean_object* v_numEq0_x3f_604_; uint8_t v_numEq0Updated_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_toRing_587_ = lean_ctor_get(v_s_586_, 0);
v_invFn_x3f_588_ = lean_ctor_get(v_s_586_, 1);
v_semiringId_x3f_589_ = lean_ctor_get(v_s_586_, 2);
v_commSemiringInst_590_ = lean_ctor_get(v_s_586_, 3);
v_commRingInst_591_ = lean_ctor_get(v_s_586_, 4);
v_noZeroDivInst_x3f_592_ = lean_ctor_get(v_s_586_, 5);
v_fieldInst_x3f_593_ = lean_ctor_get(v_s_586_, 6);
v_powIdentityInst_x3f_594_ = lean_ctor_get(v_s_586_, 7);
v_denoteEntries_595_ = lean_ctor_get(v_s_586_, 8);
v_nextId_596_ = lean_ctor_get(v_s_586_, 9);
v_steps_597_ = lean_ctor_get(v_s_586_, 10);
v_queue_598_ = lean_ctor_get(v_s_586_, 11);
v_basis_599_ = lean_ctor_get(v_s_586_, 12);
v_diseqs_600_ = lean_ctor_get(v_s_586_, 13);
v_recheck_601_ = lean_ctor_get_uint8(v_s_586_, sizeof(void*)*17);
v_invSet_602_ = lean_ctor_get(v_s_586_, 14);
v_powIdentityVarCount_603_ = lean_ctor_get(v_s_586_, 15);
v_numEq0_x3f_604_ = lean_ctor_get(v_s_586_, 16);
v_numEq0Updated_605_ = lean_ctor_get_uint8(v_s_586_, sizeof(void*)*17 + 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_s_586_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v_s_586_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_numEq0_x3f_604_);
lean_inc(v_powIdentityVarCount_603_);
lean_inc(v_invSet_602_);
lean_inc(v_diseqs_600_);
lean_inc(v_basis_599_);
lean_inc(v_queue_598_);
lean_inc(v_steps_597_);
lean_inc(v_nextId_596_);
lean_inc(v_denoteEntries_595_);
lean_inc(v_powIdentityInst_x3f_594_);
lean_inc(v_fieldInst_x3f_593_);
lean_inc(v_noZeroDivInst_x3f_592_);
lean_inc(v_commRingInst_591_);
lean_inc(v_commSemiringInst_590_);
lean_inc(v_semiringId_x3f_589_);
lean_inc(v_invFn_x3f_588_);
lean_inc(v_toRing_587_);
lean_dec(v_s_586_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_apply_1(v_f_585_, v_toRing_587_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_invFn_x3f_588_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_semiringId_x3f_589_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_commSemiringInst_590_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_commRingInst_591_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v_noZeroDivInst_x3f_592_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v_fieldInst_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v_powIdentityInst_x3f_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v_denoteEntries_595_);
lean_ctor_set(v_reuseFailAlloc_612_, 9, v_nextId_596_);
lean_ctor_set(v_reuseFailAlloc_612_, 10, v_steps_597_);
lean_ctor_set(v_reuseFailAlloc_612_, 11, v_queue_598_);
lean_ctor_set(v_reuseFailAlloc_612_, 12, v_basis_599_);
lean_ctor_set(v_reuseFailAlloc_612_, 13, v_diseqs_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 14, v_invSet_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 15, v_powIdentityVarCount_603_);
lean_ctor_set(v_reuseFailAlloc_612_, 16, v_numEq0_x3f_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_612_, sizeof(void*)*17, v_recheck_601_);
lean_ctor_set_uint8(v_reuseFailAlloc_612_, sizeof(void*)*17 + 1, v_numEq0Updated_605_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object* v_f_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_ringId_x3f_629_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v_ringId_x3f_629_ = lean_ctor_get(v_a_628_, 1);
lean_inc(v_ringId_x3f_629_);
lean_dec(v_a_628_);
if (lean_obj_tag(v_ringId_x3f_629_) == 1)
{
lean_object* v_val_630_; lean_object* v___f_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_val_630_ = lean_ctor_get(v_ringId_x3f_629_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_ringId_x3f_629_, 1);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0), 2, 1);
lean_closure_set(v___f_631_, 0, v_f_614_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_633_, 0, v_val_630_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_632_);
v___x_634_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_631_, v___x_633_, v___y_616_);
lean_dec_ref_known(v___x_633_, 1);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec(v_ringId_x3f_629_);
lean_dec_ref(v_f_614_);
v___x_635_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v___x_635_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_f_614_);
v_a_636_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_627_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object* v_f_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(v_f_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v___y_646_);
lean_dec(v___y_645_);
return v_res_657_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1(void){
_start:
{
lean_object* v___f_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___f_659_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0));
v___x_660_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed), 12, 0);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___f_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM(void){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object* v_x_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v_ringId_x3f_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v_ringId_x3f_678_ = lean_ctor_get(v_a_677_, 1);
lean_inc(v_ringId_x3f_678_);
lean_dec(v_a_677_);
if (lean_obj_tag(v_ringId_x3f_678_) == 1)
{
lean_object* v_val_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_val_679_ = lean_ctor_get(v_ringId_x3f_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_ringId_x3f_678_, 1);
v___x_680_ = 0;
v___x_681_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_681_, 0, v_val_679_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v___x_680_);
lean_inc(v_a_674_);
lean_inc_ref(v_a_673_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
lean_inc(v_a_670_);
lean_inc_ref(v_a_669_);
lean_inc(v_a_668_);
lean_inc_ref(v_a_667_);
lean_inc(v_a_666_);
lean_inc(v_a_665_);
v___x_682_ = lean_apply_12(v_x_663_, v___x_681_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, lean_box(0));
return v___x_682_;
}
else
{
lean_object* v___x_683_; 
lean_dec(v_ringId_x3f_678_);
lean_dec_ref(v_x_663_);
v___x_683_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_671_, v_a_672_, v_a_673_, v_a_674_);
return v___x_683_;
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_x_663_);
v_a_684_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_676_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_676_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object* v_x_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec(v_a_694_);
lean_dec(v_a_693_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object* v_00_u03b1_706_, lean_object* v_x_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object* v_00_u03b1_721_, lean_object* v_x_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(v_00_u03b1_721_, v_x_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec(v_a_724_);
lean_dec(v_a_723_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object* v_a_736_, lean_object* v_f_737_, lean_object* v_s_738_){
_start:
{
lean_object* v_structs_739_; lean_object* v_typeIdOf_740_; lean_object* v_exprToStructId_741_; lean_object* v_exprToStructIdEntries_742_; lean_object* v_forbiddenNatModules_743_; lean_object* v_natStructs_744_; lean_object* v_natTypeIdOf_745_; lean_object* v_exprToNatStructId_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_structs_739_ = lean_ctor_get(v_s_738_, 0);
v_typeIdOf_740_ = lean_ctor_get(v_s_738_, 1);
v_exprToStructId_741_ = lean_ctor_get(v_s_738_, 2);
v_exprToStructIdEntries_742_ = lean_ctor_get(v_s_738_, 3);
v_forbiddenNatModules_743_ = lean_ctor_get(v_s_738_, 4);
v_natStructs_744_ = lean_ctor_get(v_s_738_, 5);
v_natTypeIdOf_745_ = lean_ctor_get(v_s_738_, 6);
v_exprToNatStructId_746_ = lean_ctor_get(v_s_738_, 7);
v___x_747_ = lean_array_get_size(v_structs_739_);
v___x_748_ = lean_nat_dec_lt(v_a_736_, v___x_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v_f_737_);
return v_s_738_;
}
else
{
lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_760_; 
lean_inc_ref(v_exprToNatStructId_746_);
lean_inc_ref(v_natTypeIdOf_745_);
lean_inc_ref(v_natStructs_744_);
lean_inc_ref(v_forbiddenNatModules_743_);
lean_inc_ref(v_exprToStructIdEntries_742_);
lean_inc_ref(v_exprToStructId_741_);
lean_inc_ref(v_typeIdOf_740_);
lean_inc_ref(v_structs_739_);
v_isSharedCheck_760_ = !lean_is_exclusive(v_s_738_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; 
v_unused_761_ = lean_ctor_get(v_s_738_, 7);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_s_738_, 6);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_s_738_, 5);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_s_738_, 4);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_s_738_, 3);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_s_738_, 2);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_s_738_, 1);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_s_738_, 0);
lean_dec(v_unused_768_);
v___x_750_ = v_s_738_;
v_isShared_751_ = v_isSharedCheck_760_;
goto v_resetjp_749_;
}
else
{
lean_dec(v_s_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_760_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_v_752_; lean_object* v___x_753_; lean_object* v_xs_x27_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v_v_752_ = lean_array_fget(v_structs_739_, v_a_736_);
v___x_753_ = lean_box(0);
v_xs_x27_754_ = lean_array_fset(v_structs_739_, v_a_736_, v___x_753_);
v___x_755_ = lean_apply_1(v_f_737_, v_v_752_);
v___x_756_ = lean_array_fset(v_xs_x27_754_, v_a_736_, v___x_755_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_756_);
v___x_758_ = v___x_750_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_typeIdOf_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_exprToStructId_741_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_exprToStructIdEntries_742_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_forbiddenNatModules_743_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v_natStructs_744_);
lean_ctor_set(v_reuseFailAlloc_759_, 6, v_natTypeIdOf_745_);
lean_ctor_set(v_reuseFailAlloc_759_, 7, v_exprToNatStructId_746_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_769_, lean_object* v_f_770_, lean_object* v_s_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(v_a_769_, v_f_770_, v_s_771_);
lean_dec(v_a_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object* v_f_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_inc(v_a_774_);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_777_, 0, v_a_774_);
lean_closure_set(v___f_777_, 1, v_f_773_);
v___x_778_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_778_, v___f_777_, v_a_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object* v_f_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec(v_a_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object* v_f_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_inc(v_a_786_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_798_, 0, v_a_786_);
lean_closure_set(v___f_798_, 1, v_f_785_);
v___x_799_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_800_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_799_, v___f_798_, v_a_787_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object* v_f_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(v_f_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec(v_a_803_);
lean_dec(v_a_802_);
return v_res_814_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
