// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Function public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Lemmas import Lean.Meta.Tactic.BVDecide.Prover.Bitblast import Lean.Meta.Tactic.BVDecide.External
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
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkUf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "bv_decide reached its round limit, consider increasing it via the `cegarRounds` config option"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___boxed(lean_object**);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1));
v___x_51_ = l_Lean_stringToMessageData(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___y_68_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0));
v___x_90_ = l_Lean_Core_checkSystem(v___x_89_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; lean_object* v_roundBudget_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
lean_dec_ref_known(v___x_90_, 1);
v___x_91_ = lean_st_ref_get(v_a_53_);
v_roundBudget_92_ = lean_ctor_get(v___x_91_, 5);
lean_inc(v_roundBudget_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_nat_dec_eq(v_roundBudget_92_, v___x_93_);
lean_dec(v_roundBudget_92_);
if (v___x_94_ == 0)
{
v___y_68_ = v_a_53_;
goto v___jp_67_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2);
v___x_96_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_95_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
return v___x_96_;
}
}
else
{
return v___x_90_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v_satExpr_70_; lean_object* v_hypQueue_71_; lean_object* v_usedHyps_72_; uint8_t v_didChange_73_; lean_object* v_theoryState_74_; lean_object* v_solverTimeBudgetMs_75_; lean_object* v_roundBudget_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_88_; 
v___x_69_ = lean_st_ref_take(v___y_68_);
v_satExpr_70_ = lean_ctor_get(v___x_69_, 0);
v_hypQueue_71_ = lean_ctor_get(v___x_69_, 1);
v_usedHyps_72_ = lean_ctor_get(v___x_69_, 2);
v_didChange_73_ = lean_ctor_get_uint8(v___x_69_, sizeof(void*)*6);
v_theoryState_74_ = lean_ctor_get(v___x_69_, 3);
v_solverTimeBudgetMs_75_ = lean_ctor_get(v___x_69_, 4);
v_roundBudget_76_ = lean_ctor_get(v___x_69_, 5);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_88_ == 0)
{
v___x_78_ = v___x_69_;
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_roundBudget_76_);
lean_inc(v_solverTimeBudgetMs_75_);
lean_inc(v_theoryState_74_);
lean_inc(v_usedHyps_72_);
lean_inc(v_hypQueue_71_);
lean_inc(v_satExpr_70_);
lean_dec(v___x_69_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_80_ = lean_box(0);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v_roundBudget_76_, v___x_81_);
lean_dec(v_roundBudget_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 5, v___x_82_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_satExpr_70_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_hypQueue_71_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_usedHyps_72_);
lean_ctor_set(v_reuseFailAlloc_87_, 3, v_theoryState_74_);
lean_ctor_set(v_reuseFailAlloc_87_, 4, v_solverTimeBudgetMs_75_);
lean_ctor_set(v_reuseFailAlloc_87_, 5, v___x_82_);
lean_ctor_set_uint8(v_reuseFailAlloc_87_, sizeof(void*)*6, v_didChange_73_);
v___x_84_ = v_reuseFailAlloc_87_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_st_ref_put(v___y_68_, v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_80_);
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___boxed(lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_object* v_00_u03b1_113_, lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_114_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_131_ = _args[0];
lean_object* v_msg_132_ = _args[1];
lean_object* v___y_133_ = _args[2];
lean_object* v___y_134_ = _args[3];
lean_object* v___y_135_ = _args[4];
lean_object* v___y_136_ = _args[5];
lean_object* v___y_137_ = _args[6];
lean_object* v___y_138_ = _args[7];
lean_object* v___y_139_ = _args[8];
lean_object* v___y_140_ = _args[9];
lean_object* v___y_141_ = _args[10];
lean_object* v___y_142_ = _args[11];
lean_object* v___y_143_ = _args[12];
lean_object* v___y_144_ = _args[13];
lean_object* v___y_145_ = _args[14];
lean_object* v___y_146_ = _args[15];
lean_object* v___y_147_ = _args[16];
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(v_00_u03b1_131_, v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_150_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_tacticContext_153_; lean_object* v_config_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_166_; 
v_tacticContext_153_ = lean_ctor_get(v_a_149_, 2);
v_config_154_ = lean_ctor_get(v_tacticContext_153_, 5);
v_a_155_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_166_ == 0)
{
v___x_157_ = v___x_152_;
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_152_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
uint8_t v_solverMode_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v_solverMode_159_ = lean_ctor_get_uint8(v_config_154_, sizeof(void*)*3 + 10);
v___x_160_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_solverMode_159_);
v___x_161_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(v___x_160_);
v___x_162_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v___x_161_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v___x_161_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_162_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_152_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_152_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg___boxed(lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_179_, v_a_180_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___boxed(lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(size_t v_sz_211_, size_t v_i_212_, lean_object* v_bs_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = lean_usize_dec_lt(v_i_212_, v_sz_211_);
if (v___x_214_ == 0)
{
return v_bs_213_;
}
else
{
lean_object* v_v_215_; lean_object* v_funExpr_216_; lean_object* v___x_217_; lean_object* v_bs_x27_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; 
v_v_215_ = lean_array_uget_borrowed(v_bs_213_, v_i_212_);
v_funExpr_216_ = lean_ctor_get(v_v_215_, 0);
lean_inc_ref(v_funExpr_216_);
v___x_217_ = lean_unsigned_to_nat(0u);
v_bs_x27_218_ = lean_array_uset(v_bs_213_, v_i_212_, v___x_217_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_212_, v___x_219_);
v___x_221_ = lean_array_uset(v_bs_x27_218_, v_i_212_, v_funExpr_216_);
v_i_212_ = v___x_220_;
v_bs_213_ = v___x_221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2___boxed(lean_object* v_sz_223_, lean_object* v_i_224_, lean_object* v_bs_225_){
_start:
{
size_t v_sz_boxed_226_; size_t v_i_boxed_227_; lean_object* v_res_228_; 
v_sz_boxed_226_ = lean_unbox_usize(v_sz_223_);
lean_dec(v_sz_223_);
v_i_boxed_227_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_res_228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_boxed_226_, v_i_boxed_227_, v_bs_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(lean_object* v_as_229_, size_t v_i_230_, size_t v_stop_231_, lean_object* v_b_232_){
_start:
{
lean_object* v___y_234_; uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_eq(v_i_230_, v_stop_231_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v_snd_240_; lean_object* v_fst_241_; uint8_t v___x_242_; 
v___x_239_ = lean_array_uget_borrowed(v_as_229_, v_i_230_);
v_snd_240_ = lean_ctor_get(v___x_239_, 1);
lean_inc(v_snd_240_);
v_fst_241_ = lean_ctor_get(v_snd_240_, 0);
v___x_242_ = lean_unbox(v_fst_241_);
if (v___x_242_ == 0)
{
lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_fst_243_ = lean_ctor_get(v___x_239_, 0);
v_snd_244_ = lean_ctor_get(v_snd_240_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_snd_240_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_snd_240_, 0);
lean_dec(v_unused_253_);
v___x_246_ = v_snd_240_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snd_244_);
lean_dec(v_snd_240_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
lean_inc(v_fst_243_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v_fst_243_);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_fst_243_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_snd_244_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_array_push(v_b_232_, v___x_249_);
v___y_234_ = v___x_250_;
goto v___jp_233_;
}
}
}
else
{
lean_dec(v_snd_240_);
v___y_234_ = v_b_232_;
goto v___jp_233_;
}
}
else
{
return v_b_232_;
}
v___jp_233_:
{
size_t v___x_235_; size_t v___x_236_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_230_, v___x_235_);
v_i_230_ = v___x_236_;
v_b_232_ = v___y_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1___boxed(lean_object* v_as_254_, lean_object* v_i_255_, lean_object* v_stop_256_, lean_object* v_b_257_){
_start:
{
size_t v_i_boxed_258_; size_t v_stop_boxed_259_; lean_object* v_res_260_; 
v_i_boxed_258_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_stop_boxed_259_ = lean_unbox_usize(v_stop_256_);
lean_dec(v_stop_256_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_254_, v_i_boxed_258_, v_stop_boxed_259_, v_b_257_);
lean_dec_ref(v_as_254_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(lean_object* v_as_263_, lean_object* v_start_264_, lean_object* v_stop_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___closed__0));
v___x_267_ = lean_nat_dec_lt(v_start_264_, v_stop_265_);
if (v___x_267_ == 0)
{
return v___x_266_;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_array_get_size(v_as_263_);
v___x_269_ = lean_nat_dec_le(v_stop_265_, v___x_268_);
if (v___x_269_ == 0)
{
uint8_t v___x_270_; 
v___x_270_ = lean_nat_dec_lt(v_start_264_, v___x_268_);
if (v___x_270_ == 0)
{
return v___x_266_;
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_usize_of_nat(v_start_264_);
v___x_272_ = lean_usize_of_nat(v___x_268_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_263_, v___x_271_, v___x_272_, v___x_266_);
return v___x_273_;
}
}
else
{
size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_usize_of_nat(v_start_264_);
v___x_275_ = lean_usize_of_nat(v_stop_265_);
v___x_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_263_, v___x_274_, v___x_275_, v___x_266_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___boxed(lean_object* v_as_277_, lean_object* v_start_278_, lean_object* v_stop_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_as_277_, v_start_278_, v_stop_279_);
lean_dec(v_stop_279_);
lean_dec(v_start_278_);
lean_dec_ref(v_as_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(lean_object* v_a_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_snd_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_456_; 
v_snd_297_ = lean_ctor_get(v_a_281_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_a_281_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_a_281_, 0);
lean_dec(v_unused_457_);
v___x_299_ = v_a_281_;
v_isShared_300_ = v_isSharedCheck_456_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_snd_297_);
lean_dec(v_a_281_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_456_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; uint8_t v_didChange_304_; 
v___x_301_ = lean_box(0);
v___x_302_ = 1;
v___x_303_ = lean_st_ref_get(v___y_283_);
v_didChange_304_ = lean_ctor_get_uint8(v___x_303_, sizeof(void*)*6);
lean_dec(v___x_303_);
if (v_didChange_304_ == 0)
{
lean_object* v___x_306_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_306_ = v___x_299_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_snd_297_);
v___x_306_ = v_reuseFailAlloc_308_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
else
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v___x_310_; 
lean_dec_ref_known(v___x_309_, 1);
v___x_310_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
if (lean_obj_tag(v_a_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_snd_297_);
v_a_312_ = lean_ctor_get(v_a_311_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_a_311_);
if (v_isSharedCheck_409_ == 0)
{
v___x_314_ = v_a_311_;
v_isShared_315_ = v_isSharedCheck_409_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v_a_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_409_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_a_312_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___x_318_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkUf(v_a_317_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_319_; 
lean_dec_ref_known(v___x_318_, 1);
v___x_319_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; uint8_t v___x_321_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v___x_321_ = lean_unbox(v_a_320_);
lean_dec(v_a_320_);
switch(v___x_321_)
{
case 0:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_301_, v___y_283_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_337_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_337_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 1);
lean_ctor_set(v___x_314_, 0, v_a_323_);
v___x_328_ = v___x_314_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_336_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_a_312_);
lean_ctor_set(v___x_299_, 0, v___x_329_);
v___x_331_ = v___x_299_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_a_312_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_331_);
v___x_333_ = v___x_325_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
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
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_del_object(v___x_314_);
lean_dec(v_a_312_);
lean_del_object(v___x_299_);
v_a_338_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_322_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_322_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
case 1:
{
lean_object* v___x_346_; lean_object* v_satExpr_347_; lean_object* v_hypQueue_348_; lean_object* v_usedHyps_349_; lean_object* v_theoryState_350_; lean_object* v_solverTimeBudgetMs_351_; lean_object* v_roundBudget_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
lean_del_object(v___x_314_);
v___x_346_ = lean_st_ref_take(v___y_283_);
v_satExpr_347_ = lean_ctor_get(v___x_346_, 0);
v_hypQueue_348_ = lean_ctor_get(v___x_346_, 1);
v_usedHyps_349_ = lean_ctor_get(v___x_346_, 2);
v_theoryState_350_ = lean_ctor_get(v___x_346_, 3);
v_solverTimeBudgetMs_351_ = lean_ctor_get(v___x_346_, 4);
v_roundBudget_352_ = lean_ctor_get(v___x_346_, 5);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_364_ == 0)
{
v___x_354_ = v___x_346_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_roundBudget_352_);
lean_inc(v_solverTimeBudgetMs_351_);
lean_inc(v_theoryState_350_);
lean_inc(v_usedHyps_349_);
lean_inc(v_hypQueue_348_);
lean_inc(v_satExpr_347_);
lean_dec(v___x_346_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_satExpr_347_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_hypQueue_348_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_usedHyps_349_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_theoryState_350_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_solverTimeBudgetMs_351_);
lean_ctor_set(v_reuseFailAlloc_363_, 5, v_roundBudget_352_);
v___x_357_ = v_reuseFailAlloc_363_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*6, v___x_302_);
v___x_358_ = lean_st_ref_put(v___y_283_, v___x_357_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_a_312_);
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_360_ = v___x_299_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_a_312_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
v_a_281_ = v___x_360_;
goto _start;
}
}
}
}
default: 
{
uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v_satExpr_367_; lean_object* v_hypQueue_368_; lean_object* v_usedHyps_369_; lean_object* v_theoryState_370_; lean_object* v_solverTimeBudgetMs_371_; lean_object* v_roundBudget_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_384_; 
lean_del_object(v___x_314_);
v___x_365_ = 0;
v___x_366_ = lean_st_ref_take(v___y_283_);
v_satExpr_367_ = lean_ctor_get(v___x_366_, 0);
v_hypQueue_368_ = lean_ctor_get(v___x_366_, 1);
v_usedHyps_369_ = lean_ctor_get(v___x_366_, 2);
v_theoryState_370_ = lean_ctor_get(v___x_366_, 3);
v_solverTimeBudgetMs_371_ = lean_ctor_get(v___x_366_, 4);
v_roundBudget_372_ = lean_ctor_get(v___x_366_, 5);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_384_ == 0)
{
v___x_374_ = v___x_366_;
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_roundBudget_372_);
lean_inc(v_solverTimeBudgetMs_371_);
lean_inc(v_theoryState_370_);
lean_inc(v_usedHyps_369_);
lean_inc(v_hypQueue_368_);
lean_inc(v_satExpr_367_);
lean_dec(v___x_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_satExpr_367_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_hypQueue_368_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_usedHyps_369_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_theoryState_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_solverTimeBudgetMs_371_);
lean_ctor_set(v_reuseFailAlloc_383_, 5, v_roundBudget_372_);
v___x_377_ = v_reuseFailAlloc_383_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*6, v___x_365_);
v___x_378_ = lean_st_ref_put(v___y_283_, v___x_377_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_a_312_);
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_380_ = v___x_299_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_312_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v_a_281_ = v___x_380_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_del_object(v___x_314_);
lean_dec(v_a_312_);
lean_del_object(v___x_299_);
v_a_385_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_319_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_319_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
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
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_del_object(v___x_314_);
lean_dec(v_a_312_);
lean_del_object(v___x_299_);
v_a_393_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_318_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_318_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_314_);
lean_dec(v_a_312_);
lean_del_object(v___x_299_);
v_a_401_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_316_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_316_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_439_; 
v_a_410_ = lean_ctor_get(v_a_311_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_311_);
if (v_isSharedCheck_439_ == 0)
{
v___x_412_ = v_a_311_;
v_isShared_413_ = v_isSharedCheck_439_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v_a_311_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_439_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_a_410_);
v___x_415_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_414_, v___y_283_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_430_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_430_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_430_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_430_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v_a_416_);
v___x_421_ = v___x_412_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_429_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_422_);
v___x_424_ = v___x_299_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_snd_297_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_424_);
v___x_426_ = v___x_418_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_del_object(v___x_412_);
lean_del_object(v___x_299_);
lean_dec(v_snd_297_);
v_a_431_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_415_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_415_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_del_object(v___x_299_);
lean_dec(v_snd_297_);
v_a_440_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_310_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_310_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_299_);
lean_dec(v_snd_297_);
v_a_448_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_309_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_309_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg___boxed(lean_object* v_a_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(lean_object* v_ctx_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_lastCex_497_; uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v_config_500_; lean_object* v_satExpr_501_; lean_object* v_unusedHypotheses_502_; lean_object* v_timeout_503_; lean_object* v_cegarRounds_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_a_511_; lean_object* v___x_514_; lean_object* v_satExpr_515_; lean_object* v_hypQueue_516_; lean_object* v_usedHyps_517_; lean_object* v_theoryState_518_; lean_object* v_solverTimeBudgetMs_519_; lean_object* v_roundBudget_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_561_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v_lastCex_497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0));
v___x_498_ = 1;
v___x_499_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_500_ = lean_ctor_get(v_ctx_480_, 5);
v_satExpr_501_ = lean_ctor_get(v_a_482_, 0);
v_unusedHypotheses_502_ = lean_ctor_get(v_a_482_, 1);
v_timeout_503_ = lean_ctor_get(v_config_500_, 0);
v_cegarRounds_504_ = lean_ctor_get(v_config_500_, 2);
v___x_505_ = lean_unsigned_to_nat(1000u);
v___x_506_ = lean_nat_mul(v_timeout_503_, v___x_505_);
lean_inc(v_cegarRounds_504_);
lean_inc_ref(v_satExpr_501_);
v___x_507_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_507_, 0, v_satExpr_501_);
lean_ctor_set(v___x_507_, 1, v_lastCex_497_);
lean_ctor_set(v___x_507_, 2, v_lastCex_497_);
lean_ctor_set(v___x_507_, 3, v___x_499_);
lean_ctor_set(v___x_507_, 4, v___x_506_);
lean_ctor_set(v___x_507_, 5, v_cegarRounds_504_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*6, v___x_498_);
lean_inc_ref(v_unusedHypotheses_502_);
lean_inc(v_a_481_);
v___x_508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_508_, 0, v_a_481_);
lean_ctor_set(v___x_508_, 1, v_unusedHypotheses_502_);
lean_ctor_set(v___x_508_, 2, v_ctx_480_);
v___x_509_ = lean_st_mk_ref(v___x_507_);
v___x_514_ = lean_st_ref_take(v___x_509_);
v_satExpr_515_ = lean_ctor_get(v___x_514_, 0);
v_hypQueue_516_ = lean_ctor_get(v___x_514_, 1);
v_usedHyps_517_ = lean_ctor_get(v___x_514_, 2);
v_theoryState_518_ = lean_ctor_get(v___x_514_, 3);
v_solverTimeBudgetMs_519_ = lean_ctor_get(v___x_514_, 4);
v_roundBudget_520_ = lean_ctor_get(v___x_514_, 5);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_561_ == 0)
{
v___x_522_ = v___x_514_;
v_isShared_523_ = v_isSharedCheck_561_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_roundBudget_520_);
lean_inc(v_solverTimeBudgetMs_519_);
lean_inc(v_theoryState_518_);
lean_inc(v_usedHyps_517_);
lean_inc(v_hypQueue_516_);
lean_inc(v_satExpr_515_);
lean_dec(v___x_514_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_561_;
goto v_resetjp_521_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_st_ref_get(v___x_509_);
lean_dec(v___x_509_);
lean_dec(v___x_512_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_a_511_);
return v___x_513_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_satExpr_515_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_hypQueue_516_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_usedHyps_517_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_theoryState_518_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_solverTimeBudgetMs_519_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_roundBudget_520_);
v___x_525_ = v_reuseFailAlloc_560_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*6, v___x_498_);
v___x_526_ = lean_st_ref_put(v___x_509_, v___x_525_);
v___x_527_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v___x_508_, v___x_509_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref_known(v___x_527_, 1);
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1));
v___x_529_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v___x_528_, v___x_508_, v___x_509_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec_ref_known(v___x_508_, 3);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v_fst_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v_fst_531_ = lean_ctor_get(v_a_530_, 0);
if (lean_obj_tag(v_fst_531_) == 0)
{
lean_object* v_snd_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_theoryState_536_; lean_object* v_atoms_537_; size_t v_sz_538_; size_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_snd_532_ = lean_ctor_get(v_a_530_, 1);
lean_inc(v_snd_532_);
lean_dec(v_a_530_);
v___x_533_ = lean_array_get_size(v_snd_532_);
v___x_534_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_snd_532_, v___x_496_, v___x_533_);
lean_dec(v_snd_532_);
v___x_535_ = lean_st_ref_get(v_a_485_);
v_theoryState_536_ = lean_ctor_get(v___x_535_, 4);
lean_inc_ref(v_theoryState_536_);
lean_dec(v___x_535_);
v_atoms_537_ = lean_ctor_get(v_theoryState_536_, 0);
lean_inc_ref(v_atoms_537_);
lean_dec_ref(v_theoryState_536_);
v_sz_538_ = lean_array_size(v_atoms_537_);
v___x_539_ = ((size_t)0ULL);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_538_, v___x_539_, v_atoms_537_);
lean_inc_ref(v_unusedHypotheses_502_);
v___x_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_541_, 0, v_a_481_);
lean_ctor_set(v___x_541_, 1, v_unusedHypotheses_502_);
lean_ctor_set(v___x_541_, 2, v___x_534_);
lean_ctor_set(v___x_541_, 3, v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v_a_511_ = v___x_542_;
goto v___jp_510_;
}
else
{
lean_object* v_val_543_; 
lean_inc_ref(v_fst_531_);
lean_dec(v_a_530_);
lean_dec(v_a_481_);
v_val_543_ = lean_ctor_get(v_fst_531_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_fst_531_, 1);
v_a_511_ = v_val_543_;
goto v___jp_510_;
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v___x_509_);
lean_dec(v_a_481_);
v_a_544_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_529_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_529_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v___x_509_);
lean_dec_ref_known(v___x_508_, 3);
lean_dec(v_a_481_);
v_a_552_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_527_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_527_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___boxed(lean_object* v_ctx_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_object* v_inst_579_, lean_object* v_a_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___boxed(lean_object** _args){
lean_object* v_inst_597_ = _args[0];
lean_object* v_a_598_ = _args[1];
lean_object* v___y_599_ = _args[2];
lean_object* v___y_600_ = _args[3];
lean_object* v___y_601_ = _args[4];
lean_object* v___y_602_ = _args[5];
lean_object* v___y_603_ = _args[6];
lean_object* v___y_604_ = _args[7];
lean_object* v___y_605_ = _args[8];
lean_object* v___y_606_ = _args[9];
lean_object* v___y_607_ = _args[10];
lean_object* v___y_608_ = _args[11];
lean_object* v___y_609_ = _args[12];
lean_object* v___y_610_ = _args[13];
lean_object* v___y_611_ = _args[14];
lean_object* v___y_612_ = _args[15];
lean_object* v___y_613_ = _args[16];
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(v_inst_597_, v_a_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster(lean_object* v_ctx_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_config_632_; uint8_t v_uf_633_; 
v_config_632_ = lean_ctor_get(v_ctx_616_, 5);
v_uf_633_ = lean_ctor_get_uint8(v_config_632_, sizeof(void*)*3 + 11);
if (v_uf_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0));
v___x_635_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed), 16, 1);
lean_closure_set(v___x_635_, 0, v_ctx_616_);
v___x_636_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v___x_634_, v___x_635_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec_ref(v_a_618_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object* v_ctx_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_Tactic_BVDecide_cegarBlaster(v_ctx_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
return v_res_654_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
}
#ifdef __cplusplus
}
#endif
