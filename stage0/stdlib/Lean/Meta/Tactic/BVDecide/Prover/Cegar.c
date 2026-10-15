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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1));
v___x_53_ = l_Lean_stringToMessageData(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___y_70_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0));
v___x_92_ = l_Lean_Core_checkSystem(v___x_91_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; lean_object* v_roundBudget_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
lean_dec_ref_known(v___x_92_, 1);
v___x_93_ = lean_st_ref_get(v_a_55_);
v_roundBudget_94_ = lean_ctor_get(v___x_93_, 5);
lean_inc(v_roundBudget_94_);
lean_dec(v___x_93_);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_nat_dec_eq(v_roundBudget_94_, v___x_95_);
lean_dec(v_roundBudget_94_);
if (v___x_96_ == 0)
{
v___y_70_ = v_a_55_;
goto v___jp_69_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2);
v___x_98_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_97_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
return v___x_98_;
}
}
else
{
return v___x_92_;
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v_satExpr_72_; lean_object* v_hypQueue_73_; lean_object* v_usedHyps_74_; uint8_t v_didChange_75_; lean_object* v_theoryState_76_; lean_object* v_solverTimeBudgetMs_77_; lean_object* v_roundBudget_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_90_; 
v___x_71_ = lean_st_ref_take(v___y_70_);
v_satExpr_72_ = lean_ctor_get(v___x_71_, 0);
v_hypQueue_73_ = lean_ctor_get(v___x_71_, 1);
v_usedHyps_74_ = lean_ctor_get(v___x_71_, 2);
v_didChange_75_ = lean_ctor_get_uint8(v___x_71_, sizeof(void*)*6);
v_theoryState_76_ = lean_ctor_get(v___x_71_, 3);
v_solverTimeBudgetMs_77_ = lean_ctor_get(v___x_71_, 4);
v_roundBudget_78_ = lean_ctor_get(v___x_71_, 5);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_90_ == 0)
{
v___x_80_ = v___x_71_;
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_roundBudget_78_);
lean_inc(v_solverTimeBudgetMs_77_);
lean_inc(v_theoryState_76_);
lean_inc(v_usedHyps_74_);
lean_inc(v_hypQueue_73_);
lean_inc(v_satExpr_72_);
lean_dec(v___x_71_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_sub(v_roundBudget_78_, v___x_83_);
lean_dec(v_roundBudget_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 5, v___x_84_);
v___x_86_ = v___x_80_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_satExpr_72_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_hypQueue_73_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_usedHyps_74_);
lean_ctor_set(v_reuseFailAlloc_89_, 3, v_theoryState_76_);
lean_ctor_set(v_reuseFailAlloc_89_, 4, v_solverTimeBudgetMs_77_);
lean_ctor_set(v_reuseFailAlloc_89_, 5, v___x_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_89_, sizeof(void*)*6, v_didChange_75_);
v___x_86_ = v_reuseFailAlloc_89_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_st_ref_put(v___y_70_, v___x_86_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_82_);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___boxed(lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_object* v_00_u03b1_115_, lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_116_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_133_ = _args[0];
lean_object* v_msg_134_ = _args[1];
lean_object* v___y_135_ = _args[2];
lean_object* v___y_136_ = _args[3];
lean_object* v___y_137_ = _args[4];
lean_object* v___y_138_ = _args[5];
lean_object* v___y_139_ = _args[6];
lean_object* v___y_140_ = _args[7];
lean_object* v___y_141_ = _args[8];
lean_object* v___y_142_ = _args[9];
lean_object* v___y_143_ = _args[10];
lean_object* v___y_144_ = _args[11];
lean_object* v___y_145_ = _args[12];
lean_object* v___y_146_ = _args[13];
lean_object* v___y_147_ = _args[14];
lean_object* v___y_148_ = _args[15];
lean_object* v___y_149_ = _args[16];
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(v_00_u03b1_133_, v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_152_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_tacticContext_155_; lean_object* v_config_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_168_; 
v_tacticContext_155_ = lean_ctor_get(v_a_151_, 2);
v_config_156_ = lean_ctor_get(v_tacticContext_155_, 5);
v_a_157_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_168_ == 0)
{
v___x_159_ = v___x_154_;
v_isShared_160_ = v_isSharedCheck_168_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_154_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_168_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v_solverMode_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v_solverMode_161_ = lean_ctor_get_uint8(v_config_156_, sizeof(void*)*3 + 10);
v___x_162_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_solverMode_161_);
v___x_163_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(v___x_162_);
v___x_164_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v___x_163_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v___x_163_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_164_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_169_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_154_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_154_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg___boxed(lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_181_, v_a_182_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___boxed(lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(size_t v_sz_213_, size_t v_i_214_, lean_object* v_bs_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_216_ == 0)
{
return v_bs_215_;
}
else
{
lean_object* v_v_217_; lean_object* v_funExpr_218_; lean_object* v___x_219_; lean_object* v_bs_x27_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v_v_217_ = lean_array_uget_borrowed(v_bs_215_, v_i_214_);
v_funExpr_218_ = lean_ctor_get(v_v_217_, 0);
lean_inc_ref(v_funExpr_218_);
v___x_219_ = lean_unsigned_to_nat(0u);
v_bs_x27_220_ = lean_array_uset(v_bs_215_, v_i_214_, v___x_219_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_214_, v___x_221_);
v___x_223_ = lean_array_uset(v_bs_x27_220_, v_i_214_, v_funExpr_218_);
v_i_214_ = v___x_222_;
v_bs_215_ = v___x_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2___boxed(lean_object* v_sz_225_, lean_object* v_i_226_, lean_object* v_bs_227_){
_start:
{
size_t v_sz_boxed_228_; size_t v_i_boxed_229_; lean_object* v_res_230_; 
v_sz_boxed_228_ = lean_unbox_usize(v_sz_225_);
lean_dec(v_sz_225_);
v_i_boxed_229_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_boxed_228_, v_i_boxed_229_, v_bs_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(lean_object* v_as_231_, size_t v_i_232_, size_t v_stop_233_, lean_object* v_b_234_){
_start:
{
lean_object* v___y_236_; uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_eq(v_i_232_, v_stop_233_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v_snd_242_; lean_object* v_fst_243_; uint8_t v___x_244_; 
v___x_241_ = lean_array_uget_borrowed(v_as_231_, v_i_232_);
v_snd_242_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_snd_242_);
v_fst_243_ = lean_ctor_get(v_snd_242_, 0);
v___x_244_ = lean_unbox(v_fst_243_);
if (v___x_244_ == 0)
{
lean_object* v_fst_245_; lean_object* v_snd_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_fst_245_ = lean_ctor_get(v___x_241_, 0);
v_snd_246_ = lean_ctor_get(v_snd_242_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_snd_242_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v_snd_242_, 0);
lean_dec(v_unused_255_);
v___x_248_ = v_snd_242_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_snd_246_);
lean_dec(v_snd_242_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
lean_inc(v_fst_245_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v_fst_245_);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_fst_245_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_246_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_push(v_b_234_, v___x_251_);
v___y_236_ = v___x_252_;
goto v___jp_235_;
}
}
}
else
{
lean_dec(v_snd_242_);
v___y_236_ = v_b_234_;
goto v___jp_235_;
}
}
else
{
return v_b_234_;
}
v___jp_235_:
{
size_t v___x_237_; size_t v___x_238_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_232_, v___x_237_);
v_i_232_ = v___x_238_;
v_b_234_ = v___y_236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1___boxed(lean_object* v_as_256_, lean_object* v_i_257_, lean_object* v_stop_258_, lean_object* v_b_259_){
_start:
{
size_t v_i_boxed_260_; size_t v_stop_boxed_261_; lean_object* v_res_262_; 
v_i_boxed_260_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_stop_boxed_261_ = lean_unbox_usize(v_stop_258_);
lean_dec(v_stop_258_);
v_res_262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_256_, v_i_boxed_260_, v_stop_boxed_261_, v_b_259_);
lean_dec_ref(v_as_256_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(lean_object* v_as_265_, lean_object* v_start_266_, lean_object* v_stop_267_){
_start:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___closed__0));
v___x_269_ = lean_nat_dec_lt(v_start_266_, v_stop_267_);
if (v___x_269_ == 0)
{
return v___x_268_;
}
else
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_array_get_size(v_as_265_);
v___x_271_ = lean_nat_dec_le(v_stop_267_, v___x_270_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_lt(v_start_266_, v___x_270_);
if (v___x_272_ == 0)
{
return v___x_268_;
}
else
{
size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_usize_of_nat(v_start_266_);
v___x_274_ = lean_usize_of_nat(v___x_270_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_265_, v___x_273_, v___x_274_, v___x_268_);
return v___x_275_;
}
}
else
{
size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_usize_of_nat(v_start_266_);
v___x_277_ = lean_usize_of_nat(v_stop_267_);
v___x_278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_265_, v___x_276_, v___x_277_, v___x_268_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___boxed(lean_object* v_as_279_, lean_object* v_start_280_, lean_object* v_stop_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_as_279_, v_start_280_, v_stop_281_);
lean_dec(v_stop_281_);
lean_dec(v_start_280_);
lean_dec_ref(v_as_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(lean_object* v_a_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_snd_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_458_; 
v_snd_299_ = lean_ctor_get(v_a_283_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v_a_283_, 0);
lean_dec(v_unused_459_);
v___x_301_ = v_a_283_;
v_isShared_302_ = v_isSharedCheck_458_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snd_299_);
lean_dec(v_a_283_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_458_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; uint8_t v_didChange_306_; 
v___x_303_ = lean_box(0);
v___x_304_ = 1;
v___x_305_ = lean_st_ref_get(v___y_285_);
v_didChange_306_ = lean_ctor_get_uint8(v___x_305_, sizeof(void*)*6);
lean_dec(v___x_305_);
if (v_didChange_306_ == 0)
{
lean_object* v___x_308_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_303_);
v___x_308_ = v___x_301_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_snd_299_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
else
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; 
lean_dec_ref_known(v___x_311_, 1);
v___x_312_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
if (lean_obj_tag(v_a_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_snd_299_);
v_a_314_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_411_ == 0)
{
v___x_316_ = v_a_313_;
v_isShared_317_ = v_isSharedCheck_411_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v_a_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_411_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_a_314_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v___x_320_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkUf(v_a_319_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v___x_321_; 
lean_dec_ref_known(v___x_320_, 1);
v___x_321_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; uint8_t v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
switch(v___x_323_)
{
case 0:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_303_, v___y_285_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_339_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_339_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 1);
lean_ctor_set(v___x_316_, 0, v_a_325_);
v___x_330_ = v___x_316_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_338_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_a_314_);
lean_ctor_set(v___x_301_, 0, v___x_331_);
v___x_333_ = v___x_301_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_314_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_333_);
v___x_335_ = v___x_327_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_del_object(v___x_316_);
lean_dec(v_a_314_);
lean_del_object(v___x_301_);
v_a_340_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_324_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_324_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
case 1:
{
lean_object* v___x_348_; lean_object* v_satExpr_349_; lean_object* v_hypQueue_350_; lean_object* v_usedHyps_351_; lean_object* v_theoryState_352_; lean_object* v_solverTimeBudgetMs_353_; lean_object* v_roundBudget_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_366_; 
lean_del_object(v___x_316_);
v___x_348_ = lean_st_ref_take(v___y_285_);
v_satExpr_349_ = lean_ctor_get(v___x_348_, 0);
v_hypQueue_350_ = lean_ctor_get(v___x_348_, 1);
v_usedHyps_351_ = lean_ctor_get(v___x_348_, 2);
v_theoryState_352_ = lean_ctor_get(v___x_348_, 3);
v_solverTimeBudgetMs_353_ = lean_ctor_get(v___x_348_, 4);
v_roundBudget_354_ = lean_ctor_get(v___x_348_, 5);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_366_ == 0)
{
v___x_356_ = v___x_348_;
v_isShared_357_ = v_isSharedCheck_366_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_roundBudget_354_);
lean_inc(v_solverTimeBudgetMs_353_);
lean_inc(v_theoryState_352_);
lean_inc(v_usedHyps_351_);
lean_inc(v_hypQueue_350_);
lean_inc(v_satExpr_349_);
lean_dec(v___x_348_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_366_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_satExpr_349_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_hypQueue_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_usedHyps_351_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_theoryState_352_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_solverTimeBudgetMs_353_);
lean_ctor_set(v_reuseFailAlloc_365_, 5, v_roundBudget_354_);
v___x_359_ = v_reuseFailAlloc_365_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*6, v___x_304_);
v___x_360_ = lean_st_ref_put(v___y_285_, v___x_359_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_a_314_);
lean_ctor_set(v___x_301_, 0, v___x_303_);
v___x_362_ = v___x_301_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_314_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v_a_283_ = v___x_362_;
goto _start;
}
}
}
}
default: 
{
uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v_satExpr_369_; lean_object* v_hypQueue_370_; lean_object* v_usedHyps_371_; lean_object* v_theoryState_372_; lean_object* v_solverTimeBudgetMs_373_; lean_object* v_roundBudget_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_316_);
v___x_367_ = 0;
v___x_368_ = lean_st_ref_take(v___y_285_);
v_satExpr_369_ = lean_ctor_get(v___x_368_, 0);
v_hypQueue_370_ = lean_ctor_get(v___x_368_, 1);
v_usedHyps_371_ = lean_ctor_get(v___x_368_, 2);
v_theoryState_372_ = lean_ctor_get(v___x_368_, 3);
v_solverTimeBudgetMs_373_ = lean_ctor_get(v___x_368_, 4);
v_roundBudget_374_ = lean_ctor_get(v___x_368_, 5);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_386_ == 0)
{
v___x_376_ = v___x_368_;
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_roundBudget_374_);
lean_inc(v_solverTimeBudgetMs_373_);
lean_inc(v_theoryState_372_);
lean_inc(v_usedHyps_371_);
lean_inc(v_hypQueue_370_);
lean_inc(v_satExpr_369_);
lean_dec(v___x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_satExpr_369_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_hypQueue_370_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_usedHyps_371_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_theoryState_372_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v_solverTimeBudgetMs_373_);
lean_ctor_set(v_reuseFailAlloc_385_, 5, v_roundBudget_374_);
v___x_379_ = v_reuseFailAlloc_385_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*6, v___x_367_);
v___x_380_ = lean_st_ref_put(v___y_285_, v___x_379_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_a_314_);
lean_ctor_set(v___x_301_, 0, v___x_303_);
v___x_382_ = v___x_301_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_a_314_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v_a_283_ = v___x_382_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_del_object(v___x_316_);
lean_dec(v_a_314_);
lean_del_object(v___x_301_);
v_a_387_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_321_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_321_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_del_object(v___x_316_);
lean_dec(v_a_314_);
lean_del_object(v___x_301_);
v_a_395_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_320_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_320_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_del_object(v___x_316_);
lean_dec(v_a_314_);
lean_del_object(v___x_301_);
v_a_403_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_318_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_318_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_441_; 
v_a_412_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_441_ == 0)
{
v___x_414_ = v_a_313_;
v_isShared_415_ = v_isSharedCheck_441_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v_a_313_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_441_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_a_412_);
v___x_417_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_416_, v___y_285_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_432_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_432_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_a_418_);
v___x_423_ = v___x_414_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_431_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_424_);
v___x_426_ = v___x_301_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_snd_299_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_426_);
v___x_428_ = v___x_420_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_del_object(v___x_414_);
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
v_a_433_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_417_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_417_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
v_a_442_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_312_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_312_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_del_object(v___x_301_);
lean_dec(v_snd_299_);
v_a_450_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_311_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_311_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg___boxed(lean_object* v_a_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(lean_object* v_ctx_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_lastCex_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v_config_502_; lean_object* v_satExpr_503_; lean_object* v_unusedHypotheses_504_; lean_object* v_timeout_505_; lean_object* v_cegarRounds_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_a_513_; lean_object* v___x_516_; lean_object* v_satExpr_517_; lean_object* v_hypQueue_518_; lean_object* v_usedHyps_519_; lean_object* v_theoryState_520_; lean_object* v_solverTimeBudgetMs_521_; lean_object* v_roundBudget_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_563_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v_lastCex_499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0));
v___x_500_ = 1;
v___x_501_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_502_ = lean_ctor_get(v_ctx_482_, 5);
v_satExpr_503_ = lean_ctor_get(v_a_484_, 0);
v_unusedHypotheses_504_ = lean_ctor_get(v_a_484_, 1);
v_timeout_505_ = lean_ctor_get(v_config_502_, 0);
v_cegarRounds_506_ = lean_ctor_get(v_config_502_, 2);
v___x_507_ = lean_unsigned_to_nat(1000u);
v___x_508_ = lean_nat_mul(v_timeout_505_, v___x_507_);
lean_inc(v_cegarRounds_506_);
lean_inc_ref(v_satExpr_503_);
v___x_509_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_509_, 0, v_satExpr_503_);
lean_ctor_set(v___x_509_, 1, v_lastCex_499_);
lean_ctor_set(v___x_509_, 2, v_lastCex_499_);
lean_ctor_set(v___x_509_, 3, v___x_501_);
lean_ctor_set(v___x_509_, 4, v___x_508_);
lean_ctor_set(v___x_509_, 5, v_cegarRounds_506_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*6, v___x_500_);
lean_inc_ref(v_unusedHypotheses_504_);
lean_inc(v_a_483_);
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v_a_483_);
lean_ctor_set(v___x_510_, 1, v_unusedHypotheses_504_);
lean_ctor_set(v___x_510_, 2, v_ctx_482_);
v___x_511_ = lean_st_mk_ref(v___x_509_);
v___x_516_ = lean_st_ref_take(v___x_511_);
v_satExpr_517_ = lean_ctor_get(v___x_516_, 0);
v_hypQueue_518_ = lean_ctor_get(v___x_516_, 1);
v_usedHyps_519_ = lean_ctor_get(v___x_516_, 2);
v_theoryState_520_ = lean_ctor_get(v___x_516_, 3);
v_solverTimeBudgetMs_521_ = lean_ctor_get(v___x_516_, 4);
v_roundBudget_522_ = lean_ctor_get(v___x_516_, 5);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_563_ == 0)
{
v___x_524_ = v___x_516_;
v_isShared_525_ = v_isSharedCheck_563_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_roundBudget_522_);
lean_inc(v_solverTimeBudgetMs_521_);
lean_inc(v_theoryState_520_);
lean_inc(v_usedHyps_519_);
lean_inc(v_hypQueue_518_);
lean_inc(v_satExpr_517_);
lean_dec(v___x_516_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_563_;
goto v_resetjp_523_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_st_ref_get(v___x_511_);
lean_dec(v___x_511_);
lean_dec(v___x_514_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_a_513_);
return v___x_515_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_satExpr_517_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_hypQueue_518_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_usedHyps_519_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_theoryState_520_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_solverTimeBudgetMs_521_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_roundBudget_522_);
v___x_527_ = v_reuseFailAlloc_562_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*6, v___x_500_);
v___x_528_ = lean_st_ref_put(v___x_511_, v___x_527_);
v___x_529_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v___x_510_, v___x_511_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec_ref_known(v___x_529_, 1);
v___x_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1));
v___x_531_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v___x_530_, v___x_510_, v___x_511_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec_ref_known(v___x_510_, 3);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v_fst_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v_fst_533_ = lean_ctor_get(v_a_532_, 0);
if (lean_obj_tag(v_fst_533_) == 0)
{
lean_object* v_snd_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_theoryState_538_; lean_object* v_atoms_539_; size_t v_sz_540_; size_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_snd_534_ = lean_ctor_get(v_a_532_, 1);
lean_inc(v_snd_534_);
lean_dec(v_a_532_);
v___x_535_ = lean_array_get_size(v_snd_534_);
v___x_536_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_snd_534_, v___x_498_, v___x_535_);
lean_dec(v_snd_534_);
v___x_537_ = lean_st_ref_get(v_a_487_);
v_theoryState_538_ = lean_ctor_get(v___x_537_, 4);
lean_inc_ref(v_theoryState_538_);
lean_dec(v___x_537_);
v_atoms_539_ = lean_ctor_get(v_theoryState_538_, 0);
lean_inc_ref(v_atoms_539_);
lean_dec_ref(v_theoryState_538_);
v_sz_540_ = lean_array_size(v_atoms_539_);
v___x_541_ = ((size_t)0ULL);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_540_, v___x_541_, v_atoms_539_);
lean_inc_ref(v_unusedHypotheses_504_);
v___x_543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_543_, 0, v_a_483_);
lean_ctor_set(v___x_543_, 1, v_unusedHypotheses_504_);
lean_ctor_set(v___x_543_, 2, v___x_536_);
lean_ctor_set(v___x_543_, 3, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v_a_513_ = v___x_544_;
goto v___jp_512_;
}
else
{
lean_object* v_val_545_; 
lean_inc_ref(v_fst_533_);
lean_dec(v_a_532_);
lean_dec(v_a_483_);
v_val_545_ = lean_ctor_get(v_fst_533_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_fst_533_, 1);
v_a_513_ = v_val_545_;
goto v___jp_512_;
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v___x_511_);
lean_dec(v_a_483_);
v_a_546_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_531_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_531_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v___x_511_);
lean_dec_ref_known(v___x_510_, 3);
lean_dec(v_a_483_);
v_a_554_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_529_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_529_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___boxed(lean_object* v_ctx_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_object* v_inst_581_, lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___boxed(lean_object** _args){
lean_object* v_inst_599_ = _args[0];
lean_object* v_a_600_ = _args[1];
lean_object* v___y_601_ = _args[2];
lean_object* v___y_602_ = _args[3];
lean_object* v___y_603_ = _args[4];
lean_object* v___y_604_ = _args[5];
lean_object* v___y_605_ = _args[6];
lean_object* v___y_606_ = _args[7];
lean_object* v___y_607_ = _args[8];
lean_object* v___y_608_ = _args[9];
lean_object* v___y_609_ = _args[10];
lean_object* v___y_610_ = _args[11];
lean_object* v___y_611_ = _args[12];
lean_object* v___y_612_ = _args[13];
lean_object* v___y_613_ = _args[14];
lean_object* v___y_614_ = _args[15];
lean_object* v___y_615_ = _args[16];
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(v_inst_599_, v_a_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster(lean_object* v_ctx_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_config_634_; uint8_t v_uf_635_; 
v_config_634_ = lean_ctor_get(v_ctx_618_, 5);
v_uf_635_ = lean_ctor_get_uint8(v_config_634_, sizeof(void*)*3 + 11);
if (v_uf_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0));
v___x_637_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed), 16, 1);
lean_closure_set(v___x_637_, 0, v_ctx_618_);
v___x_638_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v___x_636_, v___x_637_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec_ref(v_a_620_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object* v_ctx_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Tactic_BVDecide_cegarBlaster(v_ctx_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
return v_res_656_;
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
