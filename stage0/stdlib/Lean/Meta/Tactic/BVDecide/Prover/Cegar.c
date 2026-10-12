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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___y_72_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0));
v___x_94_ = l_Lean_Core_checkSystem(v___x_93_, v_a_68_, v_a_69_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; lean_object* v_roundBudget_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
lean_dec_ref_known(v___x_94_, 1);
v___x_95_ = lean_st_ref_get(v_a_57_);
v_roundBudget_96_ = lean_ctor_get(v___x_95_, 5);
lean_inc(v_roundBudget_96_);
lean_dec(v___x_95_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_dec_eq(v_roundBudget_96_, v___x_97_);
lean_dec(v_roundBudget_96_);
if (v___x_98_ == 0)
{
v___y_72_ = v_a_57_;
goto v___jp_71_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2);
v___x_100_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_99_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
return v___x_100_;
}
}
else
{
return v___x_94_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v_satExpr_74_; lean_object* v_hypQueue_75_; lean_object* v_usedHyps_76_; uint8_t v_didChange_77_; lean_object* v_theoryState_78_; lean_object* v_solverTimeBudgetMs_79_; lean_object* v_roundBudget_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_92_; 
v___x_73_ = lean_st_ref_take(v___y_72_);
v_satExpr_74_ = lean_ctor_get(v___x_73_, 0);
v_hypQueue_75_ = lean_ctor_get(v___x_73_, 1);
v_usedHyps_76_ = lean_ctor_get(v___x_73_, 2);
v_didChange_77_ = lean_ctor_get_uint8(v___x_73_, sizeof(void*)*6);
v_theoryState_78_ = lean_ctor_get(v___x_73_, 3);
v_solverTimeBudgetMs_79_ = lean_ctor_get(v___x_73_, 4);
v_roundBudget_80_ = lean_ctor_get(v___x_73_, 5);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_92_ == 0)
{
v___x_82_ = v___x_73_;
v_isShared_83_ = v_isSharedCheck_92_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_roundBudget_80_);
lean_inc(v_solverTimeBudgetMs_79_);
lean_inc(v_theoryState_78_);
lean_inc(v_usedHyps_76_);
lean_inc(v_hypQueue_75_);
lean_inc(v_satExpr_74_);
lean_dec(v___x_73_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_92_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_84_ = lean_box(0);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_sub(v_roundBudget_80_, v___x_85_);
lean_dec(v_roundBudget_80_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 5, v___x_86_);
v___x_88_ = v___x_82_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_satExpr_74_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_hypQueue_75_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_usedHyps_76_);
lean_ctor_set(v_reuseFailAlloc_91_, 3, v_theoryState_78_);
lean_ctor_set(v_reuseFailAlloc_91_, 4, v_solverTimeBudgetMs_79_);
lean_ctor_set(v_reuseFailAlloc_91_, 5, v___x_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_91_, sizeof(void*)*6, v_didChange_77_);
v___x_88_ = v_reuseFailAlloc_91_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_st_ref_put(v___y_72_, v___x_88_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_84_);
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_56_ = stack[0].m_obj;
lean_object* v_a_57_ = stack[1].m_obj;
lean_object* v_a_58_ = stack[2].m_obj;
lean_object* v_a_59_ = stack[3].m_obj;
lean_object* v_a_60_ = stack[4].m_obj;
lean_object* v_a_61_ = stack[5].m_obj;
lean_object* v_a_62_ = stack[6].m_obj;
lean_object* v_a_63_ = stack[7].m_obj;
lean_object* v_a_64_ = stack[8].m_obj;
lean_object* v_a_65_ = stack[9].m_obj;
lean_object* v_a_66_ = stack[10].m_obj;
lean_object* v_a_67_ = stack[11].m_obj;
lean_object* v_a_68_ = stack[12].m_obj;
lean_object* v_a_69_ = stack[13].m_obj;
lean_object* v_res_101_;
v_res_101_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___boxed(lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_117_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_object* v_00_u03b1_118_, lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_119_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_119_ = stack[1].m_obj;
lean_object* v___y_120_ = stack[2].m_obj;
lean_object* v___y_121_ = stack[3].m_obj;
lean_object* v___y_122_ = stack[4].m_obj;
lean_object* v___y_123_ = stack[5].m_obj;
lean_object* v___y_124_ = stack[6].m_obj;
lean_object* v___y_125_ = stack[7].m_obj;
lean_object* v___y_126_ = stack[8].m_obj;
lean_object* v___y_127_ = stack[9].m_obj;
lean_object* v___y_128_ = stack[10].m_obj;
lean_object* v___y_129_ = stack[11].m_obj;
lean_object* v___y_130_ = stack[12].m_obj;
lean_object* v___y_131_ = stack[13].m_obj;
lean_object* v___y_132_ = stack[14].m_obj;
lean_object* v___y_133_ = stack[15].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_box(0), v_msg_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_137_ = _args[0];
lean_object* v_msg_138_ = _args[1];
lean_object* v___y_139_ = _args[2];
lean_object* v___y_140_ = _args[3];
lean_object* v___y_141_ = _args[4];
lean_object* v___y_142_ = _args[5];
lean_object* v___y_143_ = _args[6];
lean_object* v___y_144_ = _args[7];
lean_object* v___y_145_ = _args[8];
lean_object* v___y_146_ = _args[9];
lean_object* v___y_147_ = _args[10];
lean_object* v___y_148_ = _args[11];
lean_object* v___y_149_ = _args[12];
lean_object* v___y_150_ = _args[13];
lean_object* v___y_151_ = _args[14];
lean_object* v___y_152_ = _args[15];
lean_object* v___y_153_ = _args[16];
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(v_00_u03b1_137_, v_msg_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_154_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_tacticContext_159_; lean_object* v_config_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_172_; 
v_tacticContext_159_ = lean_ctor_get(v_a_155_, 2);
v_config_160_ = lean_ctor_get(v_tacticContext_159_, 5);
v_a_161_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_172_ == 0)
{
v___x_163_ = v___x_158_;
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_158_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
uint8_t v_solverMode_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v_solverMode_165_ = lean_ctor_get_uint8(v_config_160_, sizeof(void*)*3 + 10);
v___x_166_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_solverMode_165_);
v___x_167_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(v___x_166_);
v___x_168_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v___x_167_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v___x_167_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_168_);
v___x_170_ = v___x_163_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_158_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_158_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_155_ = stack[0].m_obj;
lean_object* v_a_156_ = stack[1].m_obj;
lean_object* v_res_181_;
v_res_181_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_155_, v_a_156_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg___boxed(lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_185_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_186_, v_a_187_);
return v___x_201_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_186_ = stack[0].m_obj;
lean_object* v_a_187_ = stack[1].m_obj;
lean_object* v_a_188_ = stack[2].m_obj;
lean_object* v_a_189_ = stack[3].m_obj;
lean_object* v_a_190_ = stack[4].m_obj;
lean_object* v_a_191_ = stack[5].m_obj;
lean_object* v_a_192_ = stack[6].m_obj;
lean_object* v_a_193_ = stack[7].m_obj;
lean_object* v_a_194_ = stack[8].m_obj;
lean_object* v_a_195_ = stack[9].m_obj;
lean_object* v_a_196_ = stack[10].m_obj;
lean_object* v_a_197_ = stack[11].m_obj;
lean_object* v_a_198_ = stack[12].m_obj;
lean_object* v_a_199_ = stack[13].m_obj;
lean_object* v_res_202_;
v_res_202_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___boxed(lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_218_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(size_t v_sz_219_, size_t v_i_220_, lean_object* v_bs_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_lt(v_i_220_, v_sz_219_);
if (v___x_222_ == 0)
{
return v_bs_221_;
}
else
{
lean_object* v_v_223_; lean_object* v_funExpr_224_; lean_object* v___x_225_; lean_object* v_bs_x27_226_; size_t v___x_227_; size_t v___x_228_; lean_object* v___x_229_; 
v_v_223_ = lean_array_uget_borrowed(v_bs_221_, v_i_220_);
v_funExpr_224_ = lean_ctor_get(v_v_223_, 0);
lean_inc_ref(v_funExpr_224_);
v___x_225_ = lean_unsigned_to_nat(0u);
v_bs_x27_226_ = lean_array_uset(v_bs_221_, v_i_220_, v___x_225_);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_add(v_i_220_, v___x_227_);
v___x_229_ = lean_array_uset(v_bs_x27_226_, v_i_220_, v_funExpr_224_);
v_i_220_ = v___x_228_;
v_bs_221_ = v___x_229_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_219_ = stack[0].m_num;
size_t v_i_220_ = stack[1].m_num;
lean_object* v_bs_221_ = stack[2].m_obj;
lean_object* v_res_231_;
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_219_, v_i_220_, v_bs_221_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2___boxed(lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_bs_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_boxed_235_, v_i_boxed_236_, v_bs_234_);
return v_res_237_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(lean_object* v_as_238_, size_t v_i_239_, size_t v_stop_240_, lean_object* v_b_241_){
_start:
{
lean_object* v___y_243_; uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_eq(v_i_239_, v_stop_240_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v_snd_249_; lean_object* v_fst_250_; uint8_t v___x_251_; 
v___x_248_ = lean_array_uget_borrowed(v_as_238_, v_i_239_);
v_snd_249_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_snd_249_);
v_fst_250_ = lean_ctor_get(v_snd_249_, 0);
v___x_251_ = lean_unbox(v_fst_250_);
if (v___x_251_ == 0)
{
lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_fst_252_ = lean_ctor_get(v___x_248_, 0);
v_snd_253_ = lean_ctor_get(v_snd_249_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v_snd_249_, 0);
lean_dec(v_unused_262_);
v___x_255_ = v_snd_249_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_snd_253_);
lean_dec(v_snd_249_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
lean_inc(v_fst_252_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v_fst_252_);
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_fst_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_snd_253_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = lean_array_push(v_b_241_, v___x_258_);
v___y_243_ = v___x_259_;
goto v___jp_242_;
}
}
}
else
{
lean_dec(v_snd_249_);
v___y_243_ = v_b_241_;
goto v___jp_242_;
}
}
else
{
return v_b_241_;
}
v___jp_242_:
{
size_t v___x_244_; size_t v___x_245_; 
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_239_, v___x_244_);
v_i_239_ = v___x_245_;
v_b_241_ = v___y_243_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_238_ = stack[0].m_obj;
size_t v_i_239_ = stack[1].m_num;
size_t v_stop_240_ = stack[2].m_num;
lean_object* v_b_241_ = stack[3].m_obj;
lean_object* v_res_263_;
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_238_, v_i_239_, v_stop_240_, v_b_241_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1___boxed(lean_object* v_as_264_, lean_object* v_i_265_, lean_object* v_stop_266_, lean_object* v_b_267_){
_start:
{
size_t v_i_boxed_268_; size_t v_stop_boxed_269_; lean_object* v_res_270_; 
v_i_boxed_268_ = lean_unbox_usize(v_i_265_);
lean_dec(v_i_265_);
v_stop_boxed_269_ = lean_unbox_usize(v_stop_266_);
lean_dec(v_stop_266_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_264_, v_i_boxed_268_, v_stop_boxed_269_, v_b_267_);
lean_dec_ref(v_as_264_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(lean_object* v_as_273_, lean_object* v_start_274_, lean_object* v_stop_275_){
_start:
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___closed__0));
v___x_277_ = lean_nat_dec_lt(v_start_274_, v_stop_275_);
if (v___x_277_ == 0)
{
return v___x_276_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_array_get_size(v_as_273_);
v___x_279_ = lean_nat_dec_le(v_stop_275_, v___x_278_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; 
v___x_280_ = lean_nat_dec_lt(v_start_274_, v___x_278_);
if (v___x_280_ == 0)
{
return v___x_276_;
}
else
{
size_t v___x_281_; size_t v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_usize_of_nat(v_start_274_);
v___x_282_ = lean_usize_of_nat(v___x_278_);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_273_, v___x_281_, v___x_282_, v___x_276_);
return v___x_283_;
}
}
else
{
size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_usize_of_nat(v_start_274_);
v___x_285_ = lean_usize_of_nat(v_stop_275_);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1_spec__1(v_as_273_, v___x_284_, v___x_285_, v___x_276_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___boxed(lean_object* v_as_287_, lean_object* v_start_288_, lean_object* v_stop_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_as_287_, v_start_288_, v_stop_289_);
lean_dec(v_stop_289_);
lean_dec(v_start_288_);
lean_dec_ref(v_as_287_);
return v_res_290_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(lean_object* v_a_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_snd_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_466_; 
v_snd_307_ = lean_ctor_get(v_a_291_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_a_291_, 0);
lean_dec(v_unused_467_);
v___x_309_ = v_a_291_;
v_isShared_310_ = v_isSharedCheck_466_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_snd_307_);
lean_dec(v_a_291_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_466_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; uint8_t v_didChange_314_; 
v___x_311_ = lean_box(0);
v___x_312_ = 1;
v___x_313_ = lean_st_ref_get(v___y_293_);
v_didChange_314_ = lean_ctor_get_uint8(v___x_313_, sizeof(void*)*6);
lean_dec(v___x_313_);
if (v_didChange_314_ == 0)
{
lean_object* v___x_316_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_311_);
v___x_316_ = v___x_309_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_snd_307_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
else
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_320_; 
lean_dec_ref_known(v___x_319_, 1);
v___x_320_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
if (lean_obj_tag(v_a_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_snd_307_);
v_a_322_ = lean_ctor_get(v_a_321_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_321_);
if (v_isSharedCheck_419_ == 0)
{
v___x_324_ = v_a_321_;
v_isShared_325_ = v_isSharedCheck_419_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v_a_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_419_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_a_322_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkUf(v_a_327_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec_ref_known(v___x_328_, 1);
v___x_329_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; uint8_t v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = lean_unbox(v_a_330_);
lean_dec(v_a_330_);
switch(v___x_331_)
{
case 0:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_311_, v___y_293_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_347_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_347_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_347_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_347_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 1);
lean_ctor_set(v___x_324_, 0, v_a_333_);
v___x_338_ = v___x_324_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_346_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_a_322_);
lean_ctor_set(v___x_309_, 0, v___x_339_);
v___x_341_ = v___x_309_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_a_322_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_341_);
v___x_343_ = v___x_335_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
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
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_del_object(v___x_324_);
lean_dec(v_a_322_);
lean_del_object(v___x_309_);
v_a_348_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_332_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_332_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
case 1:
{
lean_object* v___x_356_; lean_object* v_satExpr_357_; lean_object* v_hypQueue_358_; lean_object* v_usedHyps_359_; lean_object* v_theoryState_360_; lean_object* v_solverTimeBudgetMs_361_; lean_object* v_roundBudget_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_374_; 
lean_del_object(v___x_324_);
v___x_356_ = lean_st_ref_take(v___y_293_);
v_satExpr_357_ = lean_ctor_get(v___x_356_, 0);
v_hypQueue_358_ = lean_ctor_get(v___x_356_, 1);
v_usedHyps_359_ = lean_ctor_get(v___x_356_, 2);
v_theoryState_360_ = lean_ctor_get(v___x_356_, 3);
v_solverTimeBudgetMs_361_ = lean_ctor_get(v___x_356_, 4);
v_roundBudget_362_ = lean_ctor_get(v___x_356_, 5);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_374_ == 0)
{
v___x_364_ = v___x_356_;
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_roundBudget_362_);
lean_inc(v_solverTimeBudgetMs_361_);
lean_inc(v_theoryState_360_);
lean_inc(v_usedHyps_359_);
lean_inc(v_hypQueue_358_);
lean_inc(v_satExpr_357_);
lean_dec(v___x_356_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_satExpr_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_hypQueue_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_usedHyps_359_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_theoryState_360_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_solverTimeBudgetMs_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_roundBudget_362_);
v___x_367_ = v_reuseFailAlloc_373_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*6, v___x_312_);
v___x_368_ = lean_st_ref_put(v___y_293_, v___x_367_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_a_322_);
lean_ctor_set(v___x_309_, 0, v___x_311_);
v___x_370_ = v___x_309_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_a_322_);
v___x_370_ = v_reuseFailAlloc_372_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v_a_291_ = v___x_370_;
goto _start;
}
}
}
}
default: 
{
uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v_satExpr_377_; lean_object* v_hypQueue_378_; lean_object* v_usedHyps_379_; lean_object* v_theoryState_380_; lean_object* v_solverTimeBudgetMs_381_; lean_object* v_roundBudget_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_394_; 
lean_del_object(v___x_324_);
v___x_375_ = 0;
v___x_376_ = lean_st_ref_take(v___y_293_);
v_satExpr_377_ = lean_ctor_get(v___x_376_, 0);
v_hypQueue_378_ = lean_ctor_get(v___x_376_, 1);
v_usedHyps_379_ = lean_ctor_get(v___x_376_, 2);
v_theoryState_380_ = lean_ctor_get(v___x_376_, 3);
v_solverTimeBudgetMs_381_ = lean_ctor_get(v___x_376_, 4);
v_roundBudget_382_ = lean_ctor_get(v___x_376_, 5);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_394_ == 0)
{
v___x_384_ = v___x_376_;
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_roundBudget_382_);
lean_inc(v_solverTimeBudgetMs_381_);
lean_inc(v_theoryState_380_);
lean_inc(v_usedHyps_379_);
lean_inc(v_hypQueue_378_);
lean_inc(v_satExpr_377_);
lean_dec(v___x_376_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_satExpr_377_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_hypQueue_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_usedHyps_379_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_theoryState_380_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_solverTimeBudgetMs_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 5, v_roundBudget_382_);
v___x_387_ = v_reuseFailAlloc_393_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*6, v___x_375_);
v___x_388_ = lean_st_ref_put(v___y_293_, v___x_387_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_a_322_);
lean_ctor_set(v___x_309_, 0, v___x_311_);
v___x_390_ = v___x_309_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_a_322_);
v___x_390_ = v_reuseFailAlloc_392_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
v_a_291_ = v___x_390_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_del_object(v___x_324_);
lean_dec(v_a_322_);
lean_del_object(v___x_309_);
v_a_395_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_329_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_329_);
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
lean_del_object(v___x_324_);
lean_dec(v_a_322_);
lean_del_object(v___x_309_);
v_a_403_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_328_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_328_);
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
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_del_object(v___x_324_);
lean_dec(v_a_322_);
lean_del_object(v___x_309_);
v_a_411_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_326_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_326_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_449_; 
v_a_420_ = lean_ctor_get(v_a_321_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_321_);
if (v_isSharedCheck_449_ == 0)
{
v___x_422_ = v_a_321_;
v_isShared_423_ = v_isSharedCheck_449_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v_a_321_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_449_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_a_420_);
v___x_425_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_424_, v___y_293_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_440_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_440_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_440_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_440_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_a_426_);
v___x_431_ = v___x_422_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_439_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_432_);
v___x_434_ = v___x_309_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_307_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_434_);
v___x_436_ = v___x_428_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
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
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_del_object(v___x_422_);
lean_del_object(v___x_309_);
lean_dec(v_snd_307_);
v_a_441_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_425_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_425_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_del_object(v___x_309_);
lean_dec(v_snd_307_);
v_a_450_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_320_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_320_);
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
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_del_object(v___x_309_);
lean_dec(v_snd_307_);
v_a_458_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_319_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_319_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_291_ = stack[0].m_obj;
lean_object* v___y_292_ = stack[1].m_obj;
lean_object* v___y_293_ = stack[2].m_obj;
lean_object* v___y_294_ = stack[3].m_obj;
lean_object* v___y_295_ = stack[4].m_obj;
lean_object* v___y_296_ = stack[5].m_obj;
lean_object* v___y_297_ = stack[6].m_obj;
lean_object* v___y_298_ = stack[7].m_obj;
lean_object* v___y_299_ = stack[8].m_obj;
lean_object* v___y_300_ = stack[9].m_obj;
lean_object* v___y_301_ = stack[10].m_obj;
lean_object* v___y_302_ = stack[11].m_obj;
lean_object* v___y_303_ = stack[12].m_obj;
lean_object* v___y_304_ = stack[13].m_obj;
lean_object* v___y_305_ = stack[14].m_obj;
lean_object* v_res_468_;
v_res_468_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg___boxed(lean_object* v_a_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_485_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(lean_object* v_ctx_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; lean_object* v_lastCex_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v_config_511_; lean_object* v_satExpr_512_; lean_object* v_unusedHypotheses_513_; lean_object* v_timeout_514_; lean_object* v_cegarRounds_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_a_522_; lean_object* v___x_525_; lean_object* v_satExpr_526_; lean_object* v_hypQueue_527_; lean_object* v_usedHyps_528_; lean_object* v_theoryState_529_; lean_object* v_solverTimeBudgetMs_530_; lean_object* v_roundBudget_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_572_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v_lastCex_508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0));
v___x_509_ = 1;
v___x_510_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_511_ = lean_ctor_get(v_ctx_491_, 5);
v_satExpr_512_ = lean_ctor_get(v_a_493_, 0);
v_unusedHypotheses_513_ = lean_ctor_get(v_a_493_, 1);
v_timeout_514_ = lean_ctor_get(v_config_511_, 0);
v_cegarRounds_515_ = lean_ctor_get(v_config_511_, 2);
v___x_516_ = lean_unsigned_to_nat(1000u);
v___x_517_ = lean_nat_mul(v_timeout_514_, v___x_516_);
lean_inc(v_cegarRounds_515_);
lean_inc_ref(v_satExpr_512_);
v___x_518_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_518_, 0, v_satExpr_512_);
lean_ctor_set(v___x_518_, 1, v_lastCex_508_);
lean_ctor_set(v___x_518_, 2, v_lastCex_508_);
lean_ctor_set(v___x_518_, 3, v___x_510_);
lean_ctor_set(v___x_518_, 4, v___x_517_);
lean_ctor_set(v___x_518_, 5, v_cegarRounds_515_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*6, v___x_509_);
lean_inc_ref(v_unusedHypotheses_513_);
lean_inc(v_a_492_);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v_a_492_);
lean_ctor_set(v___x_519_, 1, v_unusedHypotheses_513_);
lean_ctor_set(v___x_519_, 2, v_ctx_491_);
v___x_520_ = lean_st_mk_ref(v___x_518_);
v___x_525_ = lean_st_ref_take(v___x_520_);
v_satExpr_526_ = lean_ctor_get(v___x_525_, 0);
v_hypQueue_527_ = lean_ctor_get(v___x_525_, 1);
v_usedHyps_528_ = lean_ctor_get(v___x_525_, 2);
v_theoryState_529_ = lean_ctor_get(v___x_525_, 3);
v_solverTimeBudgetMs_530_ = lean_ctor_get(v___x_525_, 4);
v_roundBudget_531_ = lean_ctor_get(v___x_525_, 5);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_572_ == 0)
{
v___x_533_ = v___x_525_;
v_isShared_534_ = v_isSharedCheck_572_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_roundBudget_531_);
lean_inc(v_solverTimeBudgetMs_530_);
lean_inc(v_theoryState_529_);
lean_inc(v_usedHyps_528_);
lean_inc(v_hypQueue_527_);
lean_inc(v_satExpr_526_);
lean_dec(v___x_525_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_572_;
goto v_resetjp_532_;
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_st_ref_get(v___x_520_);
lean_dec(v___x_520_);
lean_dec(v___x_523_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_a_522_);
return v___x_524_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_satExpr_526_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_hypQueue_527_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_usedHyps_528_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_theoryState_529_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_solverTimeBudgetMs_530_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v_roundBudget_531_);
v___x_536_ = v_reuseFailAlloc_571_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*6, v___x_509_);
v___x_537_ = lean_st_ref_put(v___x_520_, v___x_536_);
v___x_538_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v___x_519_, v___x_520_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1));
v___x_540_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v___x_539_, v___x_519_, v___x_520_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec_ref_known(v___x_519_, 3);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v_fst_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v_fst_542_ = lean_ctor_get(v_a_541_, 0);
if (lean_obj_tag(v_fst_542_) == 0)
{
lean_object* v_snd_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_theoryState_547_; lean_object* v_atoms_548_; size_t v_sz_549_; size_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_snd_543_ = lean_ctor_get(v_a_541_, 1);
lean_inc(v_snd_543_);
lean_dec(v_a_541_);
v___x_544_ = lean_array_get_size(v_snd_543_);
v___x_545_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_snd_543_, v___x_507_, v___x_544_);
lean_dec(v_snd_543_);
v___x_546_ = lean_st_ref_get(v_a_496_);
v_theoryState_547_ = lean_ctor_get(v___x_546_, 4);
lean_inc_ref(v_theoryState_547_);
lean_dec(v___x_546_);
v_atoms_548_ = lean_ctor_get(v_theoryState_547_, 0);
lean_inc_ref(v_atoms_548_);
lean_dec_ref(v_theoryState_547_);
v_sz_549_ = lean_array_size(v_atoms_548_);
v___x_550_ = ((size_t)0ULL);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__2(v_sz_549_, v___x_550_, v_atoms_548_);
lean_inc_ref(v_unusedHypotheses_513_);
v___x_552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_552_, 0, v_a_492_);
lean_ctor_set(v___x_552_, 1, v_unusedHypotheses_513_);
lean_ctor_set(v___x_552_, 2, v___x_545_);
lean_ctor_set(v___x_552_, 3, v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v_a_522_ = v___x_553_;
goto v___jp_521_;
}
else
{
lean_object* v_val_554_; 
lean_inc_ref(v_fst_542_);
lean_dec(v_a_541_);
lean_dec(v_a_492_);
v_val_554_ = lean_ctor_get(v_fst_542_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_fst_542_, 1);
v_a_522_ = v_val_554_;
goto v___jp_521_;
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v___x_520_);
lean_dec(v_a_492_);
v_a_555_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_540_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_540_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v___x_520_);
lean_dec_ref_known(v___x_519_, 3);
lean_dec(v_a_492_);
v_a_563_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_538_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_538_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_491_ = stack[0].m_obj;
lean_object* v_a_492_ = stack[1].m_obj;
lean_object* v_a_493_ = stack[2].m_obj;
lean_object* v_a_494_ = stack[3].m_obj;
lean_object* v_a_495_ = stack[4].m_obj;
lean_object* v_a_496_ = stack[5].m_obj;
lean_object* v_a_497_ = stack[6].m_obj;
lean_object* v_a_498_ = stack[7].m_obj;
lean_object* v_a_499_ = stack[8].m_obj;
lean_object* v_a_500_ = stack[9].m_obj;
lean_object* v_a_501_ = stack[10].m_obj;
lean_object* v_a_502_ = stack[11].m_obj;
lean_object* v_a_503_ = stack[12].m_obj;
lean_object* v_a_504_ = stack[13].m_obj;
lean_object* v_a_505_ = stack[14].m_obj;
lean_object* v_res_573_;
v_res_573_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___boxed(lean_object* v_ctx_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
return v_res_590_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_object* v_inst_591_, lean_object* v_a_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_608_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_592_ = stack[1].m_obj;
lean_object* v___y_593_ = stack[2].m_obj;
lean_object* v___y_594_ = stack[3].m_obj;
lean_object* v___y_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v___y_598_ = stack[7].m_obj;
lean_object* v___y_599_ = stack[8].m_obj;
lean_object* v___y_600_ = stack[9].m_obj;
lean_object* v___y_601_ = stack[10].m_obj;
lean_object* v___y_602_ = stack[11].m_obj;
lean_object* v___y_603_ = stack[12].m_obj;
lean_object* v___y_604_ = stack[13].m_obj;
lean_object* v___y_605_ = stack[14].m_obj;
lean_object* v___y_606_ = stack[15].m_obj;
lean_object* v_res_609_;
v_res_609_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_box(0), v_a_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___boxed(lean_object** _args){
lean_object* v_inst_610_ = _args[0];
lean_object* v_a_611_ = _args[1];
lean_object* v___y_612_ = _args[2];
lean_object* v___y_613_ = _args[3];
lean_object* v___y_614_ = _args[4];
lean_object* v___y_615_ = _args[5];
lean_object* v___y_616_ = _args[6];
lean_object* v___y_617_ = _args[7];
lean_object* v___y_618_ = _args[8];
lean_object* v___y_619_ = _args[9];
lean_object* v___y_620_ = _args[10];
lean_object* v___y_621_ = _args[11];
lean_object* v___y_622_ = _args[12];
lean_object* v___y_623_ = _args[13];
lean_object* v___y_624_ = _args[14];
lean_object* v___y_625_ = _args[15];
lean_object* v___y_626_ = _args[16];
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(v_inst_610_, v_a_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_627_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster(lean_object* v_ctx_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_config_645_; uint8_t v_uf_646_; 
v_config_645_ = lean_ctor_get(v_ctx_629_, 5);
v_uf_646_ = lean_ctor_get_uint8(v_config_645_, sizeof(void*)*3 + 11);
if (v_uf_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0));
v___x_648_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed), 16, 1);
lean_closure_set(v___x_648_, 0, v_ctx_629_);
v___x_649_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v___x_647_, v___x_648_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec_ref(v_a_631_);
return v___x_650_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_cegarBlaster_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_629_ = stack[0].m_obj;
lean_object* v_a_630_ = stack[1].m_obj;
lean_object* v_a_631_ = stack[2].m_obj;
lean_object* v_a_632_ = stack[3].m_obj;
lean_object* v_a_633_ = stack[4].m_obj;
lean_object* v_a_634_ = stack[5].m_obj;
lean_object* v_a_635_ = stack[6].m_obj;
lean_object* v_a_636_ = stack[7].m_obj;
lean_object* v_a_637_ = stack[8].m_obj;
lean_object* v_a_638_ = stack[9].m_obj;
lean_object* v_a_639_ = stack[10].m_obj;
lean_object* v_a_640_ = stack[11].m_obj;
lean_object* v_a_641_ = stack[12].m_obj;
lean_object* v_a_642_ = stack[13].m_obj;
lean_object* v_a_643_ = stack[14].m_obj;
lean_object* v_res_651_;
v_res_651_ = l_Lean_Meta_Tactic_BVDecide_cegarBlaster(v_ctx_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object* v_ctx_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_Tactic_BVDecide_cegarBlaster(v_ctx_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
return v_res_668_;
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
