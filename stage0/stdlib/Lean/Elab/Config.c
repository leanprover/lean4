// Lean compiler output
// Module: Lean.Elab.Config
// Imports: public import Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_setElabConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_setElabConfig(lean_object* v_cfg_1_){
_start:
{
uint8_t v_isDefEqStuckEx_2_; uint8_t v_unificationHints_3_; uint8_t v_proofIrrelevance_4_; uint8_t v_assignSyntheticOpaque_5_; uint8_t v_offsetCnstrs_6_; uint8_t v_transparency_7_; uint8_t v_etaStruct_8_; uint8_t v_univApprox_9_; uint8_t v_iota_10_; uint8_t v_beta_11_; uint8_t v_proj_12_; uint8_t v_zeta_13_; uint8_t v_zetaDelta_14_; uint8_t v_zetaUnused_15_; uint8_t v_zetaHave_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_25_; 
v_isDefEqStuckEx_2_ = lean_ctor_get_uint8(v_cfg_1_, 4);
v_unificationHints_3_ = lean_ctor_get_uint8(v_cfg_1_, 5);
v_proofIrrelevance_4_ = lean_ctor_get_uint8(v_cfg_1_, 6);
v_assignSyntheticOpaque_5_ = lean_ctor_get_uint8(v_cfg_1_, 7);
v_offsetCnstrs_6_ = lean_ctor_get_uint8(v_cfg_1_, 8);
v_transparency_7_ = lean_ctor_get_uint8(v_cfg_1_, 9);
v_etaStruct_8_ = lean_ctor_get_uint8(v_cfg_1_, 10);
v_univApprox_9_ = lean_ctor_get_uint8(v_cfg_1_, 11);
v_iota_10_ = lean_ctor_get_uint8(v_cfg_1_, 12);
v_beta_11_ = lean_ctor_get_uint8(v_cfg_1_, 13);
v_proj_12_ = lean_ctor_get_uint8(v_cfg_1_, 14);
v_zeta_13_ = lean_ctor_get_uint8(v_cfg_1_, 15);
v_zetaDelta_14_ = lean_ctor_get_uint8(v_cfg_1_, 16);
v_zetaUnused_15_ = lean_ctor_get_uint8(v_cfg_1_, 17);
v_zetaHave_16_ = lean_ctor_get_uint8(v_cfg_1_, 18);
v_isSharedCheck_25_ = !lean_is_exclusive(v_cfg_1_);
if (v_isSharedCheck_25_ == 0)
{
v___x_18_ = v_cfg_1_;
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
else
{
lean_dec(v_cfg_1_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_25_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; uint8_t v___x_21_; lean_object* v___x_23_; 
v___x_20_ = 1;
v___x_21_ = 0;
if (v_isShared_19_ == 0)
{
v___x_23_ = v___x_18_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 4, v_isDefEqStuckEx_2_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 5, v_unificationHints_3_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 6, v_proofIrrelevance_4_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 7, v_assignSyntheticOpaque_5_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 8, v_offsetCnstrs_6_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 9, v_transparency_7_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 10, v_etaStruct_8_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 11, v_univApprox_9_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 12, v_iota_10_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 13, v_beta_11_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 14, v_proj_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 15, v_zeta_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 16, v_zetaDelta_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 17, v_zetaUnused_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, 18, v_zetaHave_16_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_ctor_set_uint8(v___x_23_, 0, v___x_20_);
lean_ctor_set_uint8(v___x_23_, 1, v___x_20_);
lean_ctor_set_uint8(v___x_23_, 2, v___x_21_);
lean_ctor_set_uint8(v___x_23_, 3, v___x_21_);
return v___x_23_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Config(builtin);
}
#ifdef __cplusplus
}
#endif
