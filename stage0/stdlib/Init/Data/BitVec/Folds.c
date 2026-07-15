// Lean compiler output
// Module: Init.Data.BitVec.Folds
// Imports: import all Init.Data.BitVec.Basic public import Init.Data.BitVec.Basic public import Init.Ext import Init.Data.BitVec.Lemmas import Init.Data.Fin.Iterate
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
lean_object* l_BitVec_cons(lean_object*, uint8_t, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Fin_hIterate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BitVec_iunfoldr___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_iunfoldr___redArg___closed__0;
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___lam__0(lean_object* v_f_1_, lean_object* v_i_2_, lean_object* v_q_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_17_; 
v_fst_4_ = lean_ctor_get(v_q_3_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_q_3_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_q_3_);
lean_inc(v_i_2_);
v___x_6_ = lean_apply_2(v_f_1_, v_i_2_, v_fst_4_);
v_fst_7_ = lean_ctor_get(v___x_6_, 0);
v_snd_8_ = lean_ctor_get(v___x_6_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_17_ == 0)
{
v___x_10_ = v___x_6_;
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_snd_8_);
lean_inc(v_fst_7_);
lean_dec(v___x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_12_ = lean_unbox(v_snd_8_);
lean_dec(v_snd_8_);
v___x_13_ = l_BitVec_cons(v_i_2_, v___x_12_, v_snd_5_);
lean_dec(v_snd_5_);
lean_dec(v_i_2_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___x_13_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_fst_7_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
static lean_object* _init_l_BitVec_iunfoldr___redArg___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = l_BitVec_ofNat(v___x_18_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg(lean_object* v_w_20_, lean_object* v_f_21_, lean_object* v_s_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___f_23_ = lean_alloc_closure((void*)(l_BitVec_iunfoldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_23_, 0, v_f_21_);
v___x_24_ = lean_obj_once(&l_BitVec_iunfoldr___redArg___closed__0, &l_BitVec_iunfoldr___redArg___closed__0_once, _init_l_BitVec_iunfoldr___redArg___closed__0);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v_s_22_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
v___x_26_ = l_Fin_hIterate___redArg(v_w_20_, v___x_25_, v___f_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___boxed(lean_object* v_w_27_, lean_object* v_f_28_, lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_BitVec_iunfoldr___redArg(v_w_27_, v_f_28_, v_s_29_);
lean_dec(v_w_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr(lean_object* v_w_31_, lean_object* v_00_u03b1_32_, lean_object* v_f_33_, lean_object* v_s_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_BitVec_iunfoldr___redArg(v_w_31_, v_f_33_, v_s_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___boxed(lean_object* v_w_36_, lean_object* v_00_u03b1_37_, lean_object* v_f_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_BitVec_iunfoldr(v_w_36_, v_00_u03b1_37_, v_f_38_, v_s_39_);
lean_dec(v_w_36_);
return v_res_40_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Iterate(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Folds(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Folds(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Iterate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Folds(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Folds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Folds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Folds(builtin);
}
#ifdef __cplusplus
}
#endif
