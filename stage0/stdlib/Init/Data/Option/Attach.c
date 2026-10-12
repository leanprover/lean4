// Lean compiler output
// Module: Init.Data.Option.Attach
// Imports: public import Init.Data.Array.Attach public import Init.Data.Option.Lemmas import Init.Data.Bool import Init.Data.Option.Array import Init.Data.Option.List import Init.Data.Subtype.Basic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Option_instMonadAttach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_instMonadAttach___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Option_instMonadAttach___closed__0 = (const lean_object*)&l_Option_instMonadAttach___closed__0_value;
LEAN_EXPORT const lean_object* l_Option_instMonadAttach = (const lean_object*)&l_Option_instMonadAttach___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(lean_object* v_o_1_){
_start:
{
lean_inc(v_o_1_);
return v_o_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(lean_object* v_o_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(v_o_2_);
lean_dec(v_o_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(lean_object* v_00_u03b1_4_, lean_object* v_o_5_, lean_object* v_P_6_, lean_object* v_x_7_){
_start:
{
lean_inc(v_o_5_);
return v_o_5_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_o_9_, lean_object* v_P_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(v_00_u03b1_8_, v_o_9_, v_P_10_, v_x_11_);
lean_dec(v_o_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Option_attach___redArg(lean_object* v_xs_13_){
_start:
{
lean_inc(v_xs_13_);
return v_xs_13_;
}
}
LEAN_EXPORT lean_object* l_Option_attach___redArg___boxed(lean_object* v_xs_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Option_attach___redArg(v_xs_14_);
lean_dec(v_xs_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Option_attach(lean_object* v_00_u03b1_16_, lean_object* v_xs_17_){
_start:
{
lean_inc(v_xs_17_);
return v_xs_17_;
}
}
LEAN_EXPORT lean_object* l_Option_attach___boxed(lean_object* v_00_u03b1_18_, lean_object* v_xs_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Option_attach(v_00_u03b1_18_, v_xs_19_);
lean_dec(v_xs_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Option_unattach___redArg(lean_object* v_o_21_){
_start:
{
if (lean_obj_tag(v_o_21_) == 0)
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
else
{
lean_object* v_val_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_val_23_ = lean_ctor_get(v_o_21_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_o_21_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v_o_21_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_val_23_);
lean_dec(v_o_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_val_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_unattach(lean_object* v_00_u03b1_31_, lean_object* v_p_32_, lean_object* v_o_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Option_unattach___redArg(v_o_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0(lean_object* v_00_u03b1_35_, lean_object* v_x_36_){
_start:
{
lean_inc(v_x_36_);
return v_x_36_;
}
}
LEAN_EXPORT lean_object* l_Option_instMonadAttach___lam__0___boxed(lean_object* v_00_u03b1_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Option_instMonadAttach___lam__0(v_00_u03b1_37_, v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___redArg(lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_45_; 
lean_dec(v_h__1_43_);
v___x_45_ = lean_apply_1(v_h__2_44_, lean_box(0));
return v___x_45_;
}
else
{
lean_object* v_val_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_44_);
v_val_46_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_x_42_, 1);
v___x_47_ = lean_apply_2(v_h__1_43_, v_val_46_, lean_box(0));
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(lean_object* v_m_48_, lean_object* v_inst_49_, lean_object* v_00_u03b1_50_, lean_object* v_x_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_56_; 
lean_dec(v_h__1_54_);
v___x_56_ = lean_apply_1(v_h__2_55_, lean_box(0));
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_55_);
v_val_57_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_x_53_, 1);
v___x_58_ = lean_apply_2(v_h__1_54_, v_val_57_, lean_box(0));
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___boxed(lean_object* v_m_59_, lean_object* v_inst_60_, lean_object* v_00_u03b1_61_, lean_object* v_x_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(v_m_59_, v_inst_60_, v_00_u03b1_61_, v_x_62_, v_motive_63_, v_x_64_, v_h__1_65_, v_h__2_66_);
lean_dec(v_x_62_);
lean_dec(v_inst_60_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter___redArg(lean_object* v_____do__lift_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
if (lean_obj_tag(v_____do__lift_68_) == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__2_70_, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_70_);
v_val_73_ = lean_ctor_get(v_____do__lift_68_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v_____do__lift_68_, 1);
v___x_74_ = lean_apply_1(v_h__1_69_, v_val_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter(lean_object* v_00_u03b1_75_, lean_object* v_motive_76_, lean_object* v_____do__lift_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_____do__lift_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__2_79_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_79_);
v_val_82_ = lean_ctor_get(v_____do__lift_77_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v_____do__lift_77_, 1);
v___x_83_ = lean_apply_1(v_h__1_78_, v_val_82_);
return v___x_83_;
}
}
}
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Option_List(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
