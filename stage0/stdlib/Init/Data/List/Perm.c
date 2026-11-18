// Lean compiler output
// Module: Init.Data.List.Perm
// Imports: import all Init.Data.List.Attach public import Init.Data.List.Attach import Init.Data.List.Erase public import Init.Data.List.Impl import Init.Data.List.Pairwise import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isPermTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg();
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm(lean_object*);
LEAN_EXPORT lean_object* l_List_isSetoid___redArg();
LEAN_EXPORT lean_object* l_List_isSetoid___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_isSetoid(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidablePerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidablePerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidablePerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_List_instTransPerm___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_List_instTransPerm(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_List_isSetoid___redArg(){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_List_isSetoid___redArg___boxed(lean_object* v___dummy_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_List_isSetoid___redArg();
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_List_isSetoid(lean_object* v_00_u03b1_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_17_; 
lean_dec(v_h__2_16_);
v___x_17_ = lean_apply_1(v_h__1_15_, v_x_13_);
return v___x_17_;
}
else
{
lean_object* v_head_18_; lean_object* v_tail_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v_head_18_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_18_);
v_tail_19_ = lean_ctor_get(v_x_14_, 1);
lean_inc(v_tail_19_);
lean_dec_ref_known(v_x_14_, 2);
v___x_20_ = lean_apply_3(v_h__2_16_, v_x_13_, v_head_18_, v_tail_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_28_; 
lean_dec(v_h__2_27_);
v___x_28_ = lean_apply_1(v_h__1_26_, v_x_24_);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_26_);
v_head_29_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_head_29_);
v_tail_30_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_tail_30_);
lean_dec_ref_known(v_x_25_, 2);
v___x_31_ = lean_apply_3(v_h__2_27_, v_x_24_, v_head_29_, v_tail_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_34_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__1_33_, v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_33_);
v_head_37_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_37_);
v_tail_38_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_tail_38_);
lean_dec_ref_known(v_x_32_, 2);
v___x_39_ = lean_apply_2(v_h__2_34_, v_head_37_, v_tail_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_40_, lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_44_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_apply_1(v_h__1_43_, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_43_);
v_head_47_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_head_47_);
v_tail_48_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_tail_48_);
lean_dec_ref_known(v_x_42_, 2);
v___x_49_ = lean_apply_2(v_h__2_44_, v_head_47_, v_tail_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT uint8_t l_List_decidablePerm___redArg(lean_object* v_inst_50_, lean_object* v_l_u2081_51_, lean_object* v_l_u2082_52_){
_start:
{
lean_object* v___f_53_; uint8_t v___x_54_; 
v___f_53_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_53_, 0, v_inst_50_);
v___x_54_ = l_List_isPermTR___redArg(v___f_53_, v_l_u2081_51_, v_l_u2082_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_List_decidablePerm___redArg___boxed(lean_object* v_inst_55_, lean_object* v_l_u2081_56_, lean_object* v_l_u2082_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_List_decidablePerm___redArg(v_inst_55_, v_l_u2081_56_, v_l_u2082_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_List_decidablePerm(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_l_u2081_62_, lean_object* v_l_u2082_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = l_List_decidablePerm___redArg(v_inst_61_, v_l_u2081_62_, v_l_u2082_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_List_decidablePerm___boxed(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_l_u2081_67_, lean_object* v_l_u2082_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_List_decidablePerm(v_00_u03b1_65_, v_inst_66_, v_l_u2081_67_, v_l_u2082_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Perm(builtin);
}
#ifdef __cplusplus
}
#endif
