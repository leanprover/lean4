// Lean compiler output
// Module: Init.Data.List.Perm
// Imports: import all Init.Data.List.Attach public import Init.Data.List.Attach import Init.Data.List.Erase import Init.Data.List.Pairwise import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas
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
uint8_t l_List_isPerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm(lean_object*);
LEAN_EXPORT lean_object* l_List_isSetoid(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidablePerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidablePerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidablePerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_isSetoid(lean_object* v_00_u03b1_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(lean_object* v_x_5_, lean_object* v_x_6_, lean_object* v_h__1_7_, lean_object* v_h__2_8_){
_start:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v___x_9_; 
lean_dec(v_h__2_8_);
v___x_9_ = lean_apply_1(v_h__1_7_, v_x_5_);
return v___x_9_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_12_; 
lean_dec(v_h__1_7_);
v_head_10_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_head_10_);
v_tail_11_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_tail_11_);
lean_dec_ref(v_x_6_);
v___x_12_ = lean_apply_3(v_h__2_8_, v_x_5_, v_head_10_, v_tail_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Init_Data_List_Perm_0__List_foldl_match__1_splitter___redArg(v_x_16_, v_x_17_, v_h__1_18_, v_h__2_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v___x_25_; 
lean_dec(v_h__2_24_);
v___x_25_ = lean_apply_1(v_h__1_23_, v_x_22_);
return v___x_25_;
}
else
{
lean_object* v_head_26_; lean_object* v_tail_27_; lean_object* v___x_28_; 
lean_dec(v_h__1_23_);
v_head_26_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_head_26_);
v_tail_27_ = lean_ctor_get(v_x_21_, 1);
lean_inc(v_tail_27_);
lean_dec_ref(v_x_21_);
v___x_28_ = lean_apply_3(v_h__2_24_, v_head_26_, v_tail_27_, v_x_22_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter___redArg(v_x_31_, v_x_32_, v_h__1_33_, v_h__2_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_38_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__1_37_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_head_41_; lean_object* v_tail_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_37_);
v_head_41_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_head_41_);
v_tail_42_ = lean_ctor_get(v_x_36_, 1);
lean_inc(v_tail_42_);
lean_dec_ref(v_x_36_);
v___x_43_ = lean_apply_2(v_h__2_38_, v_head_41_, v_tail_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(v_x_46_, v_h__1_47_, v_h__2_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_List_decidablePerm___redArg(lean_object* v_inst_50_, lean_object* v_l_u2081_51_, lean_object* v_l_u2082_52_){
_start:
{
lean_object* v___f_53_; uint8_t v___x_54_; 
v___f_53_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_53_, 0, v_inst_50_);
v___x_54_ = l_List_isPerm___redArg(v___f_53_, v_l_u2081_51_, v_l_u2082_52_);
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
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
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
