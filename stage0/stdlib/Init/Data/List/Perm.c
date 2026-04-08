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
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_20_; 
lean_dec(v_h__2_19_);
v___x_20_ = lean_apply_1(v_h__1_18_, v_x_16_);
return v___x_20_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_head_21_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_head_21_);
v_tail_22_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_tail_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_3(v_h__2_19_, v_x_16_, v_head_21_, v_tail_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_28_; 
lean_dec(v_h__2_27_);
v___x_28_ = lean_apply_1(v_h__1_26_, v_x_25_);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_26_);
v_head_29_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_head_29_);
v_tail_30_ = lean_ctor_get(v_x_24_, 1);
lean_inc(v_tail_30_);
lean_dec_ref(v_x_24_);
v___x_31_ = lean_apply_3(v_h__2_27_, v_head_29_, v_tail_30_, v_x_25_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_32_, lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_38_; 
lean_dec(v_h__2_37_);
v___x_38_ = lean_apply_1(v_h__1_36_, v_x_35_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v_tail_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_36_);
v_head_39_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_head_39_);
v_tail_40_ = lean_ctor_get(v_x_34_, 1);
lean_inc(v_tail_40_);
lean_dec_ref(v_x_34_);
v___x_41_ = lean_apply_3(v_h__2_37_, v_head_39_, v_tail_40_, v_x_35_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
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
lean_dec_ref(v_x_42_);
v___x_49_ = lean_apply_2(v_h__2_44_, v_head_47_, v_tail_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Perm_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__1_53_, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v_tail_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_53_);
v_head_57_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_head_57_);
v_tail_58_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_tail_58_);
lean_dec_ref(v_x_52_);
v___x_59_ = lean_apply_2(v_h__2_54_, v_head_57_, v_tail_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT uint8_t l_List_decidablePerm___redArg(lean_object* v_inst_60_, lean_object* v_l_u2081_61_, lean_object* v_l_u2082_62_){
_start:
{
lean_object* v___f_63_; uint8_t v___x_64_; 
v___f_63_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_63_, 0, v_inst_60_);
v___x_64_ = l_List_isPerm___redArg(v___f_63_, v_l_u2081_61_, v_l_u2082_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_List_decidablePerm___redArg___boxed(lean_object* v_inst_65_, lean_object* v_l_u2081_66_, lean_object* v_l_u2082_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_List_decidablePerm___redArg(v_inst_65_, v_l_u2081_66_, v_l_u2082_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_List_decidablePerm(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_l_u2081_72_, lean_object* v_l_u2082_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_List_decidablePerm___redArg(v_inst_71_, v_l_u2081_72_, v_l_u2082_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_List_decidablePerm___boxed(lean_object* v_00_u03b1_75_, lean_object* v_inst_76_, lean_object* v_l_u2081_77_, lean_object* v_l_u2082_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_List_decidablePerm(v_00_u03b1_75_, v_inst_76_, v_l_u2081_77_, v_l_u2082_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
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
