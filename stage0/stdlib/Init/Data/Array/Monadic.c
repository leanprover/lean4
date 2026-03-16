// Lean compiler output
// Module: Init.Data.Array.Monadic
// Imports: import all Init.Data.List.Control import all Init.Data.Array.Basic public import Init.Data.Array.Attach import Init.Data.Bool
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Array_Monadic_0__List_foldlM__filterMap_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__2_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v_val_19_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_19_);
lean_dec_ref(v_x_14_);
v___x_20_ = lean_apply_1(v_h__1_15_, v_val_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter(lean_object* v_00_u03b2_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Init_Data_Array_Monadic_0__Array_foldlM__filterMap_match__1_splitter___redArg(v_x_23_, v_h__1_24_, v_h__2_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_b_27_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_28_);
v_a_30_ = lean_ctor_get(v_b_27_, 0);
lean_inc(v_a_30_);
lean_dec_ref(v_b_27_);
v___x_31_ = lean_apply_1(v_h__2_29_, v_a_30_);
return v___x_31_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_29_);
v_a_32_ = lean_ctor_get(v_b_27_, 0);
lean_inc(v_a_32_);
lean_dec_ref(v_b_27_);
v___x_33_ = lean_apply_1(v_h__1_28_, v_a_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_34_, lean_object* v_motive_35_, lean_object* v_b_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Init_Data_Array_Monadic_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(v_b_36_, v_h__1_37_, v_h__2_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
if (lean_obj_tag(v_b_40_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_41_);
v_a_43_ = lean_ctor_get(v_b_40_, 0);
lean_inc(v_a_43_);
lean_dec_ref(v_b_40_);
v___x_44_ = lean_apply_1(v_h__2_42_, v_a_43_);
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_42_);
v_a_45_ = lean_ctor_get(v_b_40_, 0);
lean_inc(v_a_45_);
lean_dec_ref(v_b_40_);
v___x_46_ = lean_apply_1(v_h__1_41_, v_a_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_47_, lean_object* v_motive_48_, lean_object* v_b_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_Array_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(v_b_49_, v_h__1_50_, v_h__2_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
if (lean_obj_tag(v_____do__lift_53_) == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_54_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_apply_1(v_h__2_55_, v___x_56_);
return v___x_57_;
}
else
{
lean_object* v_val_58_; lean_object* v___x_59_; 
lean_dec(v_h__2_55_);
v_val_58_ = lean_ctor_get(v_____do__lift_53_, 0);
lean_inc(v_val_58_);
lean_dec_ref(v_____do__lift_53_);
v___x_59_ = lean_apply_1(v_h__1_54_, v_val_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter(lean_object* v_00_u03b2_60_, lean_object* v_motive_61_, lean_object* v_____do__lift_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Init_Data_Array_Monadic_0__Array_filterMapM_match__1_splitter___redArg(v_____do__lift_62_, v_h__1_63_, v_h__2_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter___redArg(lean_object* v_____do__lift_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
if (lean_obj_tag(v_____do__lift_66_) == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_68_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_67_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_67_);
v_val_71_ = lean_ctor_get(v_____do__lift_66_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v_____do__lift_66_);
v___x_72_ = lean_apply_1(v_h__2_68_, v_val_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter(lean_object* v_00_u03b2_73_, lean_object* v_motive_74_, lean_object* v_____do__lift_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Init_Data_Array_Monadic_0__List_filterMapM_match__1_splitter___redArg(v_____do__lift_75_, v_h__1_76_, v_h__2_77_);
return v___x_78_;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Monadic(builtin);
}
#ifdef __cplusplus
}
#endif
