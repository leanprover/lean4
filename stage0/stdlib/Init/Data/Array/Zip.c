// Lean compiler output
// Module: Init.Data.Array.Zip
// Imports: import all Init.Data.Array.Basic public import Init.Control.Lawful public import Init.Data.Function import Init.Data.Array.Lemmas import Init.Data.List.Nat.TakeDrop import Init.Data.List.Zip import Init.Data.Option.Lemmas import Init.Data.Prod import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 1)
{
if (lean_obj_tag(v_x_2_) == 1)
{
lean_object* v_val_5_; lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_4_);
v_val_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_x_1_);
v_val_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_2_);
v___x_7_ = lean_apply_2(v_h__1_3_, v_val_5_, v_val_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v___x_8_ = lean_apply_3(v_h__2_4_, v_x_1_, v_x_2_, lean_box(0));
return v___x_8_;
}
}
else
{
lean_object* v___x_9_; 
lean_dec(v_h__1_3_);
v___x_9_ = lean_apply_3(v_h__2_4_, v_x_1_, v_x_2_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_motive_12_, lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_13_) == 1)
{
if (lean_obj_tag(v_x_14_) == 1)
{
lean_object* v_val_17_; lean_object* v_val_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_16_);
v_val_17_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v_x_13_);
v_val_18_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_18_);
lean_dec_ref(v_x_14_);
v___x_19_ = lean_apply_2(v_h__1_15_, v_val_17_, v_val_18_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v___x_20_ = lean_apply_3(v_h__2_16_, v_x_13_, v_x_14_, lean_box(0));
return v___x_20_;
}
}
else
{
lean_object* v___x_21_; 
lean_dec(v_h__1_15_);
v___x_21_ = lean_apply_3(v_h__2_16_, v_x_13_, v_x_14_, lean_box(0));
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
if (lean_obj_tag(v_x_22_) == 1)
{
if (lean_obj_tag(v_x_23_) == 1)
{
lean_object* v_val_26_; lean_object* v_val_27_; lean_object* v___x_28_; 
lean_dec(v_h__2_25_);
v_val_26_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_val_26_);
lean_dec_ref(v_x_22_);
v_val_27_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_val_27_);
lean_dec_ref(v_x_23_);
v___x_28_ = lean_apply_2(v_h__1_24_, v_val_26_, v_val_27_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; 
lean_dec(v_h__1_24_);
v___x_29_ = lean_apply_3(v_h__2_25_, v_x_22_, v_x_23_, lean_box(0));
return v___x_29_;
}
}
else
{
lean_object* v___x_30_; 
lean_dec(v_h__1_24_);
v___x_30_ = lean_apply_3(v_h__2_25_, v_x_22_, v_x_23_, lean_box(0));
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_x_34_) == 1)
{
if (lean_obj_tag(v_x_35_) == 1)
{
lean_object* v_val_38_; lean_object* v_val_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_37_);
v_val_38_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_val_38_);
lean_dec_ref(v_x_34_);
v_val_39_ = lean_ctor_get(v_x_35_, 0);
lean_inc(v_val_39_);
lean_dec_ref(v_x_35_);
v___x_40_ = lean_apply_2(v_h__1_36_, v_val_38_, v_val_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
lean_dec(v_h__1_36_);
v___x_41_ = lean_apply_3(v_h__2_37_, v_x_34_, v_x_35_, lean_box(0));
return v___x_41_;
}
}
else
{
lean_object* v___x_42_; 
lean_dec(v_h__1_36_);
v___x_42_ = lean_apply_3(v_h__2_37_, v_x_34_, v_x_35_, lean_box(0));
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_46_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__1_45_, v___x_47_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; 
lean_dec(v_h__1_45_);
v___x_49_ = lean_apply_3(v_h__2_46_, v_x_43_, v_x_44_, lean_box(0));
return v___x_49_;
}
}
else
{
lean_object* v___x_50_; 
lean_dec(v_h__1_45_);
v___x_50_ = lean_apply_3(v_h__2_46_, v_x_43_, v_x_44_, lean_box(0));
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__2_57_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__1_56_, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
lean_dec(v_h__1_56_);
v___x_60_ = lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, lean_box(0));
return v___x_60_;
}
}
else
{
lean_object* v___x_61_; 
lean_dec(v_h__1_56_);
v___x_61_ = lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_65_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_1(v_h__1_64_, v___x_66_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; 
lean_dec(v_h__1_64_);
v___x_68_ = lean_apply_3(v_h__2_65_, v_x_62_, v_x_63_, lean_box(0));
return v___x_68_;
}
}
else
{
lean_object* v___x_69_; 
lean_dec(v_h__1_64_);
v___x_69_ = lean_apply_3(v_h__2_65_, v_x_62_, v_x_63_, lean_box(0));
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Zip_0__Array_getElem_x3f__zipWithAll_match__1_splitter(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h__2_76_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_apply_1(v_h__1_75_, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; 
lean_dec(v_h__1_75_);
v___x_79_ = lean_apply_3(v_h__2_76_, v_x_73_, v_x_74_, lean_box(0));
return v___x_79_;
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v_h__1_75_);
v___x_80_ = lean_apply_3(v_h__2_76_, v_x_73_, v_x_74_, lean_box(0));
return v___x_80_;
}
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
