// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Find.Basic
// Imports: public import Init.Data.String.Slice public import Init.Data.String.Search public import Init.Data.String.Lemmas.Pattern.Basic import all Init.Data.String.Slice import all Init.Data.String.Search import Init.Data.Iterators.Lemmas.Consumers.Loop import Init.Data.String.Lemmas.Order import Init.Data.String.Lemmas.Basic import Init.Data.String.OrderInstances import Init.Grind
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_startPos_4_; lean_object* v_endPos_5_; lean_object* v___x_6_; 
lean_dec(v_h__1_2_);
v_startPos_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_startPos_4_);
v_endPos_5_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_endPos_5_);
lean_dec_ref(v_x_1_);
v___x_6_ = lean_apply_2(v_h__2_3_, v_startPos_4_, v_endPos_5_);
return v___x_6_;
}
else
{
lean_object* v_startPos_7_; lean_object* v_endPos_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_3_);
v_startPos_7_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_startPos_7_);
v_endPos_8_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_endPos_8_);
lean_dec_ref(v_x_1_);
v___x_9_ = lean_apply_2(v_h__1_2_, v_startPos_7_, v_endPos_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(lean_object* v_s_10_, lean_object* v_motive_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v_startPos_15_; lean_object* v_endPos_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_13_);
v_startPos_15_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_startPos_15_);
v_endPos_16_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_endPos_16_);
lean_dec_ref(v_x_12_);
v___x_17_ = lean_apply_2(v_h__2_14_, v_startPos_15_, v_endPos_16_);
return v___x_17_;
}
else
{
lean_object* v_startPos_18_; lean_object* v_endPos_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_14_);
v_startPos_18_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_startPos_18_);
v_endPos_19_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_endPos_19_);
lean_dec_ref(v_x_12_);
v___x_20_ = lean_apply_2(v_h__1_13_, v_startPos_18_, v_endPos_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___boxed(lean_object* v_s_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(v_s_21_, v_motive_22_, v_x_23_, v_h__1_24_, v_h__2_25_);
lean_dec_ref(v_s_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___redArg(lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v_startPos_30_; lean_object* v_endPos_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_28_);
v_startPos_30_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_startPos_30_);
v_endPos_31_ = lean_ctor_get(v_x_27_, 1);
lean_inc(v_endPos_31_);
lean_dec_ref(v_x_27_);
v___x_32_ = lean_apply_2(v_h__2_29_, v_startPos_30_, v_endPos_31_);
return v___x_32_;
}
else
{
lean_object* v_startPos_33_; lean_object* v_endPos_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_29_);
v_startPos_33_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_startPos_33_);
v_endPos_34_ = lean_ctor_get(v_x_27_, 1);
lean_inc(v_endPos_34_);
lean_dec_ref(v_x_27_);
v___x_35_ = lean_apply_2(v_h__1_28_, v_startPos_33_, v_endPos_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(lean_object* v_s_36_, lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v_startPos_41_; lean_object* v_endPos_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_39_);
v_startPos_41_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_startPos_41_);
v_endPos_42_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_endPos_42_);
lean_dec_ref(v_x_38_);
v___x_43_ = lean_apply_2(v_h__2_40_, v_startPos_41_, v_endPos_42_);
return v___x_43_;
}
else
{
lean_object* v_startPos_44_; lean_object* v_endPos_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_40_);
v_startPos_44_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_startPos_44_);
v_endPos_45_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_endPos_45_);
lean_dec_ref(v_x_38_);
v___x_46_ = lean_apply_2(v_h__1_39_, v_startPos_44_, v_endPos_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___boxed(lean_object* v_s_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(v_s_47_, v_motive_48_, v_x_49_, v_h__1_50_, v_h__2_51_);
lean_dec_ref(v_s_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
if (lean_obj_tag(v_x_53_) == 1)
{
lean_object* v_startPos_56_; lean_object* v_endPos_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_55_);
v_startPos_56_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_startPos_56_);
v_endPos_57_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_endPos_57_);
lean_dec_ref(v_x_53_);
v___x_58_ = lean_apply_2(v_h__1_54_, v_startPos_56_, v_endPos_57_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; 
lean_dec(v_h__1_54_);
v___x_59_ = lean_apply_2(v_h__2_55_, v_x_53_, lean_box(0));
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(lean_object* v_s_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_x_62_) == 1)
{
lean_object* v_startPos_65_; lean_object* v_endPos_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_64_);
v_startPos_65_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_startPos_65_);
v_endPos_66_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_endPos_66_);
lean_dec_ref(v_x_62_);
v___x_67_ = lean_apply_2(v_h__1_63_, v_startPos_65_, v_endPos_66_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; 
lean_dec(v_h__1_63_);
v___x_68_ = lean_apply_2(v_h__2_64_, v_x_62_, lean_box(0));
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___boxed(lean_object* v_s_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(v_s_69_, v_motive_70_, v_x_71_, v_h__1_72_, v_h__2_73_);
lean_dec_ref(v_s_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__1_76_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__2_77_, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_77_);
v_val_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_80_);
lean_dec_ref(v_x_75_);
v___x_81_ = lean_apply_1(v_h__1_76_, v_val_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_h__1_85_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_apply_1(v_h__2_86_, v___x_87_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_86_);
v_val_89_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_val_89_);
lean_dec_ref(v_x_84_);
v___x_90_ = lean_apply_1(v_h__1_85_, v_val_89_);
return v___x_90_;
}
}
}
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
