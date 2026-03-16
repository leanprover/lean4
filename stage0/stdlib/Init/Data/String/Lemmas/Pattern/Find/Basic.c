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
lean_object* v___x_15_; 
v___x_15_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___redArg(v_x_12_, v_h__1_13_, v_h__2_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___boxed(lean_object* v_s_16_, lean_object* v_motive_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(v_s_16_, v_motive_17_, v_x_18_, v_h__1_19_, v_h__2_20_);
lean_dec_ref(v_s_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___redArg(lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v_startPos_25_; lean_object* v_endPos_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_23_);
v_startPos_25_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_startPos_25_);
v_endPos_26_ = lean_ctor_get(v_x_22_, 1);
lean_inc(v_endPos_26_);
lean_dec_ref(v_x_22_);
v___x_27_ = lean_apply_2(v_h__2_24_, v_startPos_25_, v_endPos_26_);
return v___x_27_;
}
else
{
lean_object* v_startPos_28_; lean_object* v_endPos_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_24_);
v_startPos_28_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_startPos_28_);
v_endPos_29_ = lean_ctor_get(v_x_22_, 1);
lean_inc(v_endPos_29_);
lean_dec_ref(v_x_22_);
v___x_30_ = lean_apply_2(v_h__1_23_, v_startPos_28_, v_endPos_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(lean_object* v_s_31_, lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___redArg(v_x_33_, v_h__1_34_, v_h__2_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___boxed(lean_object* v_s_37_, lean_object* v_motive_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(v_s_37_, v_motive_38_, v_x_39_, v_h__1_40_, v_h__2_41_);
lean_dec_ref(v_s_37_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_x_43_) == 1)
{
lean_object* v_startPos_46_; lean_object* v_endPos_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_45_);
v_startPos_46_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_startPos_46_);
v_endPos_47_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_endPos_47_);
lean_dec_ref(v_x_43_);
v___x_48_ = lean_apply_2(v_h__1_44_, v_startPos_46_, v_endPos_47_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; 
lean_dec(v_h__1_44_);
v___x_49_ = lean_apply_2(v_h__2_45_, v_x_43_, lean_box(0));
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(lean_object* v_s_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_x_52_) == 1)
{
lean_object* v_startPos_55_; lean_object* v_endPos_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_54_);
v_startPos_55_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_startPos_55_);
v_endPos_56_ = lean_ctor_get(v_x_52_, 1);
lean_inc(v_endPos_56_);
lean_dec_ref(v_x_52_);
v___x_57_ = lean_apply_2(v_h__1_53_, v_startPos_55_, v_endPos_56_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; 
lean_dec(v_h__1_53_);
v___x_58_ = lean_apply_2(v_h__2_54_, v_x_52_, lean_box(0));
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___boxed(lean_object* v_s_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(v_s_59_, v_motive_60_, v_x_61_, v_h__1_62_, v_h__2_63_);
lean_dec_ref(v_s_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_h__1_66_);
v___x_68_ = lean_box(0);
v___x_69_ = lean_apply_1(v_h__2_67_, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_67_);
v_val_70_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_val_70_);
lean_dec_ref(v_x_65_);
v___x_71_ = lean_apply_1(v_h__1_66_, v_val_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_72_, lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter___redArg(v_x_74_, v_h__1_75_, v_h__2_76_);
return v___x_77_;
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
