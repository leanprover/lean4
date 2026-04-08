// Lean compiler output
// Module: Init.Data.String.Lemmas.Iterate
// Imports: public import Init.Data.String.Iterate public import Init.Data.Iterators.Consumers.Collect public import Init.Data.String.Lemmas.Splits import all Init.Data.String.Iterate import Init.Data.String.Termination import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.ByCases import Init.Data.Iterators.Lemmas.Combinators.FilterMap import Init.Data.String.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Loop public import Init.Data.String.Lemmas.Order import Init.Data.String.OrderInstances import Init.Data.Subtype.Basic
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom(lean_object* v_s_1_, lean_object* v_p_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_str_3_ = lean_ctor_get(v_s_1_, 0);
v_startInclusive_4_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_5_ = lean_ctor_get(v_s_1_, 2);
v___x_6_ = lean_nat_sub(v_endExclusive_5_, v_startInclusive_4_);
v___x_7_ = lean_nat_dec_eq(v_p_2_, v___x_6_);
lean_dec(v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_8_ = lean_nat_add(v_startInclusive_4_, v_p_2_);
v___x_9_ = lean_string_utf8_next_fast(v_str_3_, v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lean_nat_sub(v___x_9_, v_startInclusive_4_);
v___x_11_ = l_String_Slice_Model_positionsFrom(v_s_1_, v___x_10_);
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v_p_2_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; 
lean_dec(v_p_2_);
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Model_positionsFrom___boxed(lean_object* v_s_14_, lean_object* v_p_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_Slice_Model_positionsFrom(v_s_14_, v_p_15_);
lean_dec_ref(v_s_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
switch(lean_obj_tag(v_x_17_))
{
case 0:
{
lean_object* v_it_21_; lean_object* v_out_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v_it_21_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_21_);
v_out_22_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_out_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_2(v_h__1_18_, v_it_21_, v_out_22_);
return v___x_23_;
}
case 1:
{
lean_object* v_it_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__1_18_);
v_it_24_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_it_24_);
lean_dec_ref(v_x_17_);
v___x_25_ = lean_apply_1(v_h__2_19_, v_it_24_);
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_19_);
lean_dec(v_h__1_18_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__3_20_, v___x_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_, lean_object* v_h__3_34_){
_start:
{
switch(lean_obj_tag(v_x_31_))
{
case 0:
{
lean_object* v_it_35_; lean_object* v_out_36_; lean_object* v___x_37_; 
lean_dec(v_h__3_34_);
lean_dec(v_h__2_33_);
v_it_35_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_it_35_);
v_out_36_ = lean_ctor_get(v_x_31_, 1);
lean_inc(v_out_36_);
lean_dec_ref(v_x_31_);
v___x_37_ = lean_apply_2(v_h__1_32_, v_it_35_, v_out_36_);
return v___x_37_;
}
case 1:
{
lean_object* v_it_38_; lean_object* v___x_39_; 
lean_dec(v_h__3_34_);
lean_dec(v_h__1_32_);
v_it_38_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_it_38_);
lean_dec_ref(v_x_31_);
v___x_39_ = lean_apply_1(v_h__2_33_, v_it_38_);
return v___x_39_;
}
default: 
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_33_);
lean_dec(v_h__1_32_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__3_34_, v___x_40_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom(lean_object* v_s_42_, lean_object* v_p_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_dec_eq(v_p_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_sub(v_p_43_, v___x_46_);
v___x_48_ = l_String_Slice_posLE(v_s_42_, v___x_47_);
v___x_49_ = l_String_Slice_Model_revPositionsFrom(v_s_42_, v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Model_revPositionsFrom___boxed(lean_object* v_s_52_, lean_object* v_p_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_String_Slice_Model_revPositionsFrom(v_s_52_, v_p_53_);
lean_dec(v_p_53_);
lean_dec_ref(v_s_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_Model_positionsFrom(lean_object* v_s_55_, lean_object* v_p_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_string_utf8_byte_size(v_s_55_);
v___x_58_ = lean_nat_dec_eq(v_p_56_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_string_utf8_next_fast(v_s_55_, v_p_56_);
v___x_60_ = l_String_Model_positionsFrom(v_s_55_, v___x_59_);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v_p_56_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; 
lean_dec(v_p_56_);
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_String_Model_positionsFrom___boxed(lean_object* v_s_63_, lean_object* v_p_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_String_Model_positionsFrom(v_s_63_, v_p_64_);
lean_dec_ref(v_s_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___redArg(lean_object* v_x_66_, lean_object* v_h__1_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_apply_2(v_h__1_67_, v_x_66_, lean_box(0));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(lean_object* v_s_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_apply_2(v_h__1_72_, v_x_71_, lean_box(0));
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___boxed(lean_object* v_s_74_, lean_object* v_motive_75_, lean_object* v_x_76_, lean_object* v_h__1_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(v_s_74_, v_motive_75_, v_x_76_, v_h__1_77_);
lean_dec_ref(v_s_74_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom(lean_object* v_s_79_, lean_object* v_p_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v_p_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_83_ = lean_string_utf8_byte_size(v_s_79_);
lean_inc_ref(v_s_79_);
v___x_84_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_84_, 0, v_s_79_);
lean_ctor_set(v___x_84_, 1, v___x_81_);
lean_ctor_set(v___x_84_, 2, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_sub(v_p_80_, v___x_85_);
v___x_87_ = l_String_Slice_posLE(v___x_84_, v___x_86_);
lean_dec_ref(v___x_84_);
v___x_88_ = l_String_Model_revPositionsFrom(v_s_79_, v___x_87_);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
lean_dec_ref(v_s_79_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_String_Model_revPositionsFrom___boxed(lean_object* v_s_91_, lean_object* v_p_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_String_Model_revPositionsFrom(v_s_91_, v_p_92_);
lean_dec(v_p_92_);
return v_res_93_;
}
}
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Iterate(builtin);
}
#ifdef __cplusplus
}
#endif
