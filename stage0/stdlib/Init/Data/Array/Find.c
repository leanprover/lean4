// Lean compiler output
// Module: Init.Data.Array.Find
// Imports: import Init.Data.List.Nat.Sum import all Init.Data.Array.Basic public import Init.Data.Array.Attach public import Init.Data.Option.BasicAux import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Array.MapIdx import Init.Data.Bool import Init.Data.Fin.Lemmas import Init.Data.List.Count import Init.Data.List.Find import Init.Data.List.Impl import Init.Data.List.Nat.Find import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object* v_00_u03b1_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(v_x_23_, v_h__1_24_, v_h__2_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object* v_o_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_o_27_) == 0)
{
lean_object* v___x_30_; 
lean_dec(v_h__2_29_);
v___x_30_ = lean_apply_1(v_h__1_28_, lean_box(0));
return v___x_30_;
}
else
{
lean_object* v_val_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_28_);
v_val_31_ = lean_ctor_get(v_o_27_, 0);
lean_inc(v_val_31_);
lean_dec_ref(v_o_27_);
v___x_32_ = lean_apply_2(v_h__2_29_, v_val_31_, lean_box(0));
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter(lean_object* v_00_u03b1_33_, lean_object* v_p_34_, lean_object* v_o_x27_35_, lean_object* v_motive_36_, lean_object* v_o_37_, lean_object* v_h_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___redArg(v_o_37_, v_h__1_39_, v_h__2_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object* v_00_u03b1_42_, lean_object* v_p_43_, lean_object* v_o_x27_44_, lean_object* v_motive_45_, lean_object* v_o_46_, lean_object* v_h_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter(v_00_u03b1_42_, v_p_43_, v_o_x27_44_, v_motive_45_, v_o_46_, v_h_47_, v_h__1_48_, v_h__2_49_);
lean_dec(v_o_x27_44_);
return v_res_50_;
}
}
lean_object* runtime_initialize_Init_Data_List_Nat_Sum(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Find(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Nat_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Find(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Nat_Sum(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Find(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Nat_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Find(builtin);
}
#ifdef __cplusplus
}
#endif
