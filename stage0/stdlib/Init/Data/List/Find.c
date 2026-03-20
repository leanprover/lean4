// Lean compiler output
// Module: Init.Data.List.Find
// Imports: import all Init.Data.List.Attach public import Init.Data.List.Attach import Init.Data.Fin.Lemmas import Init.Data.List.Impl import Init.Data.List.Range import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas import Init.Data.Prod import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(uint8_t v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (v_x_14_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__1_15_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_apply_1(v_h__2_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__2_16_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__1_15_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
uint8_t v_x_22__boxed_24_; lean_object* v_res_25_; 
v_x_22__boxed_24_ = lean_unbox(v_x_21_);
v_res_25_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_24_, v_h__1_22_, v_h__2_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_object* v_motive_26_, uint8_t v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(v_x_27_, v_h__1_28_, v_h__2_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
uint8_t v_x_33__boxed_35_; lean_object* v_res_36_; 
v_x_33__boxed_35_ = lean_unbox(v_x_32_);
v_res_36_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(v_motive_31_, v_x_33__boxed_35_, v_h__1_33_, v_h__2_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_39_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_38_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_38_);
v_val_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_val_42_);
lean_dec_ref(v_x_37_);
v___x_43_ = lean_apply_1(v_h__2_39_, v_val_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(v_x_46_, v_h__1_47_, v_h__2_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_54_; 
lean_dec(v_h__2_53_);
v___x_54_ = lean_apply_1(v_h__1_52_, v_x_51_);
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v_head_55_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_head_55_);
v_tail_56_ = lean_ctor_get(v_x_50_, 1);
lean_inc(v_tail_56_);
lean_dec_ref(v_x_50_);
v___x_57_ = lean_apply_3(v_h__2_53_, v_head_55_, v_tail_56_, v_x_51_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(v_x_60_, v_x_61_, v_h__1_62_, v_h__2_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object* v_00_u03b1_72_, lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(v_x_74_, v_h__1_75_, v_h__2_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_82_; 
lean_dec(v_h__2_81_);
v___x_82_ = lean_apply_2(v_h__1_80_, v_x_79_, lean_box(0));
return v___x_82_;
}
else
{
lean_object* v_head_83_; lean_object* v_tail_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_80_);
v_head_83_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_head_83_);
v_tail_84_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_tail_84_);
lean_dec_ref(v_x_78_);
v___x_85_ = lean_apply_4(v_h__2_81_, v_head_83_, v_tail_84_, v_x_79_, lean_box(0));
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object* v_00_u03b1_86_, lean_object* v_l_87_, lean_object* v_motive_88_, lean_object* v_x_89_, lean_object* v_x_90_, lean_object* v_x_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(v_x_89_, v_x_90_, v_h__1_92_, v_h__2_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object* v_00_u03b1_95_, lean_object* v_l_96_, lean_object* v_motive_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(v_00_u03b1_95_, v_l_96_, v_motive_97_, v_x_98_, v_x_99_, v_x_100_, v_h__1_101_, v_h__2_102_);
lean_dec(v_l_96_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object* v_o_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
if (lean_obj_tag(v_o_104_) == 0)
{
lean_object* v___x_107_; 
lean_dec(v_h__2_106_);
v___x_107_ = lean_apply_1(v_h__1_105_, lean_box(0));
return v___x_107_;
}
else
{
lean_object* v_val_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_105_);
v_val_108_ = lean_ctor_get(v_o_104_, 0);
lean_inc(v_val_108_);
lean_dec_ref(v_o_104_);
v___x_109_ = lean_apply_2(v_h__2_106_, v_val_108_, lean_box(0));
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(lean_object* v_00_u03b1_110_, lean_object* v_p_111_, lean_object* v_o_x27_112_, lean_object* v_motive_113_, lean_object* v_o_114_, lean_object* v_h_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(v_o_114_, v_h__1_116_, v_h__2_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object* v_00_u03b1_119_, lean_object* v_p_120_, lean_object* v_o_x27_121_, lean_object* v_motive_122_, lean_object* v_o_123_, lean_object* v_h_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(v_00_u03b1_119_, v_p_120_, v_o_x27_121_, v_motive_122_, v_o_123_, v_h_124_, v_h__1_125_, v_h__2_126_);
lean_dec(v_o_x27_121_);
return v_res_127_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
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
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
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
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Find(builtin);
}
#ifdef __cplusplus
}
#endif
