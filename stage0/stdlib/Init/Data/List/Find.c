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
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref(v_x_10_);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(uint8_t v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (v_x_17_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_h__1_18_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_apply_1(v_h__2_19_, v___x_20_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_19_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_18_, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
uint8_t v_x_26__boxed_27_; lean_object* v_res_28_; 
v_x_26__boxed_27_ = lean_unbox(v_x_24_);
v_res_28_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_27_, v_h__1_25_, v_h__2_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_object* v_motive_29_, uint8_t v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (v_x_30_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_31_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__2_32_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_32_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__1_31_, v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
uint8_t v_x_37__boxed_41_; lean_object* v_res_42_; 
v_x_37__boxed_41_ = lean_unbox(v_x_38_);
v_res_42_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(v_motive_37_, v_x_37__boxed_41_, v_h__1_39_, v_h__2_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_45_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_apply_1(v_h__1_44_, v___x_46_);
return v___x_47_;
}
else
{
lean_object* v_val_48_; lean_object* v___x_49_; 
lean_dec(v_h__1_44_);
v_val_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_val_48_);
lean_dec_ref(v_x_43_);
v___x_49_ = lean_apply_1(v_h__2_45_, v_val_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
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
lean_object* v_val_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_53_);
v_val_57_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_val_57_);
lean_dec_ref(v_x_52_);
v___x_58_ = lean_apply_1(v_h__2_54_, v_val_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_63_; 
lean_dec(v_h__2_62_);
v___x_63_ = lean_apply_1(v_h__1_61_, v_x_60_);
return v___x_63_;
}
else
{
lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_61_);
v_head_64_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_tail_65_);
lean_dec_ref(v_x_59_);
v___x_66_ = lean_apply_3(v_h__2_62_, v_head_64_, v_tail_65_, v_x_60_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_67_, lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_73_; 
lean_dec(v_h__2_72_);
v___x_73_ = lean_apply_1(v_h__1_71_, v_x_70_);
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_71_);
v_head_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_tail_75_);
lean_dec_ref(v_x_69_);
v___x_76_ = lean_apply_3(v_h__2_72_, v_head_74_, v_tail_75_, v_x_70_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__2_79_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_79_);
v_val_82_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_82_);
lean_dec_ref(v_x_77_);
v___x_83_ = lean_apply_1(v_h__1_78_, v_val_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object* v_00_u03b1_84_, lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_87_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_apply_1(v_h__2_88_, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v_val_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_88_);
v_val_91_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_val_91_);
lean_dec_ref(v_x_86_);
v___x_92_ = lean_apply_1(v_h__1_87_, v_val_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_97_; 
lean_dec(v_h__2_96_);
v___x_97_ = lean_apply_2(v_h__1_95_, v_x_94_, lean_box(0));
return v___x_97_;
}
else
{
lean_object* v_head_98_; lean_object* v_tail_99_; lean_object* v___x_100_; 
lean_dec(v_h__1_95_);
v_head_98_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_head_98_);
v_tail_99_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_tail_99_);
lean_dec_ref(v_x_93_);
v___x_100_ = lean_apply_4(v_h__2_96_, v_head_98_, v_tail_99_, v_x_94_, lean_box(0));
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object* v_00_u03b1_101_, lean_object* v_l_102_, lean_object* v_motive_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v___x_109_; 
lean_dec(v_h__2_108_);
v___x_109_ = lean_apply_2(v_h__1_107_, v_x_105_, lean_box(0));
return v___x_109_;
}
else
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_112_; 
lean_dec(v_h__1_107_);
v_head_110_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_head_110_);
v_tail_111_ = lean_ctor_get(v_x_104_, 1);
lean_inc(v_tail_111_);
lean_dec_ref(v_x_104_);
v___x_112_ = lean_apply_4(v_h__2_108_, v_head_110_, v_tail_111_, v_x_105_, lean_box(0));
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object* v_00_u03b1_113_, lean_object* v_l_114_, lean_object* v_motive_115_, lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(v_00_u03b1_113_, v_l_114_, v_motive_115_, v_x_116_, v_x_117_, v_x_118_, v_h__1_119_, v_h__2_120_);
lean_dec(v_l_114_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object* v_o_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
if (lean_obj_tag(v_o_122_) == 0)
{
lean_object* v___x_125_; 
lean_dec(v_h__2_124_);
v___x_125_ = lean_apply_1(v_h__1_123_, lean_box(0));
return v___x_125_;
}
else
{
lean_object* v_val_126_; lean_object* v___x_127_; 
lean_dec(v_h__1_123_);
v_val_126_ = lean_ctor_get(v_o_122_, 0);
lean_inc(v_val_126_);
lean_dec_ref(v_o_122_);
v___x_127_ = lean_apply_2(v_h__2_124_, v_val_126_, lean_box(0));
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(lean_object* v_00_u03b1_128_, lean_object* v_p_129_, lean_object* v_o_x27_130_, lean_object* v_motive_131_, lean_object* v_o_132_, lean_object* v_h_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_o_132_) == 0)
{
lean_object* v___x_136_; 
lean_dec(v_h__2_135_);
v___x_136_ = lean_apply_1(v_h__1_134_, lean_box(0));
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; 
lean_dec(v_h__1_134_);
v_val_137_ = lean_ctor_get(v_o_132_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v_o_132_);
v___x_138_ = lean_apply_2(v_h__2_135_, v_val_137_, lean_box(0));
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object* v_00_u03b1_139_, lean_object* v_p_140_, lean_object* v_o_x27_141_, lean_object* v_motive_142_, lean_object* v_o_143_, lean_object* v_h_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(v_00_u03b1_139_, v_p_140_, v_o_x27_141_, v_motive_142_, v_o_143_, v_h_144_, v_h__1_145_, v_h__2_146_);
lean_dec(v_o_x27_141_);
return v_res_147_;
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
