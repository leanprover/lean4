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
lean_dec_ref_known(v_x_1_, 1);
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
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(uint8_t v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
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
LEAN_EXPORT void l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_17_ = stack[0].m_num;
lean_object* v_h__1_18_ = stack[1].m_obj;
lean_object* v_h__2_19_ = stack[2].m_obj;
lean_object* v_res_24_;
v_res_24_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_25_, lean_object* v_h__1_26_, lean_object* v_h__2_27_){
_start:
{
uint8_t v_x_24__boxed_28_; lean_object* v_res_29_; 
v_x_24__boxed_28_ = lean_unbox(v_x_25_);
v_res_29_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_28_, v_h__1_26_, v_h__2_27_);
return v_res_29_;
}
}
lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_object* v_motive_30_, uint8_t v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (v_x_31_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__1_32_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__2_33_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_33_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__1_32_, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Find_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_31_ = stack[1].m_num;
lean_object* v_h__1_32_ = stack[2].m_obj;
lean_object* v_h__2_33_ = stack[3].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(lean_box(0), v_x_31_, v_h__1_32_, v_h__2_33_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
uint8_t v_x_41__boxed_43_; lean_object* v_res_44_; 
v_x_41__boxed_43_ = lean_unbox(v_x_40_);
v_res_44_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(v_motive_39_, v_x_41__boxed_43_, v_h__1_41_, v_h__2_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v_val_50_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_val_50_);
lean_dec_ref_known(v_x_45_, 1);
v___x_51_ = lean_apply_1(v_h__2_47_, v_val_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_52_, lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_56_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_h__1_55_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_55_);
v_val_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v_x_54_, 1);
v___x_60_ = lean_apply_1(v_h__2_56_, v_val_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_65_; 
lean_dec(v_h__2_64_);
v___x_65_ = lean_apply_1(v_h__1_63_, v_x_62_);
return v___x_65_;
}
else
{
lean_object* v_head_66_; lean_object* v_tail_67_; lean_object* v___x_68_; 
lean_dec(v_h__1_63_);
v_head_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_head_66_);
v_tail_67_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_tail_67_);
lean_dec_ref_known(v_x_61_, 2);
v___x_68_ = lean_apply_3(v_h__2_64_, v_head_66_, v_tail_67_, v_x_62_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v___x_75_; 
lean_dec(v_h__2_74_);
v___x_75_ = lean_apply_1(v_h__1_73_, v_x_72_);
return v___x_75_;
}
else
{
lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_73_);
v_head_76_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_head_76_);
v_tail_77_ = lean_ctor_get(v_x_71_, 1);
lean_inc(v_tail_77_);
lean_dec_ref_known(v_x_71_, 2);
v___x_78_ = lean_apply_3(v_h__2_74_, v_head_76_, v_tail_77_, v_x_72_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__1_80_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__2_81_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_81_);
v_val_84_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v_x_79_, 1);
v___x_85_ = lean_apply_1(v_h__1_80_, v_val_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(lean_object* v_00_u03b1_86_, lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_89_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__2_90_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_94_; 
lean_dec(v_h__2_90_);
v_val_93_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_val_93_);
lean_dec_ref_known(v_x_88_, 1);
v___x_94_ = lean_apply_1(v_h__1_89_, v_val_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v___x_99_; 
lean_dec(v_h__2_98_);
v___x_99_ = lean_apply_2(v_h__1_97_, v_x_96_, lean_box(0));
return v___x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_97_);
v_head_100_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_tail_101_);
lean_dec_ref_known(v_x_95_, 2);
v___x_102_ = lean_apply_4(v_h__2_98_, v_head_100_, v_tail_101_, v_x_96_, lean_box(0));
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(lean_object* v_00_u03b1_103_, lean_object* v_l_104_, lean_object* v_motive_105_, lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v___x_111_; 
lean_dec(v_h__2_110_);
v___x_111_ = lean_apply_2(v_h__1_109_, v_x_107_, lean_box(0));
return v___x_111_;
}
else
{
lean_object* v_head_112_; lean_object* v_tail_113_; lean_object* v___x_114_; 
lean_dec(v_h__1_109_);
v_head_112_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_head_112_);
v_tail_113_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_tail_113_);
lean_dec_ref_known(v_x_106_, 2);
v___x_114_ = lean_apply_4(v_h__2_110_, v_head_112_, v_tail_113_, v_x_107_, lean_box(0));
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(lean_object* v_00_u03b1_115_, lean_object* v_l_116_, lean_object* v_motive_117_, lean_object* v_x_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(v_00_u03b1_115_, v_l_116_, v_motive_117_, v_x_118_, v_x_119_, v_x_120_, v_h__1_121_, v_h__2_122_);
lean_dec(v_l_116_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(lean_object* v_o_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
if (lean_obj_tag(v_o_124_) == 0)
{
lean_object* v___x_127_; 
lean_dec(v_h__2_126_);
v___x_127_ = lean_apply_1(v_h__1_125_, lean_box(0));
return v___x_127_;
}
else
{
lean_object* v_val_128_; lean_object* v___x_129_; 
lean_dec(v_h__1_125_);
v_val_128_ = lean_ctor_get(v_o_124_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v_o_124_, 1);
v___x_129_ = lean_apply_2(v_h__2_126_, v_val_128_, lean_box(0));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(lean_object* v_00_u03b1_130_, lean_object* v_p_131_, lean_object* v_o_x27_132_, lean_object* v_motive_133_, lean_object* v_o_134_, lean_object* v_h_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
if (lean_obj_tag(v_o_134_) == 0)
{
lean_object* v___x_138_; 
lean_dec(v_h__2_137_);
v___x_138_ = lean_apply_1(v_h__1_136_, lean_box(0));
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_140_; 
lean_dec(v_h__1_136_);
v_val_139_ = lean_ctor_get(v_o_134_, 0);
lean_inc(v_val_139_);
lean_dec_ref_known(v_o_134_, 1);
v___x_140_ = lean_apply_2(v_h__2_137_, v_val_139_, lean_box(0));
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(lean_object* v_00_u03b1_141_, lean_object* v_p_142_, lean_object* v_o_x27_143_, lean_object* v_motive_144_, lean_object* v_o_145_, lean_object* v_h_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(v_00_u03b1_141_, v_p_142_, v_o_x27_143_, v_motive_144_, v_o_145_, v_h_146_, v_h__1_147_, v_h__2_148_);
lean_dec(v_o_x27_143_);
return v_res_149_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
