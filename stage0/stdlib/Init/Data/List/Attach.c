// Lean compiler output
// Module: Init.Data.List.Attach
// Imports: import all Init.Data.List.Lemmas public import Init.Data.List.Lemmas import Init.Data.List.Count import Init.Data.Subtype.Basic
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
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_pmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmapImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmap___redArg(lean_object* v_f_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
lean_dec(v_f_1_);
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
lean_inc(v_f_1_);
v___x_9_ = lean_apply_2(v_f_1_, v_head_4_, lean_box(0));
v___x_10_ = l_List_pmap___redArg(v_f_1_, v_tail_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_10_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_pmap(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_P_17_, lean_object* v_f_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_List_pmap___redArg(v_f_18_, v_x_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(lean_object* v_l_22_){
_start:
{
lean_inc(v_l_22_);
return v_l_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg___boxed(lean_object* v_l_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl___redArg(v_l_23_);
lean_dec(v_l_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl(lean_object* v_00_u03b1_25_, lean_object* v_l_26_, lean_object* v_P_27_, lean_object* v_x_28_){
_start:
{
lean_inc(v_l_26_);
return v_l_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___boxed(lean_object* v_00_u03b1_29_, lean_object* v_l_30_, lean_object* v_P_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Init_Data_List_Attach_0__List_attachWithImpl(v_00_u03b1_29_, v_l_30_, v_P_31_, v_x_32_);
lean_dec(v_l_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_List_attach___redArg(lean_object* v_l_34_){
_start:
{
lean_inc(v_l_34_);
return v_l_34_;
}
}
LEAN_EXPORT lean_object* l_List_attach___redArg___boxed(lean_object* v_l_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_List_attach___redArg(v_l_35_);
lean_dec(v_l_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_List_attach(lean_object* v_00_u03b1_37_, lean_object* v_l_38_){
_start:
{
lean_inc(v_l_38_);
return v_l_38_;
}
}
LEAN_EXPORT lean_object* l_List_attach___boxed(lean_object* v_00_u03b1_39_, lean_object* v_l_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_List_attach(v_00_u03b1_39_, v_l_40_);
lean_dec(v_l_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg___lam__0(lean_object* v_f_42_, lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_apply_2(v_f_42_, v_x_43_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_List_pmapImpl___redArg(lean_object* v_f_45_, lean_object* v_l_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___f_47_ = lean_alloc_closure((void*)(l_List_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_47_, 0, v_f_45_);
v___x_48_ = lean_box(0);
v___x_49_ = l_List_mapTR_loop___redArg(v___f_47_, v_l_46_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_List_pmapImpl(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_P_52_, lean_object* v_f_53_, lean_object* v_l_54_, lean_object* v_H_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___f_56_ = lean_alloc_closure((void*)(l_List_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_56_, 0, v_f_53_);
v___x_57_ = lean_box(0);
v___x_58_ = l_List_mapTR_loop___redArg(v___f_56_, v_l_54_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_61_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_apply_1(v_h__1_60_, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v_val_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_60_);
v_val_64_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v_x_59_, 1);
v___x_65_ = lean_apply_1(v_h__2_61_, v_val_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__2_70_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__1_69_, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_69_);
v_val_73_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v_x_68_, 1);
v___x_74_ = lean_apply_1(v_h__2_70_, v_val_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
if (lean_obj_tag(v_a_75_) == 0)
{
lean_object* v___x_77_; 
v___x_77_ = l_List_reverse___redArg(v_a_76_);
return v___x_77_;
}
else
{
lean_object* v_head_78_; lean_object* v_tail_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
v_head_78_ = lean_ctor_get(v_a_75_, 0);
v_tail_79_ = lean_ctor_get(v_a_75_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_a_75_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v_a_75_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_tail_79_);
lean_inc(v_head_78_);
lean_dec(v_a_75_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_a_76_);
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_head_78_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_a_76_);
v___x_84_ = v_reuseFailAlloc_86_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
v_a_75_ = v_tail_79_;
v_a_76_ = v___x_84_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_unattach___redArg(lean_object* v_l_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(0);
v___x_90_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_l_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_List_unattach(lean_object* v_00_u03b1_91_, lean_object* v_p_92_, lean_object* v_l_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_List_unattach___redArg(v_l_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_unattach_spec__0(lean_object* v_00_u03b1_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_List_mapTR_loop___at___00List_unattach_spec__0___redArg(v_a_96_, v_a_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v_h__1_100_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_apply_1(v_h__2_101_, v___x_102_);
return v___x_103_;
}
else
{
lean_object* v_val_104_; lean_object* v___x_105_; 
lean_dec(v_h__2_101_);
v_val_104_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v_x_99_, 1);
v___x_105_ = lean_apply_1(v_h__1_100_, v_val_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_106_, lean_object* v_motive_107_, lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__1_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__2_110_, v___x_111_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_110_);
v_val_113_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v_x_108_, 1);
v___x_114_ = lean_apply_1(v_h__1_109_, v_val_113_);
return v___x_114_;
}
}
}
lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(uint8_t v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (v_x_115_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_h__1_116_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_1(v_h__2_117_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_117_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__1_116_, v___x_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_115_ = stack[0].m_num;
lean_object* v_h__1_116_ = stack[1].m_obj;
lean_object* v_h__2_117_ = stack[2].m_obj;
lean_object* v_res_122_;
v_res_122_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(v_x_115_, v_h__1_116_, v_h__2_117_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
uint8_t v_x_24__boxed_126_; lean_object* v_res_127_; 
v_x_24__boxed_126_ = lean_unbox(v_x_123_);
v_res_127_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_126_, v_h__1_124_, v_h__2_125_);
return v_res_127_;
}
}
lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(lean_object* v_motive_128_, uint8_t v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (v_x_129_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_130_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__2_131_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_131_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_apply_1(v_h__1_130_, v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_129_ = stack[1].m_num;
lean_object* v_h__1_130_ = stack[2].m_obj;
lean_object* v_h__2_131_ = stack[3].m_obj;
lean_object* v_res_136_;
v_res_136_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(lean_box(0), v_x_129_, v_h__1_130_, v_h__2_131_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
uint8_t v_x_41__boxed_141_; lean_object* v_res_142_; 
v_x_41__boxed_141_ = lean_unbox(v_x_138_);
v_res_142_ = l___private_Init_Data_List_Attach_0__List_filter_match__1_splitter(v_motive_137_, v_x_41__boxed_141_, v_h__1_139_, v_h__2_140_);
return v_res_142_;
}
}
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
