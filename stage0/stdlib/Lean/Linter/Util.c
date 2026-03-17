// Lean compiler output
// Module: Lean.Linter.Util
// Imports: public import Lean.Server.InfoUtils public import Lean.Linter.Basic
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
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_contains(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value;
static const lean_closure_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value;
static const lean_array_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = 1;
v___x_6_ = lean_box(v___x_5_);
v___x_7_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object* v_toPure_8_, lean_object* v_x_9_, lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(v_toPure_8_, v_x_9_, v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object* v_toPure_18_, lean_object* v_range_19_, lean_object* v_x_20_, lean_object* v_i_21_, lean_object* v_x_22_, lean_object* v_results_23_){
_start:
{
uint8_t v___y_25_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_results_44_; 
v___x_41_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1));
v___x_42_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2));
v___x_43_ = l_List_filterMapTR_go___redArg(v___x_41_, v_results_23_, v___x_42_);
v_results_44_ = l_List_filterMapTR_go___redArg(v___x_41_, v___x_43_, v___x_42_);
if (lean_obj_tag(v_results_44_) == 1)
{
if (lean_obj_tag(v_i_21_) == 4)
{
lean_object* v_head_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_61_; 
v_head_45_ = lean_ctor_get(v_results_44_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_results_44_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v_results_44_, 1);
lean_dec(v_unused_62_);
v___x_47_ = v_results_44_;
v_isShared_48_ = v_isSharedCheck_61_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_head_45_);
lean_dec(v_results_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_61_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_i_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_60_; 
v_i_49_ = lean_ctor_get(v_i_21_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_i_21_);
if (v_isSharedCheck_60_ == 0)
{
v___x_51_ = v_i_21_;
v_isShared_52_ = v_isSharedCheck_60_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_i_49_);
lean_dec(v_i_21_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_60_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v_head_45_);
lean_ctor_set(v___x_47_, 0, v_i_49_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_i_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_head_45_);
v___x_54_ = v_reuseFailAlloc_59_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 1);
lean_ctor_set(v___x_51_, 0, v___x_54_);
v___x_56_ = v___x_51_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_58_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; 
v___x_57_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_56_);
return v___x_57_;
}
}
}
}
}
else
{
lean_object* v_head_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec_ref(v_i_21_);
v_head_63_ = lean_ctor_get(v_results_44_, 0);
lean_inc(v_head_63_);
lean_dec_ref(v_results_44_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v_head_63_);
v___x_65_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_64_);
return v___x_65_;
}
}
else
{
lean_object* v_start_66_; lean_object* v_stop_67_; uint8_t v___x_68_; uint8_t v___x_69_; 
lean_dec(v_results_44_);
v_start_66_ = lean_ctor_get(v_range_19_, 0);
v_stop_67_ = lean_ctor_get(v_range_19_, 1);
v___x_68_ = 0;
v___x_69_ = l_Lean_Elab_Info_contains(v_i_21_, v_start_66_, v___x_68_);
if (v___x_69_ == 0)
{
v___y_25_ = v___x_69_;
goto v___jp_24_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = l_Lean_Elab_Info_contains(v_i_21_, v_stop_67_, v___x_69_);
v___y_25_ = v___x_70_;
goto v___jp_24_;
}
}
v___jp_24_:
{
if (v___y_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec_ref(v_i_21_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_26_);
return v___x_27_;
}
else
{
if (lean_obj_tag(v_i_21_) == 4)
{
lean_object* v_i_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_38_; 
v_i_28_ = lean_ctor_get(v_i_21_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v_i_21_);
if (v_isSharedCheck_38_ == 0)
{
v___x_30_ = v_i_21_;
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_i_28_);
lean_dec(v_i_21_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v_i_28_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
if (v_isShared_31_ == 0)
{
lean_ctor_set_tag(v___x_30_, 1);
lean_ctor_set(v___x_30_, 0, v___x_33_);
v___x_35_ = v___x_30_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_37_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_35_);
return v___x_36_;
}
}
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec_ref(v_i_21_);
v___x_39_ = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0));
v___x_40_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_39_);
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object* v_toPure_71_, lean_object* v_range_72_, lean_object* v_x_73_, lean_object* v_i_74_, lean_object* v_x_75_, lean_object* v_results_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(v_toPure_71_, v_range_72_, v_x_73_, v_i_74_, v_x_75_, v_results_76_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_x_73_);
lean_dec_ref(v_range_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object* v_inst_78_, lean_object* v_range_79_, lean_object* v_tree_80_){
_start:
{
lean_object* v_toApplicative_81_; lean_object* v_toPure_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_toApplicative_81_ = lean_ctor_get(v_inst_78_, 0);
v_toPure_82_ = lean_ctor_get(v_toApplicative_81_, 1);
lean_inc(v_toPure_82_);
v___f_83_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_83_, 0, v_toPure_82_);
lean_inc(v_toPure_82_);
v___f_84_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_84_, 0, v_toPure_82_);
lean_closure_set(v___f_84_, 1, v_range_79_);
v___x_85_ = lean_box(0);
v___x_86_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_box(0), lean_box(0), v_inst_78_, v___f_83_, v___f_84_, v___x_85_, v_tree_80_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object* v_m_87_, lean_object* v_inst_88_, lean_object* v_range_89_, lean_object* v_tree_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(v_inst_88_, v_range_89_, v_tree_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object* v_toPure_92_, lean_object* v_____do__lift_93_){
_start:
{
if (lean_obj_tag(v_____do__lift_93_) == 1)
{
lean_object* v_val_97_; 
v_val_97_ = lean_ctor_get(v_____do__lift_93_, 0);
lean_inc(v_val_97_);
lean_dec_ref(v_____do__lift_93_);
if (lean_obj_tag(v_val_97_) == 1)
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_val_98_ = lean_ctor_get(v_val_97_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_val_97_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_val_97_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_val_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = l_List_reverse___redArg(v_val_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_106_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_104_);
return v___x_105_;
}
}
}
else
{
lean_dec(v_val_97_);
goto v___jp_94_;
}
}
else
{
lean_dec(v_____do__lift_93_);
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_box(0);
v___x_96_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object* v_inst_108_, lean_object* v_range_109_, lean_object* v_tree_110_){
_start:
{
lean_object* v_toApplicative_111_; lean_object* v_toBind_112_; lean_object* v_toPure_113_; lean_object* v___x_114_; lean_object* v___f_115_; lean_object* v___x_116_; 
v_toApplicative_111_ = lean_ctor_get(v_inst_108_, 0);
v_toBind_112_ = lean_ctor_get(v_inst_108_, 1);
lean_inc(v_toBind_112_);
v_toPure_113_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toPure_113_);
v___x_114_ = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(v_inst_108_, v_range_109_, v_tree_110_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_115_, 0, v_toPure_113_);
v___x_116_ = lean_apply_4(v_toBind_112_, lean_box(0), lean_box(0), v___x_114_, v___f_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object* v_m_117_, lean_object* v_inst_118_, lean_object* v_range_119_, lean_object* v_tree_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Linter_collectMacroExpansions_x3f___redArg(v_inst_118_, v_range_119_, v_tree_120_);
return v___x_121_;
}
}
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Util(builtin);
}
#ifdef __cplusplus
}
#endif
