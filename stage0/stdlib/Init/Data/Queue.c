// Lean compiler output
// Module: Init.Data.Queue
// Imports: public import Init.Data.List.Control
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
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Queue_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Queue_empty___closed__0 = (const lean_object*)&l_Std_Queue_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object*);
static lean_once_cell_t l_Std_Queue_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Queue_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object*);
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object* v_00_u03b1_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Std_Queue_empty___closed__0));
return v___x_4_;
}
}
static lean_object* _init_l_Std_Queue_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Std_Queue_empty(lean_box(0));
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Std_Queue_instEmptyCollection___closed__0, &l_Std_Queue_instEmptyCollection___closed__0_once, _init_l_Std_Queue_instEmptyCollection___closed__0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object* v_00_u03b1_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Std_Queue_instEmptyCollection___closed__0, &l_Std_Queue_instEmptyCollection___closed__0_once, _init_l_Std_Queue_instEmptyCollection___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object* v_q_10_){
_start:
{
lean_object* v_eList_11_; lean_object* v_dList_12_; uint8_t v___x_13_; 
v_eList_11_ = lean_ctor_get(v_q_10_, 0);
v_dList_12_ = lean_ctor_get(v_q_10_, 1);
v___x_13_ = l_List_isEmpty___redArg(v_dList_12_);
if (v___x_13_ == 0)
{
return v___x_13_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = l_List_isEmpty___redArg(v_eList_11_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object* v_q_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Std_Queue_isEmpty___redArg(v_q_15_);
lean_dec_ref(v_q_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object* v_00_u03b1_18_, lean_object* v_q_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Std_Queue_isEmpty___redArg(v_q_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object* v_00_u03b1_21_, lean_object* v_q_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Std_Queue_isEmpty(v_00_u03b1_21_, v_q_22_);
lean_dec_ref(v_q_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object* v_v_25_, lean_object* v_q_26_){
_start:
{
lean_object* v_eList_27_; lean_object* v_dList_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_36_; 
v_eList_27_ = lean_ctor_get(v_q_26_, 0);
v_dList_28_ = lean_ctor_get(v_q_26_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_q_26_);
if (v_isSharedCheck_36_ == 0)
{
v___x_30_ = v_q_26_;
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_dList_28_);
lean_inc(v_eList_27_);
lean_dec(v_q_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v_v_25_);
lean_ctor_set(v___x_32_, 1, v_eList_27_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_32_);
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_dList_28_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object* v_00_u03b1_37_, lean_object* v_v_38_, lean_object* v_q_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Queue_enqueue___redArg(v_v_38_, v_q_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object* v_vs_41_, lean_object* v_q_42_){
_start:
{
lean_object* v_eList_43_; lean_object* v_dList_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_eList_43_ = lean_ctor_get(v_q_42_, 0);
v_dList_44_ = lean_ctor_get(v_q_42_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_q_42_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v_q_42_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_dList_44_);
lean_inc(v_eList_43_);
lean_dec(v_q_42_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = l_List_appendTR___redArg(v_vs_41_, v_eList_43_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_dList_44_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object* v_00_u03b1_53_, lean_object* v_vs_54_, lean_object* v_q_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Queue_enqueueAll___redArg(v_vs_54_, v_q_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object* v_q_57_){
_start:
{
lean_object* v_dList_58_; 
v_dList_58_ = lean_ctor_get(v_q_57_, 1);
lean_inc(v_dList_58_);
if (lean_obj_tag(v_dList_58_) == 0)
{
lean_object* v_eList_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_78_; 
v_eList_59_ = lean_ctor_get(v_q_57_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_q_57_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_q_57_, 1);
lean_dec(v_unused_79_);
v___x_61_ = v_q_57_;
v_isShared_62_ = v_isSharedCheck_78_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_eList_59_);
lean_dec(v_q_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_78_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; 
v___x_63_ = l_List_reverse___redArg(v_eList_59_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; 
lean_del_object(v___x_61_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_77_; 
v_head_65_ = lean_ctor_get(v___x_63_, 0);
v_tail_66_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_77_ == 0)
{
v___x_68_ = v___x_63_;
v_isShared_69_ = v_isSharedCheck_77_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_tail_66_);
lean_inc(v_head_65_);
lean_dec(v___x_63_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_77_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_tail_66_);
lean_ctor_set(v___x_61_, 0, v_dList_58_);
v___x_71_ = v___x_61_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_dList_58_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_tail_66_);
v___x_71_ = v_reuseFailAlloc_76_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_73_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set_tag(v___x_68_, 0);
lean_ctor_set(v___x_68_, 1, v___x_71_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_head_65_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_75_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
}
}
}
else
{
lean_object* v_eList_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_97_; 
v_eList_80_ = lean_ctor_get(v_q_57_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_q_57_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_q_57_, 1);
lean_dec(v_unused_98_);
v___x_82_ = v_q_57_;
v_isShared_83_ = v_isSharedCheck_97_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_eList_80_);
lean_dec(v_q_57_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_97_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_96_; 
v_head_84_ = lean_ctor_get(v_dList_58_, 0);
v_tail_85_ = lean_ctor_get(v_dList_58_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_dList_58_);
if (v_isSharedCheck_96_ == 0)
{
v___x_87_ = v_dList_58_;
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_tail_85_);
lean_inc(v_head_84_);
lean_dec(v_dList_58_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_tail_85_);
v___x_90_ = v___x_82_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_eList_80_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_tail_85_);
v___x_90_ = v_reuseFailAlloc_95_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_92_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 0);
lean_ctor_set(v___x_87_, 1, v___x_90_);
v___x_92_ = v___x_87_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_head_84_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_94_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object* v_00_u03b1_99_, lean_object* v_q_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_Queue_dequeue_x3f___redArg(v_q_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object* v_q_102_){
_start:
{
lean_object* v_eList_103_; lean_object* v_dList_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_eList_103_ = lean_ctor_get(v_q_102_, 0);
lean_inc(v_eList_103_);
v_dList_104_ = lean_ctor_get(v_q_102_, 1);
lean_inc(v_dList_104_);
lean_dec_ref(v_q_102_);
v___x_105_ = lean_array_mk(v_dList_104_);
v___x_106_ = lean_array_mk(v_eList_103_);
v___x_107_ = l_Array_reverse___redArg(v___x_106_);
v___x_108_ = l_Array_append___redArg(v___x_105_, v___x_107_);
lean_dec_ref(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object* v_00_u03b1_109_, lean_object* v_q_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Queue_toArray___redArg(v_q_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object* v_dList_112_, lean_object* v_toPure_113_, lean_object* v_eList_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_List_isEmpty___redArg(v_dList_112_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_eList_114_);
lean_ctor_set(v___x_116_, 1, v_dList_112_);
v___x_117_ = lean_apply_2(v_toPure_113_, lean_box(0), v___x_116_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_dList_112_);
v___x_118_ = lean_box(0);
v___x_119_ = l_List_reverse___redArg(v_eList_114_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_apply_2(v_toPure_113_, lean_box(0), v___x_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object* v_toPure_122_, lean_object* v_as_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = l_List_reverse___redArg(v_as_123_);
v___x_125_ = lean_apply_2(v_toPure_122_, lean_box(0), v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object* v_toPure_126_, lean_object* v_inst_127_, lean_object* v_p_128_, lean_object* v_eList_129_, lean_object* v_toBind_130_, lean_object* v_dList_131_){
_start:
{
lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_inc(v_toPure_126_);
v___f_132_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_132_, 0, v_dList_131_);
lean_closure_set(v___f_132_, 1, v_toPure_126_);
v___x_133_ = lean_box(0);
v___x_134_ = l_List_filterAuxM___redArg(v_inst_127_, v_p_128_, v_eList_129_, v___x_133_);
v___f_135_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_135_, 0, v_toPure_126_);
lean_inc(v_toBind_130_);
v___x_136_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_134_, v___f_135_);
v___x_137_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_136_, v___f_132_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object* v_inst_138_, lean_object* v_p_139_, lean_object* v_q_140_){
_start:
{
lean_object* v_toApplicative_141_; lean_object* v_toBind_142_; lean_object* v_eList_143_; lean_object* v_dList_144_; lean_object* v_toPure_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_138_, 0);
v_toBind_142_ = lean_ctor_get(v_inst_138_, 1);
lean_inc_n(v_toBind_142_, 3);
v_eList_143_ = lean_ctor_get(v_q_140_, 0);
lean_inc(v_eList_143_);
v_dList_144_ = lean_ctor_get(v_q_140_, 1);
lean_inc(v_dList_144_);
lean_dec_ref(v_q_140_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_141_, 1);
lean_inc_n(v_toPure_145_, 2);
lean_inc(v_p_139_);
lean_inc_ref(v_inst_138_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_146_, 0, v_toPure_145_);
lean_closure_set(v___f_146_, 1, v_inst_138_);
lean_closure_set(v___f_146_, 2, v_p_139_);
lean_closure_set(v___f_146_, 3, v_eList_143_);
lean_closure_set(v___f_146_, 4, v_toBind_142_);
v___x_147_ = lean_box(0);
v___x_148_ = l_List_filterAuxM___redArg(v_inst_138_, v_p_139_, v_dList_144_, v___x_147_);
v___f_149_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_149_, 0, v_toPure_145_);
v___x_150_ = lean_apply_4(v_toBind_142_, lean_box(0), lean_box(0), v___x_148_, v___f_149_);
v___x_151_ = lean_apply_4(v_toBind_142_, lean_box(0), lean_box(0), v___x_150_, v___f_146_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object* v_m_152_, lean_object* v_inst_153_, lean_object* v_00_u03b1_154_, lean_object* v_p_155_, lean_object* v_q_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Queue_filterM___redArg(v_inst_153_, v_p_155_, v_q_156_);
return v___x_157_;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Queue(builtin);
}
#ifdef __cplusplus
}
#endif
