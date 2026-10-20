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
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Queue_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Queue_empty___redArg___closed__0 = (const lean_object*)&l_Std_Queue_empty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Queue_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Queue_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Queue_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_empty___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Std_Queue_empty___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_empty___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Queue_empty___redArg();
return v_res_6_;
}
}
static lean_object* _init_l_Std_Queue_empty___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Std_Queue_empty___redArg();
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object* v_00_u03b1_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_Queue_instEmptyCollection___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object* v_00_u03b1_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited___redArg(){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited___redArg___boxed(lean_object* v___dummy_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Queue_instInhabited___redArg();
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object* v_00_u03b1_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object* v_q_22_){
_start:
{
lean_object* v_eList_23_; lean_object* v_dList_24_; uint8_t v___x_25_; 
v_eList_23_ = lean_ctor_get(v_q_22_, 0);
v_dList_24_ = lean_ctor_get(v_q_22_, 1);
v___x_25_ = l_List_isEmpty___redArg(v_dList_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = l_List_isEmpty___redArg(v_eList_23_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object* v_q_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Std_Queue_isEmpty___redArg(v_q_27_);
lean_dec_ref(v_q_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object* v_00_u03b1_30_, lean_object* v_q_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = l_Std_Queue_isEmpty___redArg(v_q_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object* v_00_u03b1_33_, lean_object* v_q_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Queue_isEmpty(v_00_u03b1_33_, v_q_34_);
lean_dec_ref(v_q_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object* v_v_37_, lean_object* v_q_38_){
_start:
{
lean_object* v_eList_39_; lean_object* v_dList_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_48_; 
v_eList_39_ = lean_ctor_get(v_q_38_, 0);
v_dList_40_ = lean_ctor_get(v_q_38_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_q_38_);
if (v_isSharedCheck_48_ == 0)
{
v___x_42_ = v_q_38_;
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_dList_40_);
lean_inc(v_eList_39_);
lean_dec(v_q_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v_v_37_);
lean_ctor_set(v___x_44_, 1, v_eList_39_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_dList_40_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object* v_00_u03b1_49_, lean_object* v_v_50_, lean_object* v_q_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_Queue_enqueue___redArg(v_v_50_, v_q_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object* v_vs_53_, lean_object* v_q_54_){
_start:
{
lean_object* v_eList_55_; lean_object* v_dList_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_eList_55_ = lean_ctor_get(v_q_54_, 0);
v_dList_56_ = lean_ctor_get(v_q_54_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_q_54_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v_q_54_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_dList_56_);
lean_inc(v_eList_55_);
lean_dec(v_q_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = l_List_appendTR___redArg(v_vs_53_, v_eList_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_dList_56_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object* v_00_u03b1_65_, lean_object* v_vs_66_, lean_object* v_q_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Queue_enqueueAll___redArg(v_vs_66_, v_q_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object* v_q_69_){
_start:
{
lean_object* v_dList_70_; 
v_dList_70_ = lean_ctor_get(v_q_69_, 1);
lean_inc(v_dList_70_);
if (lean_obj_tag(v_dList_70_) == 0)
{
lean_object* v_eList_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_90_; 
v_eList_71_ = lean_ctor_get(v_q_69_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_q_69_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_q_69_, 1);
lean_dec(v_unused_91_);
v___x_73_ = v_q_69_;
v_isShared_74_ = v_isSharedCheck_90_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_eList_71_);
lean_dec(v_q_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_90_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; 
v___x_75_ = l_List_reverse___redArg(v_eList_71_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_76_; 
lean_del_object(v___x_73_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v_head_77_; lean_object* v_tail_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_89_; 
v_head_77_ = lean_ctor_get(v___x_75_, 0);
v_tail_78_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_89_ == 0)
{
v___x_80_ = v___x_75_;
v_isShared_81_ = v_isSharedCheck_89_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_tail_78_);
lean_inc(v_head_77_);
lean_dec(v___x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_89_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v_tail_78_);
lean_ctor_set(v___x_73_, 0, v_dList_70_);
v___x_83_ = v___x_73_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_dList_70_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_tail_78_);
v___x_83_ = v_reuseFailAlloc_88_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 0);
lean_ctor_set(v___x_80_, 1, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_head_77_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_83_);
v___x_85_ = v_reuseFailAlloc_87_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; 
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
}
}
}
}
else
{
lean_object* v_eList_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_109_; 
v_eList_92_ = lean_ctor_get(v_q_69_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_q_69_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v_q_69_, 1);
lean_dec(v_unused_110_);
v___x_94_ = v_q_69_;
v_isShared_95_ = v_isSharedCheck_109_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_eList_92_);
lean_dec(v_q_69_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_109_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_head_96_; lean_object* v_tail_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v_head_96_ = lean_ctor_get(v_dList_70_, 0);
v_tail_97_ = lean_ctor_get(v_dList_70_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_dList_70_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v_dList_70_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_tail_97_);
lean_inc(v_head_96_);
lean_dec(v_dList_70_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_tail_97_);
v___x_102_ = v___x_94_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_eList_92_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_tail_97_);
v___x_102_ = v_reuseFailAlloc_107_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_104_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set_tag(v___x_99_, 0);
lean_ctor_set(v___x_99_, 1, v___x_102_);
v___x_104_ = v___x_99_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_head_96_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_106_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object* v_00_u03b1_111_, lean_object* v_q_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Queue_dequeue_x3f___redArg(v_q_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object* v_q_114_){
_start:
{
lean_object* v_eList_115_; lean_object* v_dList_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_eList_115_ = lean_ctor_get(v_q_114_, 0);
lean_inc(v_eList_115_);
v_dList_116_ = lean_ctor_get(v_q_114_, 1);
lean_inc(v_dList_116_);
lean_dec_ref(v_q_114_);
v___x_117_ = lean_array_mk(v_dList_116_);
v___x_118_ = lean_array_mk(v_eList_115_);
v___x_119_ = l_Array_reverse___redArg(v___x_118_);
v___x_120_ = l_Array_append___redArg(v___x_117_, v___x_119_);
lean_dec_ref(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object* v_00_u03b1_121_, lean_object* v_q_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Queue_toArray___redArg(v_q_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object* v_toPure_124_, lean_object* v_as_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = l_List_reverse___redArg(v_as_125_);
v___x_127_ = lean_apply_2(v_toPure_124_, lean_box(0), v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object* v_dList_128_, lean_object* v_toPure_129_, lean_object* v___x_130_, lean_object* v_eList_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = l_List_isEmpty___redArg(v_dList_128_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v___x_130_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_eList_131_);
lean_ctor_set(v___x_133_, 1, v_dList_128_);
v___x_134_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_dList_128_);
v___x_135_ = l_List_reverse___redArg(v_eList_131_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_130_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object* v_toPure_138_, lean_object* v___x_139_, lean_object* v_inst_140_, lean_object* v_p_141_, lean_object* v_eList_142_, lean_object* v_toBind_143_, lean_object* v___f_144_, lean_object* v_dList_145_){
_start:
{
lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_inc(v___x_139_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_146_, 0, v_dList_145_);
lean_closure_set(v___f_146_, 1, v_toPure_138_);
lean_closure_set(v___f_146_, 2, v___x_139_);
v___x_147_ = l_List_filterAuxM___redArg(v_inst_140_, v_p_141_, v_eList_142_, v___x_139_);
lean_inc(v_toBind_143_);
v___x_148_ = lean_apply_4(v_toBind_143_, lean_box(0), lean_box(0), v___x_147_, v___f_144_);
v___x_149_ = lean_apply_4(v_toBind_143_, lean_box(0), lean_box(0), v___x_148_, v___f_146_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object* v_inst_150_, lean_object* v_p_151_, lean_object* v_q_152_){
_start:
{
lean_object* v_toApplicative_153_; lean_object* v_toBind_154_; lean_object* v_eList_155_; lean_object* v_dList_156_; lean_object* v_toPure_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_toApplicative_153_ = lean_ctor_get(v_inst_150_, 0);
v_toBind_154_ = lean_ctor_get(v_inst_150_, 1);
lean_inc_n(v_toBind_154_, 3);
v_eList_155_ = lean_ctor_get(v_q_152_, 0);
lean_inc(v_eList_155_);
v_dList_156_ = lean_ctor_get(v_q_152_, 1);
lean_inc(v_dList_156_);
lean_dec_ref(v_q_152_);
v_toPure_157_ = lean_ctor_get(v_toApplicative_153_, 1);
lean_inc_n(v_toPure_157_, 2);
v___x_158_ = lean_box(0);
lean_inc(v_p_151_);
lean_inc_ref(v_inst_150_);
v___x_159_ = l_List_filterAuxM___redArg(v_inst_150_, v_p_151_, v_dList_156_, v___x_158_);
v___f_160_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_160_, 0, v_toPure_157_);
lean_inc_ref(v___f_160_);
v___f_161_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__2), 8, 7);
lean_closure_set(v___f_161_, 0, v_toPure_157_);
lean_closure_set(v___f_161_, 1, v___x_158_);
lean_closure_set(v___f_161_, 2, v_inst_150_);
lean_closure_set(v___f_161_, 3, v_p_151_);
lean_closure_set(v___f_161_, 4, v_eList_155_);
lean_closure_set(v___f_161_, 5, v_toBind_154_);
lean_closure_set(v___f_161_, 6, v___f_160_);
v___x_162_ = lean_apply_4(v_toBind_154_, lean_box(0), lean_box(0), v___x_159_, v___f_160_);
v___x_163_ = lean_apply_4(v_toBind_154_, lean_box(0), lean_box(0), v___x_162_, v___f_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object* v_m_164_, lean_object* v_inst_165_, lean_object* v_00_u03b1_166_, lean_object* v_p_167_, lean_object* v_q_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Queue_filterM___redArg(v_inst_165_, v_p_167_, v_q_168_);
return v___x_169_;
}
}
lean_object* runtime_initialize_Init_Data_List_Control(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
