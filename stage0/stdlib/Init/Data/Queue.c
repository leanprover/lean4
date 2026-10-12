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
lean_object* l_Std_Queue_empty___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Std_Queue_empty___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Queue_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5_;
v_res_5_ = l_Std_Queue_empty___redArg();
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Queue_empty___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Queue_empty___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_Std_Queue_empty___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Queue_empty___redArg();
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object* v_00_u03b1_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_10_;
}
}
lean_object* l_Std_Queue_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT void l_Std_Queue_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_13_;
v_res_13_ = l_Std_Queue_instEmptyCollection___redArg();
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection___redArg___boxed(lean_object* v___dummy_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Queue_instEmptyCollection___redArg();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object* v_00_u03b1_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_17_;
}
}
lean_object* l_Std_Queue_instInhabited___redArg(){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_19_;
}
}
LEAN_EXPORT void l_Std_Queue_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_20_;
v_res_20_ = l_Std_Queue_instInhabited___redArg();
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Queue_instInhabited___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object* v_00_u03b1_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Std_Queue_empty___closed__0, &l_Std_Queue_empty___closed__0_once, _init_l_Std_Queue_empty___closed__0);
return v___x_24_;
}
}
uint8_t l_Std_Queue_isEmpty___redArg(lean_object* v_q_25_){
_start:
{
lean_object* v_eList_26_; lean_object* v_dList_27_; uint8_t v___x_28_; 
v_eList_26_ = lean_ctor_get(v_q_25_, 0);
v_dList_27_ = lean_ctor_get(v_q_25_, 1);
v___x_28_ = l_List_isEmpty___redArg(v_dList_27_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_List_isEmpty___redArg(v_eList_26_);
return v___x_29_;
}
}
}
LEAN_EXPORT void l_Std_Queue_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_25_ = stack[0].m_obj;
uint8_t v_res_30_;
v_res_30_ = l_Std_Queue_isEmpty___redArg(v_q_25_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object* v_q_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_Queue_isEmpty___redArg(v_q_31_);
lean_dec_ref(v_q_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l_Std_Queue_isEmpty(lean_object* v_00_u03b1_34_, lean_object* v_q_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Std_Queue_isEmpty___redArg(v_q_35_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_Queue_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_35_ = stack[1].m_obj;
uint8_t v_res_37_;
v_res_37_ = l_Std_Queue_isEmpty(lean_box(0), v_q_35_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object* v_00_u03b1_38_, lean_object* v_q_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Std_Queue_isEmpty(v_00_u03b1_38_, v_q_39_);
lean_dec_ref(v_q_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object* v_v_42_, lean_object* v_q_43_){
_start:
{
lean_object* v_eList_44_; lean_object* v_dList_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
v_eList_44_ = lean_ctor_get(v_q_43_, 0);
v_dList_45_ = lean_ctor_get(v_q_43_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_q_43_);
if (v_isSharedCheck_53_ == 0)
{
v___x_47_ = v_q_43_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_dList_45_);
lean_inc(v_eList_44_);
lean_dec(v_q_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v_v_42_);
lean_ctor_set(v___x_49_, 1, v_eList_44_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_dList_45_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object* v_00_u03b1_54_, lean_object* v_v_55_, lean_object* v_q_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Std_Queue_enqueue___redArg(v_v_55_, v_q_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object* v_vs_58_, lean_object* v_q_59_){
_start:
{
lean_object* v_eList_60_; lean_object* v_dList_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_69_; 
v_eList_60_ = lean_ctor_get(v_q_59_, 0);
v_dList_61_ = lean_ctor_get(v_q_59_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_q_59_);
if (v_isSharedCheck_69_ == 0)
{
v___x_63_ = v_q_59_;
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_dList_61_);
lean_inc(v_eList_60_);
lean_dec(v_q_59_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = l_List_appendTR___redArg(v_vs_58_, v_eList_60_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_dList_61_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object* v_00_u03b1_70_, lean_object* v_vs_71_, lean_object* v_q_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_Queue_enqueueAll___redArg(v_vs_71_, v_q_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object* v_q_74_){
_start:
{
lean_object* v_dList_75_; 
v_dList_75_ = lean_ctor_get(v_q_74_, 1);
lean_inc(v_dList_75_);
if (lean_obj_tag(v_dList_75_) == 0)
{
lean_object* v_eList_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_95_; 
v_eList_76_ = lean_ctor_get(v_q_74_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_q_74_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v_q_74_, 1);
lean_dec(v_unused_96_);
v___x_78_ = v_q_74_;
v_isShared_79_ = v_isSharedCheck_95_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_eList_76_);
lean_dec(v_q_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_95_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; 
v___x_80_ = l_List_reverse___redArg(v_eList_76_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_81_; 
lean_del_object(v___x_78_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v_head_82_; lean_object* v_tail_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_94_; 
v_head_82_ = lean_ctor_get(v___x_80_, 0);
v_tail_83_ = lean_ctor_get(v___x_80_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_94_ == 0)
{
v___x_85_ = v___x_80_;
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_tail_83_);
lean_inc(v_head_82_);
lean_dec(v___x_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v_tail_83_);
lean_ctor_set(v___x_78_, 0, v_dList_75_);
v___x_88_ = v___x_78_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_dList_75_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_tail_83_);
v___x_88_ = v_reuseFailAlloc_93_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 0);
lean_ctor_set(v___x_85_, 1, v___x_88_);
v___x_90_ = v___x_85_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_head_82_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
}
}
}
}
else
{
lean_object* v_eList_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_114_; 
v_eList_97_ = lean_ctor_get(v_q_74_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v_q_74_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; 
v_unused_115_ = lean_ctor_get(v_q_74_, 1);
lean_dec(v_unused_115_);
v___x_99_ = v_q_74_;
v_isShared_100_ = v_isSharedCheck_114_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_eList_97_);
lean_dec(v_q_74_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_114_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_113_; 
v_head_101_ = lean_ctor_get(v_dList_75_, 0);
v_tail_102_ = lean_ctor_get(v_dList_75_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_dList_75_);
if (v_isSharedCheck_113_ == 0)
{
v___x_104_ = v_dList_75_;
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_tail_102_);
lean_inc(v_head_101_);
lean_dec(v_dList_75_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_tail_102_);
v___x_107_ = v___x_99_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_eList_97_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_tail_102_);
v___x_107_ = v_reuseFailAlloc_112_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 0);
lean_ctor_set(v___x_104_, 1, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_head_101_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object* v_00_u03b1_116_, lean_object* v_q_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Queue_dequeue_x3f___redArg(v_q_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object* v_q_119_){
_start:
{
lean_object* v_eList_120_; lean_object* v_dList_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_eList_120_ = lean_ctor_get(v_q_119_, 0);
lean_inc(v_eList_120_);
v_dList_121_ = lean_ctor_get(v_q_119_, 1);
lean_inc(v_dList_121_);
lean_dec_ref(v_q_119_);
v___x_122_ = lean_array_mk(v_dList_121_);
v___x_123_ = lean_array_mk(v_eList_120_);
v___x_124_ = l_Array_reverse___redArg(v___x_123_);
v___x_125_ = l_Array_append___redArg(v___x_122_, v___x_124_);
lean_dec_ref(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object* v_00_u03b1_126_, lean_object* v_q_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_Queue_toArray___redArg(v_q_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object* v_toPure_129_, lean_object* v_as_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = l_List_reverse___redArg(v_as_130_);
v___x_132_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object* v_dList_133_, lean_object* v_toPure_134_, lean_object* v___x_135_, lean_object* v_eList_136_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = l_List_isEmpty___redArg(v_dList_133_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v___x_135_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_eList_136_);
lean_ctor_set(v___x_138_, 1, v_dList_133_);
v___x_139_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_dList_133_);
v___x_140_ = l_List_reverse___redArg(v_eList_136_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_135_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object* v_toPure_143_, lean_object* v___x_144_, lean_object* v_inst_145_, lean_object* v_p_146_, lean_object* v_eList_147_, lean_object* v_toBind_148_, lean_object* v___f_149_, lean_object* v_dList_150_){
_start:
{
lean_object* v___f_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_inc(v___x_144_);
v___f_151_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_151_, 0, v_dList_150_);
lean_closure_set(v___f_151_, 1, v_toPure_143_);
lean_closure_set(v___f_151_, 2, v___x_144_);
v___x_152_ = l_List_filterAuxM___redArg(v_inst_145_, v_p_146_, v_eList_147_, v___x_144_);
lean_inc(v_toBind_148_);
v___x_153_ = lean_apply_4(v_toBind_148_, lean_box(0), lean_box(0), v___x_152_, v___f_149_);
v___x_154_ = lean_apply_4(v_toBind_148_, lean_box(0), lean_box(0), v___x_153_, v___f_151_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object* v_inst_155_, lean_object* v_p_156_, lean_object* v_q_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toBind_159_; lean_object* v_eList_160_; lean_object* v_dList_161_; lean_object* v_toPure_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_155_, 0);
v_toBind_159_ = lean_ctor_get(v_inst_155_, 1);
lean_inc_n(v_toBind_159_, 3);
v_eList_160_ = lean_ctor_get(v_q_157_, 0);
lean_inc(v_eList_160_);
v_dList_161_ = lean_ctor_get(v_q_157_, 1);
lean_inc(v_dList_161_);
lean_dec_ref(v_q_157_);
v_toPure_162_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc_n(v_toPure_162_, 2);
v___x_163_ = lean_box(0);
lean_inc(v_p_156_);
lean_inc_ref(v_inst_155_);
v___x_164_ = l_List_filterAuxM___redArg(v_inst_155_, v_p_156_, v_dList_161_, v___x_163_);
v___f_165_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_165_, 0, v_toPure_162_);
lean_inc_ref(v___f_165_);
v___f_166_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__2), 8, 7);
lean_closure_set(v___f_166_, 0, v_toPure_162_);
lean_closure_set(v___f_166_, 1, v___x_163_);
lean_closure_set(v___f_166_, 2, v_inst_155_);
lean_closure_set(v___f_166_, 3, v_p_156_);
lean_closure_set(v___f_166_, 4, v_eList_160_);
lean_closure_set(v___f_166_, 5, v_toBind_159_);
lean_closure_set(v___f_166_, 6, v___f_165_);
v___x_167_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_164_, v___f_165_);
v___x_168_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_167_, v___f_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object* v_m_169_, lean_object* v_inst_170_, lean_object* v_00_u03b1_171_, lean_object* v_p_172_, lean_object* v_q_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Queue_filterM___redArg(v_inst_170_, v_p_172_, v_q_173_);
return v___x_174_;
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
