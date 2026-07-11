// Lean compiler output
// Module: Lake.Util.Cycle
// Imports: public import Init.Data.ToString
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_formatCycle___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_Lake_formatCycle___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_formatCycle___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_formatCycle___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lake_formatCycle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_formatCycle___redArg___closed__0 = (const lean_object*)&l_Lake_formatCycle___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_formatCycle___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfMonadCallStackOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfMonadCallStackOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfMonadCycleOf___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfMonadCycleOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfMonadCycleOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfMonadCycle___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfMonadCycle(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0 = (const lean_object*)&l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_guardCycle___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_guardCycle___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_guardCycle___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_guardCycle___redArg___lam__1___closed__0 = (const lean_object*)&l_Lake_guardCycle___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_guardCycle___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_guardCycle___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_guardCycle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___redArg___lam__0(lean_object* v_inst_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = ((lean_object*)(l_Lake_formatCycle___redArg___lam__0___closed__0));
v___x_5_ = lean_apply_1(v_inst_2_, v_x_3_);
v___x_6_ = lean_string_append(v___x_4_, v___x_5_);
lean_dec_ref(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___redArg(lean_object* v_inst_8_, lean_object* v_cycle_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_10_ = lean_alloc_closure((void*)(l_Lake_formatCycle___redArg___lam__0), 2, 1);
lean_closure_set(v___f_10_, 0, v_inst_8_);
v___x_11_ = ((lean_object*)(l_Lake_formatCycle___redArg___closed__0));
v___x_12_ = lean_box(0);
v___x_13_ = l_List_mapTR_loop___redArg(v___f_10_, v_cycle_9_, v___x_12_);
v___x_14_ = l_String_intercalate(v___x_11_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle(lean_object* v_00_u03ba_15_, lean_object* v_inst_16_, lean_object* v_cycle_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lake_formatCycle___redArg(v_inst_16_, v_cycle_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfMonadCallStackOf___redArg___lam__0(lean_object* v_withCallStack_19_, lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_3(v_withCallStack_19_, lean_box(0), v___y_21_, v___y_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(lean_object* v_inst_24_){
_start:
{
lean_object* v_getCallStack_25_; lean_object* v_withCallStack_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_34_; 
v_getCallStack_25_ = lean_ctor_get(v_inst_24_, 0);
v_withCallStack_26_ = lean_ctor_get(v_inst_24_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_inst_24_);
if (v_isSharedCheck_34_ == 0)
{
v___x_28_ = v_inst_24_;
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_withCallStack_26_);
lean_inc(v_getCallStack_25_);
lean_dec(v_inst_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___f_30_; lean_object* v___x_32_; 
v___f_30_ = lean_alloc_closure((void*)(l_Lake_instMonadCallStackOfMonadCallStackOf___redArg___lam__0), 4, 1);
lean_closure_set(v___f_30_, 0, v_withCallStack_26_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v___f_30_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_getCallStack_25_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___f_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfMonadCallStackOf(lean_object* v_00_u03ba_35_, lean_object* v_m_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(v_inst_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object* v_withCallStack_39_, lean_object* v_s_40_, lean_object* v_00_u03b2_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_apply_3(v_withCallStack_39_, lean_box(0), v_s_40_, v___y_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__1(lean_object* v_withCallStack_44_, lean_object* v_inst_45_, lean_object* v_00_u03b1_46_, lean_object* v_s_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; 
v___f_49_ = lean_alloc_closure((void*)(l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_49_, 0, v_withCallStack_44_);
lean_closure_set(v___f_49_, 1, v_s_47_);
v___x_50_ = lean_apply_3(v_inst_45_, lean_box(0), v___f_49_, v___y_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_getCallStack_54_; lean_object* v_withCallStack_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_64_; 
v_getCallStack_54_ = lean_ctor_get(v_inst_53_, 0);
v_withCallStack_55_ = lean_ctor_get(v_inst_53_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_inst_53_);
if (v_isSharedCheck_64_ == 0)
{
v___x_57_ = v_inst_53_;
v_isShared_58_ = v_isSharedCheck_64_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_withCallStack_55_);
lean_inc(v_getCallStack_54_);
lean_dec(v_inst_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_64_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___f_59_ = lean_alloc_closure((void*)(l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_59_, 0, v_withCallStack_55_);
lean_closure_set(v___f_59_, 1, v_inst_52_);
v___x_60_ = lean_apply_2(v_inst_51_, lean_box(0), v_getCallStack_54_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___f_59_);
lean_ctor_set(v___x_57_, 0, v___x_60_);
v___x_62_ = v___x_57_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___f_59_);
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
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor(lean_object* v_m_65_, lean_object* v_n_66_, lean_object* v_00_u03ba_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(v_inst_68_, v_inst_69_, v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfMonadCycleOf___redArg___lam__0(lean_object* v_throwCycle_72_, lean_object* v_00_u03b1_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_apply_2(v_throwCycle_72_, lean_box(0), v___y_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfMonadCycleOf___redArg(lean_object* v_inst_76_){
_start:
{
lean_object* v_toMonadCallStackOf_77_; lean_object* v_throwCycle_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
v_toMonadCallStackOf_77_ = lean_ctor_get(v_inst_76_, 0);
v_throwCycle_78_ = lean_ctor_get(v_inst_76_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_inst_76_);
if (v_isSharedCheck_87_ == 0)
{
v___x_80_ = v_inst_76_;
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_throwCycle_78_);
lean_inc(v_toMonadCallStackOf_77_);
lean_dec(v_inst_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___f_82_ = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfMonadCycleOf___redArg___lam__0), 3, 1);
lean_closure_set(v___f_82_, 0, v_throwCycle_78_);
v___x_83_ = l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(v_toMonadCallStackOf_77_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___f_82_);
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___f_82_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfMonadCycleOf(lean_object* v_00_u03ba_88_, lean_object* v_m_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lake_instMonadCycleOfMonadCycleOf___redArg(v_inst_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg___lam__0(lean_object* v_throwCycle_92_, lean_object* v_inst_93_, lean_object* v_00_u03b1_94_, lean_object* v_cycle_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_apply_2(v_throwCycle_92_, lean_box(0), v_cycle_95_);
v___x_97_ = lean_apply_2(v_inst_93_, lean_box(0), v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg(lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_){
_start:
{
lean_object* v_toMonadCallStackOf_101_; lean_object* v_throwCycle_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_111_; 
v_toMonadCallStackOf_101_ = lean_ctor_get(v_inst_100_, 0);
v_throwCycle_102_ = lean_ctor_get(v_inst_100_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_inst_100_);
if (v_isSharedCheck_111_ == 0)
{
v___x_104_ = v_inst_100_;
v_isShared_105_ = v_isSharedCheck_111_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_throwCycle_102_);
lean_inc(v_toMonadCallStackOf_101_);
lean_dec(v_inst_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_111_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_inc(v_inst_98_);
v___f_106_ = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_106_, 0, v_throwCycle_102_);
lean_closure_set(v___f_106_, 1, v_inst_98_);
v___x_107_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(v_inst_98_, v_inst_99_, v_toMonadCallStackOf_101_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___f_106_);
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___f_106_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor(lean_object* v_m_112_, lean_object* v_n_113_, lean_object* v_00_u03ba_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg(v_inst_115_, v_inst_116_, v_inst_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfMonadCycle___redArg(lean_object* v_inst_119_){
_start:
{
lean_object* v_throwCycle_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_throwCycle_120_ = lean_ctor_get(v_inst_119_, 1);
lean_inc(v_throwCycle_120_);
lean_dec_ref(v_inst_119_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_2(v_throwCycle_120_, lean_box(0), v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfMonadCycle(lean_object* v_00_u03ba_123_, lean_object* v_m_124_, lean_object* v_00_u03b1_125_, lean_object* v_inst_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lake_inhabitedOfMonadCycle___redArg(v_inst_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0(lean_object* v_00_u03b1_128_, lean_object* v_s_129_, lean_object* v_x_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_apply_1(v_x_130_, v_s_129_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0___boxed(lean_object* v_00_u03b1_133_, lean_object* v_s_134_, lean_object* v_x_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0(v_00_u03b1_133_, v_s_134_, v_x_135_, v___y_136_);
lean_dec(v___y_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object* v_inst_139_){
_start:
{
lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___f_140_ = ((lean_object*)(l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0));
v___x_141_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_141_, 0, lean_box(0));
lean_closure_set(v___x_141_, 1, lean_box(0));
lean_closure_set(v___x_141_, 2, v_inst_139_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___f_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad(lean_object* v_m_143_, lean_object* v_00_u03ba_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v_inst_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0(lean_object* v_inst_147_, lean_object* v_00_u03b1_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_toApplicative_151_; lean_object* v_toPure_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_toApplicative_151_ = lean_ctor_get(v_inst_147_, 0);
lean_inc_ref(v_toApplicative_151_);
lean_dec_ref(v_inst_147_);
v_toPure_152_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_inc(v_toPure_152_);
lean_dec_ref(v_toApplicative_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___y_149_);
v___x_154_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0___boxed(lean_object* v_inst_155_, lean_object* v_00_u03b1_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0(v_inst_155_, v_00_u03b1_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad___redArg(lean_object* v_inst_160_){
_start:
{
lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_inc_ref_n(v_inst_160_, 7);
v___f_161_ = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_161_, 0, v_inst_160_);
v___f_162_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_162_, 0, v_inst_160_);
v___f_163_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_163_, 0, v_inst_160_);
v___f_164_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_164_, 0, v_inst_160_);
v___f_165_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_165_, 0, v_inst_160_);
v___x_166_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_166_, 0, lean_box(0));
lean_closure_set(v___x_166_, 1, lean_box(0));
lean_closure_set(v___x_166_, 2, v_inst_160_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___f_162_);
v___x_168_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_168_, 0, lean_box(0));
lean_closure_set(v___x_168_, 1, lean_box(0));
lean_closure_set(v___x_168_, 2, v_inst_160_);
v___x_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
lean_ctor_set(v___x_169_, 2, v___f_163_);
lean_ctor_set(v___x_169_, 3, v___f_164_);
lean_ctor_set(v___x_169_, 4, v___f_165_);
v___x_170_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, lean_box(0));
lean_closure_set(v___x_170_, 2, v_inst_160_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v___x_171_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___f_161_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfCycleTOfMonad(lean_object* v_m_174_, lean_object* v_00_u03ba_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lake_instMonadCycleOfCycleTOfMonad___redArg(v_inst_176_);
return v___x_177_;
}
}
LEAN_EXPORT uint8_t l_Lake_guardCycle___redArg___lam__0(lean_object* v_inst_178_, lean_object* v_key_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_apply_2(v_inst_178_, v_x_180_, v_key_179_);
v___x_182_ = lean_unbox(v___x_181_);
v___x_183_ = lean_bool_not(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_guardCycle___redArg___lam__0___boxed(lean_object* v_inst_184_, lean_object* v_key_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lake_guardCycle___redArg___lam__0(v_inst_184_, v_key_185_, v_x_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_guardCycle___redArg___lam__1(lean_object* v_inst_191_, lean_object* v_key_192_, lean_object* v_withCallStack_193_, lean_object* v_act_194_, lean_object* v___f_195_, lean_object* v_throwCycle_196_, lean_object* v_parents_197_){
_start:
{
uint8_t v___x_198_; 
lean_inc(v_parents_197_);
lean_inc(v_key_192_);
v___x_198_ = l_List_elem___redArg(v_inst_191_, v_key_192_, v_parents_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_throwCycle_196_);
lean_dec_ref(v___f_195_);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v_key_192_);
lean_ctor_set(v___x_199_, 1, v_parents_197_);
v___x_200_ = lean_apply_3(v_withCallStack_193_, lean_box(0), v___x_199_, v_act_194_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_fst_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_act_194_);
lean_dec(v_withCallStack_193_);
v___x_201_ = lean_box(0);
v___x_202_ = ((lean_object*)(l_Lake_guardCycle___redArg___lam__1___closed__0));
v___x_203_ = l_List_partition_loop___redArg(v___f_195_, v_parents_197_, v___x_202_);
v_fst_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v___x_203_, 1);
lean_dec(v_unused_215_);
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_214_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_fst_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_214_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
lean_inc(v_key_192_);
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 1);
lean_ctor_set(v___x_206_, 1, v_fst_204_);
lean_ctor_set(v___x_206_, 0, v_key_192_);
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_key_192_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_fst_204_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v_key_192_);
lean_ctor_set(v___x_210_, 1, v___x_201_);
v___x_211_ = l_List_appendTR___redArg(v___x_209_, v___x_210_);
v___x_212_ = lean_apply_2(v_throwCycle_196_, lean_box(0), v___x_211_);
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_guardCycle___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_key_219_, lean_object* v_act_220_){
_start:
{
lean_object* v_toMonadCallStack_221_; lean_object* v_toBind_222_; lean_object* v_throwCycle_223_; lean_object* v_getCallStack_224_; lean_object* v_withCallStack_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; 
v_toMonadCallStack_221_ = lean_ctor_get(v_inst_218_, 0);
lean_inc_ref(v_toMonadCallStack_221_);
v_toBind_222_ = lean_ctor_get(v_inst_217_, 1);
lean_inc(v_toBind_222_);
lean_dec_ref(v_inst_217_);
v_throwCycle_223_ = lean_ctor_get(v_inst_218_, 1);
lean_inc(v_throwCycle_223_);
lean_dec_ref(v_inst_218_);
v_getCallStack_224_ = lean_ctor_get(v_toMonadCallStack_221_, 0);
lean_inc(v_getCallStack_224_);
v_withCallStack_225_ = lean_ctor_get(v_toMonadCallStack_221_, 1);
lean_inc(v_withCallStack_225_);
lean_dec_ref(v_toMonadCallStack_221_);
lean_inc(v_key_219_);
lean_inc_ref(v_inst_216_);
v___f_226_ = lean_alloc_closure((void*)(l_Lake_guardCycle___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_226_, 0, v_inst_216_);
lean_closure_set(v___f_226_, 1, v_key_219_);
v___f_227_ = lean_alloc_closure((void*)(l_Lake_guardCycle___redArg___lam__1), 7, 6);
lean_closure_set(v___f_227_, 0, v_inst_216_);
lean_closure_set(v___f_227_, 1, v_key_219_);
lean_closure_set(v___f_227_, 2, v_withCallStack_225_);
lean_closure_set(v___f_227_, 3, v_act_220_);
lean_closure_set(v___f_227_, 4, v___f_226_);
lean_closure_set(v___f_227_, 5, v_throwCycle_223_);
v___x_228_ = lean_apply_4(v_toBind_222_, lean_box(0), lean_box(0), v_getCallStack_224_, v___f_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_guardCycle(lean_object* v_00_u03ba_229_, lean_object* v_m_230_, lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_key_235_, lean_object* v_act_236_){
_start:
{
lean_object* v_toMonadCallStack_237_; lean_object* v_toBind_238_; lean_object* v_throwCycle_239_; lean_object* v_getCallStack_240_; lean_object* v_withCallStack_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___x_244_; 
v_toMonadCallStack_237_ = lean_ctor_get(v_inst_234_, 0);
lean_inc_ref(v_toMonadCallStack_237_);
v_toBind_238_ = lean_ctor_get(v_inst_233_, 1);
lean_inc(v_toBind_238_);
lean_dec_ref(v_inst_233_);
v_throwCycle_239_ = lean_ctor_get(v_inst_234_, 1);
lean_inc(v_throwCycle_239_);
lean_dec_ref(v_inst_234_);
v_getCallStack_240_ = lean_ctor_get(v_toMonadCallStack_237_, 0);
lean_inc(v_getCallStack_240_);
v_withCallStack_241_ = lean_ctor_get(v_toMonadCallStack_237_, 1);
lean_inc(v_withCallStack_241_);
lean_dec_ref(v_toMonadCallStack_237_);
lean_inc(v_key_235_);
lean_inc_ref(v_inst_232_);
v___f_242_ = lean_alloc_closure((void*)(l_Lake_guardCycle___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_242_, 0, v_inst_232_);
lean_closure_set(v___f_242_, 1, v_key_235_);
v___f_243_ = lean_alloc_closure((void*)(l_Lake_guardCycle___redArg___lam__1), 7, 6);
lean_closure_set(v___f_243_, 0, v_inst_232_);
lean_closure_set(v___f_243_, 1, v_key_235_);
lean_closure_set(v___f_243_, 2, v_withCallStack_241_);
lean_closure_set(v___f_243_, 3, v_act_236_);
lean_closure_set(v___f_243_, 4, v___f_242_);
lean_closure_set(v___f_243_, 5, v_throwCycle_239_);
v___x_244_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v_getCallStack_240_, v___f_243_);
return v___x_244_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Cycle(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Cycle(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Cycle(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Cycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Cycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Cycle(builtin);
}
#ifdef __cplusplus
}
#endif
