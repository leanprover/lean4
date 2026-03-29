// Lean compiler output
// Module: Lean.Elab.Deriving.SizeOf
// Imports: public import Lean.Meta.SizeOf public import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkSizeOfInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SizeOf"};
static const lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_isInductiveCore(v_env_5_, v_declName_1_);
v___x_7_ = lean_box(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v_declName_13_, v___y_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___boxed(lean_object* v_declName_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1(v_declName_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(uint8_t v_____do__lift_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
if (v_____do__lift_23_ == 0)
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = 1;
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
else
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = 0;
v___x_31_ = lean_box(v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0___boxed(lean_object* v_____do__lift_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
uint8_t v_____do__lift_1887__boxed_37_; lean_object* v_res_38_; 
v_____do__lift_1887__boxed_37_ = lean_unbox(v_____do__lift_33_);
v_res_38_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v_____do__lift_1887__boxed_37_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(lean_object* v_as_39_, size_t v_i_40_, size_t v_stop_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = lean_usize_dec_eq(v_i_40_, v_stop_41_);
if (v___x_45_ == 0)
{
uint8_t v___x_46_; uint8_t v_a_48_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_46_ = 1;
v___x_54_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
lean_inc(v___x_54_);
v___x_55_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v___x_54_, v___y_43_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_65_ == 0)
{
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
uint8_t v___x_60_; 
v___x_60_ = lean_unbox(v_a_56_);
lean_dec(v_a_56_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = lean_box(v___x_46_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_61_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
else
{
lean_del_object(v___x_58_);
v_a_48_ = v___x_45_;
goto v___jp_47_;
}
}
}
else
{
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_66_; uint8_t v___x_67_; 
v_a_66_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_55_);
v___x_67_ = lean_unbox(v_a_66_);
lean_dec(v_a_66_);
v_a_48_ = v___x_67_;
goto v___jp_47_;
}
else
{
return v___x_55_;
}
}
v___jp_47_:
{
if (v_a_48_ == 0)
{
size_t v___x_49_; size_t v___x_50_; 
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_40_, v___x_49_);
v_i_40_ = v___x_50_;
goto _start;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_box(v___x_46_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
}
else
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = 0;
v___x_69_ = lean_box(v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2___boxed(lean_object* v_as_71_, lean_object* v_i_72_, lean_object* v_stop_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
size_t v_i_boxed_77_; size_t v_stop_boxed_78_; lean_object* v_res_79_; 
v_i_boxed_77_ = lean_unbox_usize(v_i_72_);
lean_dec(v_i_72_);
v_stop_boxed_78_ = lean_unbox_usize(v_stop_73_);
lean_dec(v_stop_73_);
v_res_79_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_as_71_, v_i_boxed_77_, v_stop_boxed_78_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec_ref(v_as_71_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(lean_object* v_a_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_mkSizeOfInstances(v_a_80_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed(lean_object* v_a_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(v_a_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(lean_object* v_as_98_, size_t v_sz_99_, size_t v_i_100_, lean_object* v_b_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = lean_usize_dec_lt(v_i_100_, v_sz_99_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v_b_101_);
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_a_107_ = lean_array_uget_borrowed(v_as_98_, v_i_100_);
lean_inc_n(v_a_107_, 2);
v___f_108_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(v___f_108_, 0, v_a_107_);
v___x_109_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_109_, 0, lean_box(0));
lean_closure_set(v___x_109_, 1, v___f_108_);
v___x_110_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_107_, v___x_109_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; size_t v___x_112_; size_t v___x_113_; 
lean_dec_ref(v___x_110_);
v___x_111_ = lean_box(0);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_i_100_, v___x_112_);
v_i_100_ = v___x_113_;
v_b_101_ = v___x_111_;
goto _start;
}
else
{
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___boxed(lean_object* v_as_115_, lean_object* v_sz_116_, lean_object* v_i_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
size_t v_sz_boxed_122_; size_t v_i_boxed_123_; lean_object* v_res_124_; 
v_sz_boxed_122_ = lean_unbox_usize(v_sz_116_);
lean_dec(v_sz_116_);
v_i_boxed_123_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_as_115_, v_sz_boxed_122_, v_i_boxed_123_, v_b_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec_ref(v_as_115_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object* v_declNames_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___y_153_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_array_get_size(v_declNames_125_);
v___x_158_ = lean_nat_dec_lt(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_158_, v_a_126_, v_a_127_);
v___y_153_ = v___x_159_;
goto v___jp_152_;
}
else
{
if (v___x_158_ == 0)
{
goto v___jp_129_;
}
else
{
size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((size_t)0ULL);
v___x_161_ = lean_usize_of_nat(v___x_157_);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_declNames_125_, v___x_160_, v___x_161_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; uint8_t v___x_164_; lean_object* v___x_165_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref(v___x_162_);
v___x_164_ = lean_unbox(v_a_163_);
lean_dec(v_a_163_);
v___x_165_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_164_, v_a_126_, v_a_127_);
v___y_153_ = v___x_165_;
goto v___jp_152_;
}
else
{
v___y_153_ = v___x_162_;
goto v___jp_152_;
}
}
}
v___jp_129_:
{
lean_object* v___x_130_; size_t v_sz_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_box(0);
v_sz_131_ = lean_array_size(v_declNames_125_);
v___x_132_ = ((size_t)0ULL);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_declNames_125_, v_sz_131_, v___x_132_, v___x_130_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_142_; 
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v___x_133_, 0);
lean_dec(v_unused_143_);
v___x_135_ = v___x_133_;
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
else
{
lean_dec(v___x_133_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_137_ = 1;
v___x_138_ = lean_box(v___x_137_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_133_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_133_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
v___jp_152_:
{
if (lean_obj_tag(v___y_153_) == 0)
{
lean_object* v_a_154_; uint8_t v___x_155_; 
v_a_154_ = lean_ctor_get(v___y_153_, 0);
v___x_155_ = lean_unbox(v_a_154_);
if (v___x_155_ == 0)
{
return v___y_153_;
}
else
{
lean_dec_ref(v___y_153_);
goto v___jp_129_;
}
}
else
{
return v___y_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object* v_declNames_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(v_declNames_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec_ref(v_declNames_166_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_178_ = l_Lean_Elab_registerDerivingHandler(v___x_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2____boxed(lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
return v_res_180_;
}
}
lean_object* runtime_initialize_Lean_Meta_SizeOf(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_SizeOf(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_SizeOf(builtin);
}
#ifdef __cplusplus
}
#endif
