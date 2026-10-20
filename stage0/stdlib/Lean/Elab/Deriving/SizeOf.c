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
uint8_t v_____do__lift_1794__boxed_37_; lean_object* v_res_38_; 
v_____do__lift_1794__boxed_37_ = lean_unbox(v_____do__lift_33_);
v_res_38_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v_____do__lift_1794__boxed_37_, v___y_34_, v___y_35_);
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
uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = 1;
v___x_47_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
lean_inc(v___x_47_);
v___x_48_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v___x_47_, v___y_43_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_61_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_61_ == 0)
{
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_61_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_61_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; 
v___x_53_ = lean_unbox(v_a_49_);
lean_dec(v_a_49_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_54_ = lean_box(v___x_46_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_54_);
v___x_56_ = v___x_51_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
else
{
size_t v___x_58_; size_t v___x_59_; 
lean_del_object(v___x_51_);
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_40_, v___x_58_);
v_i_40_ = v___x_59_;
goto _start;
}
}
}
else
{
return v___x_48_;
}
}
else
{
uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = 0;
v___x_63_ = lean_box(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
size_t v_i_boxed_71_; size_t v_stop_boxed_72_; lean_object* v_res_73_; 
v_i_boxed_71_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_72_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_73_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_as_65_, v_i_boxed_71_, v_stop_boxed_72_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec_ref(v_as_65_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(lean_object* v_a_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_mkSizeOfInstances(v_a_74_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed(lean_object* v_a_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(v_a_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(lean_object* v_as_92_, size_t v_sz_93_, size_t v_i_94_, lean_object* v_b_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_usize_dec_lt(v_i_94_, v_sz_93_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v_b_95_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v_a_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_101_ = lean_box(0);
v_a_102_ = lean_array_uget_borrowed(v_as_92_, v_i_94_);
lean_inc_n(v_a_102_, 2);
v___f_103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(v___f_103_, 0, v_a_102_);
v___x_104_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, v___f_103_);
v___x_105_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_102_, v___x_104_, v___y_96_, v___y_97_);
if (lean_obj_tag(v___x_105_) == 0)
{
size_t v___x_106_; size_t v___x_107_; 
lean_dec_ref_known(v___x_105_, 1);
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_94_, v___x_106_);
v_i_94_ = v___x_107_;
v_b_95_ = v___x_101_;
goto _start;
}
else
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___boxed(lean_object* v_as_109_, lean_object* v_sz_110_, lean_object* v_i_111_, lean_object* v_b_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
size_t v_sz_boxed_116_; size_t v_i_boxed_117_; lean_object* v_res_118_; 
v_sz_boxed_116_ = lean_unbox_usize(v_sz_110_);
lean_dec(v_sz_110_);
v_i_boxed_117_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_as_109_, v_sz_boxed_116_, v_i_boxed_117_, v_b_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec_ref(v_as_109_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object* v_declNames_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___y_147_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_array_get_size(v_declNames_119_);
v___x_152_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_152_, v_a_120_, v_a_121_);
v___y_147_ = v___x_153_;
goto v___jp_146_;
}
else
{
if (v___x_152_ == 0)
{
goto v___jp_123_;
}
else
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((size_t)0ULL);
v___x_155_ = lean_usize_of_nat(v___x_151_);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_declNames_119_, v___x_154_, v___x_155_, v_a_120_, v_a_121_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; uint8_t v___x_158_; lean_object* v___x_159_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = lean_unbox(v_a_157_);
lean_dec(v_a_157_);
v___x_159_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_158_, v_a_120_, v_a_121_);
v___y_147_ = v___x_159_;
goto v___jp_146_;
}
else
{
return v___x_156_;
}
}
}
v___jp_123_:
{
uint8_t v___x_124_; lean_object* v___x_125_; size_t v_sz_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_124_ = 1;
v___x_125_ = lean_box(0);
v_sz_126_ = lean_array_size(v_declNames_119_);
v___x_127_ = ((size_t)0ULL);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_declNames_119_, v_sz_126_, v___x_127_, v___x_125_, v_a_120_, v_a_121_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_137_);
v___x_130_ = v___x_128_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_dec(v___x_128_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_box(v___x_124_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_128_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_128_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
v___jp_146_:
{
lean_object* v_a_148_; uint8_t v___x_149_; 
v_a_148_ = lean_ctor_get(v___y_147_, 0);
v___x_149_ = lean_unbox(v_a_148_);
if (v___x_149_ == 0)
{
return v___y_147_;
}
else
{
lean_dec_ref(v___y_147_);
goto v___jp_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object* v_declNames_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(v_declNames_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec_ref(v_declNames_160_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_171_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_172_ = l_Lean_Elab_registerDerivingHandler(v___x_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2____boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
return v_res_174_;
}
}
lean_object* runtime_initialize_Lean_Meta_SizeOf(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
