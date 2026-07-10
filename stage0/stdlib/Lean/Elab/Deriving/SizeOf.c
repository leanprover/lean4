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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_bool_not(v_____do__lift_23_);
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0___boxed(lean_object* v_____do__lift_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
uint8_t v_____do__lift_1811__boxed_34_; lean_object* v_res_35_; 
v_____do__lift_1811__boxed_34_ = lean_unbox(v_____do__lift_30_);
v_res_35_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v_____do__lift_1811__boxed_34_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(lean_object* v_as_36_, size_t v_i_37_, size_t v_stop_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = lean_usize_dec_eq(v_i_37_, v_stop_38_);
if (v___x_42_ == 0)
{
uint8_t v___x_43_; uint8_t v_a_45_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_43_ = 1;
v___x_51_ = lean_array_uget_borrowed(v_as_36_, v_i_37_);
lean_inc(v___x_51_);
v___x_52_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v___x_51_, v___y_40_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; uint8_t v___x_54_; uint8_t v___x_55_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_52_, 1);
v___x_54_ = lean_unbox(v_a_53_);
lean_dec(v_a_53_);
v___x_55_ = lean_bool_not(v___x_54_);
v_a_45_ = v___x_55_;
goto v___jp_44_;
}
else
{
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_56_; uint8_t v___x_57_; 
v_a_56_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_56_);
lean_dec_ref_known(v___x_52_, 1);
v___x_57_ = lean_unbox(v_a_56_);
lean_dec(v_a_56_);
v_a_45_ = v___x_57_;
goto v___jp_44_;
}
else
{
return v___x_52_;
}
}
v___jp_44_:
{
if (v_a_45_ == 0)
{
size_t v___x_46_; size_t v___x_47_; 
v___x_46_ = ((size_t)1ULL);
v___x_47_ = lean_usize_add(v_i_37_, v___x_46_);
v_i_37_ = v___x_47_;
goto _start;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_box(v___x_43_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
}
else
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = 0;
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2___boxed(lean_object* v_as_61_, lean_object* v_i_62_, lean_object* v_stop_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; lean_object* v_res_69_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_62_);
lean_dec(v_i_62_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_63_);
lean_dec(v_stop_63_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_as_61_, v_i_boxed_67_, v_stop_boxed_68_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec_ref(v_as_61_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(lean_object* v_a_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_mkSizeOfInstances(v_a_70_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed(lean_object* v_a_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(v_a_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(lean_object* v_as_88_, size_t v_sz_89_, size_t v_i_90_, lean_object* v_b_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_usize_dec_lt(v_i_90_, v_sz_89_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_b_91_);
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_97_ = lean_array_uget_borrowed(v_as_88_, v_i_90_);
lean_inc_n(v_a_97_, 2);
v___f_98_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(v___f_98_, 0, v_a_97_);
v___x_99_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_99_, 0, lean_box(0));
lean_closure_set(v___x_99_, 1, v___f_98_);
v___x_100_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_97_, v___x_99_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_101_; size_t v___x_102_; size_t v___x_103_; 
lean_dec_ref_known(v___x_100_, 1);
v___x_101_ = lean_box(0);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_add(v_i_90_, v___x_102_);
v_i_90_ = v___x_103_;
v_b_91_ = v___x_101_;
goto _start;
}
else
{
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___boxed(lean_object* v_as_105_, lean_object* v_sz_106_, lean_object* v_i_107_, lean_object* v_b_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_106_);
lean_dec(v_sz_106_);
v_i_boxed_113_ = lean_unbox_usize(v_i_107_);
lean_dec(v_i_107_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_as_105_, v_sz_boxed_112_, v_i_boxed_113_, v_b_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec_ref(v_as_105_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object* v_declNames_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
uint8_t v_a_120_; lean_object* v___y_145_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_array_get_size(v_declNames_115_);
v___x_150_ = lean_nat_dec_lt(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_150_, v_a_116_, v_a_117_);
v___y_145_ = v___x_151_;
goto v___jp_144_;
}
else
{
if (v___x_150_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = lean_bool_not(v___x_150_);
v_a_120_ = v___x_152_;
goto v___jp_119_;
}
else
{
size_t v___x_153_; size_t v___x_154_; lean_object* v___x_155_; 
v___x_153_ = ((size_t)0ULL);
v___x_154_ = lean_usize_of_nat(v___x_149_);
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_declNames_115_, v___x_153_, v___x_154_, v_a_116_, v_a_117_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; uint8_t v___x_157_; lean_object* v___x_158_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
v___x_157_ = lean_unbox(v_a_156_);
lean_dec(v_a_156_);
v___x_158_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_157_, v_a_116_, v_a_117_);
v___y_145_ = v___x_158_;
goto v___jp_144_;
}
else
{
v___y_145_ = v___x_155_;
goto v___jp_144_;
}
}
}
v___jp_119_:
{
if (v_a_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_box(v_a_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v___x_123_; size_t v_sz_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_box(0);
v_sz_124_ = lean_array_size(v_declNames_115_);
v___x_125_ = ((size_t)0ULL);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_declNames_115_, v_sz_124_, v___x_125_, v___x_123_, v_a_116_, v_a_117_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_134_; 
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v___x_126_, 0);
lean_dec(v_unused_135_);
v___x_128_ = v___x_126_;
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
else
{
lean_dec(v___x_126_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_134_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_box(v_a_120_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_126_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_126_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
v___jp_144_:
{
if (lean_obj_tag(v___y_145_) == 0)
{
lean_object* v_a_146_; uint8_t v___x_147_; 
v_a_146_ = lean_ctor_get(v___y_145_, 0);
lean_inc(v_a_146_);
lean_dec_ref_known(v___y_145_, 1);
v___x_147_ = lean_unbox(v_a_146_);
lean_dec(v_a_146_);
v_a_120_ = v___x_147_;
goto v___jp_119_;
}
else
{
return v___y_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object* v_declNames_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(v_declNames_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec_ref(v_declNames_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_171_ = l_Lean_Elab_registerDerivingHandler(v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2____boxed(lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
return v_res_173_;
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
