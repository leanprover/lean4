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
uint8_t v_____do__lift_1785__boxed_37_; lean_object* v_res_38_; 
v_____do__lift_1785__boxed_37_ = lean_unbox(v_____do__lift_33_);
v_res_38_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v_____do__lift_1785__boxed_37_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(lean_object* v_as_39_, size_t v_i_40_, size_t v_stop_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_usize_dec_eq(v_i_40_, v_stop_41_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = 1;
v___x_51_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
lean_inc(v___x_51_);
v___x_52_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v___x_51_, v___y_43_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_62_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_62_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = lean_unbox(v_a_53_);
lean_dec(v_a_53_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_box(v___x_50_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
else
{
lean_del_object(v___x_55_);
goto v___jp_45_;
}
}
}
else
{
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_72_; 
v_a_63_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_72_ == 0)
{
v___x_65_ = v___x_52_;
v_isShared_66_ = v_isSharedCheck_72_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_52_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_72_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint8_t v___x_67_; 
v___x_67_ = lean_unbox(v_a_63_);
lean_dec(v_a_63_);
if (v___x_67_ == 0)
{
lean_del_object(v___x_65_);
goto v___jp_45_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_box(v___x_50_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 0);
lean_ctor_set(v___x_65_, 0, v___x_68_);
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
else
{
return v___x_52_;
}
}
}
else
{
uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = 0;
v___x_74_ = lean_box(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
v___jp_45_:
{
size_t v___x_46_; size_t v___x_47_; 
v___x_46_ = ((size_t)1ULL);
v___x_47_ = lean_usize_add(v_i_40_, v___x_46_);
v_i_40_ = v___x_47_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2___boxed(lean_object* v_as_76_, lean_object* v_i_77_, lean_object* v_stop_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
size_t v_i_boxed_82_; size_t v_stop_boxed_83_; lean_object* v_res_84_; 
v_i_boxed_82_ = lean_unbox_usize(v_i_77_);
lean_dec(v_i_77_);
v_stop_boxed_83_ = lean_unbox_usize(v_stop_78_);
lean_dec(v_stop_78_);
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_as_76_, v_i_boxed_82_, v_stop_boxed_83_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec_ref(v_as_76_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(lean_object* v_a_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_mkSizeOfInstances(v_a_85_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed(lean_object* v_a_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(v_a_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(lean_object* v_as_103_, size_t v_sz_104_, size_t v_i_105_, lean_object* v_b_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = lean_usize_dec_lt(v_i_105_, v_sz_104_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v_b_106_);
return v___x_111_;
}
else
{
lean_object* v_a_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_a_112_ = lean_array_uget_borrowed(v_as_103_, v_i_105_);
lean_inc_n(v_a_112_, 2);
v___f_113_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(v___f_113_, 0, v_a_112_);
v___x_114_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_114_, 0, lean_box(0));
lean_closure_set(v___x_114_, 1, v___f_113_);
v___x_115_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_112_, v___x_114_, v___y_107_, v___y_108_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = lean_box(0);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_add(v_i_105_, v___x_117_);
v_i_105_ = v___x_118_;
v_b_106_ = v___x_116_;
goto _start;
}
else
{
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___boxed(lean_object* v_as_120_, lean_object* v_sz_121_, lean_object* v_i_122_, lean_object* v_b_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
size_t v_sz_boxed_127_; size_t v_i_boxed_128_; lean_object* v_res_129_; 
v_sz_boxed_127_ = lean_unbox_usize(v_sz_121_);
lean_dec(v_sz_121_);
v_i_boxed_128_ = lean_unbox_usize(v_i_122_);
lean_dec(v_i_122_);
v_res_129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_as_120_, v_sz_boxed_127_, v_i_boxed_128_, v_b_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec_ref(v_as_120_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(lean_object* v_declNames_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___y_158_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_declNames_130_);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_163_, v_a_131_, v_a_132_);
v___y_158_ = v___x_164_;
goto v___jp_157_;
}
else
{
if (v___x_163_ == 0)
{
goto v___jp_134_;
}
else
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
v___x_165_ = ((size_t)0ULL);
v___x_166_ = lean_usize_of_nat(v___x_162_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_declNames_130_, v___x_165_, v___x_166_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; uint8_t v___x_169_; lean_object* v___x_170_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = lean_unbox(v_a_168_);
lean_dec(v_a_168_);
v___x_170_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(v___x_169_, v_a_131_, v_a_132_);
v___y_158_ = v___x_170_;
goto v___jp_157_;
}
else
{
v___y_158_ = v___x_167_;
goto v___jp_157_;
}
}
}
v___jp_134_:
{
lean_object* v___x_135_; size_t v_sz_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_box(0);
v_sz_136_ = lean_array_size(v_declNames_130_);
v___x_137_ = ((size_t)0ULL);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_declNames_130_, v_sz_136_, v___x_137_, v___x_135_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_147_; 
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_138_, 0);
lean_dec(v_unused_148_);
v___x_140_ = v___x_138_;
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
else
{
lean_dec(v___x_138_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = 1;
v___x_143_ = lean_box(v___x_142_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_138_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
v___jp_157_:
{
if (lean_obj_tag(v___y_158_) == 0)
{
lean_object* v_a_159_; uint8_t v___x_160_; 
v_a_159_ = lean_ctor_get(v___y_158_, 0);
v___x_160_ = lean_unbox(v_a_159_);
if (v___x_160_ == 0)
{
return v___y_158_;
}
else
{
lean_dec_ref_known(v___y_158_, 1);
goto v___jp_134_;
}
}
else
{
return v___y_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(lean_object* v_declNames_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(v_declNames_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec_ref(v_declNames_171_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_182_ = ((lean_object*)(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_));
v___x_183_ = l_Lean_Elab_registerDerivingHandler(v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2____boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
return v_res_185_;
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
