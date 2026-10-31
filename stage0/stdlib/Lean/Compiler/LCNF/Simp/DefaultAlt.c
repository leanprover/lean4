// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.DefaultAlt
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM import Lean.Compiler.LCNF.Simp.Used
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Alt_getParams(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v___y_4_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v_fvarId_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_fvarId_8_ = lean_ctor_get(v___x_7_, 0);
v___x_9_ = 1;
v___x_10_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_8_, v___y_4_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_23_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_23_ == 0)
{
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_23_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_23_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
uint8_t v___x_15_; 
v___x_15_ = lean_unbox(v_a_11_);
lean_dec(v_a_11_);
if (v___x_15_ == 0)
{
size_t v___x_16_; size_t v___x_17_; 
lean_del_object(v___x_13_);
v___x_16_ = ((size_t)1ULL);
v___x_17_ = lean_usize_add(v_i_2_, v___x_16_);
v_i_2_ = v___x_17_;
goto _start;
}
else
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_box(v___x_9_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_19_);
v___x_21_ = v___x_13_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
else
{
return v___x_10_;
}
}
else
{
uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = 0;
v___x_25_ = lean_box(v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg___boxed(lean_object* v_as_27_, lean_object* v_i_28_, lean_object* v_stop_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
size_t v_i_boxed_32_; size_t v_stop_boxed_33_; lean_object* v_res_34_; 
v_i_boxed_32_ = lean_unbox_usize(v_i_28_);
lean_dec(v_i_28_);
v_stop_boxed_33_ = lean_unbox_usize(v_stop_29_);
lean_dec(v_stop_29_);
v_res_34_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_27_, v_i_boxed_32_, v_stop_boxed_33_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v_as_27_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(lean_object* v_alt_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_48_ = l_Lean_Compiler_LCNF_Alt_getParams(v_alt_35_);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_array_get_size(v___x_48_);
v___x_51_ = lean_nat_dec_lt(v___x_49_, v___x_50_);
if (v___x_51_ == 0)
{
lean_dec_ref(v___x_48_);
goto v___jp_44_;
}
else
{
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec_ref(v___x_48_);
v___x_52_ = lean_box(v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
else
{
size_t v___x_54_; size_t v___x_55_; lean_object* v___x_56_; 
v___x_54_ = ((size_t)0ULL);
v___x_55_ = lean_usize_of_nat(v___x_50_);
v___x_56_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v___x_48_, v___x_54_, v___x_55_, v_a_37_);
lean_dec_ref(v___x_48_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_67_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_67_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_67_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_67_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
uint8_t v___x_61_; 
v___x_61_ = lean_unbox(v_a_57_);
lean_dec(v_a_57_);
if (v___x_61_ == 0)
{
lean_del_object(v___x_59_);
goto v___jp_44_;
}
else
{
uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_62_ = 0;
v___x_63_ = lean_box(v___x_62_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_63_);
v___x_65_ = v___x_59_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
return v___x_56_;
}
}
}
v___jp_44_:
{
uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = 1;
v___x_46_ = lean_box(v___x_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams___boxed(lean_object* v_alt_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_alt_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec_ref(v_alt_68_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(lean_object* v_as_78_, size_t v_i_79_, size_t v_stop_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_78_, v_i_79_, v_stop_80_, v___y_82_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
size_t v_i_boxed_101_; size_t v_stop_boxed_102_; lean_object* v_res_103_; 
v_i_boxed_101_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_102_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(v_as_90_, v_i_boxed_101_, v_stop_boxed_102_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_as_90_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(lean_object* v_as_104_, size_t v_sz_105_, size_t v_i_106_, lean_object* v_b_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_usize_dec_lt(v_i_106_, v_sz_105_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_b_107_);
return v___x_117_;
}
else
{
lean_object* v_snd_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_155_; 
v_snd_118_ = lean_ctor_get(v_b_107_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_b_107_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v_b_107_, 0);
lean_dec(v_unused_156_);
v___x_120_ = v_b_107_;
v_isShared_121_ = v_isSharedCheck_155_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_118_);
lean_dec(v_b_107_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_155_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_124_; 
v___x_122_ = lean_box(0);
v_a_123_ = lean_array_uget_borrowed(v_as_104_, v_i_106_);
v___x_124_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_a_123_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_146_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_146_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_146_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_146_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___x_129_; 
v___x_129_ = lean_unbox(v_a_125_);
lean_dec(v_a_125_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_del_object(v___x_127_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_add(v_snd_118_, v___x_130_);
lean_dec(v_snd_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_131_);
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_133_ = v___x_120_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
size_t v___x_134_; size_t v___x_135_; 
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_add(v_i_106_, v___x_134_);
v_i_106_ = v___x_135_;
v_b_107_ = v___x_133_;
goto _start;
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
lean_inc(v_snd_118_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v_snd_118_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_139_);
v___x_141_ = v___x_120_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_snd_118_);
v___x_141_ = v_reuseFailAlloc_145_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_141_);
v___x_143_ = v___x_127_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
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
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_del_object(v___x_120_);
lean_dec(v_snd_118_);
v_a_147_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_124_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_124_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1___boxed(lean_object* v_as_157_, lean_object* v_sz_158_, lean_object* v_i_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
size_t v_sz_boxed_169_; size_t v_i_boxed_170_; lean_object* v_res_171_; 
v_sz_boxed_169_ = lean_unbox_usize(v_sz_158_);
lean_dec(v_sz_158_);
v_i_boxed_170_ = lean_unbox_usize(v_i_159_);
lean_dec(v_i_159_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_as_157_, v_sz_boxed_169_, v_i_boxed_170_, v_b_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec_ref(v_as_157_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(lean_object* v_as_172_, lean_object* v_j_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_array_get_size(v_as_172_);
v___x_175_ = lean_nat_dec_lt(v_j_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v_j_173_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_array_fget(v_as_172_, v_j_173_);
if (lean_obj_tag(v___x_177_) == 2)
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_177_, 0);
lean_dec(v_unused_185_);
v___x_179_ = v___x_177_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_dec(v___x_177_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 1);
lean_ctor_set(v___x_179_, 0, v_j_173_);
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_j_173_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v___x_177_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_j_173_, v___x_186_);
lean_dec(v_j_173_);
v_j_173_ = v___x_187_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0___boxed(lean_object* v_as_189_, lean_object* v_j_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(v_as_189_, v_j_190_);
lean_dec_ref(v_as_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(lean_object* v_alts_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(v_alts_195_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 1)
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; size_t v_sz_209_; size_t v___x_210_; lean_object* v___x_211_; 
lean_dec(v___x_205_);
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___closed__0));
v_sz_209_ = lean_array_size(v_alts_195_);
v___x_210_ = ((size_t)0ULL);
v___x_211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_alts_195_, v_sz_209_, v___x_210_, v___x_208_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_224_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_224_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_224_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_224_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_fst_216_; 
v_fst_216_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_fst_216_);
lean_dec(v_a_212_);
if (lean_obj_tag(v_fst_216_) == 0)
{
lean_object* v___x_218_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_207_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_207_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
else
{
lean_object* v_val_220_; lean_object* v___x_222_; 
v_val_220_ = lean_ctor_get(v_fst_216_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v_fst_216_, 1);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v_val_220_);
v___x_222_ = v___x_214_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_val_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_a_225_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_211_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_211_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___boxed(lean_object* v_alts_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec_ref(v_alts_233_);
return v_res_242_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(lean_object* v_upperBound_244_, lean_object* v_val_245_, lean_object* v_alts_246_, lean_object* v_a_247_, lean_object* v_b_248_){
_start:
{
lean_object* v_a_251_; uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_lt(v_a_247_, v_upperBound_244_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_a_247_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_b_248_);
return v___x_256_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = lean_nat_dec_eq(v_a_247_, v_val_245_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0);
v___x_259_ = lean_array_get_borrowed(v___x_258_, v_alts_246_, v_a_247_);
lean_inc(v___x_259_);
v___x_260_ = lean_array_push(v_b_248_, v___x_259_);
v_a_251_ = v___x_260_;
goto v___jp_250_;
}
else
{
v_a_251_ = v_b_248_;
goto v___jp_250_;
}
}
v___jp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_add(v_a_247_, v___x_252_);
lean_dec(v_a_247_);
v_a_247_ = v___x_253_;
v_b_248_ = v_a_251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___boxed(lean_object* v_upperBound_261_, lean_object* v_val_262_, lean_object* v_alts_263_, lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_261_, v_val_262_, v_alts_263_, v_a_264_, v_b_265_);
lean_dec_ref(v_alts_263_);
lean_dec(v_val_262_);
lean_dec(v_upperBound_261_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(lean_object* v_alts_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_319_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_319_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_319_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_319_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
if (lean_obj_tag(v_a_278_) == 1)
{
lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_314_; 
lean_del_object(v___x_280_);
v_val_282_ = lean_ctor_get(v_a_278_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_314_ == 0)
{
v___x_284_ = v_a_278_;
v_isShared_285_ = v_isSharedCheck_314_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_dec(v_a_278_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_314_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_286_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0);
v___x_287_ = lean_array_get_size(v_alts_268_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_sub(v___x_287_, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_array_get_borrowed(v___x_286_, v_alts_268_, v_val_282_);
v___x_292_ = lean_mk_empty_array_with_capacity(v___x_289_);
lean_dec(v___x_289_);
v___x_293_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v___x_287_, v_val_282_, v_alts_268_, v___x_290_, v___x_292_);
lean_dec(v_val_282_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_305_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_305_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_inc(v___x_291_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_291_);
lean_ctor_set(v___x_298_, 1, v_a_294_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_298_);
v___x_300_ = v___x_284_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_300_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_del_object(v___x_284_);
v_a_306_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_293_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_293_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v_a_278_);
v___x_315_ = lean_box(0);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_315_);
v___x_317_ = v___x_280_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_277_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_277_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt___boxed(lean_object* v_alts_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec_ref(v_alts_328_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(lean_object* v_upperBound_338_, lean_object* v_val_339_, lean_object* v_alts_340_, lean_object* v_inst_341_, lean_object* v_R_342_, lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_c_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_338_, v_val_339_, v_alts_340_, v_a_343_, v_b_344_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___boxed(lean_object* v_upperBound_355_, lean_object* v_val_356_, lean_object* v_alts_357_, lean_object* v_inst_358_, lean_object* v_R_359_, lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_c_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(v_upperBound_355_, v_val_356_, v_alts_357_, v_inst_358_, v_R_359_, v_a_360_, v_b_361_, v_c_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_alts_357_);
lean_dec(v_val_356_);
lean_dec(v_upperBound_355_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(lean_object* v_as_372_, size_t v_i_373_, size_t v_stop_374_, lean_object* v_b_375_, lean_object* v___y_376_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_eq(v_i_373_, v_stop_374_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_379_ = 0;
v___x_380_ = lean_array_uget_borrowed(v_as_372_, v_i_373_);
v___x_381_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_380_);
v___x_382_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_379_, v___x_381_, v___y_376_);
lean_dec_ref(v___x_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___y_384_; 
lean_dec_ref_known(v___x_382_, 1);
switch(lean_obj_tag(v___x_380_))
{
case 0:
{
lean_object* v_code_390_; 
v_code_390_ = lean_ctor_get(v___x_380_, 2);
v___y_384_ = v_code_390_;
goto v___jp_383_;
}
case 1:
{
lean_object* v_code_391_; 
v_code_391_ = lean_ctor_get(v___x_380_, 1);
v___y_384_ = v_code_391_;
goto v___jp_383_;
}
default: 
{
lean_object* v_code_392_; 
v_code_392_ = lean_ctor_get(v___x_380_, 0);
v___y_384_ = v_code_392_;
goto v___jp_383_;
}
}
v___jp_383_:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_379_, v___y_384_, v___y_376_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; size_t v___x_387_; size_t v___x_388_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_add(v_i_373_, v___x_387_);
v_i_373_ = v___x_388_;
v_b_375_ = v_a_386_;
goto _start;
}
else
{
return v___x_385_;
}
}
}
else
{
return v___x_382_;
}
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v_b_375_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg___boxed(lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_stop_396_, lean_object* v_b_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
size_t v_i_boxed_400_; size_t v_stop_boxed_401_; lean_object* v_res_402_; 
v_i_boxed_400_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_stop_boxed_401_ = lean_unbox_usize(v_stop_396_);
lean_dec(v_stop_396_);
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_394_, v_i_boxed_400_, v_stop_boxed_401_, v_b_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v_as_394_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(lean_object* v_fst_403_, lean_object* v_as_404_, size_t v_sz_405_, size_t v_i_406_, lean_object* v_b_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_a_417_; uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_406_, v_sz_405_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec_ref(v_fst_403_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_b_407_);
return v___x_422_;
}
else
{
lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_460_; 
v_fst_423_ = lean_ctor_get(v_b_407_, 0);
v_snd_424_ = lean_ctor_get(v_b_407_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_b_407_);
if (v_isSharedCheck_460_ == 0)
{
v___x_426_ = v_b_407_;
v_isShared_427_ = v_isSharedCheck_460_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_inc(v_fst_423_);
lean_dec(v_b_407_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_460_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_a_428_; lean_object* v___x_434_; 
v_a_428_ = lean_array_uget_borrowed(v_as_404_, v_i_406_);
v___x_434_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_a_428_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; uint8_t v___x_436_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_436_ == 0)
{
goto v___jp_429_;
}
else
{
uint8_t v___x_437_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_445_; 
v___x_437_ = 0;
switch(lean_obj_tag(v_a_428_))
{
case 0:
{
lean_object* v_code_449_; 
v_code_449_ = lean_ctor_get(v_a_428_, 2);
lean_inc_ref(v_code_449_);
v___y_445_ = v_code_449_;
goto v___jp_444_;
}
case 1:
{
lean_object* v_code_450_; 
v_code_450_ = lean_ctor_get(v_a_428_, 1);
lean_inc_ref(v_code_450_);
v___y_445_ = v_code_450_;
goto v___jp_444_;
}
default: 
{
lean_object* v_code_451_; 
v_code_451_ = lean_ctor_get(v_a_428_, 0);
lean_inc_ref(v_code_451_);
v___y_445_ = v_code_451_;
goto v___jp_444_;
}
}
v___jp_438_:
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_437_, v___y_439_, v___y_440_);
if (v___x_441_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_del_object(v___x_426_);
lean_inc(v_a_428_);
v___x_442_ = lean_array_push(v_snd_424_, v_a_428_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_fst_423_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v_a_417_ = v___x_443_;
goto v___jp_416_;
}
}
v___jp_444_:
{
switch(lean_obj_tag(v_fst_403_))
{
case 0:
{
lean_object* v_code_446_; 
v_code_446_ = lean_ctor_get(v_fst_403_, 2);
lean_inc_ref(v_code_446_);
v___y_439_ = v___y_445_;
v___y_440_ = v_code_446_;
goto v___jp_438_;
}
case 1:
{
lean_object* v_code_447_; 
v_code_447_ = lean_ctor_get(v_fst_403_, 1);
lean_inc_ref(v_code_447_);
v___y_439_ = v___y_445_;
v___y_440_ = v_code_447_;
goto v___jp_438_;
}
default: 
{
lean_object* v_code_448_; 
v_code_448_ = lean_ctor_get(v_fst_403_, 0);
lean_inc_ref(v_code_448_);
v___y_439_ = v___y_445_;
v___y_440_ = v_code_448_;
goto v___jp_438_;
}
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_del_object(v___x_426_);
lean_dec(v_snd_424_);
lean_dec(v_fst_423_);
lean_dec_ref(v_fst_403_);
v_a_452_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_434_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_434_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
v___jp_429_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_inc(v_a_428_);
v___x_430_ = lean_array_push(v_fst_423_, v_a_428_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_430_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_snd_424_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v_a_417_ = v___x_432_;
goto v___jp_416_;
}
}
}
}
v___jp_416_:
{
size_t v___x_418_; size_t v___x_419_; 
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_add(v_i_406_, v___x_418_);
v_i_406_ = v___x_419_;
v_b_407_ = v_a_417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(lean_object* v_fst_461_, lean_object* v_as_462_, lean_object* v_sz_463_, lean_object* v_i_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
size_t v_sz_boxed_474_; size_t v_i_boxed_475_; lean_object* v_res_476_; 
v_sz_boxed_474_ = lean_unbox_usize(v_sz_463_);
lean_dec(v_sz_463_);
v_i_boxed_475_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_461_, v_as_462_, v_sz_boxed_474_, v_i_boxed_475_, v_b_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec_ref(v_as_462_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object* v_alts_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = lean_array_get_size(v_alts_481_);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_dec_le(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_578_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_578_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_578_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_578_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
if (lean_obj_tag(v_a_494_) == 1)
{
lean_object* v_val_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_574_; 
v_val_498_ = lean_ctor_get(v_a_494_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_574_ == 0)
{
v___x_500_ = v_a_494_;
v_isShared_501_ = v_isSharedCheck_574_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_val_498_);
lean_dec(v_a_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_574_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v___x_504_; lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_fst_502_ = lean_ctor_get(v_val_498_, 0);
lean_inc_n(v_fst_502_, 2);
v_snd_503_ = lean_ctor_get(v_val_498_, 1);
lean_inc(v_snd_503_);
lean_dec(v_val_498_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1));
v_sz_506_ = lean_array_size(v_snd_503_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_502_, v_snd_503_, v_sz_506_, v___x_507_, v___x_505_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v_snd_503_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_565_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_565_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_565_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_565_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___y_516_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_fst_513_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_a_509_, 1);
lean_inc(v_snd_514_);
lean_dec(v_a_509_);
v___x_528_ = lean_array_get_size(v_snd_514_);
v___x_529_ = lean_nat_dec_eq(v___x_528_, v___x_504_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_del_object(v___x_496_);
lean_dec_ref(v_alts_481_);
v___x_530_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_483_);
if (lean_obj_tag(v___x_530_) == 0)
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref_known(v___x_530_, 1);
v___x_531_ = 0;
v___x_532_ = l_Lean_Compiler_LCNF_Alt_getParams(v_fst_502_);
v___x_533_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_531_, v___x_532_, v_a_486_);
lean_dec_ref(v___x_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
uint8_t v___x_534_; 
lean_dec_ref_known(v___x_533_, 1);
v___x_534_ = lean_nat_dec_lt(v___x_504_, v___x_528_);
if (v___x_534_ == 0)
{
lean_dec(v_snd_514_);
goto v___jp_524_;
}
else
{
lean_object* v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_usize_of_nat(v___x_528_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_snd_514_, v___x_507_, v___x_536_, v___x_535_, v_a_486_);
lean_dec(v_snd_514_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_dec_ref_known(v___x_537_, 1);
goto v___jp_524_;
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_fst_513_);
lean_del_object(v___x_511_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_snd_514_);
lean_dec(v_fst_513_);
lean_del_object(v___x_511_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
v_a_546_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_533_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_533_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_snd_514_);
lean_dec(v_fst_513_);
lean_del_object(v___x_511_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
v_a_554_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_530_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_530_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v_snd_514_);
lean_dec(v_fst_513_);
lean_del_object(v___x_511_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_alts_481_);
v___x_563_ = v___x_496_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_alts_481_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
v___jp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 2);
lean_ctor_set(v___x_500_, 0, v___y_516_);
v___x_518_ = v___x_500_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___y_516_);
v___x_518_ = v_reuseFailAlloc_523_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_array_push(v_fst_513_, v___x_518_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_519_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
v___jp_524_:
{
switch(lean_obj_tag(v_fst_502_))
{
case 0:
{
lean_object* v_code_525_; 
v_code_525_ = lean_ctor_get(v_fst_502_, 2);
lean_inc_ref(v_code_525_);
lean_dec_ref_known(v_fst_502_, 3);
v___y_516_ = v_code_525_;
goto v___jp_515_;
}
case 1:
{
lean_object* v_code_526_; 
v_code_526_ = lean_ctor_get(v_fst_502_, 1);
lean_inc_ref(v_code_526_);
lean_dec_ref_known(v_fst_502_, 2);
v___y_516_ = v_code_526_;
goto v___jp_515_;
}
default: 
{
lean_object* v_code_527_; 
v_code_527_ = lean_ctor_get(v_fst_502_, 0);
lean_inc_ref(v_code_527_);
lean_dec_ref_known(v_fst_502_, 1);
v___y_516_ = v_code_527_;
goto v___jp_515_;
}
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
lean_del_object(v___x_496_);
lean_dec_ref(v_alts_481_);
v_a_566_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_508_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_508_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
lean_object* v___x_576_; 
lean_dec(v_a_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_alts_481_);
v___x_576_ = v___x_496_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_alts_481_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_alts_481_);
v_a_579_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_493_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_493_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_alts_481_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(lean_object* v_alts_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_alts_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(lean_object* v_as_598_, size_t v_i_599_, size_t v_stop_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_598_, v_i_599_, v_stop_600_, v_b_601_, v___y_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_stop_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
size_t v_i_boxed_623_; size_t v_stop_boxed_624_; lean_object* v_res_625_; 
v_i_boxed_623_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_stop_boxed_624_ = lean_unbox_usize(v_stop_613_);
lean_dec(v_stop_613_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_as_611_, v_i_boxed_623_, v_stop_boxed_624_, v_b_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v_as_611_);
return v_res_625_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
}
#ifdef __cplusplus
}
#endif
