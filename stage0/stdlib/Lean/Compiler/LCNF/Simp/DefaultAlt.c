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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed___redArg(lean_object*, lean_object*);
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
uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v_fvarId_12_; uint8_t v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_fvarId_12_ = lean_ctor_get(v___x_11_, 0);
v___x_13_ = 1;
v___x_14_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_12_, v___y_4_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_24_ == 0)
{
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___x_19_; 
v___x_19_ = lean_unbox(v_a_15_);
lean_dec(v_a_15_);
if (v___x_19_ == 0)
{
lean_del_object(v___x_17_);
goto v___jp_6_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_20_ = lean_box(v___x_13_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_20_);
v___x_22_ = v___x_17_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_34_; 
v_a_25_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_34_ == 0)
{
v___x_27_ = v___x_14_;
v_isShared_28_ = v_isSharedCheck_34_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_14_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_34_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
uint8_t v___x_29_; 
v___x_29_ = lean_unbox(v_a_25_);
lean_dec(v_a_25_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_30_ = lean_box(v___x_13_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 0);
lean_ctor_set(v___x_27_, 0, v___x_30_);
v___x_32_ = v___x_27_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
else
{
lean_del_object(v___x_27_);
goto v___jp_6_;
}
}
}
else
{
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_44_; 
v_a_35_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_44_ == 0)
{
v___x_37_ = v___x_14_;
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_14_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
uint8_t v___x_39_; 
v___x_39_ = lean_unbox(v_a_35_);
lean_dec(v_a_35_);
if (v___x_39_ == 0)
{
lean_del_object(v___x_37_);
goto v___jp_6_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = lean_box(v___x_13_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 0);
lean_ctor_set(v___x_37_, 0, v___x_40_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
else
{
return v___x_14_;
}
}
}
}
else
{
uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = 0;
v___x_46_ = lean_box(v___x_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
v___jp_6_:
{
size_t v___x_7_; size_t v___x_8_; 
v___x_7_ = ((size_t)1ULL);
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg___boxed(lean_object* v_as_48_, lean_object* v_i_49_, lean_object* v_stop_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
size_t v_i_boxed_53_; size_t v_stop_boxed_54_; lean_object* v_res_55_; 
v_i_boxed_53_ = lean_unbox_usize(v_i_49_);
lean_dec(v_i_49_);
v_stop_boxed_54_ = lean_unbox_usize(v_stop_50_);
lean_dec(v_stop_50_);
v_res_55_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_48_, v_i_boxed_53_, v_stop_boxed_54_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v_as_48_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(lean_object* v_alt_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = l_Lean_Compiler_LCNF_Alt_getParams(v_alt_56_);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_array_get_size(v___x_69_);
v___x_72_ = lean_nat_dec_lt(v___x_70_, v___x_71_);
if (v___x_72_ == 0)
{
lean_dec_ref(v___x_69_);
goto v___jp_65_;
}
else
{
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v___x_69_);
v___x_73_ = lean_box(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
else
{
size_t v___x_75_; size_t v___x_76_; lean_object* v___x_77_; 
v___x_75_ = ((size_t)0ULL);
v___x_76_ = lean_usize_of_nat(v___x_71_);
v___x_77_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v___x_69_, v___x_75_, v___x_76_, v_a_58_);
lean_dec_ref(v___x_69_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_88_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_88_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; 
v___x_82_ = lean_unbox(v_a_78_);
lean_dec(v_a_78_);
if (v___x_82_ == 0)
{
lean_del_object(v___x_80_);
goto v___jp_65_;
}
else
{
uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = 0;
v___x_84_ = lean_box(v___x_83_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_84_);
v___x_86_ = v___x_80_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
else
{
return v___x_77_;
}
}
}
v___jp_65_:
{
uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = 1;
v___x_67_ = lean_box(v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams___boxed(lean_object* v_alt_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_alt_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec_ref(v_alt_89_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(lean_object* v_as_99_, size_t v_i_100_, size_t v_stop_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_99_, v_i_100_, v_stop_101_, v___y_103_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___boxed(lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
size_t v_i_boxed_122_; size_t v_stop_boxed_123_; lean_object* v_res_124_; 
v_i_boxed_122_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_123_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(v_as_111_, v_i_boxed_122_, v_stop_boxed_123_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec_ref(v_as_111_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(lean_object* v_as_125_, size_t v_sz_126_, size_t v_i_127_, lean_object* v_b_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = lean_usize_dec_lt(v_i_127_, v_sz_126_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_b_128_);
return v___x_138_;
}
else
{
lean_object* v_snd_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_176_; 
v_snd_139_ = lean_ctor_get(v_b_128_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_b_128_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v_b_128_, 0);
lean_dec(v_unused_177_);
v___x_141_ = v_b_128_;
v_isShared_142_ = v_isSharedCheck_176_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_snd_139_);
lean_dec(v_b_128_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_176_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v_a_144_; lean_object* v___x_145_; 
v___x_143_ = lean_box(0);
v_a_144_ = lean_array_uget_borrowed(v_as_125_, v_i_127_);
v___x_145_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_a_144_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_167_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_167_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_167_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_167_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_unbox(v_a_146_);
lean_dec(v_a_146_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
lean_del_object(v___x_148_);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_snd_139_, v___x_151_);
lean_dec(v_snd_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_152_);
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_154_ = v___x_141_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_158_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
size_t v___x_155_; size_t v___x_156_; 
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_add(v_i_127_, v___x_155_);
v_i_127_ = v___x_156_;
v_b_128_ = v___x_154_;
goto _start;
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc(v_snd_139_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v_snd_139_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_160_);
v___x_162_ = v___x_141_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_snd_139_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_162_);
v___x_164_ = v___x_148_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_del_object(v___x_141_);
lean_dec(v_snd_139_);
v_a_168_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_145_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_145_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1___boxed(lean_object* v_as_178_, lean_object* v_sz_179_, lean_object* v_i_180_, lean_object* v_b_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
size_t v_sz_boxed_190_; size_t v_i_boxed_191_; lean_object* v_res_192_; 
v_sz_boxed_190_ = lean_unbox_usize(v_sz_179_);
lean_dec(v_sz_179_);
v_i_boxed_191_ = lean_unbox_usize(v_i_180_);
lean_dec(v_i_180_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_as_178_, v_sz_boxed_190_, v_i_boxed_191_, v_b_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec_ref(v_as_178_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(lean_object* v_as_193_, lean_object* v_j_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_array_get_size(v_as_193_);
v___x_196_ = lean_nat_dec_lt(v_j_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_dec(v_j_194_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_fget(v_as_193_, v_j_194_);
if (lean_obj_tag(v___x_198_) == 2)
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v___x_198_, 0);
lean_dec(v_unused_206_);
v___x_200_ = v___x_198_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_dec(v___x_198_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 1);
lean_ctor_set(v___x_200_, 0, v_j_194_);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_j_194_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___x_198_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_j_194_, v___x_207_);
lean_dec(v_j_194_);
v_j_194_ = v___x_208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0___boxed(lean_object* v_as_210_, lean_object* v_j_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(v_as_210_, v_j_211_);
lean_dec_ref(v_as_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(lean_object* v_alts_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(v_alts_216_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 1)
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; size_t v_sz_230_; size_t v___x_231_; lean_object* v___x_232_; 
lean_dec(v___x_226_);
v___x_228_ = lean_box(0);
v___x_229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___closed__0));
v_sz_230_ = lean_array_size(v_alts_216_);
v___x_231_ = ((size_t)0ULL);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_alts_216_, v_sz_230_, v___x_231_, v___x_229_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_245_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_245_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_fst_237_; 
v_fst_237_ = lean_ctor_get(v_a_233_, 0);
lean_inc(v_fst_237_);
lean_dec(v_a_233_);
if (lean_obj_tag(v_fst_237_) == 0)
{
lean_object* v___x_239_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_228_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_228_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
else
{
lean_object* v_val_241_; lean_object* v___x_243_; 
v_val_241_ = lean_ctor_get(v_fst_237_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v_fst_237_, 1);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v_val_241_);
v___x_243_ = v___x_235_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_val_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_a_246_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_232_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_232_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___boxed(lean_object* v_alts_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec_ref(v_alts_254_);
return v_res_263_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(lean_object* v_upperBound_265_, lean_object* v_val_266_, lean_object* v_alts_267_, lean_object* v_a_268_, lean_object* v_b_269_){
_start:
{
lean_object* v_a_272_; uint8_t v___x_276_; 
v___x_276_ = lean_nat_dec_lt(v_a_268_, v_upperBound_265_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v_a_268_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_b_269_);
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = lean_nat_dec_eq(v_a_268_, v_val_266_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0);
v___x_280_ = lean_array_get_borrowed(v___x_279_, v_alts_267_, v_a_268_);
lean_inc(v___x_280_);
v___x_281_ = lean_array_push(v_b_269_, v___x_280_);
v_a_272_ = v___x_281_;
goto v___jp_271_;
}
else
{
v_a_272_ = v_b_269_;
goto v___jp_271_;
}
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_a_268_, v___x_273_);
lean_dec(v_a_268_);
v_a_268_ = v___x_274_;
v_b_269_ = v_a_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___boxed(lean_object* v_upperBound_282_, lean_object* v_val_283_, lean_object* v_alts_284_, lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_282_, v_val_283_, v_alts_284_, v_a_285_, v_b_286_);
lean_dec_ref(v_alts_284_);
lean_dec(v_val_283_);
lean_dec(v_upperBound_282_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(lean_object* v_alts_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_340_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_340_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_340_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_340_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
if (lean_obj_tag(v_a_299_) == 1)
{
lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_335_; 
lean_del_object(v___x_301_);
v_val_303_ = lean_ctor_get(v_a_299_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_a_299_);
if (v_isSharedCheck_335_ == 0)
{
v___x_305_ = v_a_299_;
v_isShared_306_ = v_isSharedCheck_335_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_dec(v_a_299_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_335_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_307_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0);
v___x_308_ = lean_array_get_size(v_alts_289_);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_sub(v___x_308_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_array_get_borrowed(v___x_307_, v_alts_289_, v_val_303_);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_310_);
lean_dec(v___x_310_);
v___x_314_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v___x_308_, v_val_303_, v_alts_289_, v___x_311_, v___x_313_);
lean_dec(v_val_303_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_326_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_326_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_326_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_326_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_inc(v___x_312_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_312_);
lean_ctor_set(v___x_319_, 1, v_a_315_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_319_);
v___x_321_ = v___x_305_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_321_);
v___x_323_ = v___x_317_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_del_object(v___x_305_);
v_a_327_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_314_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_314_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec(v_a_299_);
v___x_336_ = lean_box(0);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_336_);
v___x_338_ = v___x_301_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_298_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_298_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt___boxed(lean_object* v_alts_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_alts_349_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(lean_object* v_upperBound_359_, lean_object* v_val_360_, lean_object* v_alts_361_, lean_object* v_inst_362_, lean_object* v_R_363_, lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v_c_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_359_, v_val_360_, v_alts_361_, v_a_364_, v_b_365_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___boxed(lean_object* v_upperBound_376_, lean_object* v_val_377_, lean_object* v_alts_378_, lean_object* v_inst_379_, lean_object* v_R_380_, lean_object* v_a_381_, lean_object* v_b_382_, lean_object* v_c_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(v_upperBound_376_, v_val_377_, v_alts_378_, v_inst_379_, v_R_380_, v_a_381_, v_b_382_, v_c_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v_alts_378_);
lean_dec(v_val_377_);
lean_dec(v_upperBound_376_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(lean_object* v_as_393_, size_t v_i_394_, size_t v_stop_395_, lean_object* v_b_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___y_400_; uint8_t v___x_405_; 
v___x_405_ = lean_usize_dec_eq(v_i_394_, v_stop_395_);
if (v___x_405_ == 0)
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = 0;
v___x_407_ = lean_array_uget_borrowed(v_as_393_, v_i_394_);
v___x_408_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_407_);
v___x_409_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_406_, v___x_408_, v___y_397_);
lean_dec_ref(v___x_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___y_411_; 
lean_dec_ref_known(v___x_409_, 1);
switch(lean_obj_tag(v___x_407_))
{
case 0:
{
lean_object* v_code_413_; 
v_code_413_ = lean_ctor_get(v___x_407_, 2);
v___y_411_ = v_code_413_;
goto v___jp_410_;
}
case 1:
{
lean_object* v_code_414_; 
v_code_414_ = lean_ctor_get(v___x_407_, 1);
v___y_411_ = v_code_414_;
goto v___jp_410_;
}
default: 
{
lean_object* v_code_415_; 
v_code_415_ = lean_ctor_get(v___x_407_, 0);
v___y_411_ = v_code_415_;
goto v___jp_410_;
}
}
v___jp_410_:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_406_, v___y_411_, v___y_397_);
v___y_400_ = v___x_412_;
goto v___jp_399_;
}
}
else
{
v___y_400_ = v___x_409_;
goto v___jp_399_;
}
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v_b_396_);
return v___x_416_;
}
v___jp_399_:
{
if (lean_obj_tag(v___y_400_) == 0)
{
lean_object* v_a_401_; size_t v___x_402_; size_t v___x_403_; 
v_a_401_ = lean_ctor_get(v___y_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___y_400_, 1);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_add(v_i_394_, v___x_402_);
v_i_394_ = v___x_403_;
v_b_396_ = v_a_401_;
goto _start;
}
else
{
return v___y_400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg___boxed(lean_object* v_as_417_, lean_object* v_i_418_, lean_object* v_stop_419_, lean_object* v_b_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
size_t v_i_boxed_423_; size_t v_stop_boxed_424_; lean_object* v_res_425_; 
v_i_boxed_423_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_424_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_417_, v_i_boxed_423_, v_stop_boxed_424_, v_b_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v_as_417_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(lean_object* v_fst_426_, lean_object* v_as_427_, size_t v_sz_428_, size_t v_i_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_a_440_; uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_429_, v_sz_428_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec_ref(v_fst_426_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_b_430_);
return v___x_445_;
}
else
{
lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_490_; 
v_fst_446_ = lean_ctor_get(v_b_430_, 0);
v_snd_447_ = lean_ctor_get(v_b_430_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_b_430_);
if (v_isSharedCheck_490_ == 0)
{
v___x_449_ = v_b_430_;
v_isShared_450_ = v_isSharedCheck_490_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_snd_447_);
lean_inc(v_fst_446_);
lean_dec(v_b_430_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_490_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_a_451_; uint8_t v_a_453_; lean_object* v___y_463_; lean_object* v___x_474_; 
v_a_451_ = lean_array_uget_borrowed(v_as_427_, v_i_429_);
v___x_474_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_a_451_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; uint8_t v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
v___x_476_ = lean_unbox(v_a_475_);
lean_dec(v_a_475_);
if (v___x_476_ == 0)
{
v___y_463_ = v___x_474_;
goto v___jp_462_;
}
else
{
uint8_t v___x_477_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_483_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_477_ = 0;
switch(lean_obj_tag(v_a_451_))
{
case 0:
{
lean_object* v_code_487_; 
v_code_487_ = lean_ctor_get(v_a_451_, 2);
lean_inc_ref(v_code_487_);
v___y_483_ = v_code_487_;
goto v___jp_482_;
}
case 1:
{
lean_object* v_code_488_; 
v_code_488_ = lean_ctor_get(v_a_451_, 1);
lean_inc_ref(v_code_488_);
v___y_483_ = v_code_488_;
goto v___jp_482_;
}
default: 
{
lean_object* v_code_489_; 
v_code_489_ = lean_ctor_get(v_a_451_, 0);
lean_inc_ref(v_code_489_);
v___y_483_ = v_code_489_;
goto v___jp_482_;
}
}
v___jp_478_:
{
uint8_t v___x_481_; 
v___x_481_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_477_, v___y_479_, v___y_480_);
v_a_453_ = v___x_481_;
goto v___jp_452_;
}
v___jp_482_:
{
switch(lean_obj_tag(v_fst_426_))
{
case 0:
{
lean_object* v_code_484_; 
v_code_484_ = lean_ctor_get(v_fst_426_, 2);
lean_inc_ref(v_code_484_);
v___y_479_ = v___y_483_;
v___y_480_ = v_code_484_;
goto v___jp_478_;
}
case 1:
{
lean_object* v_code_485_; 
v_code_485_ = lean_ctor_get(v_fst_426_, 1);
lean_inc_ref(v_code_485_);
v___y_479_ = v___y_483_;
v___y_480_ = v_code_485_;
goto v___jp_478_;
}
default: 
{
lean_object* v_code_486_; 
v_code_486_ = lean_ctor_get(v_fst_426_, 0);
lean_inc_ref(v_code_486_);
v___y_479_ = v___y_483_;
v___y_480_ = v_code_486_;
goto v___jp_478_;
}
}
}
}
}
else
{
v___y_463_ = v___x_474_;
goto v___jp_462_;
}
v___jp_452_:
{
if (v_a_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_inc(v_a_451_);
v___x_454_ = lean_array_push(v_fst_446_, v_a_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_454_);
v___x_456_ = v___x_449_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_snd_447_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v_a_440_ = v___x_456_;
goto v___jp_439_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_inc(v_a_451_);
v___x_458_ = lean_array_push(v_snd_447_, v_a_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_458_);
v___x_460_ = v___x_449_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_446_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v_a_440_ = v___x_460_;
goto v___jp_439_;
}
}
}
v___jp_462_:
{
if (lean_obj_tag(v___y_463_) == 0)
{
lean_object* v_a_464_; uint8_t v___x_465_; 
v_a_464_ = lean_ctor_get(v___y_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___y_463_, 1);
v___x_465_ = lean_unbox(v_a_464_);
lean_dec(v_a_464_);
v_a_453_ = v___x_465_;
goto v___jp_452_;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_del_object(v___x_449_);
lean_dec(v_snd_447_);
lean_dec(v_fst_446_);
lean_dec_ref(v_fst_426_);
v_a_466_ = lean_ctor_get(v___y_463_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___y_463_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___y_463_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___y_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
v___jp_439_:
{
size_t v___x_441_; size_t v___x_442_; 
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_429_, v___x_441_);
v_i_429_ = v___x_442_;
v_b_430_ = v_a_440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(lean_object* v_fst_491_, lean_object* v_as_492_, lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_505_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_491_, v_as_492_, v_sz_boxed_504_, v_i_boxed_505_, v_b_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec_ref(v_as_492_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object* v_alts_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_array_get_size(v_alts_511_);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_dec_le(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_613_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_613_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_613_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_613_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
if (lean_obj_tag(v_a_524_) == 1)
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_609_; 
v_val_528_ = lean_ctor_get(v_a_524_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_a_524_);
if (v_isSharedCheck_609_ == 0)
{
v___x_530_ = v_a_524_;
v_isShared_531_ = v_isSharedCheck_609_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v_a_524_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_609_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; lean_object* v___x_535_; size_t v_sz_536_; size_t v___x_537_; lean_object* v___x_538_; 
v_fst_532_ = lean_ctor_get(v_val_528_, 0);
lean_inc_n(v_fst_532_, 2);
v_snd_533_ = lean_ctor_get(v_val_528_, 1);
lean_inc(v_snd_533_);
lean_dec(v_val_528_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1));
v_sz_536_ = lean_array_size(v_snd_533_);
v___x_537_ = ((size_t)0ULL);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_532_, v_snd_533_, v_sz_536_, v___x_537_, v___x_535_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_snd_533_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_600_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_600_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_600_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_600_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___y_546_; lean_object* v___y_559_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_fst_543_ = lean_ctor_get(v_a_539_, 0);
lean_inc(v_fst_543_);
v_snd_544_ = lean_ctor_get(v_a_539_, 1);
lean_inc(v_snd_544_);
lean_dec(v_a_539_);
v___x_568_ = lean_array_get_size(v_snd_544_);
v___x_569_ = lean_nat_dec_eq(v___x_568_, v___x_534_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_del_object(v___x_526_);
lean_dec_ref(v_alts_511_);
v___x_570_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_513_);
if (lean_obj_tag(v___x_570_) == 0)
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref_known(v___x_570_, 1);
v___x_571_ = 0;
v___x_572_ = l_Lean_Compiler_LCNF_Alt_getParams(v_fst_532_);
v___x_573_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_571_, v___x_572_, v_a_516_);
lean_dec_ref(v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
uint8_t v___x_574_; 
lean_dec_ref_known(v___x_573_, 1);
v___x_574_ = lean_nat_dec_lt(v___x_534_, v___x_568_);
if (v___x_574_ == 0)
{
lean_dec(v_snd_544_);
goto v___jp_554_;
}
else
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_nat_dec_le(v___x_568_, v___x_568_);
if (v___x_576_ == 0)
{
if (v___x_574_ == 0)
{
lean_dec(v_snd_544_);
goto v___jp_554_;
}
else
{
size_t v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_usize_of_nat(v___x_568_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_snd_544_, v___x_537_, v___x_577_, v___x_575_, v_a_516_);
lean_dec(v_snd_544_);
v___y_559_ = v___x_578_;
goto v___jp_558_;
}
}
else
{
size_t v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_usize_of_nat(v___x_568_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_snd_544_, v___x_537_, v___x_579_, v___x_575_, v_a_516_);
lean_dec(v_snd_544_);
v___y_559_ = v___x_580_;
goto v___jp_558_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_snd_544_);
lean_dec(v_fst_543_);
lean_del_object(v___x_541_);
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
v_a_581_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_573_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_573_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_snd_544_);
lean_dec(v_fst_543_);
lean_del_object(v___x_541_);
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
v_a_589_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_570_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_570_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v_snd_544_);
lean_dec(v_fst_543_);
lean_del_object(v___x_541_);
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v_alts_511_);
v___x_598_ = v___x_526_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_alts_511_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
v___jp_545_:
{
lean_object* v___x_548_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 2);
lean_ctor_set(v___x_530_, 0, v___y_546_);
v___x_548_ = v___x_530_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___y_546_);
v___x_548_ = v_reuseFailAlloc_553_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_array_push(v_fst_543_, v___x_548_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_549_);
v___x_551_ = v___x_541_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
v___jp_554_:
{
switch(lean_obj_tag(v_fst_532_))
{
case 0:
{
lean_object* v_code_555_; 
v_code_555_ = lean_ctor_get(v_fst_532_, 2);
lean_inc_ref(v_code_555_);
lean_dec_ref_known(v_fst_532_, 3);
v___y_546_ = v_code_555_;
goto v___jp_545_;
}
case 1:
{
lean_object* v_code_556_; 
v_code_556_ = lean_ctor_get(v_fst_532_, 1);
lean_inc_ref(v_code_556_);
lean_dec_ref_known(v_fst_532_, 2);
v___y_546_ = v_code_556_;
goto v___jp_545_;
}
default: 
{
lean_object* v_code_557_; 
v_code_557_ = lean_ctor_get(v_fst_532_, 0);
lean_inc_ref(v_code_557_);
lean_dec_ref_known(v_fst_532_, 1);
v___y_546_ = v_code_557_;
goto v___jp_545_;
}
}
}
v___jp_558_:
{
if (lean_obj_tag(v___y_559_) == 0)
{
lean_dec_ref_known(v___y_559_, 1);
goto v___jp_554_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_fst_543_);
lean_del_object(v___x_541_);
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
v_a_560_ = lean_ctor_get(v___y_559_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___y_559_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___y_559_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___y_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_fst_532_);
lean_del_object(v___x_530_);
lean_del_object(v___x_526_);
lean_dec_ref(v_alts_511_);
v_a_601_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_538_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_538_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v___x_611_; 
lean_dec(v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v_alts_511_);
v___x_611_ = v___x_526_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_alts_511_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_alts_511_);
v_a_614_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_523_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_523_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v_alts_511_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(lean_object* v_alts_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_alts_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(lean_object* v_as_633_, size_t v_i_634_, size_t v_stop_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_633_, v_i_634_, v_stop_635_, v_b_636_, v___y_641_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(lean_object* v_as_646_, lean_object* v_i_647_, lean_object* v_stop_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_i_boxed_658_; size_t v_stop_boxed_659_; lean_object* v_res_660_; 
v_i_boxed_658_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_stop_boxed_659_ = lean_unbox_usize(v_stop_648_);
lean_dec(v_stop_648_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_as_646_, v_i_boxed_658_, v_stop_boxed_659_, v_b_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_as_646_);
return v_res_660_;
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
