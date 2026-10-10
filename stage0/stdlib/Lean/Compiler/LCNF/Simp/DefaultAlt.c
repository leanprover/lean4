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
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v___y_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v_res_48_;
v_res_48_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_1_, v_i_2_, v_stop_3_, v___y_4_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg___boxed(lean_object* v_as_49_, lean_object* v_i_50_, lean_object* v_stop_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
size_t v_i_boxed_54_; size_t v_stop_boxed_55_; lean_object* v_res_56_; 
v_i_boxed_54_ = lean_unbox_usize(v_i_50_);
lean_dec(v_i_50_);
v_stop_boxed_55_ = lean_unbox_usize(v_stop_51_);
lean_dec(v_stop_51_);
v_res_56_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_49_, v_i_boxed_54_, v_stop_boxed_55_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v_as_49_);
return v_res_56_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(lean_object* v_alt_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_70_ = l_Lean_Compiler_LCNF_Alt_getParams(v_alt_57_);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_array_get_size(v___x_70_);
v___x_73_ = lean_nat_dec_lt(v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
lean_dec_ref(v___x_70_);
goto v___jp_66_;
}
else
{
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec_ref(v___x_70_);
v___x_74_ = lean_box(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
else
{
size_t v___x_76_; size_t v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((size_t)0ULL);
v___x_77_ = lean_usize_of_nat(v___x_72_);
v___x_78_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v___x_70_, v___x_76_, v___x_77_, v_a_59_);
lean_dec_ref(v___x_70_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_89_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_89_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
uint8_t v___x_83_; 
v___x_83_ = lean_unbox(v_a_79_);
lean_dec(v_a_79_);
if (v___x_83_ == 0)
{
lean_del_object(v___x_81_);
goto v___jp_66_;
}
else
{
uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = 0;
v___x_85_ = lean_box(v___x_84_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_85_);
v___x_87_ = v___x_81_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
return v___x_78_;
}
}
}
v___jp_66_:
{
uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = 1;
v___x_68_ = lean_box(v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_a_59_ = stack[2].m_obj;
lean_object* v_a_60_ = stack[3].m_obj;
lean_object* v_a_61_ = stack[4].m_obj;
lean_object* v_a_62_ = stack[5].m_obj;
lean_object* v_a_63_ = stack[6].m_obj;
lean_object* v_a_64_ = stack[7].m_obj;
lean_object* v_res_90_;
v_res_90_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_alt_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams___boxed(lean_object* v_alt_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_alt_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec_ref(v_alt_91_);
return v_res_100_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(lean_object* v_as_101_, size_t v_i_102_, size_t v_stop_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___redArg(v_as_101_, v_i_102_, v_stop_103_, v___y_105_);
return v___x_112_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_101_ = stack[0].m_obj;
size_t v_i_102_ = stack[1].m_num;
size_t v_stop_103_ = stack[2].m_num;
lean_object* v___y_104_ = stack[3].m_obj;
lean_object* v___y_105_ = stack[4].m_obj;
lean_object* v___y_106_ = stack[5].m_obj;
lean_object* v___y_107_ = stack[6].m_obj;
lean_object* v___y_108_ = stack[7].m_obj;
lean_object* v___y_109_ = stack[8].m_obj;
lean_object* v___y_110_ = stack[9].m_obj;
lean_object* v_res_113_;
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(v_as_101_, v_i_102_, v_stop_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
size_t v_i_boxed_125_; size_t v_stop_boxed_126_; lean_object* v_res_127_; 
v_i_boxed_125_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_126_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams_spec__0(v_as_114_, v_i_boxed_125_, v_stop_boxed_126_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v_as_114_);
return v_res_127_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(lean_object* v_as_128_, size_t v_sz_129_, size_t v_i_130_, lean_object* v_b_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = lean_usize_dec_lt(v_i_130_, v_sz_129_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_b_131_);
return v___x_141_;
}
else
{
lean_object* v_snd_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_179_; 
v_snd_142_ = lean_ctor_get(v_b_131_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_b_131_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v_b_131_, 0);
lean_dec(v_unused_180_);
v___x_144_ = v_b_131_;
v_isShared_145_ = v_isSharedCheck_179_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_snd_142_);
lean_dec(v_b_131_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_179_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v_a_147_; lean_object* v___x_148_; 
v___x_146_ = lean_box(0);
v_a_147_ = lean_array_uget_borrowed(v_as_128_, v_i_130_);
v___x_148_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_a_147_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_170_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_170_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_170_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_170_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint8_t v___x_153_; 
v___x_153_ = lean_unbox(v_a_149_);
lean_dec(v_a_149_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
lean_del_object(v___x_151_);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_snd_142_, v___x_154_);
lean_dec(v_snd_142_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_155_);
lean_ctor_set(v___x_144_, 0, v___x_146_);
v___x_157_ = v___x_144_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_161_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
size_t v___x_158_; size_t v___x_159_; 
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_130_, v___x_158_);
v_i_130_ = v___x_159_;
v_b_131_ = v___x_157_;
goto _start;
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_inc(v_snd_142_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v_snd_142_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_163_);
v___x_165_ = v___x_144_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_snd_142_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_165_);
v___x_167_ = v___x_151_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_del_object(v___x_144_);
lean_dec(v_snd_142_);
v_a_171_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_148_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_148_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_128_ = stack[0].m_obj;
size_t v_sz_129_ = stack[1].m_num;
size_t v_i_130_ = stack[2].m_num;
lean_object* v_b_131_ = stack[3].m_obj;
lean_object* v___y_132_ = stack[4].m_obj;
lean_object* v___y_133_ = stack[5].m_obj;
lean_object* v___y_134_ = stack[6].m_obj;
lean_object* v___y_135_ = stack[7].m_obj;
lean_object* v___y_136_ = stack[8].m_obj;
lean_object* v___y_137_ = stack[9].m_obj;
lean_object* v___y_138_ = stack[10].m_obj;
lean_object* v_res_181_;
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_as_128_, v_sz_129_, v_i_130_, v_b_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1___boxed(lean_object* v_as_182_, lean_object* v_sz_183_, lean_object* v_i_184_, lean_object* v_b_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
size_t v_sz_boxed_194_; size_t v_i_boxed_195_; lean_object* v_res_196_; 
v_sz_boxed_194_ = lean_unbox_usize(v_sz_183_);
lean_dec(v_sz_183_);
v_i_boxed_195_ = lean_unbox_usize(v_i_184_);
lean_dec(v_i_184_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_as_182_, v_sz_boxed_194_, v_i_boxed_195_, v_b_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec_ref(v_as_182_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(lean_object* v_as_197_, lean_object* v_j_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_get_size(v_as_197_);
v___x_200_ = lean_nat_dec_lt(v_j_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v_j_198_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_fget(v_as_197_, v_j_198_);
if (lean_obj_tag(v___x_202_) == 2)
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_202_, 0);
lean_dec(v_unused_210_);
v___x_204_ = v___x_202_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_dec(v___x_202_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v_j_198_);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_j_198_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v___x_202_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_j_198_, v___x_211_);
lean_dec(v_j_198_);
v_j_198_ = v___x_212_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0___boxed(lean_object* v_as_214_, lean_object* v_j_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(v_as_214_, v_j_215_);
lean_dec_ref(v_as_214_);
return v_res_216_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(lean_object* v_alts_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__0(v_alts_220_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 1)
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; size_t v_sz_234_; size_t v___x_235_; lean_object* v___x_236_; 
lean_dec(v___x_230_);
v___x_232_ = lean_box(0);
v___x_233_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___closed__0));
v_sz_234_ = lean_array_size(v_alts_220_);
v___x_235_ = ((size_t)0ULL);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_spec__1(v_alts_220_, v_sz_234_, v___x_235_, v___x_233_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_249_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_249_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_249_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_249_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_fst_241_; 
v_fst_241_ = lean_ctor_get(v_a_237_, 0);
lean_inc(v_fst_241_);
lean_dec(v_a_237_);
if (lean_obj_tag(v_fst_241_) == 0)
{
lean_object* v___x_243_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_232_);
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_232_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
else
{
lean_object* v_val_245_; lean_object* v___x_247_; 
v_val_245_ = lean_ctor_get(v_fst_241_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v_fst_241_, 1);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v_val_245_);
v___x_247_ = v___x_239_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_val_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_236_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_236_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_220_ = stack[0].m_obj;
lean_object* v_a_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_a_223_ = stack[3].m_obj;
lean_object* v_a_224_ = stack[4].m_obj;
lean_object* v_a_225_ = stack[5].m_obj;
lean_object* v_a_226_ = stack[6].m_obj;
lean_object* v_a_227_ = stack[7].m_obj;
lean_object* v_res_258_;
v_res_258_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx___boxed(lean_object* v_alts_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec_ref(v_alts_259_);
return v_res_268_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_269_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(lean_object* v_upperBound_270_, lean_object* v_val_271_, lean_object* v_alts_272_, lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
lean_object* v_a_277_; uint8_t v___x_281_; 
v___x_281_ = lean_nat_dec_lt(v_a_273_, v_upperBound_270_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_dec(v_a_273_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_b_274_);
return v___x_282_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = lean_nat_dec_eq(v_a_273_, v_val_271_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0);
v___x_285_ = lean_array_get_borrowed(v___x_284_, v_alts_272_, v_a_273_);
lean_inc(v___x_285_);
v___x_286_ = lean_array_push(v_b_274_, v___x_285_);
v_a_277_ = v___x_286_;
goto v___jp_276_;
}
else
{
v_a_277_ = v_b_274_;
goto v___jp_276_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_a_273_, v___x_278_);
lean_dec(v_a_273_);
v_a_273_ = v___x_279_;
v_b_274_ = v_a_277_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_270_ = stack[0].m_obj;
lean_object* v_val_271_ = stack[1].m_obj;
lean_object* v_alts_272_ = stack[2].m_obj;
lean_object* v_a_273_ = stack[3].m_obj;
lean_object* v_b_274_ = stack[4].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_270_, v_val_271_, v_alts_272_, v_a_273_, v_b_274_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___boxed(lean_object* v_upperBound_288_, lean_object* v_val_289_, lean_object* v_alts_290_, lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_288_, v_val_289_, v_alts_290_, v_a_291_, v_b_292_);
lean_dec_ref(v_alts_290_);
lean_dec(v_val_289_);
lean_dec(v_upperBound_288_);
return v_res_294_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(lean_object* v_alts_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootIdx(v_alts_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_346_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_346_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_346_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_346_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
if (lean_obj_tag(v_a_305_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_341_; 
lean_del_object(v___x_307_);
v_val_309_ = lean_ctor_get(v_a_305_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_305_);
if (v_isSharedCheck_341_ == 0)
{
v___x_311_ = v_a_305_;
v_isShared_312_ = v_isSharedCheck_341_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v_a_305_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_341_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_313_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg___closed__0);
v___x_314_ = lean_array_get_size(v_alts_295_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_sub(v___x_314_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_array_get_borrowed(v___x_313_, v_alts_295_, v_val_309_);
v___x_319_ = lean_mk_empty_array_with_capacity(v___x_316_);
lean_dec(v___x_316_);
v___x_320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v___x_314_, v_val_309_, v_alts_295_, v___x_317_, v___x_319_);
lean_dec(v_val_309_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_332_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
lean_inc(v___x_318_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_318_);
lean_ctor_set(v___x_325_, 1, v_a_321_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_325_);
v___x_327_ = v___x_311_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_327_);
v___x_329_ = v___x_323_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_del_object(v___x_311_);
v_a_333_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_320_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_320_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
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
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec(v_a_305_);
v___x_342_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_342_);
v___x_344_ = v___x_307_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_304_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_304_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_295_ = stack[0].m_obj;
lean_object* v_a_296_ = stack[1].m_obj;
lean_object* v_a_297_ = stack[2].m_obj;
lean_object* v_a_298_ = stack[3].m_obj;
lean_object* v_a_299_ = stack[4].m_obj;
lean_object* v_a_300_ = stack[5].m_obj;
lean_object* v_a_301_ = stack[6].m_obj;
lean_object* v_a_302_ = stack[7].m_obj;
lean_object* v_res_355_;
v_res_355_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt___boxed(lean_object* v_alts_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v_alts_356_);
return v_res_365_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(lean_object* v_upperBound_366_, lean_object* v_val_367_, lean_object* v_alts_368_, lean_object* v_inst_369_, lean_object* v_R_370_, lean_object* v_a_371_, lean_object* v_b_372_, lean_object* v_c_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___redArg(v_upperBound_366_, v_val_367_, v_alts_368_, v_a_371_, v_b_372_);
return v___x_382_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_366_ = stack[0].m_obj;
lean_object* v_val_367_ = stack[1].m_obj;
lean_object* v_alts_368_ = stack[2].m_obj;
lean_object* v_a_371_ = stack[5].m_obj;
lean_object* v_b_372_ = stack[6].m_obj;
lean_object* v___y_374_ = stack[8].m_obj;
lean_object* v___y_375_ = stack[9].m_obj;
lean_object* v___y_376_ = stack[10].m_obj;
lean_object* v___y_377_ = stack[11].m_obj;
lean_object* v___y_378_ = stack[12].m_obj;
lean_object* v___y_379_ = stack[13].m_obj;
lean_object* v___y_380_ = stack[14].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(v_upperBound_366_, v_val_367_, v_alts_368_, lean_box(0), lean_box(0), v_a_371_, v_b_372_, lean_box(0), v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0___boxed(lean_object* v_upperBound_384_, lean_object* v_val_385_, lean_object* v_alts_386_, lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_c_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt_spec__0(v_upperBound_384_, v_val_385_, v_alts_386_, v_inst_387_, v_R_388_, v_a_389_, v_b_390_, v_c_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v_alts_386_);
lean_dec(v_val_385_);
lean_dec(v_upperBound_384_);
return v_res_400_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(lean_object* v_as_401_, size_t v_i_402_, size_t v_stop_403_, lean_object* v_b_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___y_408_; uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_eq(v_i_402_, v_stop_403_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = 0;
v___x_415_ = lean_array_uget_borrowed(v_as_401_, v_i_402_);
v___x_416_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_415_);
v___x_417_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_414_, v___x_416_, v___y_405_);
lean_dec_ref(v___x_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___y_419_; 
lean_dec_ref_known(v___x_417_, 1);
switch(lean_obj_tag(v___x_415_))
{
case 0:
{
lean_object* v_code_421_; 
v_code_421_ = lean_ctor_get(v___x_415_, 2);
v___y_419_ = v_code_421_;
goto v___jp_418_;
}
case 1:
{
lean_object* v_code_422_; 
v_code_422_ = lean_ctor_get(v___x_415_, 1);
v___y_419_ = v_code_422_;
goto v___jp_418_;
}
default: 
{
lean_object* v_code_423_; 
v_code_423_ = lean_ctor_get(v___x_415_, 0);
v___y_419_ = v_code_423_;
goto v___jp_418_;
}
}
v___jp_418_:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_414_, v___y_419_, v___y_405_);
v___y_408_ = v___x_420_;
goto v___jp_407_;
}
}
else
{
v___y_408_ = v___x_417_;
goto v___jp_407_;
}
}
else
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v_b_404_);
return v___x_424_;
}
v___jp_407_:
{
if (lean_obj_tag(v___y_408_) == 0)
{
lean_object* v_a_409_; size_t v___x_410_; size_t v___x_411_; 
v_a_409_ = lean_ctor_get(v___y_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___y_408_, 1);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_402_, v___x_410_);
v_i_402_ = v___x_411_;
v_b_404_ = v_a_409_;
goto _start;
}
else
{
return v___y_408_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_401_ = stack[0].m_obj;
size_t v_i_402_ = stack[1].m_num;
size_t v_stop_403_ = stack[2].m_num;
lean_object* v_b_404_ = stack[3].m_obj;
lean_object* v___y_405_ = stack[4].m_obj;
lean_object* v_res_425_;
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_401_, v_i_402_, v_stop_403_, v_b_404_, v___y_405_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg___boxed(lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v_b_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
size_t v_i_boxed_432_; size_t v_stop_boxed_433_; lean_object* v_res_434_; 
v_i_boxed_432_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_433_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_426_, v_i_boxed_432_, v_stop_boxed_433_, v_b_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v_as_426_);
return v_res_434_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(lean_object* v_fst_435_, lean_object* v_as_436_, size_t v_sz_437_, size_t v_i_438_, lean_object* v_b_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_a_449_; uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec_ref(v_fst_435_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_b_439_);
return v___x_454_;
}
else
{
lean_object* v_fst_455_; lean_object* v_snd_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_499_; 
v_fst_455_ = lean_ctor_get(v_b_439_, 0);
v_snd_456_ = lean_ctor_get(v_b_439_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_b_439_);
if (v_isSharedCheck_499_ == 0)
{
v___x_458_ = v_b_439_;
v_isShared_459_ = v_isSharedCheck_499_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snd_456_);
lean_inc(v_fst_455_);
lean_dec(v_b_439_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_499_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_a_460_; uint8_t v_a_462_; lean_object* v___y_472_; lean_object* v___x_483_; 
v_a_460_ = lean_array_uget_borrowed(v_as_436_, v_i_438_);
v___x_483_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_hasNoUsedParams(v_a_460_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; uint8_t v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v___x_485_ = lean_unbox(v_a_484_);
if (v___x_485_ == 0)
{
v___y_472_ = v___x_483_;
goto v___jp_471_;
}
else
{
uint8_t v___x_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_492_; 
lean_dec_ref_known(v___x_483_, 1);
v___x_486_ = 0;
switch(lean_obj_tag(v_a_460_))
{
case 0:
{
lean_object* v_code_496_; 
v_code_496_ = lean_ctor_get(v_a_460_, 2);
lean_inc_ref(v_code_496_);
v___y_492_ = v_code_496_;
goto v___jp_491_;
}
case 1:
{
lean_object* v_code_497_; 
v_code_497_ = lean_ctor_get(v_a_460_, 1);
lean_inc_ref(v_code_497_);
v___y_492_ = v_code_497_;
goto v___jp_491_;
}
default: 
{
lean_object* v_code_498_; 
v_code_498_ = lean_ctor_get(v_a_460_, 0);
lean_inc_ref(v_code_498_);
v___y_492_ = v_code_498_;
goto v___jp_491_;
}
}
v___jp_487_:
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_486_, v___y_488_, v___y_489_);
v_a_462_ = v___x_490_;
goto v___jp_461_;
}
v___jp_491_:
{
switch(lean_obj_tag(v_fst_435_))
{
case 0:
{
lean_object* v_code_493_; 
v_code_493_ = lean_ctor_get(v_fst_435_, 2);
lean_inc_ref(v_code_493_);
v___y_488_ = v___y_492_;
v___y_489_ = v_code_493_;
goto v___jp_487_;
}
case 1:
{
lean_object* v_code_494_; 
v_code_494_ = lean_ctor_get(v_fst_435_, 1);
lean_inc_ref(v_code_494_);
v___y_488_ = v___y_492_;
v___y_489_ = v_code_494_;
goto v___jp_487_;
}
default: 
{
lean_object* v_code_495_; 
v_code_495_ = lean_ctor_get(v_fst_435_, 0);
lean_inc_ref(v_code_495_);
v___y_488_ = v___y_492_;
v___y_489_ = v_code_495_;
goto v___jp_487_;
}
}
}
}
}
else
{
v___y_472_ = v___x_483_;
goto v___jp_471_;
}
v___jp_461_:
{
if (v_a_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_inc(v_a_460_);
v___x_463_ = lean_array_push(v_fst_455_, v_a_460_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_463_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_snd_456_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
v_a_449_ = v___x_465_;
goto v___jp_448_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_a_460_);
v___x_467_ = lean_array_push(v_snd_456_, v_a_460_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_467_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_fst_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_a_449_ = v___x_469_;
goto v___jp_448_;
}
}
}
v___jp_471_:
{
if (lean_obj_tag(v___y_472_) == 0)
{
lean_object* v_a_473_; uint8_t v___x_474_; 
v_a_473_ = lean_ctor_get(v___y_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___y_472_, 1);
v___x_474_ = lean_unbox(v_a_473_);
lean_dec(v_a_473_);
v_a_462_ = v___x_474_;
goto v___jp_461_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_del_object(v___x_458_);
lean_dec(v_snd_456_);
lean_dec(v_fst_455_);
lean_dec_ref(v_fst_435_);
v_a_475_ = lean_ctor_get(v___y_472_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___y_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___y_472_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___y_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
v___jp_448_:
{
size_t v___x_450_; size_t v___x_451_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_438_, v___x_450_);
v_i_438_ = v___x_451_;
v_b_439_ = v_a_449_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_435_ = stack[0].m_obj;
lean_object* v_as_436_ = stack[1].m_obj;
size_t v_sz_437_ = stack[2].m_num;
size_t v_i_438_ = stack[3].m_num;
lean_object* v_b_439_ = stack[4].m_obj;
lean_object* v___y_440_ = stack[5].m_obj;
lean_object* v___y_441_ = stack[6].m_obj;
lean_object* v___y_442_ = stack[7].m_obj;
lean_object* v___y_443_ = stack[8].m_obj;
lean_object* v___y_444_ = stack[9].m_obj;
lean_object* v___y_445_ = stack[10].m_obj;
lean_object* v___y_446_ = stack[11].m_obj;
lean_object* v_res_500_;
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_435_, v_as_436_, v_sz_437_, v_i_438_, v_b_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(lean_object* v_fst_501_, lean_object* v_as_502_, lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_515_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_501_, v_as_502_, v_sz_boxed_514_, v_i_boxed_515_, v_b_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_as_502_);
return v_res_516_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object* v_alts_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_array_get_size(v_alts_521_);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_dec_le(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_addDefaultAlt_chooseRootAlt(v_alts_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_623_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_623_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_623_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_623_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
if (lean_obj_tag(v_a_534_) == 1)
{
lean_object* v_val_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_619_; 
v_val_538_ = lean_ctor_get(v_a_534_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_619_ == 0)
{
v___x_540_ = v_a_534_;
v_isShared_541_ = v_isSharedCheck_619_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_val_538_);
lean_dec(v_a_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_619_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; lean_object* v___x_545_; size_t v_sz_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_fst_542_ = lean_ctor_get(v_val_538_, 0);
lean_inc_n(v_fst_542_, 2);
v_snd_543_ = lean_ctor_get(v_val_538_, 1);
lean_inc(v_snd_543_);
lean_dec(v_val_538_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1));
v_sz_546_ = lean_array_size(v_snd_543_);
v___x_547_ = ((size_t)0ULL);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_fst_542_, v_snd_543_, v_sz_546_, v___x_547_, v___x_545_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_snd_543_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_610_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_610_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_610_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_610_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_fst_553_; lean_object* v_snd_554_; lean_object* v___y_556_; lean_object* v___y_569_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_fst_553_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_fst_553_);
v_snd_554_ = lean_ctor_get(v_a_549_, 1);
lean_inc(v_snd_554_);
lean_dec(v_a_549_);
v___x_578_ = lean_array_get_size(v_snd_554_);
v___x_579_ = lean_nat_dec_eq(v___x_578_, v___x_544_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
lean_del_object(v___x_536_);
lean_dec_ref(v_alts_521_);
v___x_580_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_523_);
if (lean_obj_tag(v___x_580_) == 0)
{
uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref_known(v___x_580_, 1);
v___x_581_ = 0;
v___x_582_ = l_Lean_Compiler_LCNF_Alt_getParams(v_fst_542_);
v___x_583_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_581_, v___x_582_, v_a_526_);
lean_dec_ref(v___x_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
uint8_t v___x_584_; 
lean_dec_ref_known(v___x_583_, 1);
v___x_584_ = lean_nat_dec_lt(v___x_544_, v___x_578_);
if (v___x_584_ == 0)
{
lean_dec(v_snd_554_);
goto v___jp_564_;
}
else
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_nat_dec_le(v___x_578_, v___x_578_);
if (v___x_586_ == 0)
{
if (v___x_584_ == 0)
{
lean_dec(v_snd_554_);
goto v___jp_564_;
}
else
{
size_t v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_usize_of_nat(v___x_578_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_snd_554_, v___x_547_, v___x_587_, v___x_585_, v_a_526_);
lean_dec(v_snd_554_);
v___y_569_ = v___x_588_;
goto v___jp_568_;
}
}
else
{
size_t v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_usize_of_nat(v___x_578_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_snd_554_, v___x_547_, v___x_589_, v___x_585_, v_a_526_);
lean_dec(v_snd_554_);
v___y_569_ = v___x_590_;
goto v___jp_568_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_snd_554_);
lean_dec(v_fst_553_);
lean_del_object(v___x_551_);
lean_dec(v_fst_542_);
lean_del_object(v___x_540_);
v_a_591_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_583_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_583_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_snd_554_);
lean_dec(v_fst_553_);
lean_del_object(v___x_551_);
lean_dec(v_fst_542_);
lean_del_object(v___x_540_);
v_a_599_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_580_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_580_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v___x_608_; 
lean_dec(v_snd_554_);
lean_dec(v_fst_553_);
lean_del_object(v___x_551_);
lean_dec(v_fst_542_);
lean_del_object(v___x_540_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_alts_521_);
v___x_608_ = v___x_536_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_alts_521_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
v___jp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 2);
lean_ctor_set(v___x_540_, 0, v___y_556_);
v___x_558_ = v___x_540_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___y_556_);
v___x_558_ = v_reuseFailAlloc_563_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_array_push(v_fst_553_, v___x_558_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_559_);
v___x_561_ = v___x_551_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
v___jp_564_:
{
switch(lean_obj_tag(v_fst_542_))
{
case 0:
{
lean_object* v_code_565_; 
v_code_565_ = lean_ctor_get(v_fst_542_, 2);
lean_inc_ref(v_code_565_);
lean_dec_ref_known(v_fst_542_, 3);
v___y_556_ = v_code_565_;
goto v___jp_555_;
}
case 1:
{
lean_object* v_code_566_; 
v_code_566_ = lean_ctor_get(v_fst_542_, 1);
lean_inc_ref(v_code_566_);
lean_dec_ref_known(v_fst_542_, 2);
v___y_556_ = v_code_566_;
goto v___jp_555_;
}
default: 
{
lean_object* v_code_567_; 
v_code_567_ = lean_ctor_get(v_fst_542_, 0);
lean_inc_ref(v_code_567_);
lean_dec_ref_known(v_fst_542_, 1);
v___y_556_ = v_code_567_;
goto v___jp_555_;
}
}
}
v___jp_568_:
{
if (lean_obj_tag(v___y_569_) == 0)
{
lean_dec_ref_known(v___y_569_, 1);
goto v___jp_564_;
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_fst_553_);
lean_del_object(v___x_551_);
lean_dec(v_fst_542_);
lean_del_object(v___x_540_);
v_a_570_ = lean_ctor_get(v___y_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___y_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___y_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___y_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_fst_542_);
lean_del_object(v___x_540_);
lean_del_object(v___x_536_);
lean_dec_ref(v_alts_521_);
v_a_611_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_548_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_548_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v_a_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_alts_521_);
v___x_621_ = v___x_536_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_alts_521_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_alts_521_);
v_a_624_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_533_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_533_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_alts_521_);
return v___x_632_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addDefaultAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_521_ = stack[0].m_obj;
lean_object* v_a_522_ = stack[1].m_obj;
lean_object* v_a_523_ = stack[2].m_obj;
lean_object* v_a_524_ = stack[3].m_obj;
lean_object* v_a_525_ = stack[4].m_obj;
lean_object* v_a_526_ = stack[5].m_obj;
lean_object* v_a_527_ = stack[6].m_obj;
lean_object* v_a_528_ = stack[7].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_alts_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(lean_object* v_alts_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_alts_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_643_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(lean_object* v_as_644_, size_t v_i_645_, size_t v_stop_646_, lean_object* v_b_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___redArg(v_as_644_, v_i_645_, v_stop_646_, v_b_647_, v___y_652_);
return v___x_656_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_644_ = stack[0].m_obj;
size_t v_i_645_ = stack[1].m_num;
size_t v_stop_646_ = stack[2].m_num;
lean_object* v_b_647_ = stack[3].m_obj;
lean_object* v___y_648_ = stack[4].m_obj;
lean_object* v___y_649_ = stack[5].m_obj;
lean_object* v___y_650_ = stack[6].m_obj;
lean_object* v___y_651_ = stack[7].m_obj;
lean_object* v___y_652_ = stack[8].m_obj;
lean_object* v___y_653_ = stack[9].m_obj;
lean_object* v___y_654_ = stack[10].m_obj;
lean_object* v_res_657_;
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_as_644_, v_i_645_, v_stop_646_, v_b_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(lean_object* v_as_658_, lean_object* v_i_659_, lean_object* v_stop_660_, lean_object* v_b_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
size_t v_i_boxed_670_; size_t v_stop_boxed_671_; lean_object* v_res_672_; 
v_i_boxed_670_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_stop_boxed_671_ = lean_unbox_usize(v_stop_660_);
lean_dec(v_stop_660_);
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_as_658_, v_i_boxed_670_, v_stop_boxed_671_, v_b_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v_as_658_);
return v_res_672_;
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
