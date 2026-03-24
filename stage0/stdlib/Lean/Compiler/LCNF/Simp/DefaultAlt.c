// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.DefaultAlt
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.Simp.DefaultAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Compiler.LCNF.Simp.addDefaultAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(lean_object* v_upperBound_1_, lean_object* v_alts_2_, lean_object* v_code_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_lt(v_a_4_, v_upperBound_1_);
if (v___x_6_ == 0)
{
lean_dec(v_a_4_);
lean_dec_ref(v_code_3_);
return v_b_5_;
}
else
{
uint8_t v___x_7_; lean_object* v_n_8_; lean_object* v_a_10_; lean_object* v___y_14_; lean_object* v___x_17_; 
v___x_7_ = 0;
v_n_8_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_array_fget_borrowed(v_alts_2_, v_a_4_);
switch(lean_obj_tag(v___x_17_))
{
case 0:
{
lean_object* v_code_18_; 
v_code_18_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_code_18_);
v___y_14_ = v_code_18_;
goto v___jp_13_;
}
case 1:
{
lean_object* v_code_19_; 
v_code_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc_ref(v_code_19_);
v___y_14_ = v_code_19_;
goto v___jp_13_;
}
default: 
{
lean_object* v_code_20_; 
v_code_20_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_code_20_);
v___y_14_ = v_code_20_;
goto v___jp_13_;
}
}
v___jp_9_:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_add(v_a_4_, v_n_8_);
lean_dec(v_a_4_);
v_a_4_ = v___x_11_;
v_b_5_ = v_a_10_;
goto _start;
}
v___jp_13_:
{
uint8_t v___x_15_; 
lean_inc_ref(v_code_3_);
v___x_15_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_7_, v___y_14_, v_code_3_);
if (v___x_15_ == 0)
{
v_a_10_ = v_b_5_;
goto v___jp_9_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_nat_add(v_b_5_, v_n_8_);
lean_dec(v_b_5_);
v_a_10_ = v___x_16_;
goto v___jp_9_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg___boxed(lean_object* v_upperBound_21_, lean_object* v_alts_22_, lean_object* v_code_23_, lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_21_, v_alts_22_, v_code_23_, v_a_24_, v_b_25_);
lean_dec_ref(v_alts_22_);
lean_dec(v_upperBound_21_);
return v_res_26_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0(void){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_27_ = 0;
v___x_28_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(lean_object* v_alts_29_, lean_object* v_i_30_){
_start:
{
lean_object* v___x_31_; lean_object* v_n_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_31_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0);
v_n_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_add(v_i_30_, v_n_32_);
v___x_34_ = lean_array_get_size(v_alts_29_);
v___x_35_ = lean_array_get_borrowed(v___x_31_, v_alts_29_, v_i_30_);
switch(lean_obj_tag(v___x_35_))
{
case 0:
{
lean_object* v_code_36_; lean_object* v___x_37_; 
v_code_36_ = lean_ctor_get(v___x_35_, 2);
lean_inc_ref(v_code_36_);
v___x_37_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_34_, v_alts_29_, v_code_36_, v___x_33_, v_n_32_);
return v___x_37_;
}
case 1:
{
lean_object* v_code_38_; lean_object* v___x_39_; 
v_code_38_ = lean_ctor_get(v___x_35_, 1);
lean_inc_ref(v_code_38_);
v___x_39_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_34_, v_alts_29_, v_code_38_, v___x_33_, v_n_32_);
return v___x_39_;
}
default: 
{
lean_object* v_code_40_; lean_object* v___x_41_; 
v_code_40_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_code_40_);
v___x_41_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v___x_34_, v_alts_29_, v_code_40_, v___x_33_, v_n_32_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___boxed(lean_object* v_alts_42_, lean_object* v_i_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(v_alts_42_, v_i_43_);
lean_dec(v_i_43_);
lean_dec_ref(v_alts_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0(lean_object* v_upperBound_45_, lean_object* v_alts_46_, lean_object* v_code_47_, lean_object* v_inst_48_, lean_object* v_R_49_, lean_object* v_a_50_, lean_object* v_b_51_, lean_object* v_c_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___redArg(v_upperBound_45_, v_alts_46_, v_code_47_, v_a_50_, v_b_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0___boxed(lean_object* v_upperBound_54_, lean_object* v_alts_55_, lean_object* v_code_56_, lean_object* v_inst_57_, lean_object* v_R_58_, lean_object* v_a_59_, lean_object* v_b_60_, lean_object* v_c_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf_spec__0(v_upperBound_54_, v_alts_55_, v_code_56_, v_inst_57_, v_R_58_, v_a_59_, v_b_60_, v_c_61_);
lean_dec_ref(v_alts_55_);
lean_dec(v_upperBound_54_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(lean_object* v_upperBound_63_, lean_object* v_alts_64_, lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_a_68_; uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_lt(v_a_65_, v_upperBound_63_);
if (v___x_72_ == 0)
{
lean_dec(v_a_65_);
return v_b_66_;
}
else
{
lean_object* v_fst_73_; lean_object* v_snd_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_87_; 
v_fst_73_ = lean_ctor_get(v_b_66_, 0);
v_snd_74_ = lean_ctor_get(v_b_66_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_b_66_);
if (v_isSharedCheck_87_ == 0)
{
v___x_76_ = v_b_66_;
v_isShared_77_ = v_isSharedCheck_87_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snd_74_);
lean_inc(v_fst_73_);
lean_dec(v_b_66_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_87_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(v_alts_64_, v_a_65_);
v___x_79_ = lean_nat_dec_lt(v_snd_74_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; 
lean_dec(v___x_78_);
if (v_isShared_77_ == 0)
{
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_fst_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_snd_74_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v_a_68_ = v___x_81_;
goto v___jp_67_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_85_; 
lean_dec(v_snd_74_);
lean_dec(v_fst_73_);
v___x_83_ = lean_array_fget_borrowed(v_alts_64_, v_a_65_);
lean_inc(v___x_83_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_78_);
lean_ctor_set(v___x_76_, 0, v___x_83_);
v___x_85_ = v___x_76_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_78_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
v_a_68_ = v___x_85_;
goto v___jp_67_;
}
}
}
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lean_nat_add(v_a_65_, v___x_69_);
lean_dec(v_a_65_);
v_a_65_ = v___x_70_;
v_b_66_ = v_a_68_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg___boxed(lean_object* v_upperBound_88_, lean_object* v_alts_89_, lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(v_upperBound_88_, v_alts_89_, v_a_90_, v_b_91_);
lean_dec_ref(v_alts_89_);
lean_dec(v_upperBound_88_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(lean_object* v_alts_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_maxAlt_98_; lean_object* v_max_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v___x_94_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0, &l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf___closed__0);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_array_get_size(v_alts_93_);
v___x_97_ = lean_unsigned_to_nat(0u);
v_maxAlt_98_ = lean_array_get_borrowed(v___x_94_, v_alts_93_, v___x_97_);
v_max_99_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_getNumOccsOf(v_alts_93_, v___x_97_);
lean_inc(v_maxAlt_98_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_maxAlt_98_);
lean_ctor_set(v___x_100_, 1, v_max_99_);
v___x_101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(v___x_96_, v_alts_93_, v___x_95_, v___x_100_);
v_fst_102_ = lean_ctor_get(v___x_101_, 0);
v_snd_103_ = lean_ctor_get(v___x_101_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_101_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snd_103_);
lean_inc(v_fst_102_);
lean_dec(v___x_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_fst_102_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_snd_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs___boxed(lean_object* v_alts_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(v_alts_111_);
lean_dec_ref(v_alts_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0(lean_object* v_upperBound_113_, lean_object* v_alts_114_, lean_object* v_inst_115_, lean_object* v_R_116_, lean_object* v_a_117_, lean_object* v_b_118_, lean_object* v_c_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___redArg(v_upperBound_113_, v_alts_114_, v_a_117_, v_b_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0___boxed(lean_object* v_upperBound_121_, lean_object* v_alts_122_, lean_object* v_inst_123_, lean_object* v_R_124_, lean_object* v_a_125_, lean_object* v_b_126_, lean_object* v_c_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs_spec__0(v_upperBound_121_, v_alts_122_, v_inst_123_, v_R_124_, v_a_125_, v_b_126_, v_c_127_);
lean_dec_ref(v_alts_122_);
lean_dec(v_upperBound_121_);
return v_res_128_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_instMonadEIO(lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_toApplicative_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_209_; 
v___x_143_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__0);
v___x_144_ = l_StateRefT_x27_instMonad___redArg(v___x_143_);
v_toApplicative_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_144_, 1);
lean_dec(v_unused_210_);
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_209_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_toApplicative_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_209_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_toFunctor_149_; lean_object* v_toSeq_150_; lean_object* v_toSeqLeft_151_; lean_object* v_toSeqRight_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_207_; 
v_toFunctor_149_ = lean_ctor_get(v_toApplicative_145_, 0);
v_toSeq_150_ = lean_ctor_get(v_toApplicative_145_, 2);
v_toSeqLeft_151_ = lean_ctor_get(v_toApplicative_145_, 3);
v_toSeqRight_152_ = lean_ctor_get(v_toApplicative_145_, 4);
v_isSharedCheck_207_ = !lean_is_exclusive(v_toApplicative_145_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_toApplicative_145_, 1);
lean_dec(v_unused_208_);
v___x_154_ = v_toApplicative_145_;
v_isShared_155_ = v_isSharedCheck_207_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_toSeqRight_152_);
lean_inc(v_toSeqLeft_151_);
lean_inc(v_toSeq_150_);
lean_inc(v_toFunctor_149_);
lean_dec(v_toApplicative_145_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_207_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___f_163_; lean_object* v___x_165_; 
v___f_156_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__1));
v___f_157_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__2));
lean_inc_ref(v_toFunctor_149_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_149_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_159_, 0, v_toFunctor_149_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___f_158_);
lean_ctor_set(v___x_160_, 1, v___f_159_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqRight_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeqLeft_151_);
v___f_163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_163_, 0, v_toSeq_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 4, v___f_161_);
lean_ctor_set(v___x_154_, 3, v___f_162_);
lean_ctor_set(v___x_154_, 2, v___f_163_);
lean_ctor_set(v___x_154_, 1, v___f_156_);
lean_ctor_set(v___x_154_, 0, v___x_160_);
v___x_165_ = v___x_154_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___f_156_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v___f_163_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v___f_162_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v___f_161_);
v___x_165_ = v_reuseFailAlloc_206_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___f_157_);
lean_ctor_set(v___x_147_, 0, v___x_165_);
v___x_167_ = v___x_147_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___f_157_);
v___x_167_ = v_reuseFailAlloc_205_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v_toApplicative_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_203_; 
v___x_168_ = l_StateRefT_x27_instMonad___redArg(v___x_167_);
v_toApplicative_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v___x_168_, 1);
lean_dec(v_unused_204_);
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_203_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_toApplicative_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_203_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_toFunctor_173_; lean_object* v_toSeq_174_; lean_object* v_toSeqLeft_175_; lean_object* v_toSeqRight_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_201_; 
v_toFunctor_173_ = lean_ctor_get(v_toApplicative_169_, 0);
v_toSeq_174_ = lean_ctor_get(v_toApplicative_169_, 2);
v_toSeqLeft_175_ = lean_ctor_get(v_toApplicative_169_, 3);
v_toSeqRight_176_ = lean_ctor_get(v_toApplicative_169_, 4);
v_isSharedCheck_201_ = !lean_is_exclusive(v_toApplicative_169_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_dec(v_unused_202_);
v___x_178_ = v_toApplicative_169_;
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toSeqRight_176_);
lean_inc(v_toSeqLeft_175_);
lean_inc(v_toSeq_174_);
lean_inc(v_toFunctor_173_);
lean_dec(v_toApplicative_169_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___f_187_; lean_object* v___x_189_; 
v___f_180_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__3));
v___f_181_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___closed__4));
lean_inc_ref(v_toFunctor_173_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_182_, 0, v_toFunctor_173_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_183_, 0, v_toFunctor_173_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___f_182_);
lean_ctor_set(v___x_184_, 1, v___f_183_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_185_, 0, v_toSeqRight_176_);
v___f_186_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_186_, 0, v_toSeqLeft_175_);
v___f_187_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_187_, 0, v_toSeq_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___f_185_);
lean_ctor_set(v___x_178_, 3, v___f_186_);
lean_ctor_set(v___x_178_, 2, v___f_187_);
lean_ctor_set(v___x_178_, 1, v___f_180_);
lean_ctor_set(v___x_178_, 0, v___x_184_);
v___x_189_ = v___x_178_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___f_180_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___f_187_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v___f_186_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v___f_185_);
v___x_189_ = v_reuseFailAlloc_200_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___f_181_);
lean_ctor_set(v___x_171_, 0, v___x_189_);
v___x_191_ = v___x_171_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___f_181_);
v___x_191_ = v_reuseFailAlloc_199_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___f_196_; lean_object* v___x_3441__overap_197_; lean_object* v___x_198_; 
v___x_192_ = l_ReaderT_instMonad___redArg(v___x_191_);
v___x_193_ = l_StateRefT_x27_instMonad___redArg(v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = l_instInhabitedOfMonad___redArg(v___x_193_, v___x_194_);
v___f_196_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_196_, 0, v___x_195_);
v___x_3441__overap_197_ = lean_panic_fn(v___f_196_, v_msg_134_);
lean_inc(v___y_141_);
lean_inc_ref(v___y_140_);
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
lean_inc_ref(v___y_137_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
v___x_198_ = lean_apply_8(v___x_3441__overap_197_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, lean_box(0));
return v___x_198_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0___boxed(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__2));
v___x_225_ = lean_unsigned_to_nat(35u);
v___x_226_ = lean_unsigned_to_nat(63u);
v___x_227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__1));
v___x_228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__0));
v___x_229_ = l_mkPanicMessageWithDecl(v___x_228_, v___x_227_, v___x_226_, v___x_225_, v___x_224_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(lean_object* v_snd_230_, lean_object* v_fst_231_, lean_object* v_as_232_, size_t v_sz_233_, size_t v_i_234_, lean_object* v_b_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_a_245_; uint8_t v___x_249_; 
v___x_249_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_fst_231_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_b_235_);
return v___x_250_;
}
else
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_311_; 
v_fst_251_ = lean_ctor_get(v_b_235_, 0);
v_snd_252_ = lean_ctor_get(v_b_235_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_b_235_);
if (v_isSharedCheck_311_ == 0)
{
v___x_254_ = v_b_235_;
v_isShared_255_ = v_isSharedCheck_311_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snd_252_);
lean_inc(v_fst_251_);
lean_dec(v_b_235_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_311_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v_a_263_; uint8_t v___x_264_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_304_; 
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_dec_eq(v_snd_230_, v___x_256_);
v_a_263_ = lean_array_uget_borrowed(v_as_232_, v_i_234_);
v___x_264_ = 0;
switch(lean_obj_tag(v_a_263_))
{
case 0:
{
lean_object* v_code_308_; 
v_code_308_ = lean_ctor_get(v_a_263_, 2);
lean_inc_ref(v_code_308_);
v___y_304_ = v_code_308_;
goto v___jp_303_;
}
case 1:
{
lean_object* v_code_309_; 
v_code_309_ = lean_ctor_get(v_a_263_, 1);
lean_inc_ref(v_code_309_);
v___y_304_ = v_code_309_;
goto v___jp_303_;
}
default: 
{
lean_object* v_code_310_; 
v_code_310_ = lean_ctor_get(v_a_263_, 0);
lean_inc_ref(v_code_310_);
v___y_304_ = v_code_310_;
goto v___jp_303_;
}
}
v___jp_258_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_box(v___x_257_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_259_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fst_251_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
v_a_245_ = v___x_261_;
goto v___jp_244_;
}
}
v___jp_265_:
{
uint8_t v___x_268_; 
v___x_268_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v___x_264_, v___y_266_, v___y_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_del_object(v___x_254_);
lean_inc(v_a_263_);
v___x_269_ = lean_array_push(v_fst_251_, v_a_263_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_snd_252_);
v_a_245_ = v___x_270_;
goto v___jp_244_;
}
else
{
if (lean_obj_tag(v_a_263_) == 0)
{
lean_object* v_params_271_; lean_object* v_code_272_; lean_object* v___x_273_; 
v_params_271_ = lean_ctor_get(v_a_263_, 1);
v_code_272_ = lean_ctor_get(v_a_263_, 2);
v___x_273_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_264_, v_params_271_, v___y_240_);
if (lean_obj_tag(v___x_273_) == 0)
{
uint8_t v___x_274_; 
lean_dec_ref(v___x_273_);
v___x_274_ = lean_unbox(v_snd_252_);
lean_dec(v_snd_252_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_264_, v_code_272_, v___y_240_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref(v___x_275_);
goto v___jp_258_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_del_object(v___x_254_);
lean_dec(v_fst_251_);
lean_dec_ref(v_fst_231_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
goto v___jp_258_;
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_del_object(v___x_254_);
lean_dec(v_snd_252_);
lean_dec(v_fst_251_);
lean_dec_ref(v_fst_231_);
v_a_284_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_273_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_273_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_del_object(v___x_254_);
v___x_292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___closed__3);
v___x_293_ = l_panic___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__0(v___x_292_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_294_; 
lean_dec_ref(v___x_293_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_fst_251_);
lean_ctor_set(v___x_294_, 1, v_snd_252_);
v_a_245_ = v___x_294_;
goto v___jp_244_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_snd_252_);
lean_dec(v_fst_251_);
lean_dec_ref(v_fst_231_);
v_a_295_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_293_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
v___jp_303_:
{
switch(lean_obj_tag(v_fst_231_))
{
case 0:
{
lean_object* v_code_305_; 
v_code_305_ = lean_ctor_get(v_fst_231_, 2);
lean_inc_ref(v_code_305_);
v___y_266_ = v___y_304_;
v___y_267_ = v_code_305_;
goto v___jp_265_;
}
case 1:
{
lean_object* v_code_306_; 
v_code_306_ = lean_ctor_get(v_fst_231_, 1);
lean_inc_ref(v_code_306_);
v___y_266_ = v___y_304_;
v___y_267_ = v_code_306_;
goto v___jp_265_;
}
default: 
{
lean_object* v_code_307_; 
v_code_307_ = lean_ctor_get(v_fst_231_, 0);
lean_inc_ref(v_code_307_);
v___y_266_ = v___y_304_;
v___y_267_ = v_code_307_;
goto v___jp_265_;
}
}
}
}
}
v___jp_244_:
{
size_t v___x_246_; size_t v___x_247_; 
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_add(v_i_234_, v___x_246_);
v_i_234_ = v___x_247_;
v_b_235_ = v_a_245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1___boxed(lean_object* v_snd_312_, lean_object* v_fst_313_, lean_object* v_as_314_, lean_object* v_sz_315_, lean_object* v_i_316_, lean_object* v_b_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
size_t v_sz_boxed_326_; size_t v_i_boxed_327_; lean_object* v_res_328_; 
v_sz_boxed_326_ = lean_unbox_usize(v_sz_315_);
lean_dec(v_sz_315_);
v_i_boxed_327_ = lean_unbox_usize(v_i_316_);
lean_dec(v_i_316_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_snd_312_, v_fst_313_, v_as_314_, v_sz_boxed_326_, v_i_boxed_327_, v_b_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_as_314_);
lean_dec(v_snd_312_);
return v_res_328_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(lean_object* v___x_329_, lean_object* v_as_330_, size_t v_i_331_, size_t v_stop_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_usize_dec_eq(v_i_331_, v_stop_332_);
if (v___x_333_ == 0)
{
uint8_t v___x_334_; lean_object* v___x_335_; 
v___x_334_ = 1;
v___x_335_ = lean_array_uget_borrowed(v_as_330_, v_i_331_);
if (lean_obj_tag(v___x_335_) == 2)
{
return v___x_334_;
}
else
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_dec_le(v___x_329_, v___x_336_);
if (v___x_337_ == 0)
{
size_t v___x_338_; size_t v___x_339_; 
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_add(v_i_331_, v___x_338_);
v_i_331_ = v___x_339_;
goto _start;
}
else
{
return v___x_334_;
}
}
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2___boxed(lean_object* v___x_342_, lean_object* v_as_343_, lean_object* v_i_344_, lean_object* v_stop_345_){
_start:
{
size_t v_i_boxed_346_; size_t v_stop_boxed_347_; uint8_t v_res_348_; lean_object* v_r_349_; 
v_i_boxed_346_ = lean_unbox_usize(v_i_344_);
lean_dec(v_i_344_);
v_stop_boxed_347_ = lean_unbox_usize(v_stop_345_);
lean_dec(v_stop_345_);
v_res_348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(v___x_342_, v_as_343_, v_i_boxed_346_, v_stop_boxed_347_);
lean_dec_ref(v_as_343_);
lean_dec(v___x_342_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object* v_alts_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___y_374_; uint8_t v___x_409_; 
v___x_371_ = lean_array_get_size(v_alts_356_);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_dec_le(v___x_371_, v___x_372_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_nat_dec_lt(v___x_410_, v___x_371_);
if (v___x_411_ == 0)
{
v___y_374_ = v___x_409_;
goto v___jp_373_;
}
else
{
if (v___x_411_ == 0)
{
v___y_374_ = v___x_409_;
goto v___jp_373_;
}
else
{
size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; 
v___x_412_ = ((size_t)0ULL);
v___x_413_ = lean_usize_of_nat(v___x_371_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__2(v___x_371_, v_alts_356_, v___x_412_, v___x_413_);
v___y_374_ = v___x_414_;
goto v___jp_373_;
}
}
}
else
{
v___y_374_ = v___x_409_;
goto v___jp_373_;
}
v___jp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_368_, 0, v___y_367_);
v___x_369_ = lean_array_push(v___y_366_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
v___jp_373_:
{
if (v___y_374_ == 0)
{
lean_object* v___x_375_; lean_object* v_fst_376_; lean_object* v_snd_377_; uint8_t v___x_378_; 
v___x_375_ = l___private_Lean_Compiler_LCNF_Simp_DefaultAlt_0__Lean_Compiler_LCNF_Simp_getMaxOccs(v_alts_356_);
v_fst_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_fst_376_);
v_snd_377_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_snd_377_);
lean_dec_ref(v___x_375_);
v___x_378_ = lean_nat_dec_eq(v_snd_377_, v___x_372_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_358_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; size_t v_sz_381_; size_t v___x_382_; lean_object* v___x_383_; 
lean_dec_ref(v___x_379_);
v___x_380_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_addDefaultAlt___closed__1));
v_sz_381_ = lean_array_size(v_alts_356_);
v___x_382_ = ((size_t)0ULL);
lean_inc(v_fst_376_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_addDefaultAlt_spec__1(v_snd_377_, v_fst_376_, v_alts_356_, v_sz_381_, v___x_382_, v___x_380_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec_ref(v_alts_356_);
lean_dec(v_snd_377_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
switch(lean_obj_tag(v_fst_376_))
{
case 0:
{
lean_object* v_fst_385_; lean_object* v_code_386_; 
v_fst_385_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_fst_385_);
lean_dec(v_a_384_);
v_code_386_ = lean_ctor_get(v_fst_376_, 2);
lean_inc_ref(v_code_386_);
lean_dec_ref(v_fst_376_);
v___y_366_ = v_fst_385_;
v___y_367_ = v_code_386_;
goto v___jp_365_;
}
case 1:
{
lean_object* v_fst_387_; lean_object* v_code_388_; 
v_fst_387_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_fst_387_);
lean_dec(v_a_384_);
v_code_388_ = lean_ctor_get(v_fst_376_, 1);
lean_inc_ref(v_code_388_);
lean_dec_ref(v_fst_376_);
v___y_366_ = v_fst_387_;
v___y_367_ = v_code_388_;
goto v___jp_365_;
}
default: 
{
lean_object* v_fst_389_; lean_object* v_code_390_; 
v_fst_389_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_fst_389_);
lean_dec(v_a_384_);
v_code_390_ = lean_ctor_get(v_fst_376_, 0);
lean_inc_ref(v_code_390_);
lean_dec_ref(v_fst_376_);
v___y_366_ = v_fst_389_;
v___y_367_ = v_code_390_;
goto v___jp_365_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_fst_376_);
v_a_391_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_383_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_383_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_snd_377_);
lean_dec(v_fst_376_);
lean_dec_ref(v_alts_356_);
v_a_399_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_379_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_379_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_407_; 
lean_dec(v_snd_377_);
lean_dec(v_fst_376_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_alts_356_);
return v___x_407_;
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_alts_356_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt___boxed(lean_object* v_alts_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(v_alts_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_424_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
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
