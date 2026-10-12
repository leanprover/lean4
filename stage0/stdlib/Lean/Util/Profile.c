// Lean compiler output
// Module: Lean.Util.Profile
// Imports: public import Init.Data.OfScientific public import Lean.Data.Options
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "profiler"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 199, 104, 147, 160, 34, 129, 33)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "show exclusive execution times of various Lean components\n\nSee also `trace.profiler` for an alternative profiling system with structured output."};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 106, 196, 159, 114, 195, 161, 8)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 199, 104, 147, 160, 34, 129, 33)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 19, 199, 178, 13, 14, 236, 251)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "threshold in milliseconds, profiling times under threshold will not be reported individually"};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 106, 196, 159, 114, 195, 161, 8)}};
static const lean_ctor_object l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 166, 34, 176, 223, 145, 160, 245)}};
static const lean_object* l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler_threshold;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_get_profiler(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_profiler_threshold_getSecs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_profiler_threshold_getSecs___closed__0;
LEAN_EXPORT double lean_get_profiler_threshold(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
LEAN_EXPORT lean_object* l_Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_50_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_52_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v___x_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_53_;
v_res_53_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
return v_res_55_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(lean_object* v_name_56_, lean_object* v_decl_57_, lean_object* v_ref_58_){
_start:
{
lean_object* v_defValue_60_; lean_object* v_descr_61_; lean_object* v_deprecation_x3f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_defValue_60_ = lean_ctor_get(v_decl_57_, 0);
v_descr_61_ = lean_ctor_get(v_decl_57_, 1);
v_deprecation_x3f_62_ = lean_ctor_get(v_decl_57_, 2);
lean_inc(v_defValue_60_);
v___x_63_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_63_, 0, v_defValue_60_);
lean_inc(v_deprecation_x3f_62_);
lean_inc_ref(v_descr_61_);
lean_inc_n(v_name_56_, 2);
v___x_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_64_, 0, v_name_56_);
lean_ctor_set(v___x_64_, 1, v_ref_58_);
lean_ctor_set(v___x_64_, 2, v___x_63_);
lean_ctor_set(v___x_64_, 3, v_descr_61_);
lean_ctor_set(v___x_64_, 4, v_deprecation_x3f_62_);
v___x_65_ = lean_register_option(v_name_56_, v___x_64_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_73_; 
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v___x_65_, 0);
lean_dec(v_unused_74_);
v___x_67_ = v___x_65_;
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
else
{
lean_dec(v___x_65_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
lean_inc(v_defValue_60_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_name_56_);
lean_ctor_set(v___x_69_, 1, v_defValue_60_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_69_);
v___x_71_ = v___x_67_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_name_56_);
v_a_75_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_65_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_56_ = stack[0].m_obj;
lean_object* v_decl_57_ = stack[1].m_obj;
lean_object* v_ref_58_ = stack[2].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v_name_56_, v_decl_57_, v_ref_58_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_84_, lean_object* v_decl_85_, lean_object* v_ref_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v_name_84_, v_decl_85_, v_ref_86_);
lean_dec_ref(v_decl_85_);
return v_res_88_;
}
}
lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_104_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_105_ = ((lean_object*)(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_106_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v___x_103_, v___x_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_107_;
v_res_107_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
return v_res_109_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object* v_opts_110_, lean_object* v_opt_111_){
_start:
{
lean_object* v_name_112_; lean_object* v_defValue_113_; lean_object* v_map_114_; lean_object* v___x_115_; 
v_name_112_ = lean_ctor_get(v_opt_111_, 0);
v_defValue_113_ = lean_ctor_get(v_opt_111_, 1);
v_map_114_ = lean_ctor_get(v_opts_110_, 0);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_114_, v_name_112_);
if (lean_obj_tag(v___x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = lean_unbox(v_defValue_113_);
return v___x_116_;
}
else
{
lean_object* v_val_117_; 
v_val_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v___x_115_, 1);
if (lean_obj_tag(v_val_117_) == 1)
{
uint8_t v_v_118_; 
v_v_118_ = lean_ctor_get_uint8(v_val_117_, 0);
lean_dec_ref_known(v_val_117_, 0);
return v_v_118_;
}
else
{
uint8_t v___x_119_; 
lean_dec(v_val_117_);
v___x_119_ = lean_unbox(v_defValue_113_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_110_ = stack[0].m_obj;
lean_object* v_opt_111_ = stack[1].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_opts_110_, v_opt_111_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0___boxed(lean_object* v_opts_121_, lean_object* v_opt_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_opts_121_, v_opt_122_);
lean_dec_ref(v_opt_122_);
lean_dec_ref(v_opts_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
uint8_t lean_get_profiler(lean_object* v_o_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = l_Lean_profiler;
v___x_127_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_o_125_, v___x_126_);
lean_dec_ref(v_o_125_);
return v___x_127_;
}
}
LEAN_EXPORT void lean_get_profiler_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_125_ = stack[0].m_obj;
uint8_t v_res_128_;
v_res_128_ = lean_get_profiler(v_o_125_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object* v_o_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = lean_get_profiler(v_o_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(lean_object* v_opts_132_, lean_object* v_opt_133_){
_start:
{
lean_object* v_name_134_; lean_object* v_defValue_135_; lean_object* v_map_136_; lean_object* v___x_137_; 
v_name_134_ = lean_ctor_get(v_opt_133_, 0);
v_defValue_135_ = lean_ctor_get(v_opt_133_, 1);
v_map_136_ = lean_ctor_get(v_opts_132_, 0);
v___x_137_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_136_, v_name_134_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_inc(v_defValue_135_);
return v_defValue_135_;
}
else
{
lean_object* v_val_138_; 
v_val_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v___x_137_, 1);
if (lean_obj_tag(v_val_138_) == 3)
{
lean_object* v_v_139_; 
v_v_139_ = lean_ctor_get(v_val_138_, 0);
lean_inc(v_v_139_);
lean_dec_ref_known(v_val_138_, 1);
return v_v_139_;
}
else
{
lean_dec(v_val_138_);
lean_inc(v_defValue_135_);
return v_defValue_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0___boxed(lean_object* v_opts_140_, lean_object* v_opt_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_opts_140_, v_opt_141_);
lean_dec_ref(v_opt_141_);
lean_dec_ref(v_opts_140_);
return v_res_142_;
}
}
static double _init_l_Lean_profiler_threshold_getSecs___closed__0(void){
_start:
{
lean_object* v___x_143_; double v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(1000u);
v___x_144_ = lean_float_of_nat(v___x_143_);
return v___x_144_;
}
}
double lean_get_profiler_threshold(lean_object* v_o_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; double v___x_148_; double v___x_149_; double v___x_150_; 
v___x_146_ = l_Lean_profiler_threshold;
v___x_147_ = l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_o_145_, v___x_146_);
lean_dec_ref(v_o_145_);
v___x_148_ = lean_float_of_nat(v___x_147_);
v___x_149_ = lean_float_once(&l_Lean_profiler_threshold_getSecs___closed__0, &l_Lean_profiler_threshold_getSecs___closed__0_once, _init_l_Lean_profiler_threshold_getSecs___closed__0);
v___x_150_ = lean_float_div(v___x_148_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT void lean_get_profiler_threshold_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_145_ = stack[0].m_obj;
double v_res_151_;
v_res_151_ = lean_get_profiler_threshold(v_o_145_);
stack->m_float
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object* v_o_152_){
_start:
{
double v_res_153_; lean_object* v_r_154_; 
v_res_153_ = lean_get_profiler_threshold(v_o_152_);
v_r_154_ = lean_box_float(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT void l_Lean_profileit_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_156_ = stack[1].m_obj;
lean_object* v_opts_157_ = stack[2].m_obj;
lean_object* v_fn_158_ = stack[3].m_obj;
lean_object* v_decl_159_ = stack[4].m_obj;
lean_object* v_res_160_;
v_res_160_ = lean_profileit(v_category_156_, v_opts_157_, v_fn_158_, v_decl_159_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lean_profileit___boxed(lean_object* v_00_u03b1_161_, lean_object* v_category_162_, lean_object* v_opts_163_, lean_object* v_fn_164_, lean_object* v_decl_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lean_profileit(v_category_162_, v_opts_163_, v_fn_164_, v_decl_165_);
lean_dec_ref(v_opts_163_);
lean_dec_ref(v_category_162_);
return v_res_166_;
}
}
lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0(lean_object* v_act_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_apply_1(v_act_167_, lean_box(0));
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 1);
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_a_178_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_169_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_169_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 0);
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_profileitIOUnsafe___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_167_ = stack[0].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_profileitIOUnsafe___redArg___lam__0(v_act_167_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(lean_object* v_act_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_profileitIOUnsafe___redArg___lam__0(v_act_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__1(lean_object* v___f_190_, lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_unsafeBaseIO___redArg(v___f_190_);
return v___x_192_;
}
}
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object* v_category_193_, lean_object* v_opts_194_, lean_object* v_act_195_, lean_object* v_decl_196_){
_start:
{
lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; 
v___f_198_ = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_198_, 0, v_act_195_);
v___f_199_ = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___redArg___lam__1), 2, 1);
lean_closure_set(v___f_199_, 0, v___f_198_);
v___x_200_ = lean_profileit(v_category_193_, v_opts_194_, v___f_199_, v_decl_196_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 1);
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_200_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_200_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set_tag(v___x_211_, 0);
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_profileitIOUnsafe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_193_ = stack[0].m_obj;
lean_object* v_opts_194_ = stack[1].m_obj;
lean_object* v_act_195_ = stack[2].m_obj;
lean_object* v_decl_196_ = stack[3].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_profileitIOUnsafe___redArg(v_category_193_, v_opts_194_, v_act_195_, v_decl_196_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___boxed(lean_object* v_category_218_, lean_object* v_opts_219_, lean_object* v_act_220_, lean_object* v_decl_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_profileitIOUnsafe___redArg(v_category_218_, v_opts_219_, v_act_220_, v_decl_221_);
lean_dec_ref(v_opts_219_);
lean_dec_ref(v_category_218_);
return v_res_223_;
}
}
lean_object* l_Lean_profileitIOUnsafe(lean_object* v_00_u03b5_224_, lean_object* v_00_u03b1_225_, lean_object* v_category_226_, lean_object* v_opts_227_, lean_object* v_act_228_, lean_object* v_decl_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_profileitIOUnsafe___redArg(v_category_226_, v_opts_227_, v_act_228_, v_decl_229_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_profileitIOUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_226_ = stack[2].m_obj;
lean_object* v_opts_227_ = stack[3].m_obj;
lean_object* v_act_228_ = stack[4].m_obj;
lean_object* v_decl_229_ = stack[5].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_profileitIOUnsafe(lean_box(0), lean_box(0), v_category_226_, v_opts_227_, v_act_228_, v_decl_229_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___boxed(lean_object* v_00_u03b5_233_, lean_object* v_00_u03b1_234_, lean_object* v_category_235_, lean_object* v_opts_236_, lean_object* v_act_237_, lean_object* v_decl_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_profileitIOUnsafe(v_00_u03b5_233_, v_00_u03b1_234_, v_category_235_, v_opts_236_, v_act_237_, v_decl_238_);
lean_dec_ref(v_opts_236_);
lean_dec_ref(v_category_235_);
return v_res_240_;
}
}
lean_object* l_Lean_profileitM___redArg___lam__0(lean_object* v_category_241_, lean_object* v_opts_242_, lean_object* v_decl_243_, lean_object* v_00_u03b2_244_, lean_object* v_act_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_profileitIOUnsafe___redArg(v_category_241_, v_opts_242_, v_act_245_, v_decl_243_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_profileitM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_241_ = stack[0].m_obj;
lean_object* v_opts_242_ = stack[1].m_obj;
lean_object* v_decl_243_ = stack[2].m_obj;
lean_object* v_act_245_ = stack[4].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_profileitM___redArg___lam__0(v_category_241_, v_opts_242_, v_decl_243_, lean_box(0), v_act_245_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0___boxed(lean_object* v_category_249_, lean_object* v_opts_250_, lean_object* v_decl_251_, lean_object* v_00_u03b2_252_, lean_object* v_act_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_profileitM___redArg___lam__0(v_category_249_, v_opts_250_, v_decl_251_, v_00_u03b2_252_, v_act_253_);
lean_dec_ref(v_opts_250_);
lean_dec_ref(v_category_249_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg(lean_object* v_inst_256_, lean_object* v_category_257_, lean_object* v_opts_258_, lean_object* v_act_259_, lean_object* v_decl_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; 
v___f_261_ = lean_alloc_closure((void*)(l_Lean_profileitM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_261_, 0, v_category_257_);
lean_closure_set(v___f_261_, 1, v_opts_258_);
lean_closure_set(v___f_261_, 2, v_decl_260_);
v___x_262_ = lean_apply_3(v_inst_256_, lean_box(0), v___f_261_, v_act_259_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object* v_m_263_, lean_object* v_00_u03b5_264_, lean_object* v_inst_265_, lean_object* v_00_u03b1_266_, lean_object* v_category_267_, lean_object* v_opts_268_, lean_object* v_act_269_, lean_object* v_decl_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_profileitM___redArg(v_inst_265_, v_category_267_, v_opts_268_, v_act_269_, v_decl_270_);
return v___x_271_;
}
}
LEAN_EXPORT void l_Lean_displayCumulativeProfilingTimes_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_273_;
v_res_273_ = lean_display_cumulative_profiling_times();
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_displayCumulativeProfilingTimes___boxed(lean_object* v_a_00___x40___internal___hyg_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = lean_display_cumulative_profiling_times();
return v_res_275_;
}
}
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler);
lean_dec_ref(res);
res = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler_threshold);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Profile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Profile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Profile(builtin);
}
#ifdef __cplusplus
}
#endif
