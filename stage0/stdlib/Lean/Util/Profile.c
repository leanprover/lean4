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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "profiler"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 199, 104, 147, 160, 34, 129, 33)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "show exclusive execution times of various Lean components\n\nSee also `trace.profiler` for an alternative profiling system with structured output."};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 106, 196, 159, 114, 195, 161, 8)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profiler;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 199, 104, 147, 160, 34, 129, 33)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 19, 199, 178, 13, 14, 236, 251)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "threshold in milliseconds, profiling times under threshold will not be reported individually"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 106, 196, 159, 114, 195, 161, 8)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 166, 34, 176, 223, 145, 160, 245)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_));
v___x_55_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(lean_object* v_name_58_, lean_object* v_decl_59_, lean_object* v_ref_60_){
_start:
{
lean_object* v_defValue_62_; lean_object* v_descr_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_89_; 
v_defValue_62_ = lean_ctor_get(v_decl_59_, 0);
v_descr_63_ = lean_ctor_get(v_decl_59_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_decl_59_);
if (v_isSharedCheck_89_ == 0)
{
v___x_65_ = v_decl_59_;
v_isShared_66_ = v_isSharedCheck_89_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_descr_63_);
lean_inc(v_defValue_62_);
lean_dec(v_decl_59_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_89_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc(v_defValue_62_);
v___x_67_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_67_, 0, v_defValue_62_);
lean_inc(v_name_58_);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v_name_58_);
lean_ctor_set(v___x_68_, 1, v_ref_60_);
lean_ctor_set(v___x_68_, 2, v___x_67_);
lean_ctor_set(v___x_68_, 3, v_descr_63_);
lean_inc(v_name_58_);
v___x_69_ = lean_register_option(v_name_58_, v___x_68_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v___x_69_, 0);
lean_dec(v_unused_80_);
v___x_71_ = v___x_69_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_dec(v___x_69_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_defValue_62_);
lean_ctor_set(v___x_65_, 0, v_name_58_);
v___x_74_ = v___x_65_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_name_58_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_defValue_62_);
v___x_74_ = v_reuseFailAlloc_78_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_76_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_74_);
v___x_76_ = v___x_71_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_del_object(v___x_65_);
lean_dec(v_defValue_62_);
lean_dec(v_name_58_);
v_a_81_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_69_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_69_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_90_, lean_object* v_decl_91_, lean_object* v_ref_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v_name_90_, v_decl_91_, v_ref_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_109_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_110_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_));
v___x_111_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object* v_opts_114_, lean_object* v_opt_115_){
_start:
{
lean_object* v_name_116_; lean_object* v_defValue_117_; lean_object* v_map_118_; lean_object* v___x_119_; 
v_name_116_ = lean_ctor_get(v_opt_115_, 0);
v_defValue_117_ = lean_ctor_get(v_opt_115_, 1);
v_map_118_ = lean_ctor_get(v_opts_114_, 0);
v___x_119_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_118_, v_name_116_);
if (lean_obj_tag(v___x_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = lean_unbox(v_defValue_117_);
return v___x_120_;
}
else
{
lean_object* v_val_121_; 
v_val_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_121_);
lean_dec_ref(v___x_119_);
if (lean_obj_tag(v_val_121_) == 1)
{
uint8_t v_v_122_; 
v_v_122_ = lean_ctor_get_uint8(v_val_121_, 0);
lean_dec_ref(v_val_121_);
return v_v_122_;
}
else
{
uint8_t v___x_123_; 
lean_dec(v_val_121_);
v___x_123_ = lean_unbox(v_defValue_117_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0___boxed(lean_object* v_opts_124_, lean_object* v_opt_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_opts_124_, v_opt_125_);
lean_dec_ref(v_opt_125_);
lean_dec_ref(v_opts_124_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t lean_get_profiler(lean_object* v_o_128_){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = l_Lean_profiler;
v___x_130_ = l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(v_o_128_, v___x_129_);
lean_dec_ref(v_o_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(lean_object* v_o_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = lean_get_profiler(v_o_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(lean_object* v_opts_134_, lean_object* v_opt_135_){
_start:
{
lean_object* v_name_136_; lean_object* v_defValue_137_; lean_object* v_map_138_; lean_object* v___x_139_; 
v_name_136_ = lean_ctor_get(v_opt_135_, 0);
v_defValue_137_ = lean_ctor_get(v_opt_135_, 1);
v_map_138_ = lean_ctor_get(v_opts_134_, 0);
v___x_139_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_138_, v_name_136_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_inc(v_defValue_137_);
return v_defValue_137_;
}
else
{
lean_object* v_val_140_; 
v_val_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v___x_139_);
if (lean_obj_tag(v_val_140_) == 3)
{
lean_object* v_v_141_; 
v_v_141_ = lean_ctor_get(v_val_140_, 0);
lean_inc(v_v_141_);
lean_dec_ref(v_val_140_);
return v_v_141_;
}
else
{
lean_dec(v_val_140_);
lean_inc(v_defValue_137_);
return v_defValue_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0___boxed(lean_object* v_opts_142_, lean_object* v_opt_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_opts_142_, v_opt_143_);
lean_dec_ref(v_opt_143_);
lean_dec_ref(v_opts_142_);
return v_res_144_;
}
}
static double _init_l_Lean_profiler_threshold_getSecs___closed__0(void){
_start:
{
lean_object* v___x_145_; double v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(1000u);
v___x_146_ = lean_float_of_nat(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT double lean_get_profiler_threshold(lean_object* v_o_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; double v___x_150_; double v___x_151_; double v___x_152_; 
v___x_148_ = l_Lean_profiler_threshold;
v___x_149_ = l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_o_147_, v___x_148_);
lean_dec_ref(v_o_147_);
v___x_150_ = lean_float_of_nat(v___x_149_);
v___x_151_ = lean_float_once(&l_Lean_profiler_threshold_getSecs___closed__0, &l_Lean_profiler_threshold_getSecs___closed__0_once, _init_l_Lean_profiler_threshold_getSecs___closed__0);
v___x_152_ = lean_float_div(v___x_150_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_profiler_threshold_getSecs___boxed(lean_object* v_o_153_){
_start:
{
double v_res_154_; lean_object* v_r_155_; 
v_res_154_ = lean_get_profiler_threshold(v_o_153_);
v_r_155_ = lean_box_float(v_res_154_);
return v_r_155_;
}
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
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0(lean_object* v_act_167_){
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
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(lean_object* v_act_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_profileitIOUnsafe___redArg___lam__0(v_act_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___lam__1(lean_object* v___f_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_unsafeBaseIO___redArg(v___f_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object* v_category_192_, lean_object* v_opts_193_, lean_object* v_act_194_, lean_object* v_decl_195_){
_start:
{
lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_199_; 
v___f_197_ = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_197_, 0, v_act_194_);
v___f_198_ = lean_alloc_closure((void*)(l_Lean_profileitIOUnsafe___redArg___lam__1), 2, 1);
lean_closure_set(v___f_198_, 0, v___f_197_);
v___x_199_ = lean_profileit(v_category_192_, v_opts_193_, v___f_198_, v_decl_195_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 1);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_208_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_199_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_199_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 0);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___redArg___boxed(lean_object* v_category_216_, lean_object* v_opts_217_, lean_object* v_act_218_, lean_object* v_decl_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_profileitIOUnsafe___redArg(v_category_216_, v_opts_217_, v_act_218_, v_decl_219_);
lean_dec_ref(v_opts_217_);
lean_dec_ref(v_category_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe(lean_object* v_00_u03b5_222_, lean_object* v_00_u03b1_223_, lean_object* v_category_224_, lean_object* v_opts_225_, lean_object* v_act_226_, lean_object* v_decl_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_profileitIOUnsafe___redArg(v_category_224_, v_opts_225_, v_act_226_, v_decl_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitIOUnsafe___boxed(lean_object* v_00_u03b5_230_, lean_object* v_00_u03b1_231_, lean_object* v_category_232_, lean_object* v_opts_233_, lean_object* v_act_234_, lean_object* v_decl_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_profileitIOUnsafe(v_00_u03b5_230_, v_00_u03b1_231_, v_category_232_, v_opts_233_, v_act_234_, v_decl_235_);
lean_dec_ref(v_opts_233_);
lean_dec_ref(v_category_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0(lean_object* v_category_238_, lean_object* v_opts_239_, lean_object* v_decl_240_, lean_object* v_00_u03b2_241_, lean_object* v_act_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_profileitIOUnsafe___redArg(v_category_238_, v_opts_239_, v_act_242_, v_decl_240_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg___lam__0___boxed(lean_object* v_category_245_, lean_object* v_opts_246_, lean_object* v_decl_247_, lean_object* v_00_u03b2_248_, lean_object* v_act_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_profileitM___redArg___lam__0(v_category_245_, v_opts_246_, v_decl_247_, v_00_u03b2_248_, v_act_249_);
lean_dec_ref(v_opts_246_);
lean_dec_ref(v_category_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___redArg(lean_object* v_inst_252_, lean_object* v_category_253_, lean_object* v_opts_254_, lean_object* v_act_255_, lean_object* v_decl_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; 
v___f_257_ = lean_alloc_closure((void*)(l_Lean_profileitM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_257_, 0, v_category_253_);
lean_closure_set(v___f_257_, 1, v_opts_254_);
lean_closure_set(v___f_257_, 2, v_decl_256_);
v___x_258_ = lean_apply_3(v_inst_252_, lean_box(0), v___f_257_, v_act_255_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM(lean_object* v_m_259_, lean_object* v_00_u03b5_260_, lean_object* v_inst_261_, lean_object* v_00_u03b1_262_, lean_object* v_category_263_, lean_object* v_opts_264_, lean_object* v_act_265_, lean_object* v_decl_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_profileitM___redArg(v_inst_261_, v_category_263_, v_opts_264_, v_act_265_, v_decl_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_displayCumulativeProfilingTimes___boxed(lean_object* v_a_00___x40___internal___hyg_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = lean_display_cumulative_profiling_times();
return v_res_270_;
}
}
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Profile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_profiler);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
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
