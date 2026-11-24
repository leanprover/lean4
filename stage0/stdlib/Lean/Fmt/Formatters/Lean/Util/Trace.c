// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Util.Trace
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Util.Trace import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTraceTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtTraceTerm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTraceTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTraceTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTraceTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoElemTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtDoElemTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doElemTrace[_]__"};
static const lean_object* l_Lean_Fmt_fmtDoElemTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTrace___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 144, 171, 160, 60, 151, 54, 39)}};
static const lean_object* l_Lean_Fmt_fmtDoElemTrace___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtDoElemTrace___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtDoElemTrace___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtDoElemTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(14, 219, 82, 67, 190, 62, 51, 32)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTraceTerm(lean_object* v_keyword_4_, lean_object* v_msg_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Fmt_fmt(v_msg_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_23_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_a_10_ = lean_ctor_get(v___x_8_, 1);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_23_ == 0)
{
v___x_12_ = v___x_8_;
v_isShared_13_ = v_isSharedCheck_23_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_23_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_14_ = lean_unsigned_to_nat(2u);
v___x_15_ = lean_mk_empty_array_with_capacity(v___x_14_);
v___x_16_ = lean_array_push(v___x_15_, v_keyword_4_);
v___x_17_ = lean_array_push(v___x_16_, v_a_9_);
v___x_18_ = ((lean_object*)(l_Lean_Fmt_fmtTraceTerm___closed__0));
v___x_19_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_17_, v___x_18_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_19_);
v___x_21_ = v___x_12_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_a_10_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
else
{
lean_dec_ref(v_keyword_4_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTraceTerm___boxed(lean_object* v_keyword_24_, lean_object* v_msg_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Fmt_fmtTraceTerm(v_keyword_24_, v_msg_25_, v_a_26_, v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTrace(lean_object* v_x_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemTrace___closed__2));
lean_inc(v_x_37_);
v___x_41_ = l_Lean_Syntax_isOfKind(v_x_37_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_x_37_);
v___x_42_ = l_Lean_Fmt_Error_partialFormatter;
v___x_43_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v_a_39_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = l_Lean_Syntax_getArg(v_x_37_, v___x_44_);
v___x_46_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemTrace___closed__4));
lean_inc(v___x_45_);
v___x_47_ = l_Lean_Syntax_isOfKind(v___x_45_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v___x_45_);
lean_dec(v_x_37_);
v___x_48_ = l_Lean_Fmt_Error_partialFormatter;
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v_a_39_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v_traceTk_51_; lean_object* v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v_traceTk_51_ = l_Lean_Syntax_getArg(v_x_37_, v___x_50_);
v___x_52_ = l_Lean_Fmt_fmt(v_traceTk_51_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_52_, 2);
v___x_55_ = l_Lean_Fmt_fmt(v___x_45_, v_a_38_, v_a_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v_a_57_; lean_object* v___x_58_; lean_object* v_rbTk_59_; lean_object* v___x_60_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
v_a_57_ = lean_ctor_get(v___x_55_, 1);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_55_, 2);
v___x_58_ = lean_unsigned_to_nat(2u);
v_rbTk_59_ = l_Lean_Syntax_getArg(v_x_37_, v___x_58_);
v___x_60_ = l_Lean_Fmt_fmt(v_rbTk_59_, v_a_38_, v_a_57_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_60_, 2);
v___x_63_ = lean_unsigned_to_nat(3u);
v___x_64_ = l_Lean_Syntax_getArg(v_x_37_, v___x_63_);
lean_dec(v_x_37_);
v___x_65_ = 0;
v___x_66_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_66_, 0, v___x_65_);
lean_ctor_set_uint8(v___x_66_, 1, v___x_47_);
v___x_67_ = l_Lean_Fmt_Layouts_bracketed(v_a_53_, v_a_56_, v_a_61_, v___x_66_);
v___x_68_ = l_Lean_Fmt_fmtTraceTerm(v___x_67_, v___x_64_, v_a_38_, v_a_62_);
return v___x_68_;
}
else
{
lean_dec(v_a_56_);
lean_dec(v_a_53_);
lean_dec(v_x_37_);
return v___x_60_;
}
}
else
{
lean_dec(v_a_53_);
lean_dec(v_x_37_);
return v___x_55_;
}
}
else
{
lean_dec(v___x_45_);
lean_dec(v_x_37_);
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemTrace___boxed(lean_object* v_x_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Fmt_fmtDoElemTrace(v_x_69_, v_a_70_, v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1(){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_Fmt_fmtAttribute;
v___x_81_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemTrace___closed__2));
v___x_82_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___closed__2));
v___x_83_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoElemTrace___boxed), 3, 0);
v___x_84_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_80_, v___x_81_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1___boxed(lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1();
return v_res_86_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Util_Trace_0__Lean_Fmt_fmtDoElemTrace___regBuiltin_Lean_Fmt_fmtDoElemTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
}
#ifdef __cplusplus
}
#endif
