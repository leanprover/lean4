// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.PostprocessTraces.PostprocessTracesCommand
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.PostprocessTraces.PostprocessTracesCommand import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTracedCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtTracedCommand___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTracedCommand___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTracedCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtTracedCommand___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTracedCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTracedCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTracedCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPostprocessTracesCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtPostprocessTracesCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostprocessTraces"};
static const lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtPostprocessTracesCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "postprocessTracesCmd"};
static const lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 16, 235, 102, 51, 61, 86, 237)}};
static const lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtPostprocessTracesCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPostprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 122, 181, 109, 176, 167, 231, 12)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTracedCommand(lean_object* v_keywordTk_6_, lean_object* v_arg_7_, lean_object* v_inTk_8_, lean_object* v_cmd_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Fmt_fmt(v_keywordTk_6_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v___x_12_, 1);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_12_, 2);
v___x_15_ = l_Lean_Fmt_fmt(v_arg_7_, v_a_10_, v_a_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_15_, 2);
v___x_18_ = l_Lean_Fmt_fmt(v_inTk_8_, v_a_10_, v_a_17_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
v_a_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_18_, 2);
v___x_21_ = l_Lean_Fmt_fmt(v_cmd_9_, v_a_10_, v_a_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_38_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
v_a_23_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_38_ == 0)
{
v___x_25_ = v___x_21_;
v_isShared_26_ = v_isSharedCheck_38_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_inc(v_a_22_);
lean_dec(v___x_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_38_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_29_ = lean_array_push(v___x_28_, v_a_13_);
v___x_30_ = lean_array_push(v___x_29_, v_a_16_);
v___x_31_ = ((lean_object*)(l_Lean_Fmt_fmtTracedCommand___closed__0));
v___x_32_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_30_, v___x_31_);
v___x_33_ = ((lean_object*)(l_Lean_Fmt_fmtTracedCommand___closed__1));
v___x_34_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_32_, v_a_19_, v_a_22_, v___x_33_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_34_);
v___x_36_ = v___x_25_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_a_23_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_dec(v_a_19_);
lean_dec(v_a_16_);
lean_dec(v_a_13_);
return v___x_21_;
}
}
else
{
lean_dec(v_a_16_);
lean_dec(v_a_13_);
lean_dec(v_cmd_9_);
return v___x_18_;
}
}
else
{
lean_dec(v_a_13_);
lean_dec(v_cmd_9_);
lean_dec(v_inTk_8_);
return v___x_15_;
}
}
else
{
lean_dec(v_cmd_9_);
lean_dec(v_inTk_8_);
lean_dec(v_arg_7_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTracedCommand___boxed(lean_object* v_keywordTk_39_, lean_object* v_arg_40_, lean_object* v_inTk_41_, lean_object* v_cmd_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Fmt_fmtTracedCommand(v_keywordTk_39_, v_arg_40_, v_inTk_41_, v_cmd_42_, v_a_43_, v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd(lean_object* v_x_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3));
lean_inc(v_x_53_);
v___x_57_ = l_Lean_Syntax_isOfKind(v_x_53_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_x_53_);
v___x_58_ = l_Lean_Fmt_Error_partialFormatter;
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v_a_55_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v_postprocessTk_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_inTk_65_; lean_object* v___x_66_; lean_object* v_cmd_67_; lean_object* v___x_68_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v_postprocessTk_61_ = l_Lean_Syntax_getArg(v_x_53_, v___x_60_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = l_Lean_Syntax_getArg(v_x_53_, v___x_62_);
v___x_64_ = lean_unsigned_to_nat(2u);
v_inTk_65_ = l_Lean_Syntax_getArg(v_x_53_, v___x_64_);
v___x_66_ = lean_unsigned_to_nat(3u);
v_cmd_67_ = l_Lean_Syntax_getArg(v_x_53_, v___x_66_);
lean_dec(v_x_53_);
v___x_68_ = l_Lean_Fmt_fmtTracedCommand(v_postprocessTk_61_, v___x_63_, v_inTk_65_, v_cmd_67_, v_a_54_, v_a_55_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostprocessTracesCmd___boxed(lean_object* v_x_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Fmt_fmtPostprocessTracesCmd(v_x_69_, v_a_70_, v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1(){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_Fmt_fmtAttribute;
v___x_81_ = ((lean_object*)(l_Lean_Fmt_fmtPostprocessTracesCmd___closed__3));
v___x_82_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___closed__2));
v___x_83_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostprocessTracesCmd___boxed), 3, 0);
v___x_84_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_80_, v___x_81_, v___x_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1___boxed(lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1();
return v_res_86_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand_0__Lean_Fmt_fmtPostprocessTracesCmd___regBuiltin_Lean_Fmt_fmtPostprocessTracesCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
}
#ifdef __cplusplus
}
#endif
