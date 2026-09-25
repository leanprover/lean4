// Lean compiler output
// Module: Lake.Util.Cli
// Imports: public import Init.Data.String.TakeDrop public import Init.Data.String.Search public import Init.Data.String.Length
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
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ArgsT_run_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArgsT_run_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArgsT_run_x27___redArg___closed__0 = (const lean_object*)&l_Lake_ArgsT_run_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setArgs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_takeArg_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_takeArg_x3f___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_takeArg_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_takeArg_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_takeArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_takeArgs___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_takeArgs___redArg___closed__0 = (const lean_object*)&l_Lake_takeArgs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_shortOptionWithSpace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_shortOptionWithSpace___redArg___closed__0 = (const lean_object*)&l_Lake_shortOptionWithSpace___redArg___closed__0_value;
static lean_once_cell_t l_Lake_shortOptionWithSpace___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_shortOptionWithSpace___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__1(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_collectArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_collectArgs___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_collectArgs___redArg___closed__0 = (const lean_object*)&l_Lake_collectArgs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object*, lean_object*);
static const lean_array_object l_Lake_processOptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_processOptions___redArg___closed__0 = (const lean_object*)&l_Lake_processOptions___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk(lean_object* v_args_1_){
_start:
{
lean_inc(v_args_1_);
return v_args_1_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgList_mk___boxed(lean_object* v_args_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Lake_ArgList_mk(v_args_2_);
lean_dec(v_args_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run___redArg(lean_object* v_args_4_, lean_object* v_self_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_1(v_self_5_, v_args_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run(lean_object* v_m_7_, lean_object* v_00_u03b1_8_, lean_object* v_args_9_, lean_object* v_self_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_apply_1(v_self_10_, v_args_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0(lean_object* v_x_12_){
_start:
{
lean_object* v_fst_13_; 
v_fst_13_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_fst_13_);
return v_fst_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_ArgsT_run_x27___redArg___lam__0(v_x_14_);
lean_dec_ref(v_x_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg(lean_object* v_inst_17_, lean_object* v_args_18_, lean_object* v_self_19_){
_start:
{
lean_object* v_map_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_map_20_ = lean_ctor_get(v_inst_17_, 0);
lean_inc(v_map_20_);
lean_dec_ref(v_inst_17_);
v___f_21_ = ((lean_object*)(l_Lake_ArgsT_run_x27___redArg___closed__0));
v___x_22_ = lean_apply_1(v_self_19_, v_args_18_);
v___x_23_ = lean_apply_4(v_map_20_, lean_box(0), lean_box(0), v___f_21_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27(lean_object* v_m_24_, lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_args_27_, lean_object* v_self_28_){
_start:
{
lean_object* v_map_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_map_29_ = lean_ctor_get(v_inst_26_, 0);
lean_inc(v_map_29_);
lean_dec_ref(v_inst_26_);
v___f_30_ = ((lean_object*)(l_Lake_ArgsT_run_x27___redArg___closed__0));
v___x_31_ = lean_apply_1(v_self_28_, v_args_27_);
v___x_32_ = lean_apply_4(v_map_29_, lean_box(0), lean_box(0), v___f_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg(lean_object* v_inst_33_){
_start:
{
lean_object* v_get_34_; 
v_get_34_ = lean_ctor_get(v_inst_33_, 0);
lean_inc(v_get_34_);
return v_get_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg___boxed(lean_object* v_inst_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lake_getArgs___redArg(v_inst_35_);
lean_dec_ref(v_inst_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs(lean_object* v_m_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_get_39_; 
v_get_39_ = lean_ctor_get(v_inst_38_, 0);
lean_inc(v_get_39_);
return v_get_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___boxed(lean_object* v_m_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lake_getArgs(v_m_40_, v_inst_41_);
lean_dec_ref(v_inst_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_setArgs___redArg(lean_object* v_inst_43_, lean_object* v_args_44_){
_start:
{
lean_object* v_set_45_; lean_object* v___x_46_; 
v_set_45_ = lean_ctor_get(v_inst_43_, 1);
lean_inc(v_set_45_);
lean_dec_ref(v_inst_43_);
v___x_46_ = lean_apply_1(v_set_45_, v_args_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_setArgs(lean_object* v_m_47_, lean_object* v_inst_48_, lean_object* v_args_49_){
_start:
{
lean_object* v_set_50_; lean_object* v___x_51_; 
v_set_50_ = lean_ctor_get(v_inst_48_, 1);
lean_inc(v_set_50_);
lean_dec_ref(v_inst_48_);
v___x_51_ = lean_apply_1(v_set_50_, v_args_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg___lam__0(lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_box(0);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_x_52_);
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_head_55_ = lean_ctor_get(v_x_52_, 0);
v_tail_56_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v_x_52_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_head_55_);
lean_dec(v_x_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v_head_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 0);
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_tail_56_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg(lean_object* v_inst_66_){
_start:
{
lean_object* v_modifyGet_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
v_modifyGet_67_ = lean_ctor_get(v_inst_66_, 2);
lean_inc(v_modifyGet_67_);
lean_dec_ref(v_inst_66_);
v___f_68_ = ((lean_object*)(l_Lake_takeArg_x3f___redArg___closed__0));
v___x_69_ = lean_apply_2(v_modifyGet_67_, lean_box(0), v___f_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f(lean_object* v_m_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v_modifyGet_72_; lean_object* v___f_73_; lean_object* v___x_74_; 
v_modifyGet_72_ = lean_ctor_get(v_inst_71_, 2);
lean_inc(v_modifyGet_72_);
lean_dec_ref(v_inst_71_);
v___f_73_ = ((lean_object*)(l_Lake_takeArg_x3f___redArg___closed__0));
v___x_74_ = lean_apply_2(v_modifyGet_72_, lean_box(0), v___f_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg___lam__0(lean_object* v_default_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v_default_75_);
lean_ctor_set(v___x_77_, 1, v_x_76_);
return v___x_77_;
}
else
{
lean_object* v_head_78_; lean_object* v_tail_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
lean_dec_ref(v_default_75_);
v_head_78_ = lean_ctor_get(v_x_76_, 0);
v_tail_79_ = lean_ctor_get(v_x_76_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v_x_76_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_tail_79_);
lean_inc(v_head_78_);
lean_dec(v_x_76_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 0);
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_head_78_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_tail_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg(lean_object* v_inst_87_, lean_object* v_default_88_){
_start:
{
lean_object* v_modifyGet_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
v_modifyGet_89_ = lean_ctor_get(v_inst_87_, 2);
lean_inc(v_modifyGet_89_);
lean_dec_ref(v_inst_87_);
v___f_90_ = lean_alloc_closure((void*)(l_Lake_takeArgD___redArg___lam__0), 2, 1);
lean_closure_set(v___f_90_, 0, v_default_88_);
v___x_91_ = lean_apply_2(v_modifyGet_89_, lean_box(0), v___f_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD(lean_object* v_m_92_, lean_object* v_inst_93_, lean_object* v_default_94_){
_start:
{
lean_object* v_modifyGet_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
v_modifyGet_95_ = lean_ctor_get(v_inst_93_, 2);
lean_inc(v_modifyGet_95_);
lean_dec_ref(v_inst_93_);
v___f_96_ = lean_alloc_closure((void*)(l_Lake_takeArgD___redArg___lam__0), 2, 1);
lean_closure_set(v___f_96_, 0, v_default_94_);
v___x_97_ = lean_apply_2(v_modifyGet_95_, lean_box(0), v___f_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg___lam__0(lean_object* v_args_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_args_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg(lean_object* v_inst_102_){
_start:
{
lean_object* v_modifyGet_103_; lean_object* v___f_104_; lean_object* v___x_105_; 
v_modifyGet_103_ = lean_ctor_get(v_inst_102_, 2);
lean_inc(v_modifyGet_103_);
lean_dec_ref(v_inst_102_);
v___f_104_ = ((lean_object*)(l_Lake_takeArgs___redArg___closed__0));
v___x_105_ = lean_apply_2(v_modifyGet_103_, lean_box(0), v___f_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs(lean_object* v_m_106_, lean_object* v_inst_107_){
_start:
{
lean_object* v_modifyGet_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_modifyGet_108_ = lean_ctor_get(v_inst_107_, 2);
lean_inc(v_modifyGet_108_);
lean_dec_ref(v_inst_107_);
v___f_109_ = ((lean_object*)(l_Lake_takeArgs___redArg___closed__0));
v___x_110_ = lean_apply_2(v_modifyGet_108_, lean_box(0), v___f_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg___redArg___lam__0(lean_object* v_arg_111_, lean_object* v_s_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v_arg_111_);
lean_ctor_set(v___x_114_, 1, v_s_112_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg___redArg(lean_object* v_inst_116_, lean_object* v_arg_117_){
_start:
{
lean_object* v_modifyGet_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_modifyGet_118_ = lean_ctor_get(v_inst_116_, 2);
lean_inc(v_modifyGet_118_);
lean_dec_ref(v_inst_116_);
v___f_119_ = lean_alloc_closure((void*)(l_Lake_consArg___redArg___lam__0), 2, 1);
lean_closure_set(v___f_119_, 0, v_arg_117_);
v___x_120_ = lean_apply_2(v_modifyGet_118_, lean_box(0), v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg(lean_object* v_m_121_, lean_object* v_inst_122_, lean_object* v_arg_123_){
_start:
{
lean_object* v_modifyGet_124_; lean_object* v___f_125_; lean_object* v___x_126_; 
v_modifyGet_124_ = lean_ctor_get(v_inst_122_, 2);
lean_inc(v_modifyGet_124_);
lean_dec_ref(v_inst_122_);
v___f_125_ = lean_alloc_closure((void*)(l_Lake_consArg___redArg___lam__0), 2, 1);
lean_closure_set(v___f_125_, 0, v_arg_123_);
v___x_126_ = lean_apply_2(v_modifyGet_124_, lean_box(0), v___f_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0(lean_object* v_opt_127_, lean_object* v_handle_128_, lean_object* v_____r_129_){
_start:
{
lean_object* v___x_130_; uint32_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_string_utf8_get(v_opt_127_, v___x_130_);
v___x_132_ = lean_box_uint32(v___x_131_);
v___x_133_ = lean_apply_1(v_handle_128_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0___boxed(lean_object* v_opt_134_, lean_object* v_handle_135_, lean_object* v_____r_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_shortOptionWithEq___redArg___lam__0(v_opt_134_, v_handle_135_, v_____r_136_);
lean_dec_ref(v_opt_134_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__1(lean_object* v___x_138_, lean_object* v_s_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v_s_139_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg(lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_handle_145_, lean_object* v_opt_146_){
_start:
{
lean_object* v_toBind_147_; lean_object* v___x_148_; lean_object* v_modifyGet_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_164_; 
v_toBind_147_ = lean_ctor_get(v_inst_143_, 1);
lean_inc(v_toBind_147_);
lean_dec_ref(v_inst_143_);
v___x_148_ = lean_string_utf8_byte_size(v_opt_146_);
v_modifyGet_149_ = lean_ctor_get(v_inst_144_, 2);
v_isSharedCheck_164_ = !lean_is_exclusive(v_inst_144_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; lean_object* v_unused_166_; 
v_unused_165_ = lean_ctor_get(v_inst_144_, 1);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_inst_144_, 0);
lean_dec(v_unused_166_);
v___x_151_ = v_inst_144_;
v_isShared_152_ = v_isSharedCheck_164_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_modifyGet_149_);
lean_dec(v_inst_144_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_164_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_146_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 2, v___x_148_);
lean_ctor_set(v___x_151_, 1, v___x_153_);
lean_ctor_set(v___x_151_, 0, v_opt_146_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_opt_146_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v___x_148_);
v___x_155_ = v_reuseFailAlloc_163_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_inc_ref(v_opt_146_);
v___f_156_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_156_, 0, v_opt_146_);
lean_closure_set(v___f_156_, 1, v_handle_145_);
v___x_157_ = lean_unsigned_to_nat(3u);
v___x_158_ = l_String_Slice_Pos_nextn(v___x_155_, v___x_153_, v___x_157_);
lean_dec_ref(v___x_155_);
v___x_159_ = lean_string_utf8_extract_fast(v_opt_146_, v___x_158_, v___x_148_);
lean_dec(v___x_158_);
lean_dec_ref(v_opt_146_);
v___f_160_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_160_, 0, v___x_159_);
v___x_161_ = lean_apply_2(v_modifyGet_149_, lean_box(0), v___f_160_);
v___x_162_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v___x_161_, v___f_156_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq(lean_object* v_m_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_00_u03b1_170_, lean_object* v_handle_171_, lean_object* v_opt_172_){
_start:
{
lean_object* v_toBind_173_; lean_object* v___x_174_; lean_object* v_modifyGet_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_190_; 
v_toBind_173_ = lean_ctor_get(v_inst_168_, 1);
lean_inc(v_toBind_173_);
lean_dec_ref(v_inst_168_);
v___x_174_ = lean_string_utf8_byte_size(v_opt_172_);
v_modifyGet_175_ = lean_ctor_get(v_inst_169_, 2);
v_isSharedCheck_190_ = !lean_is_exclusive(v_inst_169_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_191_ = lean_ctor_get(v_inst_169_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_inst_169_, 0);
lean_dec(v_unused_192_);
v___x_177_ = v_inst_169_;
v_isShared_178_ = v_isSharedCheck_190_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_modifyGet_175_);
lean_dec(v_inst_169_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_190_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_172_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 2, v___x_174_);
lean_ctor_set(v___x_177_, 1, v___x_179_);
lean_ctor_set(v___x_177_, 0, v_opt_172_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_opt_172_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v___x_174_);
v___x_181_ = v_reuseFailAlloc_189_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref(v_opt_172_);
v___f_182_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_182_, 0, v_opt_172_);
lean_closure_set(v___f_182_, 1, v_handle_171_);
v___x_183_ = lean_unsigned_to_nat(3u);
v___x_184_ = l_String_Slice_Pos_nextn(v___x_181_, v___x_179_, v___x_183_);
lean_dec_ref(v___x_181_);
v___x_185_ = lean_string_utf8_extract_fast(v_opt_172_, v___x_184_, v___x_174_);
lean_dec(v___x_184_);
lean_dec_ref(v_opt_172_);
v___f_186_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_186_, 0, v___x_185_);
v___x_187_ = lean_apply_2(v_modifyGet_175_, lean_box(0), v___f_186_);
v___x_188_ = lean_apply_4(v_toBind_173_, lean_box(0), lean_box(0), v___x_187_, v___f_182_);
return v___x_188_;
}
}
}
}
static lean_object* _init_l_Lake_shortOptionWithSpace___redArg___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_195_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace___redArg(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_handle_198_, lean_object* v_opt_199_){
_start:
{
lean_object* v_toBind_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_modifyGet_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_221_; 
v_toBind_200_ = lean_ctor_get(v_inst_196_, 1);
lean_inc(v_toBind_200_);
lean_dec_ref(v_inst_196_);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_string_utf8_byte_size(v_opt_199_);
lean_inc_ref(v_opt_199_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v_opt_199_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_205_ = lean_ctor_get(v_inst_197_, 2);
v_isSharedCheck_221_ = !lean_is_exclusive(v_inst_197_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; 
v_unused_222_ = lean_ctor_get(v_inst_197_, 1);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_inst_197_, 0);
lean_dec(v_unused_223_);
v___x_207_ = v_inst_197_;
v_isShared_208_ = v_isSharedCheck_221_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_modifyGet_205_);
lean_dec(v_inst_197_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_221_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v___x_213_; 
v___x_209_ = lean_unsigned_to_nat(2u);
v___x_210_ = l_String_Slice_Pos_nextn(v___x_203_, v___x_201_, v___x_209_);
lean_dec_ref_known(v___x_203_, 3);
lean_inc_ref_n(v_opt_199_, 2);
v___f_211_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_211_, 0, v_opt_199_);
lean_closure_set(v___f_211_, 1, v_handle_198_);
lean_inc(v___x_210_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v___x_202_);
lean_ctor_set(v___x_207_, 1, v___x_210_);
lean_ctor_set(v___x_207_, 0, v_opt_199_);
v___x_213_ = v___x_207_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_opt_199_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v___x_202_);
v___x_213_ = v_reuseFailAlloc_220_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_214_ = l_String_Slice_Pos_skipWhile___redArg(v___x_213_, v___x_201_, v___x_204_);
lean_dec_ref(v___x_213_);
v___x_215_ = lean_nat_add(v___x_210_, v___x_214_);
lean_dec(v___x_214_);
lean_dec(v___x_210_);
v___x_216_ = lean_string_utf8_extract_fast(v_opt_199_, v___x_215_, v___x_202_);
lean_dec(v___x_215_);
lean_dec_ref(v_opt_199_);
v___f_217_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_217_, 0, v___x_216_);
v___x_218_ = lean_apply_2(v_modifyGet_205_, lean_box(0), v___f_217_);
v___x_219_ = lean_apply_4(v_toBind_200_, lean_box(0), lean_box(0), v___x_218_, v___f_211_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object* v_m_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_00_u03b1_227_, lean_object* v_handle_228_, lean_object* v_opt_229_){
_start:
{
lean_object* v_toBind_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_modifyGet_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_251_; 
v_toBind_230_ = lean_ctor_get(v_inst_225_, 1);
lean_inc(v_toBind_230_);
lean_dec_ref(v_inst_225_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_string_utf8_byte_size(v_opt_229_);
lean_inc_ref(v_opt_229_);
v___x_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_233_, 0, v_opt_229_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
v___x_234_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_235_ = lean_ctor_get(v_inst_226_, 2);
v_isSharedCheck_251_ = !lean_is_exclusive(v_inst_226_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_252_ = lean_ctor_get(v_inst_226_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_inst_226_, 0);
lean_dec(v_unused_253_);
v___x_237_ = v_inst_226_;
v_isShared_238_ = v_isSharedCheck_251_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_modifyGet_235_);
lean_dec(v_inst_226_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_251_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___x_243_; 
v___x_239_ = lean_unsigned_to_nat(2u);
v___x_240_ = l_String_Slice_Pos_nextn(v___x_233_, v___x_231_, v___x_239_);
lean_dec_ref_known(v___x_233_, 3);
lean_inc_ref_n(v_opt_229_, 2);
v___f_241_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_241_, 0, v_opt_229_);
lean_closure_set(v___f_241_, 1, v_handle_228_);
lean_inc(v___x_240_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 2, v___x_232_);
lean_ctor_set(v___x_237_, 1, v___x_240_);
lean_ctor_set(v___x_237_, 0, v_opt_229_);
v___x_243_ = v___x_237_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_opt_229_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v___x_232_);
v___x_243_ = v_reuseFailAlloc_250_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_244_ = l_String_Slice_Pos_skipWhile___redArg(v___x_243_, v___x_231_, v___x_234_);
lean_dec_ref(v___x_243_);
v___x_245_ = lean_nat_add(v___x_240_, v___x_244_);
lean_dec(v___x_244_);
lean_dec(v___x_240_);
v___x_246_ = lean_string_utf8_extract_fast(v_opt_229_, v___x_245_, v___x_232_);
lean_dec(v___x_245_);
lean_dec_ref(v_opt_229_);
v___f_247_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_247_, 0, v___x_246_);
v___x_248_ = lean_apply_2(v_modifyGet_235_, lean_box(0), v___f_247_);
v___x_249_ = lean_apply_4(v_toBind_230_, lean_box(0), lean_box(0), v___x_248_, v___f_241_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_handle_256_, lean_object* v_opt_257_){
_start:
{
lean_object* v_toBind_258_; lean_object* v___x_259_; lean_object* v_modifyGet_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_275_; 
v_toBind_258_ = lean_ctor_get(v_inst_254_, 1);
lean_inc(v_toBind_258_);
lean_dec_ref(v_inst_254_);
v___x_259_ = lean_string_utf8_byte_size(v_opt_257_);
v_modifyGet_260_ = lean_ctor_get(v_inst_255_, 2);
v_isSharedCheck_275_ = !lean_is_exclusive(v_inst_255_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; 
v_unused_276_ = lean_ctor_get(v_inst_255_, 1);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_inst_255_, 0);
lean_dec(v_unused_277_);
v___x_262_ = v_inst_255_;
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_modifyGet_260_);
lean_dec(v_inst_255_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_257_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 2, v___x_259_);
lean_ctor_set(v___x_262_, 1, v___x_264_);
lean_ctor_set(v___x_262_, 0, v_opt_257_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_opt_257_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v___x_259_);
v___x_266_ = v_reuseFailAlloc_274_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___f_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_inc_ref(v_opt_257_);
v___f_267_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_267_, 0, v_opt_257_);
lean_closure_set(v___f_267_, 1, v_handle_256_);
v___x_268_ = lean_unsigned_to_nat(2u);
v___x_269_ = l_String_Slice_Pos_nextn(v___x_266_, v___x_264_, v___x_268_);
lean_dec_ref(v___x_266_);
v___x_270_ = lean_string_utf8_extract_fast(v_opt_257_, v___x_269_, v___x_259_);
lean_dec(v___x_269_);
lean_dec_ref(v_opt_257_);
v___f_271_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_271_, 0, v___x_270_);
v___x_272_ = lean_apply_2(v_modifyGet_260_, lean_box(0), v___f_271_);
v___x_273_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v___x_272_, v___f_267_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object* v_m_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_00_u03b1_281_, lean_object* v_handle_282_, lean_object* v_opt_283_){
_start:
{
lean_object* v_toBind_284_; lean_object* v___x_285_; lean_object* v_modifyGet_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_301_; 
v_toBind_284_ = lean_ctor_get(v_inst_279_, 1);
lean_inc(v_toBind_284_);
lean_dec_ref(v_inst_279_);
v___x_285_ = lean_string_utf8_byte_size(v_opt_283_);
v_modifyGet_286_ = lean_ctor_get(v_inst_280_, 2);
v_isSharedCheck_301_ = !lean_is_exclusive(v_inst_280_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_302_ = lean_ctor_get(v_inst_280_, 1);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_inst_280_, 0);
lean_dec(v_unused_303_);
v___x_288_ = v_inst_280_;
v_isShared_289_ = v_isSharedCheck_301_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_modifyGet_286_);
lean_dec(v_inst_280_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_301_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_283_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 2, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_290_);
lean_ctor_set(v___x_288_, 0, v_opt_283_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_opt_283_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v___x_285_);
v___x_292_ = v_reuseFailAlloc_300_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc_ref(v_opt_283_);
v___f_293_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_293_, 0, v_opt_283_);
lean_closure_set(v___f_293_, 1, v_handle_282_);
v___x_294_ = lean_unsigned_to_nat(2u);
v___x_295_ = l_String_Slice_Pos_nextn(v___x_292_, v___x_290_, v___x_294_);
lean_dec_ref(v___x_292_);
v___x_296_ = lean_string_utf8_extract_fast(v_opt_283_, v___x_295_, v___x_285_);
lean_dec(v___x_295_);
lean_dec_ref(v_opt_283_);
v___f_297_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_297_, 0, v___x_296_);
v___x_298_ = lean_apply_2(v_modifyGet_286_, lean_box(0), v___f_297_);
v___x_299_ = lean_apply_4(v_toBind_284_, lean_box(0), lean_box(0), v___x_298_, v___f_293_);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object* v_opt_304_, lean_object* v_p_305_, lean_object* v_inst_306_, lean_object* v_handle_307_, lean_object* v_____r_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(v_opt_304_, v_p_305_, v_inst_306_, v_handle_307_, v_____r_308_);
lean_dec(v_p_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(lean_object* v_inst_310_, lean_object* v_handle_311_, lean_object* v_opt_312_, lean_object* v_p_313_){
_start:
{
lean_object* v_toApplicative_314_; lean_object* v_toBind_315_; lean_object* v_toPure_316_; uint8_t v___x_317_; 
v_toApplicative_314_ = lean_ctor_get(v_inst_310_, 0);
v_toBind_315_ = lean_ctor_get(v_inst_310_, 1);
lean_inc(v_toBind_315_);
v_toPure_316_ = lean_ctor_get(v_toApplicative_314_, 1);
v___x_317_ = lean_string_utf8_at_end(v_opt_312_, v_p_313_);
if (v___x_317_ == 0)
{
lean_object* v___f_318_; uint32_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc(v_handle_311_);
lean_inc(v_p_313_);
lean_inc_ref(v_opt_312_);
v___f_318_ = lean_alloc_closure((void*)(l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_318_, 0, v_opt_312_);
lean_closure_set(v___f_318_, 1, v_p_313_);
lean_closure_set(v___f_318_, 2, v_inst_310_);
lean_closure_set(v___f_318_, 3, v_handle_311_);
v___x_319_ = lean_string_utf8_get_fast(v_opt_312_, v_p_313_);
lean_dec(v_p_313_);
lean_dec_ref(v_opt_312_);
v___x_320_ = lean_box_uint32(v___x_319_);
v___x_321_ = lean_apply_1(v_handle_311_, v___x_320_);
v___x_322_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v___x_321_, v___f_318_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_inc(v_toPure_316_);
lean_dec(v_toBind_315_);
lean_dec(v_p_313_);
lean_dec_ref(v_opt_312_);
lean_dec(v_handle_311_);
lean_dec_ref(v_inst_310_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_apply_2(v_toPure_316_, lean_box(0), v___x_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(lean_object* v_opt_325_, lean_object* v_p_326_, lean_object* v_inst_327_, lean_object* v_handle_328_, lean_object* v_____r_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_string_utf8_next_fast(v_opt_325_, v_p_326_);
v___x_331_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_327_, v_handle_328_, v_opt_325_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop(lean_object* v_m_332_, lean_object* v_inst_333_, lean_object* v_handle_334_, lean_object* v_opt_335_, lean_object* v_p_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_333_, v_handle_334_, v_opt_335_, v_p_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object* v_inst_338_, lean_object* v_handle_339_, lean_object* v_opt_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_338_, v_handle_339_, v_opt_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object* v_m_343_, lean_object* v_inst_344_, lean_object* v_handle_345_, lean_object* v_opt_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_344_, v_handle_345_, v_opt_346_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object* v_opt_349_, lean_object* v___y_350_, lean_object* v_handle_351_, lean_object* v_____r_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_string_utf8_extract_fast(v_opt_349_, v___x_353_, v___y_350_);
v___x_355_ = lean_apply_1(v_handle_351_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object* v_opt_356_, lean_object* v___y_357_, lean_object* v_handle_358_, lean_object* v_____r_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lake_longOptionOrSpace___redArg___lam__0(v_opt_356_, v___y_357_, v_handle_358_, v_____r_359_);
lean_dec(v___y_357_);
lean_dec_ref(v_opt_356_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__2(lean_object* v___x_361_, lean_object* v_opt_362_, lean_object* v___x_363_, lean_object* v_it_364_, lean_object* v_acc_365_, lean_object* v_hP_366_, lean_object* v_recur_367_){
_start:
{
uint8_t v_decide_368_; 
v_decide_368_ = lean_nat_dec_eq(v_it_364_, v___x_361_);
if (v_decide_368_ == 0)
{
uint32_t v___x_369_; uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_369_ = lean_string_utf8_get_fast(v_opt_362_, v_it_364_);
v___x_370_ = 32;
v___x_371_ = lean_uint32_dec_eq(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_string_utf8_next_fast(v_opt_362_, v_it_364_);
lean_dec(v_it_364_);
v___x_373_ = lean_apply_4(v_recur_367_, v___x_372_, v___x_363_, lean_box(0), lean_box(0));
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
lean_dec_ref(v_recur_367_);
lean_dec(v___x_363_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_it_364_);
return v___x_374_;
}
}
else
{
lean_dec_ref(v_recur_367_);
lean_dec(v_it_364_);
lean_dec(v___x_363_);
lean_inc(v_acc_365_);
return v_acc_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__2___boxed(lean_object* v___x_375_, lean_object* v_opt_376_, lean_object* v___x_377_, lean_object* v_it_378_, lean_object* v_acc_379_, lean_object* v_hP_380_, lean_object* v_recur_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_longOptionOrSpace___redArg___lam__2(v___x_375_, v_opt_376_, v___x_377_, v_it_378_, v_acc_379_, v_hP_380_, v_recur_381_);
lean_dec(v_acc_379_);
lean_dec_ref(v_opt_376_);
lean_dec(v___x_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_handle_385_, lean_object* v_opt_386_){
_start:
{
lean_object* v_toBind_387_; lean_object* v___y_389_; lean_object* v_searcher_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___x_404_; 
v_toBind_387_ = lean_ctor_get(v_inst_383_, 1);
lean_inc(v_toBind_387_);
lean_dec_ref(v_inst_383_);
v_searcher_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_string_utf8_byte_size(v_opt_386_);
v___x_402_ = lean_box(0);
lean_inc_ref(v_opt_386_);
v___f_403_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_403_, 0, v___x_401_);
lean_closure_set(v___f_403_, 1, v_opt_386_);
lean_closure_set(v___f_403_, 2, v___x_402_);
v___x_404_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_403_, v_searcher_400_, v___x_402_, lean_box(0));
if (lean_obj_tag(v___x_404_) == 0)
{
v___y_389_ = v___x_401_;
goto v___jp_388_;
}
else
{
lean_object* v_val_405_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v___x_404_, 1);
v___y_389_ = v_val_405_;
goto v___jp_388_;
}
v___jp_388_:
{
lean_object* v___x_390_; uint8_t v_decide_391_; 
v___x_390_ = lean_string_utf8_byte_size(v_opt_386_);
v_decide_391_ = lean_nat_dec_eq(v___y_389_, v___x_390_);
if (v_decide_391_ == 0)
{
lean_object* v_modifyGet_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_modifyGet_392_ = lean_ctor_get(v_inst_384_, 2);
lean_inc(v_modifyGet_392_);
lean_dec_ref(v_inst_384_);
lean_inc(v___y_389_);
lean_inc_ref(v_opt_386_);
v___f_393_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_393_, 0, v_opt_386_);
lean_closure_set(v___f_393_, 1, v___y_389_);
lean_closure_set(v___f_393_, 2, v_handle_385_);
v___x_394_ = lean_string_utf8_next_fast(v_opt_386_, v___y_389_);
lean_dec(v___y_389_);
v___x_395_ = lean_string_utf8_extract_fast(v_opt_386_, v___x_394_, v___x_390_);
lean_dec_ref(v_opt_386_);
v___f_396_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_396_, 0, v___x_395_);
v___x_397_ = lean_apply_2(v_modifyGet_392_, lean_box(0), v___f_396_);
v___x_398_ = lean_apply_4(v_toBind_387_, lean_box(0), lean_box(0), v___x_397_, v___f_393_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
lean_dec(v___y_389_);
lean_dec(v_toBind_387_);
lean_dec_ref(v_inst_384_);
v___x_399_ = lean_apply_1(v_handle_385_, v_opt_386_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object* v_m_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_00_u03b1_409_, lean_object* v_handle_410_, lean_object* v_opt_411_){
_start:
{
lean_object* v_toBind_412_; lean_object* v___y_414_; lean_object* v_searcher_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; 
v_toBind_412_ = lean_ctor_get(v_inst_407_, 1);
lean_inc(v_toBind_412_);
lean_dec_ref(v_inst_407_);
v_searcher_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_string_utf8_byte_size(v_opt_411_);
v___x_427_ = lean_box(0);
lean_inc_ref(v_opt_411_);
v___f_428_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_428_, 0, v___x_426_);
lean_closure_set(v___f_428_, 1, v_opt_411_);
lean_closure_set(v___f_428_, 2, v___x_427_);
v___x_429_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_428_, v_searcher_425_, v___x_427_, lean_box(0));
if (lean_obj_tag(v___x_429_) == 0)
{
v___y_414_ = v___x_426_;
goto v___jp_413_;
}
else
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___x_429_, 1);
v___y_414_ = v_val_430_;
goto v___jp_413_;
}
v___jp_413_:
{
lean_object* v___x_415_; uint8_t v_decide_416_; 
v___x_415_ = lean_string_utf8_byte_size(v_opt_411_);
v_decide_416_ = lean_nat_dec_eq(v___y_414_, v___x_415_);
if (v_decide_416_ == 0)
{
lean_object* v_modifyGet_417_; lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_modifyGet_417_ = lean_ctor_get(v_inst_408_, 2);
lean_inc(v_modifyGet_417_);
lean_dec_ref(v_inst_408_);
lean_inc(v___y_414_);
lean_inc_ref(v_opt_411_);
v___f_418_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_418_, 0, v_opt_411_);
lean_closure_set(v___f_418_, 1, v___y_414_);
lean_closure_set(v___f_418_, 2, v_handle_410_);
v___x_419_ = lean_string_utf8_next_fast(v_opt_411_, v___y_414_);
lean_dec(v___y_414_);
v___x_420_ = lean_string_utf8_extract_fast(v_opt_411_, v___x_419_, v___x_415_);
lean_dec_ref(v_opt_411_);
v___f_421_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_421_, 0, v___x_420_);
v___x_422_ = lean_apply_2(v_modifyGet_417_, lean_box(0), v___f_421_);
v___x_423_ = lean_apply_4(v_toBind_412_, lean_box(0), lean_box(0), v___x_422_, v___f_418_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
lean_dec(v___y_414_);
lean_dec(v_toBind_412_);
lean_dec_ref(v_inst_408_);
v___x_424_ = lean_apply_1(v_handle_410_, v_opt_411_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2(lean_object* v___x_431_, lean_object* v_opt_432_, lean_object* v___x_433_, lean_object* v_it_434_, lean_object* v_acc_435_, lean_object* v_hP_436_, lean_object* v_recur_437_){
_start:
{
uint8_t v_decide_438_; 
v_decide_438_ = lean_nat_dec_eq(v_it_434_, v___x_431_);
if (v_decide_438_ == 0)
{
uint32_t v___x_439_; uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_string_utf8_get_fast(v_opt_432_, v_it_434_);
v___x_440_ = 61;
v___x_441_ = lean_uint32_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_string_utf8_next_fast(v_opt_432_, v_it_434_);
lean_dec(v_it_434_);
v___x_443_ = lean_apply_4(v_recur_437_, v___x_442_, v___x_433_, lean_box(0), lean_box(0));
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
lean_dec_ref(v_recur_437_);
lean_dec(v___x_433_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_it_434_);
return v___x_444_;
}
}
else
{
lean_dec_ref(v_recur_437_);
lean_dec(v_it_434_);
lean_dec(v___x_433_);
lean_inc(v_acc_435_);
return v_acc_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2___boxed(lean_object* v___x_445_, lean_object* v_opt_446_, lean_object* v___x_447_, lean_object* v_it_448_, lean_object* v_acc_449_, lean_object* v_hP_450_, lean_object* v_recur_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_longOptionOrEq___redArg___lam__2(v___x_445_, v_opt_446_, v___x_447_, v_it_448_, v_acc_449_, v_hP_450_, v_recur_451_);
lean_dec(v_acc_449_);
lean_dec_ref(v_opt_446_);
lean_dec(v___x_445_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_handle_455_, lean_object* v_opt_456_){
_start:
{
lean_object* v_toBind_457_; lean_object* v___y_459_; lean_object* v_searcher_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___x_474_; 
v_toBind_457_ = lean_ctor_get(v_inst_453_, 1);
lean_inc(v_toBind_457_);
lean_dec_ref(v_inst_453_);
v_searcher_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_string_utf8_byte_size(v_opt_456_);
v___x_472_ = lean_box(0);
lean_inc_ref(v_opt_456_);
v___f_473_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_473_, 0, v___x_471_);
lean_closure_set(v___f_473_, 1, v_opt_456_);
lean_closure_set(v___f_473_, 2, v___x_472_);
v___x_474_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_473_, v_searcher_470_, v___x_472_, lean_box(0));
if (lean_obj_tag(v___x_474_) == 0)
{
v___y_459_ = v___x_471_;
goto v___jp_458_;
}
else
{
lean_object* v_val_475_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_474_, 1);
v___y_459_ = v_val_475_;
goto v___jp_458_;
}
v___jp_458_:
{
lean_object* v___x_460_; uint8_t v_decide_461_; 
v___x_460_ = lean_string_utf8_byte_size(v_opt_456_);
v_decide_461_ = lean_nat_dec_eq(v___y_459_, v___x_460_);
if (v_decide_461_ == 0)
{
lean_object* v_modifyGet_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_modifyGet_462_ = lean_ctor_get(v_inst_454_, 2);
lean_inc(v_modifyGet_462_);
lean_dec_ref(v_inst_454_);
lean_inc(v___y_459_);
lean_inc_ref(v_opt_456_);
v___f_463_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_463_, 0, v_opt_456_);
lean_closure_set(v___f_463_, 1, v___y_459_);
lean_closure_set(v___f_463_, 2, v_handle_455_);
v___x_464_ = lean_string_utf8_next_fast(v_opt_456_, v___y_459_);
lean_dec(v___y_459_);
v___x_465_ = lean_string_utf8_extract_fast(v_opt_456_, v___x_464_, v___x_460_);
lean_dec_ref(v_opt_456_);
v___f_466_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_466_, 0, v___x_465_);
v___x_467_ = lean_apply_2(v_modifyGet_462_, lean_box(0), v___f_466_);
v___x_468_ = lean_apply_4(v_toBind_457_, lean_box(0), lean_box(0), v___x_467_, v___f_463_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v___y_459_);
lean_dec(v_toBind_457_);
lean_dec_ref(v_inst_454_);
v___x_469_ = lean_apply_1(v_handle_455_, v_opt_456_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object* v_m_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_00_u03b1_479_, lean_object* v_handle_480_, lean_object* v_opt_481_){
_start:
{
lean_object* v_toBind_482_; lean_object* v___y_484_; lean_object* v_searcher_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___f_498_; lean_object* v___x_499_; 
v_toBind_482_ = lean_ctor_get(v_inst_477_, 1);
lean_inc(v_toBind_482_);
lean_dec_ref(v_inst_477_);
v_searcher_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_string_utf8_byte_size(v_opt_481_);
v___x_497_ = lean_box(0);
lean_inc_ref(v_opt_481_);
v___f_498_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_498_, 0, v___x_496_);
lean_closure_set(v___f_498_, 1, v_opt_481_);
lean_closure_set(v___f_498_, 2, v___x_497_);
v___x_499_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_498_, v_searcher_495_, v___x_497_, lean_box(0));
if (lean_obj_tag(v___x_499_) == 0)
{
v___y_484_ = v___x_496_;
goto v___jp_483_;
}
else
{
lean_object* v_val_500_; 
v_val_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v___x_499_, 1);
v___y_484_ = v_val_500_;
goto v___jp_483_;
}
v___jp_483_:
{
lean_object* v___x_485_; uint8_t v_decide_486_; 
v___x_485_ = lean_string_utf8_byte_size(v_opt_481_);
v_decide_486_ = lean_nat_dec_eq(v___y_484_, v___x_485_);
if (v_decide_486_ == 0)
{
lean_object* v_modifyGet_487_; lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_modifyGet_487_ = lean_ctor_get(v_inst_478_, 2);
lean_inc(v_modifyGet_487_);
lean_dec_ref(v_inst_478_);
lean_inc(v___y_484_);
lean_inc_ref(v_opt_481_);
v___f_488_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_488_, 0, v_opt_481_);
lean_closure_set(v___f_488_, 1, v___y_484_);
lean_closure_set(v___f_488_, 2, v_handle_480_);
v___x_489_ = lean_string_utf8_next_fast(v_opt_481_, v___y_484_);
lean_dec(v___y_484_);
v___x_490_ = lean_string_utf8_extract_fast(v_opt_481_, v___x_489_, v___x_485_);
lean_dec_ref(v_opt_481_);
v___f_491_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_491_, 0, v___x_490_);
v___x_492_ = lean_apply_2(v_modifyGet_487_, lean_box(0), v___f_491_);
v___x_493_ = lean_apply_4(v_toBind_482_, lean_box(0), lean_box(0), v___x_492_, v___f_488_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
lean_dec(v___y_484_);
lean_dec(v_toBind_482_);
lean_dec_ref(v_inst_478_);
v___x_494_ = lean_apply_1(v_handle_480_, v_opt_481_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object* v___x_501_, lean_object* v_searcher_502_, lean_object* v___y_503_, lean_object* v_handle_504_, lean_object* v_____r_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_string_utf8_extract_fast(v___x_501_, v_searcher_502_, v___y_503_);
v___x_507_ = lean_apply_1(v_handle_504_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object* v___x_508_, lean_object* v_searcher_509_, lean_object* v___y_510_, lean_object* v_handle_511_, lean_object* v_____r_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_longOption___redArg___lam__2(v___x_508_, v_searcher_509_, v___y_510_, v_handle_511_, v_____r_512_);
lean_dec(v___y_510_);
lean_dec(v_searcher_509_);
lean_dec_ref(v___x_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__1(lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v_it_517_, lean_object* v_acc_518_, lean_object* v_hP_519_, lean_object* v_recur_520_){
_start:
{
uint8_t v_decide_521_; 
v_decide_521_ = lean_nat_dec_eq(v_it_517_, v___x_514_);
if (v_decide_521_ == 0)
{
uint32_t v___x_522_; uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_string_utf8_get_fast(v___x_515_, v_it_517_);
v___x_523_ = 32;
v___x_524_ = lean_uint32_dec_eq(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_string_utf8_next_fast(v___x_515_, v_it_517_);
lean_dec(v_it_517_);
v___x_526_ = lean_apply_4(v_recur_520_, v___x_525_, v___x_516_, lean_box(0), lean_box(0));
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v_recur_520_);
lean_dec(v___x_516_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v_it_517_);
return v___x_527_;
}
}
else
{
lean_dec_ref(v_recur_520_);
lean_dec(v_it_517_);
lean_dec(v___x_516_);
lean_inc(v_acc_518_);
return v_acc_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__1___boxed(lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v_it_531_, lean_object* v_acc_532_, lean_object* v_hP_533_, lean_object* v_recur_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lake_longOption___redArg___lam__1(v___x_528_, v___x_529_, v___x_530_, v_it_531_, v_acc_532_, v_hP_533_, v_recur_534_);
lean_dec(v_acc_532_);
lean_dec_ref(v___x_529_);
lean_dec(v___x_528_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object* v_opt_536_, lean_object* v___y_537_, lean_object* v_handle_538_, lean_object* v_modifyGet_539_, lean_object* v_toBind_540_, lean_object* v_____r_541_){
_start:
{
lean_object* v_searcher_542_; lean_object* v___x_543_; lean_object* v___y_545_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
v_searcher_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_string_utf8_extract_fast(v_opt_536_, v_searcher_542_, v___y_537_);
v___x_555_ = lean_string_utf8_byte_size(v___x_543_);
v___x_556_ = lean_box(0);
lean_inc_ref(v___x_543_);
v___f_557_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_557_, 0, v___x_555_);
lean_closure_set(v___f_557_, 1, v___x_543_);
lean_closure_set(v___f_557_, 2, v___x_556_);
v___x_558_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_557_, v_searcher_542_, v___x_556_, lean_box(0));
if (lean_obj_tag(v___x_558_) == 0)
{
v___y_545_ = v___x_555_;
goto v___jp_544_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_558_, 1);
v___y_545_ = v_val_559_;
goto v___jp_544_;
}
v___jp_544_:
{
lean_object* v___x_546_; uint8_t v_decide_547_; 
v___x_546_ = lean_string_utf8_byte_size(v___x_543_);
v_decide_547_ = lean_nat_dec_eq(v___y_545_, v___x_546_);
if (v_decide_547_ == 0)
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_inc(v___y_545_);
lean_inc_ref(v___x_543_);
v___f_548_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_548_, 0, v___x_543_);
lean_closure_set(v___f_548_, 1, v_searcher_542_);
lean_closure_set(v___f_548_, 2, v___y_545_);
lean_closure_set(v___f_548_, 3, v_handle_538_);
v___x_549_ = lean_string_utf8_next_fast(v___x_543_, v___y_545_);
lean_dec(v___y_545_);
v___x_550_ = lean_string_utf8_extract_fast(v___x_543_, v___x_549_, v___x_546_);
lean_dec_ref(v___x_543_);
v___f_551_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_551_, 0, v___x_550_);
v___x_552_ = lean_apply_2(v_modifyGet_539_, lean_box(0), v___f_551_);
v___x_553_ = lean_apply_4(v_toBind_540_, lean_box(0), lean_box(0), v___x_552_, v___f_548_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; 
lean_dec(v___y_545_);
lean_dec(v_toBind_540_);
lean_dec(v_modifyGet_539_);
v___x_554_ = lean_apply_1(v_handle_538_, v___x_543_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object* v_opt_560_, lean_object* v___y_561_, lean_object* v_handle_562_, lean_object* v_modifyGet_563_, lean_object* v_toBind_564_, lean_object* v_____r_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lake_longOption___redArg___lam__0(v_opt_560_, v___y_561_, v_handle_562_, v_modifyGet_563_, v_toBind_564_, v_____r_565_);
lean_dec(v___y_561_);
lean_dec_ref(v_opt_560_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_handle_569_, lean_object* v_opt_570_){
_start:
{
lean_object* v_toBind_571_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_585_; lean_object* v_searcher_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; 
v_toBind_571_ = lean_ctor_get(v_inst_567_, 1);
lean_inc(v_toBind_571_);
lean_dec_ref(v_inst_567_);
v_searcher_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_string_utf8_byte_size(v_opt_570_);
v___x_602_ = lean_box(0);
lean_inc_ref(v_opt_570_);
v___f_603_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_603_, 0, v___x_601_);
lean_closure_set(v___f_603_, 1, v_opt_570_);
lean_closure_set(v___f_603_, 2, v___x_602_);
v___x_604_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_603_, v_searcher_600_, v___x_602_, lean_box(0));
if (lean_obj_tag(v___x_604_) == 0)
{
v___y_585_ = v___x_601_;
goto v___jp_584_;
}
else
{
lean_object* v_val_605_; 
v_val_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_604_, 1);
v___y_585_ = v_val_605_;
goto v___jp_584_;
}
v___jp_572_:
{
uint8_t v_decide_575_; 
v_decide_575_ = lean_nat_dec_eq(v___y_574_, v___y_573_);
if (v_decide_575_ == 0)
{
lean_object* v_modifyGet_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_modifyGet_576_ = lean_ctor_get(v_inst_568_, 2);
lean_inc(v_modifyGet_576_);
lean_dec_ref(v_inst_568_);
lean_inc(v___y_574_);
lean_inc_ref(v_opt_570_);
v___f_577_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_577_, 0, v_opt_570_);
lean_closure_set(v___f_577_, 1, v___y_574_);
lean_closure_set(v___f_577_, 2, v_handle_569_);
v___x_578_ = lean_string_utf8_next_fast(v_opt_570_, v___y_574_);
lean_dec(v___y_574_);
v___x_579_ = lean_string_utf8_extract_fast(v_opt_570_, v___x_578_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v_opt_570_);
v___f_580_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_580_, 0, v___x_579_);
v___x_581_ = lean_apply_2(v_modifyGet_576_, lean_box(0), v___f_580_);
v___x_582_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_581_, v___f_577_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v___y_574_);
lean_dec(v___y_573_);
lean_dec(v_toBind_571_);
lean_dec_ref(v_inst_568_);
v___x_583_ = lean_apply_1(v_handle_569_, v_opt_570_);
return v___x_583_;
}
}
v___jp_584_:
{
lean_object* v___x_586_; uint8_t v_decide_587_; 
v___x_586_ = lean_string_utf8_byte_size(v_opt_570_);
v_decide_587_ = lean_nat_dec_eq(v___y_585_, v___x_586_);
if (v_decide_587_ == 0)
{
lean_object* v_modifyGet_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_modifyGet_588_ = lean_ctor_get(v_inst_568_, 2);
lean_inc_n(v_modifyGet_588_, 2);
lean_dec_ref(v_inst_568_);
lean_inc(v_toBind_571_);
lean_inc(v___y_585_);
lean_inc_ref(v_opt_570_);
v___f_589_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_589_, 0, v_opt_570_);
lean_closure_set(v___f_589_, 1, v___y_585_);
lean_closure_set(v___f_589_, 2, v_handle_569_);
lean_closure_set(v___f_589_, 3, v_modifyGet_588_);
lean_closure_set(v___f_589_, 4, v_toBind_571_);
v___x_590_ = lean_string_utf8_next_fast(v_opt_570_, v___y_585_);
lean_dec(v___y_585_);
v___x_591_ = lean_string_utf8_extract_fast(v_opt_570_, v___x_590_, v___x_586_);
lean_dec_ref(v_opt_570_);
v___f_592_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_592_, 0, v___x_591_);
v___x_593_ = lean_apply_2(v_modifyGet_588_, lean_box(0), v___f_592_);
v___x_594_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_593_, v___f_589_);
return v___x_594_;
}
else
{
lean_object* v_searcher_595_; lean_object* v___x_596_; lean_object* v___f_597_; lean_object* v___x_598_; 
lean_dec(v___y_585_);
v_searcher_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_box(0);
lean_inc_ref(v_opt_570_);
v___f_597_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_597_, 0, v___x_586_);
lean_closure_set(v___f_597_, 1, v_opt_570_);
lean_closure_set(v___f_597_, 2, v___x_596_);
v___x_598_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_597_, v_searcher_595_, v___x_596_, lean_box(0));
if (lean_obj_tag(v___x_598_) == 0)
{
v___y_573_ = v___x_586_;
v___y_574_ = v___x_586_;
goto v___jp_572_;
}
else
{
lean_object* v_val_599_; 
v_val_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v___x_598_, 1);
v___y_573_ = v___x_586_;
v___y_574_ = v_val_599_;
goto v___jp_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object* v_m_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_00_u03b1_609_, lean_object* v_handle_610_, lean_object* v_opt_611_){
_start:
{
lean_object* v_toBind_612_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_626_; lean_object* v_searcher_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___f_644_; lean_object* v___x_645_; 
v_toBind_612_ = lean_ctor_get(v_inst_607_, 1);
lean_inc(v_toBind_612_);
lean_dec_ref(v_inst_607_);
v_searcher_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_string_utf8_byte_size(v_opt_611_);
v___x_643_ = lean_box(0);
lean_inc_ref(v_opt_611_);
v___f_644_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_644_, 0, v___x_642_);
lean_closure_set(v___f_644_, 1, v_opt_611_);
lean_closure_set(v___f_644_, 2, v___x_643_);
v___x_645_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_644_, v_searcher_641_, v___x_643_, lean_box(0));
if (lean_obj_tag(v___x_645_) == 0)
{
v___y_626_ = v___x_642_;
goto v___jp_625_;
}
else
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
v___y_626_ = v_val_646_;
goto v___jp_625_;
}
v___jp_613_:
{
uint8_t v_decide_616_; 
v_decide_616_ = lean_nat_dec_eq(v___y_615_, v___y_614_);
if (v_decide_616_ == 0)
{
lean_object* v_modifyGet_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_modifyGet_617_ = lean_ctor_get(v_inst_608_, 2);
lean_inc(v_modifyGet_617_);
lean_dec_ref(v_inst_608_);
lean_inc(v___y_615_);
lean_inc_ref(v_opt_611_);
v___f_618_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_618_, 0, v_opt_611_);
lean_closure_set(v___f_618_, 1, v___y_615_);
lean_closure_set(v___f_618_, 2, v_handle_610_);
v___x_619_ = lean_string_utf8_next_fast(v_opt_611_, v___y_615_);
lean_dec(v___y_615_);
v___x_620_ = lean_string_utf8_extract_fast(v_opt_611_, v___x_619_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v_opt_611_);
v___f_621_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_621_, 0, v___x_620_);
v___x_622_ = lean_apply_2(v_modifyGet_617_, lean_box(0), v___f_621_);
v___x_623_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v___x_622_, v___f_618_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v___y_615_);
lean_dec(v___y_614_);
lean_dec(v_toBind_612_);
lean_dec_ref(v_inst_608_);
v___x_624_ = lean_apply_1(v_handle_610_, v_opt_611_);
return v___x_624_;
}
}
v___jp_625_:
{
lean_object* v___x_627_; uint8_t v_decide_628_; 
v___x_627_ = lean_string_utf8_byte_size(v_opt_611_);
v_decide_628_ = lean_nat_dec_eq(v___y_626_, v___x_627_);
if (v_decide_628_ == 0)
{
lean_object* v_modifyGet_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_modifyGet_629_ = lean_ctor_get(v_inst_608_, 2);
lean_inc_n(v_modifyGet_629_, 2);
lean_dec_ref(v_inst_608_);
lean_inc(v_toBind_612_);
lean_inc(v___y_626_);
lean_inc_ref(v_opt_611_);
v___f_630_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_630_, 0, v_opt_611_);
lean_closure_set(v___f_630_, 1, v___y_626_);
lean_closure_set(v___f_630_, 2, v_handle_610_);
lean_closure_set(v___f_630_, 3, v_modifyGet_629_);
lean_closure_set(v___f_630_, 4, v_toBind_612_);
v___x_631_ = lean_string_utf8_next_fast(v_opt_611_, v___y_626_);
lean_dec(v___y_626_);
v___x_632_ = lean_string_utf8_extract_fast(v_opt_611_, v___x_631_, v___x_627_);
lean_dec_ref(v_opt_611_);
v___f_633_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_633_, 0, v___x_632_);
v___x_634_ = lean_apply_2(v_modifyGet_629_, lean_box(0), v___f_633_);
v___x_635_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v___x_634_, v___f_630_);
return v___x_635_;
}
else
{
lean_object* v_searcher_636_; lean_object* v___x_637_; lean_object* v___f_638_; lean_object* v___x_639_; 
lean_dec(v___y_626_);
v_searcher_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_box(0);
lean_inc_ref(v_opt_611_);
v___f_638_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_638_, 0, v___x_627_);
lean_closure_set(v___f_638_, 1, v_opt_611_);
lean_closure_set(v___f_638_, 2, v___x_637_);
v___x_639_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_638_, v_searcher_636_, v___x_637_, lean_box(0));
if (lean_obj_tag(v___x_639_) == 0)
{
v___y_614_ = v___x_627_;
v___y_615_ = v___x_627_;
goto v___jp_613_;
}
else
{
lean_object* v_val_640_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v___x_639_, 1);
v___y_614_ = v___x_627_;
v___y_615_ = v_val_640_;
goto v___jp_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object* v___x_647_, lean_object* v_opt_648_, lean_object* v_it_649_, lean_object* v_acc_650_, lean_object* v_hP_651_, lean_object* v_recur_652_){
_start:
{
uint8_t v_decide_653_; 
v_decide_653_ = lean_nat_dec_eq(v_it_649_, v___x_647_);
if (v_decide_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_string_utf8_next_fast(v_opt_648_, v_it_649_);
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_add(v_acc_650_, v___x_655_);
v___x_657_ = lean_apply_4(v_recur_652_, v___x_654_, v___x_656_, lean_box(0), lean_box(0));
return v___x_657_;
}
else
{
lean_dec_ref(v_recur_652_);
lean_inc(v_acc_650_);
return v_acc_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object* v___x_658_, lean_object* v_opt_659_, lean_object* v_it_660_, lean_object* v_acc_661_, lean_object* v_hP_662_, lean_object* v_recur_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lake_shortOption___redArg___lam__0(v___x_658_, v_opt_659_, v_it_660_, v_acc_661_, v_hP_662_, v_recur_663_);
lean_dec(v_acc_661_);
lean_dec(v_it_660_);
lean_dec_ref(v_opt_659_);
lean_dec(v___x_658_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__1(lean_object* v_opt_665_, lean_object* v_shortHandle_666_, lean_object* v_____r_667_){
_start:
{
lean_object* v___x_668_; uint32_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_string_utf8_get(v_opt_665_, v___x_668_);
v___x_670_ = lean_box_uint32(v___x_669_);
v___x_671_ = lean_apply_1(v_shortHandle_666_, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__1___boxed(lean_object* v_opt_672_, lean_object* v_shortHandle_673_, lean_object* v_____r_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lake_shortOption___redArg___lam__1(v_opt_672_, v_shortHandle_673_, v_____r_674_);
lean_dec_ref(v_opt_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_shortHandle_678_, lean_object* v_longHandle_679_, lean_object* v_opt_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___f_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_string_utf8_byte_size(v_opt_680_);
lean_inc_ref_n(v_opt_680_, 2);
v___f_683_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_683_, 0, v___x_682_);
lean_closure_set(v___f_683_, 1, v_opt_680_);
v___x_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_684_, 0, v_opt_680_);
lean_ctor_set(v___x_684_, 1, v___x_681_);
lean_ctor_set(v___x_684_, 2, v___x_682_);
v___x_685_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_683_, v___x_681_, v___x_681_, lean_box(0));
v___x_686_ = lean_unsigned_to_nat(2u);
v___x_687_ = lean_nat_dec_eq(v___x_685_, v___x_686_);
lean_dec(v___x_685_);
if (v___x_687_ == 0)
{
uint32_t v___x_688_; uint32_t v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_string_utf8_get(v_opt_680_, v___x_686_);
v___x_689_ = 61;
v___x_690_ = lean_uint32_dec_eq(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = 32;
v___x_692_ = lean_uint32_dec_eq(v___x_688_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref_known(v___x_684_, 3);
lean_dec(v_shortHandle_678_);
lean_dec_ref(v_inst_677_);
lean_dec_ref(v_inst_676_);
v___x_693_ = lean_apply_1(v_longHandle_679_, v_opt_680_);
return v___x_693_;
}
else
{
lean_object* v_toBind_694_; lean_object* v___x_695_; lean_object* v_modifyGet_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_longHandle_679_);
v_toBind_694_ = lean_ctor_get(v_inst_676_, 1);
lean_inc(v_toBind_694_);
lean_dec_ref(v_inst_676_);
v___x_695_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_696_ = lean_ctor_get(v_inst_677_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_inst_677_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_inst_677_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_inst_677_, 0);
lean_dec(v_unused_713_);
v___x_698_ = v_inst_677_;
v_isShared_699_ = v_isSharedCheck_711_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_modifyGet_696_);
lean_dec(v_inst_677_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_711_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v___x_703_; 
v___x_700_ = l_String_Slice_Pos_nextn(v___x_684_, v___x_681_, v___x_686_);
lean_dec_ref_known(v___x_684_, 3);
lean_inc_ref_n(v_opt_680_, 2);
v___f_701_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_701_, 0, v_opt_680_);
lean_closure_set(v___f_701_, 1, v_shortHandle_678_);
lean_inc(v___x_700_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v___x_682_);
lean_ctor_set(v___x_698_, 1, v___x_700_);
lean_ctor_set(v___x_698_, 0, v_opt_680_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_opt_680_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v___x_682_);
v___x_703_ = v_reuseFailAlloc_710_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = l_String_Slice_Pos_skipWhile___redArg(v___x_703_, v___x_681_, v___x_695_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_nat_add(v___x_700_, v___x_704_);
lean_dec(v___x_704_);
lean_dec(v___x_700_);
v___x_706_ = lean_string_utf8_extract_fast(v_opt_680_, v___x_705_, v___x_682_);
lean_dec(v___x_705_);
lean_dec_ref(v_opt_680_);
v___f_707_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_707_, 0, v___x_706_);
v___x_708_ = lean_apply_2(v_modifyGet_696_, lean_box(0), v___f_707_);
v___x_709_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v___x_708_, v___f_701_);
return v___x_709_;
}
}
}
}
else
{
lean_object* v_toBind_714_; lean_object* v_modifyGet_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v_longHandle_679_);
v_toBind_714_ = lean_ctor_get(v_inst_676_, 1);
lean_inc(v_toBind_714_);
lean_dec_ref(v_inst_676_);
v_modifyGet_715_ = lean_ctor_get(v_inst_677_, 2);
lean_inc(v_modifyGet_715_);
lean_dec_ref(v_inst_677_);
lean_inc_ref(v_opt_680_);
v___f_716_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_716_, 0, v_opt_680_);
lean_closure_set(v___f_716_, 1, v_shortHandle_678_);
v___x_717_ = lean_unsigned_to_nat(3u);
v___x_718_ = l_String_Slice_Pos_nextn(v___x_684_, v___x_681_, v___x_717_);
lean_dec_ref_known(v___x_684_, 3);
v___x_719_ = lean_string_utf8_extract_fast(v_opt_680_, v___x_718_, v___x_682_);
lean_dec(v___x_718_);
lean_dec_ref(v_opt_680_);
v___f_720_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_720_, 0, v___x_719_);
v___x_721_ = lean_apply_2(v_modifyGet_715_, lean_box(0), v___f_720_);
v___x_722_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_721_, v___f_716_);
return v___x_722_;
}
}
else
{
lean_object* v___x_723_; uint32_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref_known(v___x_684_, 3);
lean_dec(v_longHandle_679_);
lean_dec_ref(v_inst_677_);
lean_dec_ref(v_inst_676_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_string_utf8_get(v_opt_680_, v___x_723_);
lean_dec_ref(v_opt_680_);
v___x_725_ = lean_box_uint32(v___x_724_);
v___x_726_ = lean_apply_1(v_shortHandle_678_, v___x_725_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object* v_m_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_00_u03b1_730_, lean_object* v_shortHandle_731_, lean_object* v_longHandle_732_, lean_object* v_opt_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_string_utf8_byte_size(v_opt_733_);
lean_inc_ref_n(v_opt_733_, 2);
v___f_736_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_736_, 0, v___x_735_);
lean_closure_set(v___f_736_, 1, v_opt_733_);
v___x_737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_737_, 0, v_opt_733_);
lean_ctor_set(v___x_737_, 1, v___x_734_);
lean_ctor_set(v___x_737_, 2, v___x_735_);
v___x_738_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_736_, v___x_734_, v___x_734_, lean_box(0));
v___x_739_ = lean_unsigned_to_nat(2u);
v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
if (v___x_740_ == 0)
{
uint32_t v___x_741_; uint32_t v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_string_utf8_get(v_opt_733_, v___x_739_);
v___x_742_ = 61;
v___x_743_ = lean_uint32_dec_eq(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
uint32_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = 32;
v___x_745_ = lean_uint32_dec_eq(v___x_741_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref_known(v___x_737_, 3);
lean_dec(v_shortHandle_731_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_728_);
v___x_746_ = lean_apply_1(v_longHandle_732_, v_opt_733_);
return v___x_746_;
}
else
{
lean_object* v_toBind_747_; lean_object* v___x_748_; lean_object* v_modifyGet_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_longHandle_732_);
v_toBind_747_ = lean_ctor_get(v_inst_728_, 1);
lean_inc(v_toBind_747_);
lean_dec_ref(v_inst_728_);
v___x_748_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_749_ = lean_ctor_get(v_inst_729_, 2);
v_isSharedCheck_764_ = !lean_is_exclusive(v_inst_729_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; 
v_unused_765_ = lean_ctor_get(v_inst_729_, 1);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_inst_729_, 0);
lean_dec(v_unused_766_);
v___x_751_ = v_inst_729_;
v_isShared_752_ = v_isSharedCheck_764_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_modifyGet_749_);
lean_dec(v_inst_729_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_764_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_756_; 
v___x_753_ = l_String_Slice_Pos_nextn(v___x_737_, v___x_734_, v___x_739_);
lean_dec_ref_known(v___x_737_, 3);
lean_inc_ref_n(v_opt_733_, 2);
v___f_754_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_754_, 0, v_opt_733_);
lean_closure_set(v___f_754_, 1, v_shortHandle_731_);
lean_inc(v___x_753_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 2, v___x_735_);
lean_ctor_set(v___x_751_, 1, v___x_753_);
lean_ctor_set(v___x_751_, 0, v_opt_733_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_opt_733_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___x_735_);
v___x_756_ = v_reuseFailAlloc_763_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_757_ = l_String_Slice_Pos_skipWhile___redArg(v___x_756_, v___x_734_, v___x_748_);
lean_dec_ref(v___x_756_);
v___x_758_ = lean_nat_add(v___x_753_, v___x_757_);
lean_dec(v___x_757_);
lean_dec(v___x_753_);
v___x_759_ = lean_string_utf8_extract_fast(v_opt_733_, v___x_758_, v___x_735_);
lean_dec(v___x_758_);
lean_dec_ref(v_opt_733_);
v___f_760_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_760_, 0, v___x_759_);
v___x_761_ = lean_apply_2(v_modifyGet_749_, lean_box(0), v___f_760_);
v___x_762_ = lean_apply_4(v_toBind_747_, lean_box(0), lean_box(0), v___x_761_, v___f_754_);
return v___x_762_;
}
}
}
}
else
{
lean_object* v_toBind_767_; lean_object* v_modifyGet_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_longHandle_732_);
v_toBind_767_ = lean_ctor_get(v_inst_728_, 1);
lean_inc(v_toBind_767_);
lean_dec_ref(v_inst_728_);
v_modifyGet_768_ = lean_ctor_get(v_inst_729_, 2);
lean_inc(v_modifyGet_768_);
lean_dec_ref(v_inst_729_);
lean_inc_ref(v_opt_733_);
v___f_769_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_769_, 0, v_opt_733_);
lean_closure_set(v___f_769_, 1, v_shortHandle_731_);
v___x_770_ = lean_unsigned_to_nat(3u);
v___x_771_ = l_String_Slice_Pos_nextn(v___x_737_, v___x_734_, v___x_770_);
lean_dec_ref_known(v___x_737_, 3);
v___x_772_ = lean_string_utf8_extract_fast(v_opt_733_, v___x_771_, v___x_735_);
lean_dec(v___x_771_);
lean_dec_ref(v_opt_733_);
v___f_773_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_773_, 0, v___x_772_);
v___x_774_ = lean_apply_2(v_modifyGet_768_, lean_box(0), v___f_773_);
v___x_775_ = lean_apply_4(v_toBind_767_, lean_box(0), lean_box(0), v___x_774_, v___f_769_);
return v___x_775_;
}
}
else
{
lean_object* v___x_776_; uint32_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref_known(v___x_737_, 3);
lean_dec(v_longHandle_732_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_728_);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_string_utf8_get(v_opt_733_, v___x_776_);
lean_dec_ref(v_opt_733_);
v___x_778_ = lean_box_uint32(v___x_777_);
v___x_779_ = lean_apply_1(v_shortHandle_731_, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object* v___x_780_, lean_object* v_opt_781_, lean_object* v___x_782_, lean_object* v_it_783_, lean_object* v_acc_784_, lean_object* v_hP_785_, lean_object* v_recur_786_){
_start:
{
uint8_t v_decide_787_; 
v_decide_787_ = lean_nat_dec_eq(v_it_783_, v___x_780_);
if (v_decide_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = lean_string_utf8_next_fast(v_opt_781_, v_it_783_);
v___x_789_ = lean_nat_add(v_acc_784_, v___x_782_);
v___x_790_ = lean_apply_4(v_recur_786_, v___x_788_, v___x_789_, lean_box(0), lean_box(0));
return v___x_790_;
}
else
{
lean_dec_ref(v_recur_786_);
lean_inc(v_acc_784_);
return v_acc_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object* v___x_791_, lean_object* v_opt_792_, lean_object* v___x_793_, lean_object* v_it_794_, lean_object* v_acc_795_, lean_object* v_hP_796_, lean_object* v_recur_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_option___redArg___lam__0(v___x_791_, v_opt_792_, v___x_793_, v_it_794_, v_acc_795_, v_hP_796_, v_recur_797_);
lean_dec(v_acc_795_);
lean_dec(v_it_794_);
lean_dec(v___x_793_);
lean_dec_ref(v_opt_792_);
lean_dec(v___x_791_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__1(lean_object* v_short_799_, uint32_t v___x_800_, lean_object* v_____r_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box_uint32(v___x_800_);
v___x_803_ = lean_apply_1(v_short_799_, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__1___boxed(lean_object* v_short_804_, lean_object* v___x_805_, lean_object* v_____r_806_){
_start:
{
uint32_t v___x_890__boxed_807_; lean_object* v_res_808_; 
v___x_890__boxed_807_ = lean_unbox_uint32(v___x_805_);
lean_dec(v___x_805_);
v_res_808_ = l_Lake_option___redArg___lam__1(v_short_804_, v___x_890__boxed_807_, v_____r_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5(lean_object* v_opt_809_, lean_object* v___y_810_, lean_object* v_long_811_, lean_object* v_____r_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_string_utf8_extract_fast(v_opt_809_, v___x_813_, v___y_810_);
v___x_815_ = lean_apply_1(v_long_811_, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5___boxed(lean_object* v_opt_816_, lean_object* v___y_817_, lean_object* v_long_818_, lean_object* v_____r_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lake_option___redArg___lam__5(v_opt_816_, v___y_817_, v_long_818_, v_____r_819_);
lean_dec(v___y_817_);
lean_dec_ref(v_opt_816_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object* v___x_821_, lean_object* v_searcher_822_, lean_object* v___y_823_, lean_object* v_long_824_, lean_object* v_____r_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_string_utf8_extract_fast(v___x_821_, v_searcher_822_, v___y_823_);
v___x_827_ = lean_apply_1(v_long_824_, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object* v___x_828_, lean_object* v_searcher_829_, lean_object* v___y_830_, lean_object* v_long_831_, lean_object* v_____r_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_option___redArg___lam__3(v___x_828_, v_searcher_829_, v___y_830_, v_long_831_, v_____r_832_);
lean_dec(v___y_830_);
lean_dec(v_searcher_829_);
lean_dec_ref(v___x_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__6(lean_object* v_opt_834_, lean_object* v___y_835_, lean_object* v_long_836_, lean_object* v_modifyGet_837_, lean_object* v_toBind_838_, lean_object* v_____r_839_){
_start:
{
lean_object* v_searcher_840_; lean_object* v___x_841_; lean_object* v___y_843_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___x_856_; 
v_searcher_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_string_utf8_extract_fast(v_opt_834_, v_searcher_840_, v___y_835_);
v___x_853_ = lean_string_utf8_byte_size(v___x_841_);
v___x_854_ = lean_box(0);
lean_inc_ref(v___x_841_);
v___f_855_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_855_, 0, v___x_853_);
lean_closure_set(v___f_855_, 1, v___x_841_);
lean_closure_set(v___f_855_, 2, v___x_854_);
v___x_856_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_855_, v_searcher_840_, v___x_854_, lean_box(0));
if (lean_obj_tag(v___x_856_) == 0)
{
v___y_843_ = v___x_853_;
goto v___jp_842_;
}
else
{
lean_object* v_val_857_; 
v_val_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_856_, 1);
v___y_843_ = v_val_857_;
goto v___jp_842_;
}
v___jp_842_:
{
lean_object* v___x_844_; uint8_t v_decide_845_; 
v___x_844_ = lean_string_utf8_byte_size(v___x_841_);
v_decide_845_ = lean_nat_dec_eq(v___y_843_, v___x_844_);
if (v_decide_845_ == 0)
{
lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___f_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc(v___y_843_);
lean_inc_ref(v___x_841_);
v___f_846_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_846_, 0, v___x_841_);
lean_closure_set(v___f_846_, 1, v_searcher_840_);
lean_closure_set(v___f_846_, 2, v___y_843_);
lean_closure_set(v___f_846_, 3, v_long_836_);
v___x_847_ = lean_string_utf8_next_fast(v___x_841_, v___y_843_);
lean_dec(v___y_843_);
v___x_848_ = lean_string_utf8_extract_fast(v___x_841_, v___x_847_, v___x_844_);
lean_dec_ref(v___x_841_);
v___f_849_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_849_, 0, v___x_848_);
v___x_850_ = lean_apply_2(v_modifyGet_837_, lean_box(0), v___f_849_);
v___x_851_ = lean_apply_4(v_toBind_838_, lean_box(0), lean_box(0), v___x_850_, v___f_846_);
return v___x_851_;
}
else
{
lean_object* v___x_852_; 
lean_dec(v___y_843_);
lean_dec(v_toBind_838_);
lean_dec(v_modifyGet_837_);
v___x_852_ = lean_apply_1(v_long_836_, v___x_841_);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__6___boxed(lean_object* v_opt_858_, lean_object* v___y_859_, lean_object* v_long_860_, lean_object* v_modifyGet_861_, lean_object* v_toBind_862_, lean_object* v_____r_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lake_option___redArg___lam__6(v_opt_858_, v___y_859_, v_long_860_, v_modifyGet_861_, v_toBind_862_, v_____r_863_);
lean_dec(v___y_859_);
lean_dec_ref(v_opt_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_handlers_867_, lean_object* v_opt_868_){
_start:
{
lean_object* v___x_869_; uint32_t v___x_870_; uint32_t v___x_871_; uint8_t v___x_872_; 
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_string_utf8_get(v_opt_868_, v___x_869_);
v___x_871_ = 45;
v___x_872_ = lean_uint32_dec_eq(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v_short_873_; lean_object* v_longShort_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_926_; 
v_short_873_ = lean_ctor_get(v_handlers_867_, 1);
v_longShort_874_ = lean_ctor_get(v_handlers_867_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_handlers_867_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_handlers_867_, 0);
lean_dec(v_unused_927_);
v___x_876_ = v_handlers_867_;
v_isShared_877_ = v_isSharedCheck_926_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_longShort_874_);
lean_inc(v_short_873_);
lean_dec(v_handlers_867_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_926_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___x_882_; 
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_string_utf8_byte_size(v_opt_868_);
lean_inc_ref_n(v_opt_868_, 2);
v___f_880_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_880_, 0, v___x_879_);
lean_closure_set(v___f_880_, 1, v_opt_868_);
lean_closure_set(v___f_880_, 2, v___x_869_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 2, v___x_879_);
lean_ctor_set(v___x_876_, 1, v___x_878_);
lean_ctor_set(v___x_876_, 0, v_opt_868_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_opt_868_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___x_879_);
v___x_882_ = v_reuseFailAlloc_925_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_880_, v___x_878_, v___x_878_, lean_box(0));
v___x_884_ = lean_unsigned_to_nat(2u);
v___x_885_ = lean_nat_dec_eq(v___x_883_, v___x_884_);
lean_dec(v___x_883_);
if (v___x_885_ == 0)
{
uint32_t v___x_886_; uint32_t v___x_887_; uint8_t v___x_888_; 
v___x_886_ = lean_string_utf8_get(v_opt_868_, v___x_884_);
v___x_887_ = 61;
v___x_888_ = lean_uint32_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
uint32_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 32;
v___x_890_ = lean_uint32_dec_eq(v___x_886_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec_ref(v___x_882_);
lean_dec(v_short_873_);
lean_dec_ref(v_inst_866_);
lean_dec_ref(v_inst_865_);
v___x_891_ = lean_apply_1(v_longShort_874_, v_opt_868_);
return v___x_891_;
}
else
{
lean_object* v_toBind_892_; lean_object* v___x_893_; lean_object* v_modifyGet_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_longShort_874_);
v_toBind_892_ = lean_ctor_get(v_inst_865_, 1);
lean_inc(v_toBind_892_);
lean_dec_ref(v_inst_865_);
v___x_893_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_894_ = lean_ctor_get(v_inst_866_, 2);
v_isSharedCheck_910_ = !lean_is_exclusive(v_inst_866_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_911_ = lean_ctor_get(v_inst_866_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_inst_866_, 0);
lean_dec(v_unused_912_);
v___x_896_ = v_inst_866_;
v_isShared_897_ = v_isSharedCheck_910_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_modifyGet_894_);
lean_dec(v_inst_866_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_910_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___f_900_; lean_object* v___x_902_; 
v___x_898_ = l_String_Slice_Pos_nextn(v___x_882_, v___x_878_, v___x_884_);
lean_dec_ref(v___x_882_);
v___x_899_ = lean_box_uint32(v___x_870_);
v___f_900_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_900_, 0, v_short_873_);
lean_closure_set(v___f_900_, 1, v___x_899_);
lean_inc(v___x_898_);
lean_inc_ref(v_opt_868_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v___x_879_);
lean_ctor_set(v___x_896_, 1, v___x_898_);
lean_ctor_set(v___x_896_, 0, v_opt_868_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_opt_868_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v___x_879_);
v___x_902_ = v_reuseFailAlloc_909_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_903_ = l_String_Slice_Pos_skipWhile___redArg(v___x_902_, v___x_878_, v___x_893_);
lean_dec_ref(v___x_902_);
v___x_904_ = lean_nat_add(v___x_898_, v___x_903_);
lean_dec(v___x_903_);
lean_dec(v___x_898_);
v___x_905_ = lean_string_utf8_extract_fast(v_opt_868_, v___x_904_, v___x_879_);
lean_dec(v___x_904_);
lean_dec_ref(v_opt_868_);
v___f_906_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_906_, 0, v___x_905_);
v___x_907_ = lean_apply_2(v_modifyGet_894_, lean_box(0), v___f_906_);
v___x_908_ = lean_apply_4(v_toBind_892_, lean_box(0), lean_box(0), v___x_907_, v___f_900_);
return v___x_908_;
}
}
}
}
else
{
lean_object* v_toBind_913_; lean_object* v_modifyGet_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec(v_longShort_874_);
v_toBind_913_ = lean_ctor_get(v_inst_865_, 1);
lean_inc(v_toBind_913_);
lean_dec_ref(v_inst_865_);
v_modifyGet_914_ = lean_ctor_get(v_inst_866_, 2);
lean_inc(v_modifyGet_914_);
lean_dec_ref(v_inst_866_);
v___x_915_ = lean_box_uint32(v___x_870_);
v___f_916_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_916_, 0, v_short_873_);
lean_closure_set(v___f_916_, 1, v___x_915_);
v___x_917_ = lean_unsigned_to_nat(3u);
v___x_918_ = l_String_Slice_Pos_nextn(v___x_882_, v___x_878_, v___x_917_);
lean_dec_ref(v___x_882_);
v___x_919_ = lean_string_utf8_extract_fast(v_opt_868_, v___x_918_, v___x_879_);
lean_dec(v___x_918_);
lean_dec_ref(v_opt_868_);
v___f_920_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_920_, 0, v___x_919_);
v___x_921_ = lean_apply_2(v_modifyGet_914_, lean_box(0), v___f_920_);
v___x_922_ = lean_apply_4(v_toBind_913_, lean_box(0), lean_box(0), v___x_921_, v___f_916_);
return v___x_922_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v___x_882_);
lean_dec(v_longShort_874_);
lean_dec_ref(v_opt_868_);
lean_dec_ref(v_inst_866_);
lean_dec_ref(v_inst_865_);
v___x_923_ = lean_box_uint32(v___x_870_);
v___x_924_ = lean_apply_1(v_short_873_, v___x_923_);
return v___x_924_;
}
}
}
}
else
{
lean_object* v_long_928_; lean_object* v_toBind_929_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_943_; lean_object* v_searcher_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___f_961_; lean_object* v___x_962_; 
v_long_928_ = lean_ctor_get(v_handlers_867_, 0);
lean_inc(v_long_928_);
lean_dec_ref(v_handlers_867_);
v_toBind_929_ = lean_ctor_get(v_inst_865_, 1);
lean_inc(v_toBind_929_);
lean_dec_ref(v_inst_865_);
v_searcher_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_string_utf8_byte_size(v_opt_868_);
v___x_960_ = lean_box(0);
lean_inc_ref(v_opt_868_);
v___f_961_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_961_, 0, v___x_959_);
lean_closure_set(v___f_961_, 1, v_opt_868_);
lean_closure_set(v___f_961_, 2, v___x_960_);
v___x_962_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_961_, v_searcher_958_, v___x_960_, lean_box(0));
if (lean_obj_tag(v___x_962_) == 0)
{
v___y_943_ = v___x_959_;
goto v___jp_942_;
}
else
{
lean_object* v_val_963_; 
v_val_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v___x_962_, 1);
v___y_943_ = v_val_963_;
goto v___jp_942_;
}
v___jp_930_:
{
uint8_t v_decide_933_; 
v_decide_933_ = lean_nat_dec_eq(v___y_932_, v___y_931_);
if (v_decide_933_ == 0)
{
lean_object* v_modifyGet_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_modifyGet_934_ = lean_ctor_get(v_inst_866_, 2);
lean_inc(v_modifyGet_934_);
lean_dec_ref(v_inst_866_);
lean_inc(v___y_932_);
lean_inc_ref(v_opt_868_);
v___f_935_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_935_, 0, v_opt_868_);
lean_closure_set(v___f_935_, 1, v___y_932_);
lean_closure_set(v___f_935_, 2, v_long_928_);
v___x_936_ = lean_string_utf8_next_fast(v_opt_868_, v___y_932_);
lean_dec(v___y_932_);
v___x_937_ = lean_string_utf8_extract_fast(v_opt_868_, v___x_936_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v_opt_868_);
v___f_938_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_938_, 0, v___x_937_);
v___x_939_ = lean_apply_2(v_modifyGet_934_, lean_box(0), v___f_938_);
v___x_940_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v___x_939_, v___f_935_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v_toBind_929_);
lean_dec_ref(v_inst_866_);
v___x_941_ = lean_apply_1(v_long_928_, v_opt_868_);
return v___x_941_;
}
}
v___jp_942_:
{
lean_object* v___x_944_; uint8_t v_decide_945_; 
v___x_944_ = lean_string_utf8_byte_size(v_opt_868_);
v_decide_945_ = lean_nat_dec_eq(v___y_943_, v___x_944_);
if (v_decide_945_ == 0)
{
lean_object* v_modifyGet_946_; lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_modifyGet_946_ = lean_ctor_get(v_inst_866_, 2);
lean_inc_n(v_modifyGet_946_, 2);
lean_dec_ref(v_inst_866_);
lean_inc(v_toBind_929_);
lean_inc(v___y_943_);
lean_inc_ref(v_opt_868_);
v___f_947_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__6___boxed), 6, 5);
lean_closure_set(v___f_947_, 0, v_opt_868_);
lean_closure_set(v___f_947_, 1, v___y_943_);
lean_closure_set(v___f_947_, 2, v_long_928_);
lean_closure_set(v___f_947_, 3, v_modifyGet_946_);
lean_closure_set(v___f_947_, 4, v_toBind_929_);
v___x_948_ = lean_string_utf8_next_fast(v_opt_868_, v___y_943_);
lean_dec(v___y_943_);
v___x_949_ = lean_string_utf8_extract_fast(v_opt_868_, v___x_948_, v___x_944_);
lean_dec_ref(v_opt_868_);
v___f_950_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_950_, 0, v___x_949_);
v___x_951_ = lean_apply_2(v_modifyGet_946_, lean_box(0), v___f_950_);
v___x_952_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v___x_951_, v___f_947_);
return v___x_952_;
}
else
{
lean_object* v_searcher_953_; lean_object* v___x_954_; lean_object* v___f_955_; lean_object* v___x_956_; 
lean_dec(v___y_943_);
v_searcher_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_box(0);
lean_inc_ref(v_opt_868_);
v___f_955_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_955_, 0, v___x_944_);
lean_closure_set(v___f_955_, 1, v_opt_868_);
lean_closure_set(v___f_955_, 2, v___x_954_);
v___x_956_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_955_, v_searcher_953_, v___x_954_, lean_box(0));
if (lean_obj_tag(v___x_956_) == 0)
{
v___y_931_ = v___x_944_;
v___y_932_ = v___x_944_;
goto v___jp_930_;
}
else
{
lean_object* v_val_957_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___x_956_, 1);
v___y_931_ = v___x_944_;
v___y_932_ = v_val_957_;
goto v___jp_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option(lean_object* v_m_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_00_u03b1_967_, lean_object* v_handlers_968_, lean_object* v_opt_969_){
_start:
{
lean_object* v___x_970_; uint32_t v___x_971_; uint32_t v___x_972_; uint8_t v___x_973_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_string_utf8_get(v_opt_969_, v___x_970_);
v___x_972_ = 45;
v___x_973_ = lean_uint32_dec_eq(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v_short_974_; lean_object* v_longShort_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1027_; 
v_short_974_ = lean_ctor_get(v_handlers_968_, 1);
v_longShort_975_ = lean_ctor_get(v_handlers_968_, 2);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_handlers_968_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_handlers_968_, 0);
lean_dec(v_unused_1028_);
v___x_977_ = v_handlers_968_;
v_isShared_978_ = v_isSharedCheck_1027_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_longShort_975_);
lean_inc(v_short_974_);
lean_dec(v_handlers_968_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1027_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_983_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_string_utf8_byte_size(v_opt_969_);
lean_inc_ref_n(v_opt_969_, 2);
v___f_981_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_981_, 0, v___x_980_);
lean_closure_set(v___f_981_, 1, v_opt_969_);
lean_closure_set(v___f_981_, 2, v___x_970_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 2, v___x_980_);
lean_ctor_set(v___x_977_, 1, v___x_979_);
lean_ctor_set(v___x_977_, 0, v_opt_969_);
v___x_983_ = v___x_977_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_opt_969_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v___x_980_);
v___x_983_ = v_reuseFailAlloc_1026_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_981_, v___x_979_, v___x_979_, lean_box(0));
v___x_985_ = lean_unsigned_to_nat(2u);
v___x_986_ = lean_nat_dec_eq(v___x_984_, v___x_985_);
lean_dec(v___x_984_);
if (v___x_986_ == 0)
{
uint32_t v___x_987_; uint32_t v___x_988_; uint8_t v___x_989_; 
v___x_987_ = lean_string_utf8_get(v_opt_969_, v___x_985_);
v___x_988_ = 61;
v___x_989_ = lean_uint32_dec_eq(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
uint32_t v___x_990_; uint8_t v___x_991_; 
v___x_990_ = 32;
v___x_991_ = lean_uint32_dec_eq(v___x_987_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec_ref(v___x_983_);
lean_dec(v_short_974_);
lean_dec_ref(v_inst_966_);
lean_dec_ref(v_inst_965_);
v___x_992_ = lean_apply_1(v_longShort_975_, v_opt_969_);
return v___x_992_;
}
else
{
lean_object* v_toBind_993_; lean_object* v___x_994_; lean_object* v_modifyGet_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_longShort_975_);
v_toBind_993_ = lean_ctor_get(v_inst_965_, 1);
lean_inc(v_toBind_993_);
lean_dec_ref(v_inst_965_);
v___x_994_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_995_ = lean_ctor_get(v_inst_966_, 2);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_inst_966_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1012_ = lean_ctor_get(v_inst_966_, 1);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_inst_966_, 0);
lean_dec(v_unused_1013_);
v___x_997_ = v_inst_966_;
v_isShared_998_ = v_isSharedCheck_1011_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_modifyGet_995_);
lean_dec(v_inst_966_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1011_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1003_; 
v___x_999_ = l_String_Slice_Pos_nextn(v___x_983_, v___x_979_, v___x_985_);
lean_dec_ref(v___x_983_);
v___x_1000_ = lean_box_uint32(v___x_971_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1001_, 0, v_short_974_);
lean_closure_set(v___f_1001_, 1, v___x_1000_);
lean_inc(v___x_999_);
lean_inc_ref(v_opt_969_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v___x_980_);
lean_ctor_set(v___x_997_, 1, v___x_999_);
lean_ctor_set(v___x_997_, 0, v_opt_969_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_opt_969_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v___x_980_);
v___x_1003_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1004_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1003_, v___x_979_, v___x_994_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_nat_add(v___x_999_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v___x_999_);
v___x_1006_ = lean_string_utf8_extract_fast(v_opt_969_, v___x_1005_, v___x_980_);
lean_dec(v___x_1005_);
lean_dec_ref(v_opt_969_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1007_, 0, v___x_1006_);
v___x_1008_ = lean_apply_2(v_modifyGet_995_, lean_box(0), v___f_1007_);
v___x_1009_ = lean_apply_4(v_toBind_993_, lean_box(0), lean_box(0), v___x_1008_, v___f_1001_);
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_toBind_1014_; lean_object* v_modifyGet_1015_; lean_object* v___x_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v_longShort_975_);
v_toBind_1014_ = lean_ctor_get(v_inst_965_, 1);
lean_inc(v_toBind_1014_);
lean_dec_ref(v_inst_965_);
v_modifyGet_1015_ = lean_ctor_get(v_inst_966_, 2);
lean_inc(v_modifyGet_1015_);
lean_dec_ref(v_inst_966_);
v___x_1016_ = lean_box_uint32(v___x_971_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1017_, 0, v_short_974_);
lean_closure_set(v___f_1017_, 1, v___x_1016_);
v___x_1018_ = lean_unsigned_to_nat(3u);
v___x_1019_ = l_String_Slice_Pos_nextn(v___x_983_, v___x_979_, v___x_1018_);
lean_dec_ref(v___x_983_);
v___x_1020_ = lean_string_utf8_extract_fast(v_opt_969_, v___x_1019_, v___x_980_);
lean_dec(v___x_1019_);
lean_dec_ref(v_opt_969_);
v___f_1021_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1021_, 0, v___x_1020_);
v___x_1022_ = lean_apply_2(v_modifyGet_1015_, lean_box(0), v___f_1021_);
v___x_1023_ = lean_apply_4(v_toBind_1014_, lean_box(0), lean_box(0), v___x_1022_, v___f_1017_);
return v___x_1023_;
}
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec_ref(v___x_983_);
lean_dec(v_longShort_975_);
lean_dec_ref(v_opt_969_);
lean_dec_ref(v_inst_966_);
lean_dec_ref(v_inst_965_);
v___x_1024_ = lean_box_uint32(v___x_971_);
v___x_1025_ = lean_apply_1(v_short_974_, v___x_1024_);
return v___x_1025_;
}
}
}
}
else
{
lean_object* v_long_1029_; lean_object* v_toBind_1030_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1044_; lean_object* v_searcher_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; 
v_long_1029_ = lean_ctor_get(v_handlers_968_, 0);
lean_inc(v_long_1029_);
lean_dec_ref(v_handlers_968_);
v_toBind_1030_ = lean_ctor_get(v_inst_965_, 1);
lean_inc(v_toBind_1030_);
lean_dec_ref(v_inst_965_);
v_searcher_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_string_utf8_byte_size(v_opt_969_);
v___x_1061_ = lean_box(0);
lean_inc_ref(v_opt_969_);
v___f_1062_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1062_, 0, v___x_1060_);
lean_closure_set(v___f_1062_, 1, v_opt_969_);
lean_closure_set(v___f_1062_, 2, v___x_1061_);
v___x_1063_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1062_, v_searcher_1059_, v___x_1061_, lean_box(0));
if (lean_obj_tag(v___x_1063_) == 0)
{
v___y_1044_ = v___x_1060_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1064_; 
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_val_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___y_1044_ = v_val_1064_;
goto v___jp_1043_;
}
v___jp_1031_:
{
uint8_t v_decide_1034_; 
v_decide_1034_ = lean_nat_dec_eq(v___y_1033_, v___y_1032_);
if (v_decide_1034_ == 0)
{
lean_object* v_modifyGet_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_modifyGet_1035_ = lean_ctor_get(v_inst_966_, 2);
lean_inc(v_modifyGet_1035_);
lean_dec_ref(v_inst_966_);
lean_inc(v___y_1033_);
lean_inc_ref(v_opt_969_);
v___f_1036_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1036_, 0, v_opt_969_);
lean_closure_set(v___f_1036_, 1, v___y_1033_);
lean_closure_set(v___f_1036_, 2, v_long_1029_);
v___x_1037_ = lean_string_utf8_next_fast(v_opt_969_, v___y_1033_);
lean_dec(v___y_1033_);
v___x_1038_ = lean_string_utf8_extract_fast(v_opt_969_, v___x_1037_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v_opt_969_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1039_, 0, v___x_1038_);
v___x_1040_ = lean_apply_2(v_modifyGet_1035_, lean_box(0), v___f_1039_);
v___x_1041_ = lean_apply_4(v_toBind_1030_, lean_box(0), lean_box(0), v___x_1040_, v___f_1036_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; 
lean_dec(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v_toBind_1030_);
lean_dec_ref(v_inst_966_);
v___x_1042_ = lean_apply_1(v_long_1029_, v_opt_969_);
return v___x_1042_;
}
}
v___jp_1043_:
{
lean_object* v___x_1045_; uint8_t v_decide_1046_; 
v___x_1045_ = lean_string_utf8_byte_size(v_opt_969_);
v_decide_1046_ = lean_nat_dec_eq(v___y_1044_, v___x_1045_);
if (v_decide_1046_ == 0)
{
lean_object* v_modifyGet_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_modifyGet_1047_ = lean_ctor_get(v_inst_966_, 2);
lean_inc_n(v_modifyGet_1047_, 2);
lean_dec_ref(v_inst_966_);
lean_inc(v_toBind_1030_);
lean_inc(v___y_1044_);
lean_inc_ref(v_opt_969_);
v___f_1048_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__6___boxed), 6, 5);
lean_closure_set(v___f_1048_, 0, v_opt_969_);
lean_closure_set(v___f_1048_, 1, v___y_1044_);
lean_closure_set(v___f_1048_, 2, v_long_1029_);
lean_closure_set(v___f_1048_, 3, v_modifyGet_1047_);
lean_closure_set(v___f_1048_, 4, v_toBind_1030_);
v___x_1049_ = lean_string_utf8_next_fast(v_opt_969_, v___y_1044_);
lean_dec(v___y_1044_);
v___x_1050_ = lean_string_utf8_extract_fast(v_opt_969_, v___x_1049_, v___x_1045_);
lean_dec_ref(v_opt_969_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1051_, 0, v___x_1050_);
v___x_1052_ = lean_apply_2(v_modifyGet_1047_, lean_box(0), v___f_1051_);
v___x_1053_ = lean_apply_4(v_toBind_1030_, lean_box(0), lean_box(0), v___x_1052_, v___f_1048_);
return v___x_1053_;
}
else
{
lean_object* v_searcher_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; 
lean_dec(v___y_1044_);
v_searcher_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_box(0);
lean_inc_ref(v_opt_969_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1056_, 0, v___x_1045_);
lean_closure_set(v___f_1056_, 1, v_opt_969_);
lean_closure_set(v___f_1056_, 2, v___x_1055_);
v___x_1057_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1056_, v_searcher_1054_, v___x_1055_, lean_box(0));
if (lean_obj_tag(v___x_1057_) == 0)
{
v___y_1032_ = v___x_1045_;
v___y_1033_ = v___x_1045_;
goto v___jp_1031_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___y_1032_ = v___x_1045_;
v___y_1033_ = v_val_1058_;
goto v___jp_1031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object* v___x_1065_, lean_object* v_head_1066_, lean_object* v___x_1067_, lean_object* v_it_1068_, lean_object* v_acc_1069_, lean_object* v_hP_1070_, lean_object* v_recur_1071_){
_start:
{
uint8_t v_decide_1072_; 
v_decide_1072_ = lean_nat_dec_eq(v_it_1068_, v___x_1065_);
if (v_decide_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_string_utf8_next_fast(v_head_1066_, v_it_1068_);
v___x_1074_ = lean_nat_add(v_acc_1069_, v___x_1067_);
v___x_1075_ = lean_apply_4(v_recur_1071_, v___x_1073_, v___x_1074_, lean_box(0), lean_box(0));
return v___x_1075_;
}
else
{
lean_dec_ref(v_recur_1071_);
lean_inc(v_acc_1069_);
return v_acc_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0___boxed(lean_object* v___x_1076_, lean_object* v_head_1077_, lean_object* v___x_1078_, lean_object* v_it_1079_, lean_object* v_acc_1080_, lean_object* v_hP_1081_, lean_object* v_recur_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lake_processLeadingOption___redArg___lam__0(v___x_1076_, v_head_1077_, v___x_1078_, v_it_1079_, v_acc_1080_, v_hP_1081_, v_recur_1082_);
lean_dec(v_acc_1080_);
lean_dec(v_it_1079_);
lean_dec(v___x_1078_);
lean_dec_ref(v_head_1077_);
lean_dec(v___x_1076_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object* v_handle_1084_, lean_object* v_head_1085_, lean_object* v_____r_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_apply_1(v_handle_1084_, v_head_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__2(lean_object* v_toPure_1088_, lean_object* v_handle_1089_, lean_object* v_set_1090_, lean_object* v_toBind_1091_, lean_object* v_____do__lift_1092_){
_start:
{
if (lean_obj_tag(v_____do__lift_1092_) == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_toBind_1091_);
lean_dec(v_set_1090_);
lean_dec(v_handle_1089_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_apply_2(v_toPure_1088_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v_head_1098_; lean_object* v_tail_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_head_1098_ = lean_ctor_get(v_____do__lift_1092_, 0);
lean_inc_n(v_head_1098_, 2);
v_tail_1099_ = lean_ctor_get(v_____do__lift_1092_, 1);
lean_inc(v_tail_1099_);
lean_dec_ref_known(v_____do__lift_1092_, 2);
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_string_utf8_byte_size(v_head_1098_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1103_, 0, v___x_1102_);
lean_closure_set(v___f_1103_, 1, v_head_1098_);
lean_closure_set(v___f_1103_, 2, v___x_1100_);
v___x_1104_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1103_, v___x_1101_, v___x_1101_, lean_box(0));
v___x_1105_ = lean_nat_dec_lt(v___x_1100_, v___x_1104_);
lean_dec(v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec(v_tail_1099_);
lean_dec(v_head_1098_);
lean_dec(v_toBind_1091_);
lean_dec(v_set_1090_);
lean_dec(v_handle_1089_);
goto v___jp_1093_;
}
else
{
uint32_t v___x_1106_; uint32_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_string_utf8_get(v_head_1098_, v___x_1101_);
v___x_1107_ = 45;
v___x_1108_ = lean_uint32_dec_eq(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec(v_tail_1099_);
lean_dec(v_head_1098_);
lean_dec(v_toBind_1091_);
lean_dec(v_set_1090_);
lean_dec(v_handle_1089_);
goto v___jp_1093_;
}
else
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v_toPure_1088_);
v___f_1109_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1109_, 0, v_handle_1089_);
lean_closure_set(v___f_1109_, 1, v_head_1098_);
v___x_1110_ = lean_apply_1(v_set_1090_, v_tail_1099_);
v___x_1111_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1110_, v___f_1109_);
return v___x_1111_;
}
}
}
v___jp_1093_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_apply_2(v_toPure_1088_, lean_box(0), v___x_1094_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_handle_1114_){
_start:
{
lean_object* v_toApplicative_1115_; lean_object* v_toBind_1116_; lean_object* v_get_1117_; lean_object* v_set_1118_; lean_object* v_toPure_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; 
v_toApplicative_1115_ = lean_ctor_get(v_inst_1112_, 0);
lean_inc_ref(v_toApplicative_1115_);
v_toBind_1116_ = lean_ctor_get(v_inst_1112_, 1);
lean_inc_n(v_toBind_1116_, 2);
lean_dec_ref(v_inst_1112_);
v_get_1117_ = lean_ctor_get(v_inst_1113_, 0);
lean_inc(v_get_1117_);
v_set_1118_ = lean_ctor_get(v_inst_1113_, 1);
lean_inc(v_set_1118_);
lean_dec_ref(v_inst_1113_);
v_toPure_1119_ = lean_ctor_get(v_toApplicative_1115_, 1);
lean_inc(v_toPure_1119_);
lean_dec_ref(v_toApplicative_1115_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1120_, 0, v_toPure_1119_);
lean_closure_set(v___f_1120_, 1, v_handle_1114_);
lean_closure_set(v___f_1120_, 2, v_set_1118_);
lean_closure_set(v___f_1120_, 3, v_toBind_1116_);
v___x_1121_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v_get_1117_, v___f_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object* v_m_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_handle_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lake_processLeadingOption___redArg(v_inst_1123_, v_inst_1124_, v_handle_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object* v_handle_1127_, lean_object* v_head_1128_, lean_object* v_toBind_1129_, lean_object* v___f_1130_, lean_object* v_____r_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_apply_1(v_handle_1127_, v_head_1128_);
v___x_1133_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v___x_1132_, v___f_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object* v___x_1134_, lean_object* v_head_1135_, lean_object* v_it_1136_, lean_object* v_acc_1137_, lean_object* v_hP_1138_, lean_object* v_recur_1139_){
_start:
{
uint8_t v_decide_1140_; 
v_decide_1140_ = lean_nat_dec_eq(v_it_1136_, v___x_1134_);
if (v_decide_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = lean_string_utf8_next_fast(v_head_1135_, v_it_1136_);
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_add(v_acc_1137_, v___x_1142_);
v___x_1144_ = lean_apply_4(v_recur_1139_, v___x_1141_, v___x_1143_, lean_box(0), lean_box(0));
return v___x_1144_;
}
else
{
lean_dec_ref(v_recur_1139_);
lean_inc(v_acc_1137_);
return v_acc_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2___boxed(lean_object* v___x_1145_, lean_object* v_head_1146_, lean_object* v_it_1147_, lean_object* v_acc_1148_, lean_object* v_hP_1149_, lean_object* v_recur_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lake_processLeadingOptions___redArg___lam__2(v___x_1145_, v_head_1146_, v_it_1147_, v_acc_1148_, v_hP_1149_, v_recur_1150_);
lean_dec(v_acc_1148_);
lean_dec(v_it_1147_);
lean_dec_ref(v_head_1146_);
lean_dec(v___x_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__3(lean_object* v_toPure_1152_, lean_object* v_set_1153_, lean_object* v_toBind_1154_, lean_object* v___f_1155_, lean_object* v_handle_1156_, lean_object* v___f_1157_, lean_object* v_____do__lift_1158_){
_start:
{
if (lean_obj_tag(v_____do__lift_1158_) == 1)
{
lean_object* v_head_1159_; lean_object* v_tail_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v_len_1164_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_head_1159_ = lean_ctor_get(v_____do__lift_1158_, 0);
lean_inc_n(v_head_1159_, 2);
v_tail_1160_ = lean_ctor_get(v_____do__lift_1158_, 1);
lean_inc(v_tail_1160_);
lean_dec_ref_known(v_____do__lift_1158_, 2);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_string_utf8_byte_size(v_head_1159_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__2___boxed), 6, 2);
lean_closure_set(v___f_1163_, 0, v___x_1162_);
lean_closure_set(v___f_1163_, 1, v_head_1159_);
v_len_1164_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1163_, v___x_1161_, v___x_1161_, lean_box(0));
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_nat_dec_lt(v___x_1171_, v_len_1164_);
if (v___x_1172_ == 0)
{
lean_dec(v_head_1159_);
lean_dec(v___f_1157_);
lean_dec(v_handle_1156_);
goto v___jp_1165_;
}
else
{
uint32_t v___x_1173_; uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = lean_string_utf8_get(v_head_1159_, v___x_1161_);
v___x_1174_ = 45;
v___x_1175_ = lean_uint32_dec_eq(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_dec(v_head_1159_);
lean_dec(v___f_1157_);
lean_dec(v_handle_1156_);
goto v___jp_1165_;
}
else
{
lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_len_1164_);
lean_dec(v___f_1155_);
lean_dec(v_toPure_1152_);
lean_inc(v_toBind_1154_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1176_, 0, v_handle_1156_);
lean_closure_set(v___f_1176_, 1, v_head_1159_);
lean_closure_set(v___f_1176_, 2, v_toBind_1154_);
lean_closure_set(v___f_1176_, 3, v___f_1157_);
v___x_1177_ = lean_apply_1(v_set_1153_, v_tail_1160_);
v___x_1178_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1177_, v___f_1176_);
return v___x_1178_;
}
}
v___jp_1165_:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_nat_dec_eq(v_len_1164_, v___x_1161_);
lean_dec(v_len_1164_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_tail_1160_);
lean_dec(v___f_1155_);
lean_dec(v_toBind_1154_);
lean_dec(v_set_1153_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_apply_2(v_toPure_1152_, lean_box(0), v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v_toPure_1152_);
v___x_1169_ = lean_apply_1(v_set_1153_, v_tail_1160_);
v___x_1170_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1169_, v___f_1155_);
return v___x_1170_;
}
}
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v_____do__lift_1158_);
lean_dec(v___f_1157_);
lean_dec(v_handle_1156_);
lean_dec(v___f_1155_);
lean_dec(v_toBind_1154_);
lean_dec(v_set_1153_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_apply_2(v_toPure_1152_, lean_box(0), v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_handle_1183_){
_start:
{
lean_object* v_toApplicative_1184_; lean_object* v_toBind_1185_; lean_object* v_get_1186_; lean_object* v_set_1187_; lean_object* v_toPure_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; 
v_toApplicative_1184_ = lean_ctor_get(v_inst_1181_, 0);
v_toBind_1185_ = lean_ctor_get(v_inst_1181_, 1);
lean_inc_n(v_toBind_1185_, 2);
v_get_1186_ = lean_ctor_get(v_inst_1182_, 0);
lean_inc(v_get_1186_);
v_set_1187_ = lean_ctor_get(v_inst_1182_, 1);
lean_inc(v_set_1187_);
v_toPure_1188_ = lean_ctor_get(v_toApplicative_1184_, 1);
lean_inc(v_toPure_1188_);
lean_inc(v_handle_1183_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1189_, 0, v_inst_1181_);
lean_closure_set(v___f_1189_, 1, v_inst_1182_);
lean_closure_set(v___f_1189_, 2, v_handle_1183_);
lean_inc_ref(v___f_1189_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1190_, 0, v_toPure_1188_);
lean_closure_set(v___f_1190_, 1, v_set_1187_);
lean_closure_set(v___f_1190_, 2, v_toBind_1185_);
lean_closure_set(v___f_1190_, 3, v___f_1189_);
lean_closure_set(v___f_1190_, 4, v_handle_1183_);
lean_closure_set(v___f_1190_, 5, v___f_1189_);
v___x_1191_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v_get_1186_, v___f_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_handle_1194_, lean_object* v_____r_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lake_processLeadingOptions___redArg(v_inst_1192_, v_inst_1193_, v_handle_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object* v_m_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_handle_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lake_processLeadingOptions___redArg(v_inst_1198_, v_inst_1199_, v_handle_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_x_1202_);
return v___x_1204_;
}
else
{
lean_object* v_head_1205_; lean_object* v_tail_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_head_1205_ = lean_ctor_get(v_x_1202_, 0);
v_tail_1206_ = lean_ctor_get(v_x_1202_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1202_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v_x_1202_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_tail_1206_);
lean_inc(v_head_1205_);
lean_dec(v_x_1202_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_head_1205_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_tail_1206_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object* v___x_1215_, lean_object* v_val_1216_, lean_object* v_it_1217_, lean_object* v_acc_1218_, lean_object* v_hP_1219_, lean_object* v_recur_1220_){
_start:
{
uint8_t v_decide_1221_; 
v_decide_1221_ = lean_nat_dec_eq(v_it_1217_, v___x_1215_);
if (v_decide_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_string_utf8_next_fast(v_val_1216_, v_it_1217_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_add(v_acc_1218_, v___x_1223_);
v___x_1225_ = lean_apply_4(v_recur_1220_, v___x_1222_, v___x_1224_, lean_box(0), lean_box(0));
return v___x_1225_;
}
else
{
lean_dec_ref(v_recur_1220_);
lean_inc(v_acc_1218_);
return v_acc_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2___boxed(lean_object* v___x_1226_, lean_object* v_val_1227_, lean_object* v_it_1228_, lean_object* v_acc_1229_, lean_object* v_hP_1230_, lean_object* v_recur_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lake_collectArgs___redArg___lam__2(v___x_1226_, v_val_1227_, v_it_1228_, v_acc_1229_, v_hP_1230_, v_recur_1231_);
lean_dec(v_acc_1229_);
lean_dec(v_it_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__3(lean_object* v_args_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_option_1237_, lean_object* v_toBind_1238_, lean_object* v___f_1239_, lean_object* v_toPure_1240_, lean_object* v_____do__lift_1241_){
_start:
{
if (lean_obj_tag(v_____do__lift_1241_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; lean_object* v_len_1246_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
lean_dec(v_toPure_1240_);
v_val_1242_ = lean_ctor_get(v_____do__lift_1241_, 0);
lean_inc_n(v_val_1242_, 2);
lean_dec_ref_known(v_____do__lift_1241_, 1);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_string_utf8_byte_size(v_val_1242_);
v___f_1245_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__2___boxed), 6, 2);
lean_closure_set(v___f_1245_, 0, v___x_1244_);
lean_closure_set(v___f_1245_, 1, v_val_1242_);
v_len_1246_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1245_, v___x_1243_, v___x_1243_, lean_box(0));
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_dec_lt(v___x_1252_, v_len_1246_);
if (v___x_1253_ == 0)
{
lean_dec(v___f_1239_);
lean_dec(v_toBind_1238_);
goto v___jp_1247_;
}
else
{
uint32_t v___x_1254_; uint32_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1254_ = lean_string_utf8_get(v_val_1242_, v___x_1243_);
v___x_1255_ = 45;
v___x_1256_ = lean_uint32_dec_eq(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v___f_1239_);
lean_dec(v_toBind_1238_);
goto v___jp_1247_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v_len_1246_);
lean_dec_ref(v_inst_1236_);
lean_dec_ref(v_inst_1235_);
lean_dec_ref(v_args_1234_);
v___x_1257_ = lean_apply_1(v_option_1237_, v_val_1242_);
v___x_1258_ = lean_apply_4(v_toBind_1238_, lean_box(0), lean_box(0), v___x_1257_, v___f_1239_);
return v___x_1258_;
}
}
v___jp_1247_:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_nat_dec_eq(v_len_1246_, v___x_1243_);
lean_dec(v_len_1246_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_array_push(v_args_1234_, v_val_1242_);
v___x_1250_ = l_Lake_collectArgs___redArg(v_inst_1235_, v_inst_1236_, v_option_1237_, v___x_1249_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; 
lean_dec(v_val_1242_);
v___x_1251_ = l_Lake_collectArgs___redArg(v_inst_1235_, v_inst_1236_, v_option_1237_, v_args_1234_);
return v___x_1251_;
}
}
}
else
{
lean_object* v___x_1259_; 
lean_dec(v_____do__lift_1241_);
lean_dec(v___f_1239_);
lean_dec(v_toBind_1238_);
lean_dec(v_option_1237_);
lean_dec_ref(v_inst_1236_);
lean_dec_ref(v_inst_1235_);
v___x_1259_ = lean_apply_2(v_toPure_1240_, lean_box(0), v_args_1234_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_option_1262_, lean_object* v_args_1263_){
_start:
{
lean_object* v_toApplicative_1264_; lean_object* v_toBind_1265_; lean_object* v_modifyGet_1266_; lean_object* v_toPure_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; 
v_toApplicative_1264_ = lean_ctor_get(v_inst_1260_, 0);
v_toBind_1265_ = lean_ctor_get(v_inst_1260_, 1);
lean_inc_n(v_toBind_1265_, 2);
v_modifyGet_1266_ = lean_ctor_get(v_inst_1261_, 2);
v_toPure_1267_ = lean_ctor_get(v_toApplicative_1264_, 1);
lean_inc(v_toPure_1267_);
v___f_1268_ = ((lean_object*)(l_Lake_collectArgs___redArg___closed__0));
lean_inc_ref(v_args_1263_);
lean_inc(v_option_1262_);
lean_inc_ref(v_inst_1261_);
lean_inc_ref(v_inst_1260_);
v___f_1269_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1269_, 0, v_inst_1260_);
lean_closure_set(v___f_1269_, 1, v_inst_1261_);
lean_closure_set(v___f_1269_, 2, v_option_1262_);
lean_closure_set(v___f_1269_, 3, v_args_1263_);
lean_inc(v_modifyGet_1266_);
v___x_1270_ = lean_apply_2(v_modifyGet_1266_, lean_box(0), v___f_1268_);
v___f_1271_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1271_, 0, v_args_1263_);
lean_closure_set(v___f_1271_, 1, v_inst_1260_);
lean_closure_set(v___f_1271_, 2, v_inst_1261_);
lean_closure_set(v___f_1271_, 3, v_option_1262_);
lean_closure_set(v___f_1271_, 4, v_toBind_1265_);
lean_closure_set(v___f_1271_, 5, v___f_1269_);
lean_closure_set(v___f_1271_, 6, v_toPure_1267_);
v___x_1272_ = lean_apply_4(v_toBind_1265_, lean_box(0), lean_box(0), v___x_1270_, v___f_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_option_1275_, lean_object* v_args_1276_, lean_object* v_____r_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lake_collectArgs___redArg(v_inst_1273_, v_inst_1274_, v_option_1275_, v_args_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object* v_m_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_option_1282_, lean_object* v_args_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lake_collectArgs___redArg(v_inst_1280_, v_inst_1281_, v_option_1282_, v_args_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object* v_inst_1285_, lean_object* v_____do__lift_1286_){
_start:
{
lean_object* v_set_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_set_1287_ = lean_ctor_get(v_inst_1285_, 1);
lean_inc(v_set_1287_);
lean_dec_ref(v_inst_1285_);
v___x_1288_ = lean_array_to_list(v_____do__lift_1286_);
v___x_1289_ = lean_apply_1(v_set_1287_, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_handle_1294_){
_start:
{
lean_object* v_toBind_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_toBind_1295_ = lean_ctor_get(v_inst_1292_, 1);
lean_inc(v_toBind_1295_);
lean_inc_ref(v_inst_1293_);
v___f_1296_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1296_, 0, v_inst_1293_);
v___x_1297_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1298_ = l_Lake_collectArgs___redArg(v_inst_1292_, v_inst_1293_, v_handle_1294_, v___x_1297_);
v___x_1299_ = lean_apply_4(v_toBind_1295_, lean_box(0), lean_box(0), v___x_1298_, v___f_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object* v_m_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_handle_1303_){
_start:
{
lean_object* v_toBind_1304_; lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_toBind_1304_ = lean_ctor_get(v_inst_1301_, 1);
lean_inc(v_toBind_1304_);
lean_inc_ref(v_inst_1302_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1305_, 0, v_inst_1302_);
v___x_1306_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1307_ = l_Lake_collectArgs___redArg(v_inst_1301_, v_inst_1302_, v_handle_1303_, v___x_1306_);
v___x_1308_ = lean_apply_4(v_toBind_1304_, lean_box(0), lean_box(0), v___x_1307_, v___f_1305_);
return v___x_1308_;
}
}
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Cli(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Cli(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Cli(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Cli(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Cli(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Cli(builtin);
}
#ifdef __cplusplus
}
#endif
