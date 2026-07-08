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
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_159_ = lean_string_utf8_extract(v_opt_146_, v___x_158_, v___x_148_);
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
v___x_185_ = lean_string_utf8_extract(v_opt_172_, v___x_184_, v___x_174_);
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
v___x_216_ = lean_string_utf8_extract(v_opt_199_, v___x_215_, v___x_202_);
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
v___x_246_ = lean_string_utf8_extract(v_opt_229_, v___x_245_, v___x_232_);
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
v___x_270_ = lean_string_utf8_extract(v_opt_257_, v___x_269_, v___x_259_);
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
v___x_296_ = lean_string_utf8_extract(v_opt_283_, v___x_295_, v___x_285_);
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
uint8_t v___x_314_; 
v___x_314_ = lean_string_utf8_at_end(v_opt_312_, v_p_313_);
if (v___x_314_ == 0)
{
lean_object* v_toBind_315_; lean_object* v___f_316_; uint32_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_toBind_315_ = lean_ctor_get(v_inst_310_, 1);
lean_inc(v_toBind_315_);
lean_inc(v_handle_311_);
lean_inc(v_p_313_);
lean_inc_ref(v_opt_312_);
v___f_316_ = lean_alloc_closure((void*)(l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_316_, 0, v_opt_312_);
lean_closure_set(v___f_316_, 1, v_p_313_);
lean_closure_set(v___f_316_, 2, v_inst_310_);
lean_closure_set(v___f_316_, 3, v_handle_311_);
v___x_317_ = lean_string_utf8_get_fast(v_opt_312_, v_p_313_);
lean_dec(v_p_313_);
lean_dec_ref(v_opt_312_);
v___x_318_ = lean_box_uint32(v___x_317_);
v___x_319_ = lean_apply_1(v_handle_311_, v___x_318_);
v___x_320_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v___x_319_, v___f_316_);
return v___x_320_;
}
else
{
lean_object* v_toApplicative_321_; lean_object* v_toPure_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_p_313_);
lean_dec_ref(v_opt_312_);
lean_dec(v_handle_311_);
v_toApplicative_321_ = lean_ctor_get(v_inst_310_, 0);
lean_inc_ref(v_toApplicative_321_);
lean_dec_ref(v_inst_310_);
v_toPure_322_ = lean_ctor_get(v_toApplicative_321_, 1);
lean_inc(v_toPure_322_);
lean_dec_ref(v_toApplicative_321_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_apply_2(v_toPure_322_, lean_box(0), v___x_323_);
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
v___x_354_ = lean_string_utf8_extract(v_opt_349_, v___x_353_, v___y_350_);
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
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_eq(v_it_364_, v___x_361_);
if (v___x_368_ == 0)
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
lean_object* v___y_388_; lean_object* v_searcher_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___x_404_; 
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
v___y_388_ = v___x_401_;
goto v___jp_387_;
}
else
{
lean_object* v_val_405_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v___x_404_, 1);
v___y_388_ = v_val_405_;
goto v___jp_387_;
}
v___jp_387_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_string_utf8_byte_size(v_opt_386_);
v___x_390_ = lean_nat_dec_eq(v___y_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v_toBind_391_; lean_object* v_modifyGet_392_; lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_toBind_391_ = lean_ctor_get(v_inst_383_, 1);
lean_inc(v_toBind_391_);
lean_dec_ref(v_inst_383_);
v_modifyGet_392_ = lean_ctor_get(v_inst_384_, 2);
lean_inc(v_modifyGet_392_);
lean_dec_ref(v_inst_384_);
lean_inc(v___y_388_);
lean_inc_ref(v_opt_386_);
v___f_393_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_393_, 0, v_opt_386_);
lean_closure_set(v___f_393_, 1, v___y_388_);
lean_closure_set(v___f_393_, 2, v_handle_385_);
v___x_394_ = lean_string_utf8_next_fast(v_opt_386_, v___y_388_);
lean_dec(v___y_388_);
v___x_395_ = lean_string_utf8_extract(v_opt_386_, v___x_394_, v___x_389_);
lean_dec_ref(v_opt_386_);
v___f_396_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_396_, 0, v___x_395_);
v___x_397_ = lean_apply_2(v_modifyGet_392_, lean_box(0), v___f_396_);
v___x_398_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v___x_397_, v___f_393_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
lean_dec(v___y_388_);
lean_dec_ref(v_inst_384_);
lean_dec_ref(v_inst_383_);
v___x_399_ = lean_apply_1(v_handle_385_, v_opt_386_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object* v_m_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_00_u03b1_409_, lean_object* v_handle_410_, lean_object* v_opt_411_){
_start:
{
lean_object* v___y_413_; lean_object* v_searcher_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; 
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
v___y_413_ = v___x_426_;
goto v___jp_412_;
}
else
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___x_429_, 1);
v___y_413_ = v_val_430_;
goto v___jp_412_;
}
v___jp_412_:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_string_utf8_byte_size(v_opt_411_);
v___x_415_ = lean_nat_dec_eq(v___y_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v_toBind_416_; lean_object* v_modifyGet_417_; lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_toBind_416_ = lean_ctor_get(v_inst_407_, 1);
lean_inc(v_toBind_416_);
lean_dec_ref(v_inst_407_);
v_modifyGet_417_ = lean_ctor_get(v_inst_408_, 2);
lean_inc(v_modifyGet_417_);
lean_dec_ref(v_inst_408_);
lean_inc(v___y_413_);
lean_inc_ref(v_opt_411_);
v___f_418_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_418_, 0, v_opt_411_);
lean_closure_set(v___f_418_, 1, v___y_413_);
lean_closure_set(v___f_418_, 2, v_handle_410_);
v___x_419_ = lean_string_utf8_next_fast(v_opt_411_, v___y_413_);
lean_dec(v___y_413_);
v___x_420_ = lean_string_utf8_extract(v_opt_411_, v___x_419_, v___x_414_);
lean_dec_ref(v_opt_411_);
v___f_421_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_421_, 0, v___x_420_);
v___x_422_ = lean_apply_2(v_modifyGet_417_, lean_box(0), v___f_421_);
v___x_423_ = lean_apply_4(v_toBind_416_, lean_box(0), lean_box(0), v___x_422_, v___f_418_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
lean_dec(v___y_413_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_407_);
v___x_424_ = lean_apply_1(v_handle_410_, v_opt_411_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2(lean_object* v___x_431_, lean_object* v_opt_432_, lean_object* v___x_433_, lean_object* v_it_434_, lean_object* v_acc_435_, lean_object* v_hP_436_, lean_object* v_recur_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = lean_nat_dec_eq(v_it_434_, v___x_431_);
if (v___x_438_ == 0)
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
lean_object* v___y_458_; lean_object* v_searcher_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___x_474_; 
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
v___y_458_ = v___x_471_;
goto v___jp_457_;
}
else
{
lean_object* v_val_475_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_474_, 1);
v___y_458_ = v_val_475_;
goto v___jp_457_;
}
v___jp_457_:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_string_utf8_byte_size(v_opt_456_);
v___x_460_ = lean_nat_dec_eq(v___y_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v_toBind_461_; lean_object* v_modifyGet_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_toBind_461_ = lean_ctor_get(v_inst_453_, 1);
lean_inc(v_toBind_461_);
lean_dec_ref(v_inst_453_);
v_modifyGet_462_ = lean_ctor_get(v_inst_454_, 2);
lean_inc(v_modifyGet_462_);
lean_dec_ref(v_inst_454_);
lean_inc(v___y_458_);
lean_inc_ref(v_opt_456_);
v___f_463_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_463_, 0, v_opt_456_);
lean_closure_set(v___f_463_, 1, v___y_458_);
lean_closure_set(v___f_463_, 2, v_handle_455_);
v___x_464_ = lean_string_utf8_next_fast(v_opt_456_, v___y_458_);
lean_dec(v___y_458_);
v___x_465_ = lean_string_utf8_extract(v_opt_456_, v___x_464_, v___x_459_);
lean_dec_ref(v_opt_456_);
v___f_466_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_466_, 0, v___x_465_);
v___x_467_ = lean_apply_2(v_modifyGet_462_, lean_box(0), v___f_466_);
v___x_468_ = lean_apply_4(v_toBind_461_, lean_box(0), lean_box(0), v___x_467_, v___f_463_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v___y_458_);
lean_dec_ref(v_inst_454_);
lean_dec_ref(v_inst_453_);
v___x_469_ = lean_apply_1(v_handle_455_, v_opt_456_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object* v_m_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_00_u03b1_479_, lean_object* v_handle_480_, lean_object* v_opt_481_){
_start:
{
lean_object* v___y_483_; lean_object* v_searcher_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___f_498_; lean_object* v___x_499_; 
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
v___y_483_ = v___x_496_;
goto v___jp_482_;
}
else
{
lean_object* v_val_500_; 
v_val_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v___x_499_, 1);
v___y_483_ = v_val_500_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_string_utf8_byte_size(v_opt_481_);
v___x_485_ = lean_nat_dec_eq(v___y_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v_toBind_486_; lean_object* v_modifyGet_487_; lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_toBind_486_ = lean_ctor_get(v_inst_477_, 1);
lean_inc(v_toBind_486_);
lean_dec_ref(v_inst_477_);
v_modifyGet_487_ = lean_ctor_get(v_inst_478_, 2);
lean_inc(v_modifyGet_487_);
lean_dec_ref(v_inst_478_);
lean_inc(v___y_483_);
lean_inc_ref(v_opt_481_);
v___f_488_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_488_, 0, v_opt_481_);
lean_closure_set(v___f_488_, 1, v___y_483_);
lean_closure_set(v___f_488_, 2, v_handle_480_);
v___x_489_ = lean_string_utf8_next_fast(v_opt_481_, v___y_483_);
lean_dec(v___y_483_);
v___x_490_ = lean_string_utf8_extract(v_opt_481_, v___x_489_, v___x_484_);
lean_dec_ref(v_opt_481_);
v___f_491_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_491_, 0, v___x_490_);
v___x_492_ = lean_apply_2(v_modifyGet_487_, lean_box(0), v___f_491_);
v___x_493_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_492_, v___f_488_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
lean_dec(v___y_483_);
lean_dec_ref(v_inst_478_);
lean_dec_ref(v_inst_477_);
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
v___x_506_ = lean_string_utf8_extract(v___x_501_, v_searcher_502_, v___y_503_);
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
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_eq(v_it_517_, v___x_514_);
if (v___x_521_ == 0)
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
v___x_543_ = lean_string_utf8_extract(v_opt_536_, v_searcher_542_, v___y_537_);
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
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_string_utf8_byte_size(v___x_543_);
v___x_547_ = lean_nat_dec_eq(v___y_545_, v___x_546_);
if (v___x_547_ == 0)
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
v___x_550_ = lean_string_utf8_extract(v___x_543_, v___x_549_, v___x_546_);
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
lean_object* v___y_572_; lean_object* v___y_585_; lean_object* v_searcher_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___x_605_; 
v_searcher_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_string_utf8_byte_size(v_opt_570_);
v___x_603_ = lean_box(0);
lean_inc_ref(v_opt_570_);
v___f_604_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_604_, 0, v___x_602_);
lean_closure_set(v___f_604_, 1, v_opt_570_);
lean_closure_set(v___f_604_, 2, v___x_603_);
v___x_605_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_604_, v_searcher_601_, v___x_603_, lean_box(0));
if (lean_obj_tag(v___x_605_) == 0)
{
v___y_585_ = v___x_602_;
goto v___jp_584_;
}
else
{
lean_object* v_val_606_; 
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_605_, 1);
v___y_585_ = v_val_606_;
goto v___jp_584_;
}
v___jp_571_:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_string_utf8_byte_size(v_opt_570_);
v___x_574_ = lean_nat_dec_eq(v___y_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v_toBind_575_; lean_object* v_modifyGet_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_toBind_575_ = lean_ctor_get(v_inst_567_, 1);
lean_inc(v_toBind_575_);
lean_dec_ref(v_inst_567_);
v_modifyGet_576_ = lean_ctor_get(v_inst_568_, 2);
lean_inc(v_modifyGet_576_);
lean_dec_ref(v_inst_568_);
lean_inc(v___y_572_);
lean_inc_ref(v_opt_570_);
v___f_577_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_577_, 0, v_opt_570_);
lean_closure_set(v___f_577_, 1, v___y_572_);
lean_closure_set(v___f_577_, 2, v_handle_569_);
v___x_578_ = lean_string_utf8_next_fast(v_opt_570_, v___y_572_);
lean_dec(v___y_572_);
v___x_579_ = lean_string_utf8_extract(v_opt_570_, v___x_578_, v___x_573_);
lean_dec_ref(v_opt_570_);
v___f_580_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_580_, 0, v___x_579_);
v___x_581_ = lean_apply_2(v_modifyGet_576_, lean_box(0), v___f_580_);
v___x_582_ = lean_apply_4(v_toBind_575_, lean_box(0), lean_box(0), v___x_581_, v___f_577_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v___y_572_);
lean_dec_ref(v_inst_568_);
lean_dec_ref(v_inst_567_);
v___x_583_ = lean_apply_1(v_handle_569_, v_opt_570_);
return v___x_583_;
}
}
v___jp_584_:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_string_utf8_byte_size(v_opt_570_);
v___x_587_ = lean_nat_dec_eq(v___y_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v_toBind_588_; lean_object* v_modifyGet_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_toBind_588_ = lean_ctor_get(v_inst_567_, 1);
lean_inc_n(v_toBind_588_, 2);
lean_dec_ref(v_inst_567_);
v_modifyGet_589_ = lean_ctor_get(v_inst_568_, 2);
lean_inc_n(v_modifyGet_589_, 2);
lean_dec_ref(v_inst_568_);
lean_inc(v___y_585_);
lean_inc_ref(v_opt_570_);
v___f_590_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_590_, 0, v_opt_570_);
lean_closure_set(v___f_590_, 1, v___y_585_);
lean_closure_set(v___f_590_, 2, v_handle_569_);
lean_closure_set(v___f_590_, 3, v_modifyGet_589_);
lean_closure_set(v___f_590_, 4, v_toBind_588_);
v___x_591_ = lean_string_utf8_next_fast(v_opt_570_, v___y_585_);
lean_dec(v___y_585_);
v___x_592_ = lean_string_utf8_extract(v_opt_570_, v___x_591_, v___x_586_);
lean_dec_ref(v_opt_570_);
v___f_593_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_593_, 0, v___x_592_);
v___x_594_ = lean_apply_2(v_modifyGet_589_, lean_box(0), v___f_593_);
v___x_595_ = lean_apply_4(v_toBind_588_, lean_box(0), lean_box(0), v___x_594_, v___f_590_);
return v___x_595_;
}
else
{
lean_object* v_searcher_596_; lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___x_599_; 
lean_dec(v___y_585_);
v_searcher_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_box(0);
lean_inc_ref(v_opt_570_);
v___f_598_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_598_, 0, v___x_586_);
lean_closure_set(v___f_598_, 1, v_opt_570_);
lean_closure_set(v___f_598_, 2, v___x_597_);
v___x_599_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_598_, v_searcher_596_, v___x_597_, lean_box(0));
if (lean_obj_tag(v___x_599_) == 0)
{
v___y_572_ = v___x_586_;
goto v___jp_571_;
}
else
{
lean_object* v_val_600_; 
v_val_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v___x_599_, 1);
v___y_572_ = v_val_600_;
goto v___jp_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object* v_m_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_00_u03b1_610_, lean_object* v_handle_611_, lean_object* v_opt_612_){
_start:
{
lean_object* v___y_614_; lean_object* v___y_627_; lean_object* v_searcher_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___f_646_; lean_object* v___x_647_; 
v_searcher_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_string_utf8_byte_size(v_opt_612_);
v___x_645_ = lean_box(0);
lean_inc_ref(v_opt_612_);
v___f_646_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_646_, 0, v___x_644_);
lean_closure_set(v___f_646_, 1, v_opt_612_);
lean_closure_set(v___f_646_, 2, v___x_645_);
v___x_647_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_646_, v_searcher_643_, v___x_645_, lean_box(0));
if (lean_obj_tag(v___x_647_) == 0)
{
v___y_627_ = v___x_644_;
goto v___jp_626_;
}
else
{
lean_object* v_val_648_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_647_, 1);
v___y_627_ = v_val_648_;
goto v___jp_626_;
}
v___jp_613_:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_string_utf8_byte_size(v_opt_612_);
v___x_616_ = lean_nat_dec_eq(v___y_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v_toBind_617_; lean_object* v_modifyGet_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_toBind_617_ = lean_ctor_get(v_inst_608_, 1);
lean_inc(v_toBind_617_);
lean_dec_ref(v_inst_608_);
v_modifyGet_618_ = lean_ctor_get(v_inst_609_, 2);
lean_inc(v_modifyGet_618_);
lean_dec_ref(v_inst_609_);
lean_inc(v___y_614_);
lean_inc_ref(v_opt_612_);
v___f_619_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_619_, 0, v_opt_612_);
lean_closure_set(v___f_619_, 1, v___y_614_);
lean_closure_set(v___f_619_, 2, v_handle_611_);
v___x_620_ = lean_string_utf8_next_fast(v_opt_612_, v___y_614_);
lean_dec(v___y_614_);
v___x_621_ = lean_string_utf8_extract(v_opt_612_, v___x_620_, v___x_615_);
lean_dec_ref(v_opt_612_);
v___f_622_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_622_, 0, v___x_621_);
v___x_623_ = lean_apply_2(v_modifyGet_618_, lean_box(0), v___f_622_);
v___x_624_ = lean_apply_4(v_toBind_617_, lean_box(0), lean_box(0), v___x_623_, v___f_619_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; 
lean_dec(v___y_614_);
lean_dec_ref(v_inst_609_);
lean_dec_ref(v_inst_608_);
v___x_625_ = lean_apply_1(v_handle_611_, v_opt_612_);
return v___x_625_;
}
}
v___jp_626_:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_string_utf8_byte_size(v_opt_612_);
v___x_629_ = lean_nat_dec_eq(v___y_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v_toBind_630_; lean_object* v_modifyGet_631_; lean_object* v___f_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_toBind_630_ = lean_ctor_get(v_inst_608_, 1);
lean_inc_n(v_toBind_630_, 2);
lean_dec_ref(v_inst_608_);
v_modifyGet_631_ = lean_ctor_get(v_inst_609_, 2);
lean_inc_n(v_modifyGet_631_, 2);
lean_dec_ref(v_inst_609_);
lean_inc(v___y_627_);
lean_inc_ref(v_opt_612_);
v___f_632_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_632_, 0, v_opt_612_);
lean_closure_set(v___f_632_, 1, v___y_627_);
lean_closure_set(v___f_632_, 2, v_handle_611_);
lean_closure_set(v___f_632_, 3, v_modifyGet_631_);
lean_closure_set(v___f_632_, 4, v_toBind_630_);
v___x_633_ = lean_string_utf8_next_fast(v_opt_612_, v___y_627_);
lean_dec(v___y_627_);
v___x_634_ = lean_string_utf8_extract(v_opt_612_, v___x_633_, v___x_628_);
lean_dec_ref(v_opt_612_);
v___f_635_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_635_, 0, v___x_634_);
v___x_636_ = lean_apply_2(v_modifyGet_631_, lean_box(0), v___f_635_);
v___x_637_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v___x_636_, v___f_632_);
return v___x_637_;
}
else
{
lean_object* v_searcher_638_; lean_object* v___x_639_; lean_object* v___f_640_; lean_object* v___x_641_; 
lean_dec(v___y_627_);
v_searcher_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_box(0);
lean_inc_ref(v_opt_612_);
v___f_640_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_640_, 0, v___x_628_);
lean_closure_set(v___f_640_, 1, v_opt_612_);
lean_closure_set(v___f_640_, 2, v___x_639_);
v___x_641_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_640_, v_searcher_638_, v___x_639_, lean_box(0));
if (lean_obj_tag(v___x_641_) == 0)
{
v___y_614_ = v___x_628_;
goto v___jp_613_;
}
else
{
lean_object* v_val_642_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v___x_641_, 1);
v___y_614_ = v_val_642_;
goto v___jp_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object* v___x_649_, lean_object* v_opt_650_, lean_object* v_it_651_, lean_object* v_acc_652_, lean_object* v_hP_653_, lean_object* v_recur_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_eq(v_it_651_, v___x_649_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_string_utf8_next_fast(v_opt_650_, v_it_651_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_acc_652_, v___x_657_);
v___x_659_ = lean_apply_4(v_recur_654_, v___x_656_, v___x_658_, lean_box(0), lean_box(0));
return v___x_659_;
}
else
{
lean_dec_ref(v_recur_654_);
lean_inc(v_acc_652_);
return v_acc_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object* v___x_660_, lean_object* v_opt_661_, lean_object* v_it_662_, lean_object* v_acc_663_, lean_object* v_hP_664_, lean_object* v_recur_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_shortOption___redArg___lam__0(v___x_660_, v_opt_661_, v_it_662_, v_acc_663_, v_hP_664_, v_recur_665_);
lean_dec(v_acc_663_);
lean_dec(v_it_662_);
lean_dec_ref(v_opt_661_);
lean_dec(v___x_660_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__1(lean_object* v_opt_667_, lean_object* v_shortHandle_668_, lean_object* v_____r_669_){
_start:
{
lean_object* v___x_670_; uint32_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_string_utf8_get(v_opt_667_, v___x_670_);
v___x_672_ = lean_box_uint32(v___x_671_);
v___x_673_ = lean_apply_1(v_shortHandle_668_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__1___boxed(lean_object* v_opt_674_, lean_object* v_shortHandle_675_, lean_object* v_____r_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lake_shortOption___redArg___lam__1(v_opt_674_, v_shortHandle_675_, v_____r_676_);
lean_dec_ref(v_opt_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_shortHandle_680_, lean_object* v_longHandle_681_, lean_object* v_opt_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_string_utf8_byte_size(v_opt_682_);
lean_inc_ref_n(v_opt_682_, 2);
v___f_685_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_685_, 0, v___x_684_);
lean_closure_set(v___f_685_, 1, v_opt_682_);
v___x_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_686_, 0, v_opt_682_);
lean_ctor_set(v___x_686_, 1, v___x_683_);
lean_ctor_set(v___x_686_, 2, v___x_684_);
v___x_687_ = l_String_Slice_positions(v___x_686_);
v___x_688_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_685_, v___x_687_, v___x_683_, lean_box(0));
v___x_689_ = lean_unsigned_to_nat(2u);
v___x_690_ = lean_nat_dec_eq(v___x_688_, v___x_689_);
lean_dec(v___x_688_);
if (v___x_690_ == 0)
{
uint32_t v___x_691_; uint32_t v___x_692_; uint8_t v___x_693_; 
v___x_691_ = lean_string_utf8_get(v_opt_682_, v___x_689_);
v___x_692_ = 61;
v___x_693_ = lean_uint32_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
uint32_t v___x_694_; uint8_t v___x_695_; 
v___x_694_ = 32;
v___x_695_ = lean_uint32_dec_eq(v___x_691_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec_ref_known(v___x_686_, 3);
lean_dec(v_shortHandle_680_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
v___x_696_ = lean_apply_1(v_longHandle_681_, v_opt_682_);
return v___x_696_;
}
else
{
lean_object* v_toBind_697_; lean_object* v___x_698_; lean_object* v_modifyGet_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_longHandle_681_);
v_toBind_697_ = lean_ctor_get(v_inst_678_, 1);
lean_inc(v_toBind_697_);
lean_dec_ref(v_inst_678_);
v___x_698_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_699_ = lean_ctor_get(v_inst_679_, 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_inst_679_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_inst_679_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_inst_679_, 0);
lean_dec(v_unused_716_);
v___x_701_ = v_inst_679_;
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_modifyGet_699_);
lean_dec(v_inst_679_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___x_706_; 
v___x_703_ = l_String_Slice_Pos_nextn(v___x_686_, v___x_683_, v___x_689_);
lean_dec_ref_known(v___x_686_, 3);
lean_inc_ref_n(v_opt_682_, 2);
v___f_704_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_704_, 0, v_opt_682_);
lean_closure_set(v___f_704_, 1, v_shortHandle_680_);
lean_inc(v___x_703_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 2, v___x_684_);
lean_ctor_set(v___x_701_, 1, v___x_703_);
lean_ctor_set(v___x_701_, 0, v_opt_682_);
v___x_706_ = v___x_701_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_opt_682_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v___x_684_);
v___x_706_ = v_reuseFailAlloc_713_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_707_ = l_String_Slice_Pos_skipWhile___redArg(v___x_706_, v___x_683_, v___x_698_);
lean_dec_ref(v___x_706_);
v___x_708_ = lean_nat_add(v___x_703_, v___x_707_);
lean_dec(v___x_707_);
lean_dec(v___x_703_);
v___x_709_ = lean_string_utf8_extract(v_opt_682_, v___x_708_, v___x_684_);
lean_dec(v___x_708_);
lean_dec_ref(v_opt_682_);
v___f_710_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_710_, 0, v___x_709_);
v___x_711_ = lean_apply_2(v_modifyGet_699_, lean_box(0), v___f_710_);
v___x_712_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v___x_711_, v___f_704_);
return v___x_712_;
}
}
}
}
else
{
lean_object* v_toBind_717_; lean_object* v_modifyGet_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_longHandle_681_);
v_toBind_717_ = lean_ctor_get(v_inst_678_, 1);
lean_inc(v_toBind_717_);
lean_dec_ref(v_inst_678_);
v_modifyGet_718_ = lean_ctor_get(v_inst_679_, 2);
lean_inc(v_modifyGet_718_);
lean_dec_ref(v_inst_679_);
lean_inc_ref(v_opt_682_);
v___f_719_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_719_, 0, v_opt_682_);
lean_closure_set(v___f_719_, 1, v_shortHandle_680_);
v___x_720_ = lean_unsigned_to_nat(3u);
v___x_721_ = l_String_Slice_Pos_nextn(v___x_686_, v___x_683_, v___x_720_);
lean_dec_ref_known(v___x_686_, 3);
v___x_722_ = lean_string_utf8_extract(v_opt_682_, v___x_721_, v___x_684_);
lean_dec(v___x_721_);
lean_dec_ref(v_opt_682_);
v___f_723_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_723_, 0, v___x_722_);
v___x_724_ = lean_apply_2(v_modifyGet_718_, lean_box(0), v___f_723_);
v___x_725_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v___x_724_, v___f_719_);
return v___x_725_;
}
}
else
{
lean_object* v___x_726_; uint32_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref_known(v___x_686_, 3);
lean_dec(v_longHandle_681_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_string_utf8_get(v_opt_682_, v___x_726_);
lean_dec_ref(v_opt_682_);
v___x_728_ = lean_box_uint32(v___x_727_);
v___x_729_ = lean_apply_1(v_shortHandle_680_, v___x_728_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object* v_m_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_00_u03b1_733_, lean_object* v_shortHandle_734_, lean_object* v_longHandle_735_, lean_object* v_opt_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_string_utf8_byte_size(v_opt_736_);
lean_inc_ref_n(v_opt_736_, 2);
v___f_739_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_739_, 0, v___x_738_);
lean_closure_set(v___f_739_, 1, v_opt_736_);
v___x_740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_740_, 0, v_opt_736_);
lean_ctor_set(v___x_740_, 1, v___x_737_);
lean_ctor_set(v___x_740_, 2, v___x_738_);
v___x_741_ = l_String_Slice_positions(v___x_740_);
v___x_742_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_739_, v___x_741_, v___x_737_, lean_box(0));
v___x_743_ = lean_unsigned_to_nat(2u);
v___x_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
lean_dec(v___x_742_);
if (v___x_744_ == 0)
{
uint32_t v___x_745_; uint32_t v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_string_utf8_get(v_opt_736_, v___x_743_);
v___x_746_ = 61;
v___x_747_ = lean_uint32_dec_eq(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
uint32_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 32;
v___x_749_ = lean_uint32_dec_eq(v___x_745_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec_ref_known(v___x_740_, 3);
lean_dec(v_shortHandle_734_);
lean_dec_ref(v_inst_732_);
lean_dec_ref(v_inst_731_);
v___x_750_ = lean_apply_1(v_longHandle_735_, v_opt_736_);
return v___x_750_;
}
else
{
lean_object* v_toBind_751_; lean_object* v___x_752_; lean_object* v_modifyGet_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_longHandle_735_);
v_toBind_751_ = lean_ctor_get(v_inst_731_, 1);
lean_inc(v_toBind_751_);
lean_dec_ref(v_inst_731_);
v___x_752_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_753_ = lean_ctor_get(v_inst_732_, 2);
v_isSharedCheck_768_ = !lean_is_exclusive(v_inst_732_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_769_ = lean_ctor_get(v_inst_732_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_inst_732_, 0);
lean_dec(v_unused_770_);
v___x_755_ = v_inst_732_;
v_isShared_756_ = v_isSharedCheck_768_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_modifyGet_753_);
lean_dec(v_inst_732_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_768_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___x_760_; 
v___x_757_ = l_String_Slice_Pos_nextn(v___x_740_, v___x_737_, v___x_743_);
lean_dec_ref_known(v___x_740_, 3);
lean_inc_ref_n(v_opt_736_, 2);
v___f_758_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_758_, 0, v_opt_736_);
lean_closure_set(v___f_758_, 1, v_shortHandle_734_);
lean_inc(v___x_757_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 2, v___x_738_);
lean_ctor_set(v___x_755_, 1, v___x_757_);
lean_ctor_set(v___x_755_, 0, v_opt_736_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_opt_736_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_738_);
v___x_760_ = v_reuseFailAlloc_767_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_761_ = l_String_Slice_Pos_skipWhile___redArg(v___x_760_, v___x_737_, v___x_752_);
lean_dec_ref(v___x_760_);
v___x_762_ = lean_nat_add(v___x_757_, v___x_761_);
lean_dec(v___x_761_);
lean_dec(v___x_757_);
v___x_763_ = lean_string_utf8_extract(v_opt_736_, v___x_762_, v___x_738_);
lean_dec(v___x_762_);
lean_dec_ref(v_opt_736_);
v___f_764_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_764_, 0, v___x_763_);
v___x_765_ = lean_apply_2(v_modifyGet_753_, lean_box(0), v___f_764_);
v___x_766_ = lean_apply_4(v_toBind_751_, lean_box(0), lean_box(0), v___x_765_, v___f_758_);
return v___x_766_;
}
}
}
}
else
{
lean_object* v_toBind_771_; lean_object* v_modifyGet_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_longHandle_735_);
v_toBind_771_ = lean_ctor_get(v_inst_731_, 1);
lean_inc(v_toBind_771_);
lean_dec_ref(v_inst_731_);
v_modifyGet_772_ = lean_ctor_get(v_inst_732_, 2);
lean_inc(v_modifyGet_772_);
lean_dec_ref(v_inst_732_);
lean_inc_ref(v_opt_736_);
v___f_773_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_773_, 0, v_opt_736_);
lean_closure_set(v___f_773_, 1, v_shortHandle_734_);
v___x_774_ = lean_unsigned_to_nat(3u);
v___x_775_ = l_String_Slice_Pos_nextn(v___x_740_, v___x_737_, v___x_774_);
lean_dec_ref_known(v___x_740_, 3);
v___x_776_ = lean_string_utf8_extract(v_opt_736_, v___x_775_, v___x_738_);
lean_dec(v___x_775_);
lean_dec_ref(v_opt_736_);
v___f_777_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_777_, 0, v___x_776_);
v___x_778_ = lean_apply_2(v_modifyGet_772_, lean_box(0), v___f_777_);
v___x_779_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_778_, v___f_773_);
return v___x_779_;
}
}
else
{
lean_object* v___x_780_; uint32_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref_known(v___x_740_, 3);
lean_dec(v_longHandle_735_);
lean_dec_ref(v_inst_732_);
lean_dec_ref(v_inst_731_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_string_utf8_get(v_opt_736_, v___x_780_);
lean_dec_ref(v_opt_736_);
v___x_782_ = lean_box_uint32(v___x_781_);
v___x_783_ = lean_apply_1(v_shortHandle_734_, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object* v___x_784_, lean_object* v_opt_785_, lean_object* v___x_786_, lean_object* v_it_787_, lean_object* v_acc_788_, lean_object* v_hP_789_, lean_object* v_recur_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_eq(v_it_787_, v___x_784_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = lean_string_utf8_next_fast(v_opt_785_, v_it_787_);
v___x_793_ = lean_nat_add(v_acc_788_, v___x_786_);
v___x_794_ = lean_apply_4(v_recur_790_, v___x_792_, v___x_793_, lean_box(0), lean_box(0));
return v___x_794_;
}
else
{
lean_dec_ref(v_recur_790_);
lean_inc(v_acc_788_);
return v_acc_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object* v___x_795_, lean_object* v_opt_796_, lean_object* v___x_797_, lean_object* v_it_798_, lean_object* v_acc_799_, lean_object* v_hP_800_, lean_object* v_recur_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lake_option___redArg___lam__0(v___x_795_, v_opt_796_, v___x_797_, v_it_798_, v_acc_799_, v_hP_800_, v_recur_801_);
lean_dec(v_acc_799_);
lean_dec(v_it_798_);
lean_dec(v___x_797_);
lean_dec_ref(v_opt_796_);
lean_dec(v___x_795_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__1(lean_object* v_short_803_, uint32_t v___x_804_, lean_object* v_____r_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_box_uint32(v___x_804_);
v___x_807_ = lean_apply_1(v_short_803_, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__1___boxed(lean_object* v_short_808_, lean_object* v___x_809_, lean_object* v_____r_810_){
_start:
{
uint32_t v___x_1512__boxed_811_; lean_object* v_res_812_; 
v___x_1512__boxed_811_ = lean_unbox_uint32(v___x_809_);
lean_dec(v___x_809_);
v_res_812_ = l_Lake_option___redArg___lam__1(v_short_808_, v___x_1512__boxed_811_, v_____r_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5(lean_object* v_opt_813_, lean_object* v___y_814_, lean_object* v_long_815_, lean_object* v_____r_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_string_utf8_extract(v_opt_813_, v___x_817_, v___y_814_);
v___x_819_ = lean_apply_1(v_long_815_, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5___boxed(lean_object* v_opt_820_, lean_object* v___y_821_, lean_object* v_long_822_, lean_object* v_____r_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lake_option___redArg___lam__5(v_opt_820_, v___y_821_, v_long_822_, v_____r_823_);
lean_dec(v___y_821_);
lean_dec_ref(v_opt_820_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object* v___x_825_, lean_object* v_searcher_826_, lean_object* v___y_827_, lean_object* v_long_828_, lean_object* v_____r_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_string_utf8_extract(v___x_825_, v_searcher_826_, v___y_827_);
v___x_831_ = lean_apply_1(v_long_828_, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object* v___x_832_, lean_object* v_searcher_833_, lean_object* v___y_834_, lean_object* v_long_835_, lean_object* v_____r_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lake_option___redArg___lam__3(v___x_832_, v_searcher_833_, v___y_834_, v_long_835_, v_____r_836_);
lean_dec(v___y_834_);
lean_dec(v_searcher_833_);
lean_dec_ref(v___x_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__6(lean_object* v_opt_838_, lean_object* v___y_839_, lean_object* v_long_840_, lean_object* v_modifyGet_841_, lean_object* v_toBind_842_, lean_object* v_____r_843_){
_start:
{
lean_object* v_searcher_844_; lean_object* v___x_845_; lean_object* v___y_847_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___f_859_; lean_object* v___x_860_; 
v_searcher_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_string_utf8_extract(v_opt_838_, v_searcher_844_, v___y_839_);
v___x_857_ = lean_string_utf8_byte_size(v___x_845_);
v___x_858_ = lean_box(0);
lean_inc_ref(v___x_845_);
v___f_859_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_859_, 0, v___x_857_);
lean_closure_set(v___f_859_, 1, v___x_845_);
lean_closure_set(v___f_859_, 2, v___x_858_);
v___x_860_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_859_, v_searcher_844_, v___x_858_, lean_box(0));
if (lean_obj_tag(v___x_860_) == 0)
{
v___y_847_ = v___x_857_;
goto v___jp_846_;
}
else
{
lean_object* v_val_861_; 
v_val_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v___x_860_, 1);
v___y_847_ = v_val_861_;
goto v___jp_846_;
}
v___jp_846_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_string_utf8_byte_size(v___x_845_);
v___x_849_ = lean_nat_dec_eq(v___y_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_inc(v___y_847_);
lean_inc_ref(v___x_845_);
v___f_850_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_850_, 0, v___x_845_);
lean_closure_set(v___f_850_, 1, v_searcher_844_);
lean_closure_set(v___f_850_, 2, v___y_847_);
lean_closure_set(v___f_850_, 3, v_long_840_);
v___x_851_ = lean_string_utf8_next_fast(v___x_845_, v___y_847_);
lean_dec(v___y_847_);
v___x_852_ = lean_string_utf8_extract(v___x_845_, v___x_851_, v___x_848_);
lean_dec_ref(v___x_845_);
v___f_853_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_853_, 0, v___x_852_);
v___x_854_ = lean_apply_2(v_modifyGet_841_, lean_box(0), v___f_853_);
v___x_855_ = lean_apply_4(v_toBind_842_, lean_box(0), lean_box(0), v___x_854_, v___f_850_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; 
lean_dec(v___y_847_);
lean_dec(v_toBind_842_);
lean_dec(v_modifyGet_841_);
v___x_856_ = lean_apply_1(v_long_840_, v___x_845_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__6___boxed(lean_object* v_opt_862_, lean_object* v___y_863_, lean_object* v_long_864_, lean_object* v_modifyGet_865_, lean_object* v_toBind_866_, lean_object* v_____r_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lake_option___redArg___lam__6(v_opt_862_, v___y_863_, v_long_864_, v_modifyGet_865_, v_toBind_866_, v_____r_867_);
lean_dec(v___y_863_);
lean_dec_ref(v_opt_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_handlers_871_, lean_object* v_opt_872_){
_start:
{
lean_object* v___x_873_; uint32_t v___x_874_; uint32_t v___x_875_; uint8_t v___x_876_; 
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_string_utf8_get(v_opt_872_, v___x_873_);
v___x_875_ = 45;
v___x_876_ = lean_uint32_dec_eq(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v_short_877_; lean_object* v_longShort_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_931_; 
v_short_877_ = lean_ctor_get(v_handlers_871_, 1);
v_longShort_878_ = lean_ctor_get(v_handlers_871_, 2);
v_isSharedCheck_931_ = !lean_is_exclusive(v_handlers_871_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_handlers_871_, 0);
lean_dec(v_unused_932_);
v___x_880_ = v_handlers_871_;
v_isShared_881_ = v_isSharedCheck_931_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_longShort_878_);
lean_inc(v_short_877_);
lean_dec(v_handlers_871_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_931_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___f_884_; lean_object* v___x_886_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_string_utf8_byte_size(v_opt_872_);
lean_inc_ref_n(v_opt_872_, 2);
v___f_884_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_884_, 0, v___x_883_);
lean_closure_set(v___f_884_, 1, v_opt_872_);
lean_closure_set(v___f_884_, 2, v___x_873_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v___x_883_);
lean_ctor_set(v___x_880_, 1, v___x_882_);
lean_ctor_set(v___x_880_, 0, v_opt_872_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_opt_872_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v___x_883_);
v___x_886_ = v_reuseFailAlloc_930_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_887_ = l_String_Slice_positions(v___x_886_);
v___x_888_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_884_, v___x_887_, v___x_882_, lean_box(0));
v___x_889_ = lean_unsigned_to_nat(2u);
v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
lean_dec(v___x_888_);
if (v___x_890_ == 0)
{
uint32_t v___x_891_; uint32_t v___x_892_; uint8_t v___x_893_; 
v___x_891_ = lean_string_utf8_get(v_opt_872_, v___x_889_);
v___x_892_ = 61;
v___x_893_ = lean_uint32_dec_eq(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 32;
v___x_895_ = lean_uint32_dec_eq(v___x_891_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v___x_886_);
lean_dec(v_short_877_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
v___x_896_ = lean_apply_1(v_longShort_878_, v_opt_872_);
return v___x_896_;
}
else
{
lean_object* v_toBind_897_; lean_object* v___x_898_; lean_object* v_modifyGet_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_longShort_878_);
v_toBind_897_ = lean_ctor_get(v_inst_869_, 1);
lean_inc(v_toBind_897_);
lean_dec_ref(v_inst_869_);
v___x_898_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_899_ = lean_ctor_get(v_inst_870_, 2);
v_isSharedCheck_915_ = !lean_is_exclusive(v_inst_870_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_916_ = lean_ctor_get(v_inst_870_, 1);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_inst_870_, 0);
lean_dec(v_unused_917_);
v___x_901_ = v_inst_870_;
v_isShared_902_ = v_isSharedCheck_915_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_modifyGet_899_);
lean_dec(v_inst_870_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_915_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___f_905_; lean_object* v___x_907_; 
v___x_903_ = l_String_Slice_Pos_nextn(v___x_886_, v___x_882_, v___x_889_);
lean_dec_ref(v___x_886_);
v___x_904_ = lean_box_uint32(v___x_874_);
v___f_905_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_905_, 0, v_short_877_);
lean_closure_set(v___f_905_, 1, v___x_904_);
lean_inc(v___x_903_);
lean_inc_ref(v_opt_872_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 2, v___x_883_);
lean_ctor_set(v___x_901_, 1, v___x_903_);
lean_ctor_set(v___x_901_, 0, v_opt_872_);
v___x_907_ = v___x_901_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_opt_872_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v___x_883_);
v___x_907_ = v_reuseFailAlloc_914_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_908_ = l_String_Slice_Pos_skipWhile___redArg(v___x_907_, v___x_882_, v___x_898_);
lean_dec_ref(v___x_907_);
v___x_909_ = lean_nat_add(v___x_903_, v___x_908_);
lean_dec(v___x_908_);
lean_dec(v___x_903_);
v___x_910_ = lean_string_utf8_extract(v_opt_872_, v___x_909_, v___x_883_);
lean_dec(v___x_909_);
lean_dec_ref(v_opt_872_);
v___f_911_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_911_, 0, v___x_910_);
v___x_912_ = lean_apply_2(v_modifyGet_899_, lean_box(0), v___f_911_);
v___x_913_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v___x_912_, v___f_905_);
return v___x_913_;
}
}
}
}
else
{
lean_object* v_toBind_918_; lean_object* v_modifyGet_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_longShort_878_);
v_toBind_918_ = lean_ctor_get(v_inst_869_, 1);
lean_inc(v_toBind_918_);
lean_dec_ref(v_inst_869_);
v_modifyGet_919_ = lean_ctor_get(v_inst_870_, 2);
lean_inc(v_modifyGet_919_);
lean_dec_ref(v_inst_870_);
v___x_920_ = lean_box_uint32(v___x_874_);
v___f_921_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_921_, 0, v_short_877_);
lean_closure_set(v___f_921_, 1, v___x_920_);
v___x_922_ = lean_unsigned_to_nat(3u);
v___x_923_ = l_String_Slice_Pos_nextn(v___x_886_, v___x_882_, v___x_922_);
lean_dec_ref(v___x_886_);
v___x_924_ = lean_string_utf8_extract(v_opt_872_, v___x_923_, v___x_883_);
lean_dec(v___x_923_);
lean_dec_ref(v_opt_872_);
v___f_925_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_925_, 0, v___x_924_);
v___x_926_ = lean_apply_2(v_modifyGet_919_, lean_box(0), v___f_925_);
v___x_927_ = lean_apply_4(v_toBind_918_, lean_box(0), lean_box(0), v___x_926_, v___f_921_);
return v___x_927_;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec_ref(v___x_886_);
lean_dec(v_longShort_878_);
lean_dec_ref(v_opt_872_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
v___x_928_ = lean_box_uint32(v___x_874_);
v___x_929_ = lean_apply_1(v_short_877_, v___x_928_);
return v___x_929_;
}
}
}
}
else
{
lean_object* v_long_933_; lean_object* v___y_935_; lean_object* v___y_948_; lean_object* v_searcher_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___f_967_; lean_object* v___x_968_; 
v_long_933_ = lean_ctor_get(v_handlers_871_, 0);
lean_inc(v_long_933_);
lean_dec_ref(v_handlers_871_);
v_searcher_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_string_utf8_byte_size(v_opt_872_);
v___x_966_ = lean_box(0);
lean_inc_ref(v_opt_872_);
v___f_967_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_967_, 0, v___x_965_);
lean_closure_set(v___f_967_, 1, v_opt_872_);
lean_closure_set(v___f_967_, 2, v___x_966_);
v___x_968_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_967_, v_searcher_964_, v___x_966_, lean_box(0));
if (lean_obj_tag(v___x_968_) == 0)
{
v___y_948_ = v___x_965_;
goto v___jp_947_;
}
else
{
lean_object* v_val_969_; 
v_val_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v___x_968_, 1);
v___y_948_ = v_val_969_;
goto v___jp_947_;
}
v___jp_934_:
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_string_utf8_byte_size(v_opt_872_);
v___x_937_ = lean_nat_dec_eq(v___y_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v_toBind_938_; lean_object* v_modifyGet_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_toBind_938_ = lean_ctor_get(v_inst_869_, 1);
lean_inc(v_toBind_938_);
lean_dec_ref(v_inst_869_);
v_modifyGet_939_ = lean_ctor_get(v_inst_870_, 2);
lean_inc(v_modifyGet_939_);
lean_dec_ref(v_inst_870_);
lean_inc(v___y_935_);
lean_inc_ref(v_opt_872_);
v___f_940_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_940_, 0, v_opt_872_);
lean_closure_set(v___f_940_, 1, v___y_935_);
lean_closure_set(v___f_940_, 2, v_long_933_);
v___x_941_ = lean_string_utf8_next_fast(v_opt_872_, v___y_935_);
lean_dec(v___y_935_);
v___x_942_ = lean_string_utf8_extract(v_opt_872_, v___x_941_, v___x_936_);
lean_dec_ref(v_opt_872_);
v___f_943_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_943_, 0, v___x_942_);
v___x_944_ = lean_apply_2(v_modifyGet_939_, lean_box(0), v___f_943_);
v___x_945_ = lean_apply_4(v_toBind_938_, lean_box(0), lean_box(0), v___x_944_, v___f_940_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
lean_dec(v___y_935_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
v___x_946_ = lean_apply_1(v_long_933_, v_opt_872_);
return v___x_946_;
}
}
v___jp_947_:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_string_utf8_byte_size(v_opt_872_);
v___x_950_ = lean_nat_dec_eq(v___y_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v_toBind_951_; lean_object* v_modifyGet_952_; lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_toBind_951_ = lean_ctor_get(v_inst_869_, 1);
lean_inc_n(v_toBind_951_, 2);
lean_dec_ref(v_inst_869_);
v_modifyGet_952_ = lean_ctor_get(v_inst_870_, 2);
lean_inc_n(v_modifyGet_952_, 2);
lean_dec_ref(v_inst_870_);
lean_inc(v___y_948_);
lean_inc_ref(v_opt_872_);
v___f_953_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__6___boxed), 6, 5);
lean_closure_set(v___f_953_, 0, v_opt_872_);
lean_closure_set(v___f_953_, 1, v___y_948_);
lean_closure_set(v___f_953_, 2, v_long_933_);
lean_closure_set(v___f_953_, 3, v_modifyGet_952_);
lean_closure_set(v___f_953_, 4, v_toBind_951_);
v___x_954_ = lean_string_utf8_next_fast(v_opt_872_, v___y_948_);
lean_dec(v___y_948_);
v___x_955_ = lean_string_utf8_extract(v_opt_872_, v___x_954_, v___x_949_);
lean_dec_ref(v_opt_872_);
v___f_956_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_956_, 0, v___x_955_);
v___x_957_ = lean_apply_2(v_modifyGet_952_, lean_box(0), v___f_956_);
v___x_958_ = lean_apply_4(v_toBind_951_, lean_box(0), lean_box(0), v___x_957_, v___f_953_);
return v___x_958_;
}
else
{
lean_object* v_searcher_959_; lean_object* v___x_960_; lean_object* v___f_961_; lean_object* v___x_962_; 
lean_dec(v___y_948_);
v_searcher_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_box(0);
lean_inc_ref(v_opt_872_);
v___f_961_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_961_, 0, v___x_949_);
lean_closure_set(v___f_961_, 1, v_opt_872_);
lean_closure_set(v___f_961_, 2, v___x_960_);
v___x_962_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_961_, v_searcher_959_, v___x_960_, lean_box(0));
if (lean_obj_tag(v___x_962_) == 0)
{
v___y_935_ = v___x_949_;
goto v___jp_934_;
}
else
{
lean_object* v_val_963_; 
v_val_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v___x_962_, 1);
v___y_935_ = v_val_963_;
goto v___jp_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option(lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_00_u03b1_973_, lean_object* v_handlers_974_, lean_object* v_opt_975_){
_start:
{
lean_object* v___x_976_; uint32_t v___x_977_; uint32_t v___x_978_; uint8_t v___x_979_; 
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_string_utf8_get(v_opt_975_, v___x_976_);
v___x_978_ = 45;
v___x_979_ = lean_uint32_dec_eq(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v_short_980_; lean_object* v_longShort_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1034_; 
v_short_980_ = lean_ctor_get(v_handlers_974_, 1);
v_longShort_981_ = lean_ctor_get(v_handlers_974_, 2);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_handlers_974_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_handlers_974_, 0);
lean_dec(v_unused_1035_);
v___x_983_ = v_handlers_974_;
v_isShared_984_ = v_isSharedCheck_1034_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_longShort_981_);
lean_inc(v_short_980_);
lean_dec(v_handlers_974_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1034_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___f_987_; lean_object* v___x_989_; 
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_string_utf8_byte_size(v_opt_975_);
lean_inc_ref_n(v_opt_975_, 2);
v___f_987_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_987_, 0, v___x_986_);
lean_closure_set(v___f_987_, 1, v_opt_975_);
lean_closure_set(v___f_987_, 2, v___x_976_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 2, v___x_986_);
lean_ctor_set(v___x_983_, 1, v___x_985_);
lean_ctor_set(v___x_983_, 0, v_opt_975_);
v___x_989_ = v___x_983_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_opt_975_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v___x_986_);
v___x_989_ = v_reuseFailAlloc_1033_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_990_ = l_String_Slice_positions(v___x_989_);
v___x_991_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_987_, v___x_990_, v___x_985_, lean_box(0));
v___x_992_ = lean_unsigned_to_nat(2u);
v___x_993_ = lean_nat_dec_eq(v___x_991_, v___x_992_);
lean_dec(v___x_991_);
if (v___x_993_ == 0)
{
uint32_t v___x_994_; uint32_t v___x_995_; uint8_t v___x_996_; 
v___x_994_ = lean_string_utf8_get(v_opt_975_, v___x_992_);
v___x_995_ = 61;
v___x_996_ = lean_uint32_dec_eq(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
uint32_t v___x_997_; uint8_t v___x_998_; 
v___x_997_ = 32;
v___x_998_ = lean_uint32_dec_eq(v___x_994_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_dec_ref(v___x_989_);
lean_dec(v_short_980_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
v___x_999_ = lean_apply_1(v_longShort_981_, v_opt_975_);
return v___x_999_;
}
else
{
lean_object* v_toBind_1000_; lean_object* v___x_1001_; lean_object* v_modifyGet_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_longShort_981_);
v_toBind_1000_ = lean_ctor_get(v_inst_971_, 1);
lean_inc(v_toBind_1000_);
lean_dec_ref(v_inst_971_);
v___x_1001_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_1002_ = lean_ctor_get(v_inst_972_, 2);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_inst_972_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; lean_object* v_unused_1020_; 
v_unused_1019_ = lean_ctor_get(v_inst_972_, 1);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_inst_972_, 0);
lean_dec(v_unused_1020_);
v___x_1004_ = v_inst_972_;
v_isShared_1005_ = v_isSharedCheck_1018_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_modifyGet_1002_);
lean_dec(v_inst_972_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1018_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___x_1010_; 
v___x_1006_ = l_String_Slice_Pos_nextn(v___x_989_, v___x_985_, v___x_992_);
lean_dec_ref(v___x_989_);
v___x_1007_ = lean_box_uint32(v___x_977_);
v___f_1008_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1008_, 0, v_short_980_);
lean_closure_set(v___f_1008_, 1, v___x_1007_);
lean_inc(v___x_1006_);
lean_inc_ref(v_opt_975_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 2, v___x_986_);
lean_ctor_set(v___x_1004_, 1, v___x_1006_);
lean_ctor_set(v___x_1004_, 0, v_opt_975_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_opt_975_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_986_);
v___x_1010_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1011_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1010_, v___x_985_, v___x_1001_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = lean_nat_add(v___x_1006_, v___x_1011_);
lean_dec(v___x_1011_);
lean_dec(v___x_1006_);
v___x_1013_ = lean_string_utf8_extract(v_opt_975_, v___x_1012_, v___x_986_);
lean_dec(v___x_1012_);
lean_dec_ref(v_opt_975_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1014_, 0, v___x_1013_);
v___x_1015_ = lean_apply_2(v_modifyGet_1002_, lean_box(0), v___f_1014_);
v___x_1016_ = lean_apply_4(v_toBind_1000_, lean_box(0), lean_box(0), v___x_1015_, v___f_1008_);
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_toBind_1021_; lean_object* v_modifyGet_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v_longShort_981_);
v_toBind_1021_ = lean_ctor_get(v_inst_971_, 1);
lean_inc(v_toBind_1021_);
lean_dec_ref(v_inst_971_);
v_modifyGet_1022_ = lean_ctor_get(v_inst_972_, 2);
lean_inc(v_modifyGet_1022_);
lean_dec_ref(v_inst_972_);
v___x_1023_ = lean_box_uint32(v___x_977_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1024_, 0, v_short_980_);
lean_closure_set(v___f_1024_, 1, v___x_1023_);
v___x_1025_ = lean_unsigned_to_nat(3u);
v___x_1026_ = l_String_Slice_Pos_nextn(v___x_989_, v___x_985_, v___x_1025_);
lean_dec_ref(v___x_989_);
v___x_1027_ = lean_string_utf8_extract(v_opt_975_, v___x_1026_, v___x_986_);
lean_dec(v___x_1026_);
lean_dec_ref(v_opt_975_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
v___x_1029_ = lean_apply_2(v_modifyGet_1022_, lean_box(0), v___f_1028_);
v___x_1030_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1029_, v___f_1024_);
return v___x_1030_;
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v___x_989_);
lean_dec(v_longShort_981_);
lean_dec_ref(v_opt_975_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
v___x_1031_ = lean_box_uint32(v___x_977_);
v___x_1032_ = lean_apply_1(v_short_980_, v___x_1031_);
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_long_1036_; lean_object* v___y_1038_; lean_object* v___y_1051_; lean_object* v_searcher_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v_long_1036_ = lean_ctor_get(v_handlers_974_, 0);
lean_inc(v_long_1036_);
lean_dec_ref(v_handlers_974_);
v_searcher_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_string_utf8_byte_size(v_opt_975_);
v___x_1069_ = lean_box(0);
lean_inc_ref(v_opt_975_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1070_, 0, v___x_1068_);
lean_closure_set(v___f_1070_, 1, v_opt_975_);
lean_closure_set(v___f_1070_, 2, v___x_1069_);
v___x_1071_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1070_, v_searcher_1067_, v___x_1069_, lean_box(0));
if (lean_obj_tag(v___x_1071_) == 0)
{
v___y_1051_ = v___x_1068_;
goto v___jp_1050_;
}
else
{
lean_object* v_val_1072_; 
v_val_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___y_1051_ = v_val_1072_;
goto v___jp_1050_;
}
v___jp_1037_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_string_utf8_byte_size(v_opt_975_);
v___x_1040_ = lean_nat_dec_eq(v___y_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v_toBind_1041_; lean_object* v_modifyGet_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_toBind_1041_ = lean_ctor_get(v_inst_971_, 1);
lean_inc(v_toBind_1041_);
lean_dec_ref(v_inst_971_);
v_modifyGet_1042_ = lean_ctor_get(v_inst_972_, 2);
lean_inc(v_modifyGet_1042_);
lean_dec_ref(v_inst_972_);
lean_inc(v___y_1038_);
lean_inc_ref(v_opt_975_);
v___f_1043_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_1043_, 0, v_opt_975_);
lean_closure_set(v___f_1043_, 1, v___y_1038_);
lean_closure_set(v___f_1043_, 2, v_long_1036_);
v___x_1044_ = lean_string_utf8_next_fast(v_opt_975_, v___y_1038_);
lean_dec(v___y_1038_);
v___x_1045_ = lean_string_utf8_extract(v_opt_975_, v___x_1044_, v___x_1039_);
lean_dec_ref(v_opt_975_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1046_, 0, v___x_1045_);
v___x_1047_ = lean_apply_2(v_modifyGet_1042_, lean_box(0), v___f_1046_);
v___x_1048_ = lean_apply_4(v_toBind_1041_, lean_box(0), lean_box(0), v___x_1047_, v___f_1043_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; 
lean_dec(v___y_1038_);
lean_dec_ref(v_inst_972_);
lean_dec_ref(v_inst_971_);
v___x_1049_ = lean_apply_1(v_long_1036_, v_opt_975_);
return v___x_1049_;
}
}
v___jp_1050_:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_string_utf8_byte_size(v_opt_975_);
v___x_1053_ = lean_nat_dec_eq(v___y_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v_toBind_1054_; lean_object* v_modifyGet_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_toBind_1054_ = lean_ctor_get(v_inst_971_, 1);
lean_inc_n(v_toBind_1054_, 2);
lean_dec_ref(v_inst_971_);
v_modifyGet_1055_ = lean_ctor_get(v_inst_972_, 2);
lean_inc_n(v_modifyGet_1055_, 2);
lean_dec_ref(v_inst_972_);
lean_inc(v___y_1051_);
lean_inc_ref(v_opt_975_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__6___boxed), 6, 5);
lean_closure_set(v___f_1056_, 0, v_opt_975_);
lean_closure_set(v___f_1056_, 1, v___y_1051_);
lean_closure_set(v___f_1056_, 2, v_long_1036_);
lean_closure_set(v___f_1056_, 3, v_modifyGet_1055_);
lean_closure_set(v___f_1056_, 4, v_toBind_1054_);
v___x_1057_ = lean_string_utf8_next_fast(v_opt_975_, v___y_1051_);
lean_dec(v___y_1051_);
v___x_1058_ = lean_string_utf8_extract(v_opt_975_, v___x_1057_, v___x_1052_);
lean_dec_ref(v_opt_975_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1059_, 0, v___x_1058_);
v___x_1060_ = lean_apply_2(v_modifyGet_1055_, lean_box(0), v___f_1059_);
v___x_1061_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v___x_1060_, v___f_1056_);
return v___x_1061_;
}
else
{
lean_object* v_searcher_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; 
lean_dec(v___y_1051_);
v_searcher_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_box(0);
lean_inc_ref(v_opt_975_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1064_, 0, v___x_1052_);
lean_closure_set(v___f_1064_, 1, v_opt_975_);
lean_closure_set(v___f_1064_, 2, v___x_1063_);
v___x_1065_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1064_, v_searcher_1062_, v___x_1063_, lean_box(0));
if (lean_obj_tag(v___x_1065_) == 0)
{
v___y_1038_ = v___x_1052_;
goto v___jp_1037_;
}
else
{
lean_object* v_val_1066_; 
v_val_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___y_1038_ = v_val_1066_;
goto v___jp_1037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object* v_handle_1073_, lean_object* v_head_1074_, lean_object* v_____r_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_apply_1(v_handle_1073_, v_head_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object* v___x_1077_, lean_object* v_head_1078_, lean_object* v___x_1079_, lean_object* v_it_1080_, lean_object* v_acc_1081_, lean_object* v_hP_1082_, lean_object* v_recur_1083_){
_start:
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_eq(v_it_1080_, v___x_1077_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_string_utf8_next_fast(v_head_1078_, v_it_1080_);
v___x_1086_ = lean_nat_add(v_acc_1081_, v___x_1079_);
v___x_1087_ = lean_apply_4(v_recur_1083_, v___x_1085_, v___x_1086_, lean_box(0), lean_box(0));
return v___x_1087_;
}
else
{
lean_dec_ref(v_recur_1083_);
lean_inc(v_acc_1081_);
return v_acc_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1___boxed(lean_object* v___x_1088_, lean_object* v_head_1089_, lean_object* v___x_1090_, lean_object* v_it_1091_, lean_object* v_acc_1092_, lean_object* v_hP_1093_, lean_object* v_recur_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_processLeadingOption___redArg___lam__1(v___x_1088_, v_head_1089_, v___x_1090_, v_it_1091_, v_acc_1092_, v_hP_1093_, v_recur_1094_);
lean_dec(v_acc_1092_);
lean_dec(v_it_1091_);
lean_dec(v___x_1090_);
lean_dec_ref(v_head_1089_);
lean_dec(v___x_1088_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__2(lean_object* v_toPure_1096_, lean_object* v_handle_1097_, lean_object* v_set_1098_, lean_object* v_toBind_1099_, lean_object* v_____do__lift_1100_){
_start:
{
if (lean_obj_tag(v_____do__lift_1100_) == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v_toBind_1099_);
lean_dec(v_set_1098_);
lean_dec(v_handle_1097_);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_apply_2(v_toPure_1096_, lean_box(0), v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v_head_1103_; lean_object* v_tail_1104_; lean_object* v___f_1105_; uint8_t v___y_1107_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_head_1103_ = lean_ctor_get(v_____do__lift_1100_, 0);
lean_inc_n(v_head_1103_, 4);
v_tail_1104_ = lean_ctor_get(v_____do__lift_1100_, 1);
lean_inc(v_tail_1104_);
lean_dec_ref_known(v_____do__lift_1100_, 2);
v___f_1105_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1105_, 0, v_handle_1097_);
lean_closure_set(v___f_1105_, 1, v_head_1103_);
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_string_utf8_byte_size(v_head_1103_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_1115_, 0, v___x_1114_);
lean_closure_set(v___f_1115_, 1, v_head_1103_);
lean_closure_set(v___f_1115_, 2, v___x_1112_);
v___x_1116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1116_, 0, v_head_1103_);
lean_ctor_set(v___x_1116_, 1, v___x_1113_);
lean_ctor_set(v___x_1116_, 2, v___x_1114_);
v___x_1117_ = l_String_Slice_positions(v___x_1116_);
lean_dec_ref_known(v___x_1116_, 3);
v___x_1118_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1115_, v___x_1117_, v___x_1113_, lean_box(0));
v___x_1119_ = lean_nat_dec_lt(v___x_1112_, v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v_head_1103_);
v___y_1107_ = v___x_1119_;
goto v___jp_1106_;
}
else
{
uint32_t v___x_1120_; uint32_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = lean_string_utf8_get(v_head_1103_, v___x_1113_);
lean_dec(v_head_1103_);
v___x_1121_ = 45;
v___x_1122_ = lean_uint32_dec_eq(v___x_1120_, v___x_1121_);
v___y_1107_ = v___x_1122_;
goto v___jp_1106_;
}
v___jp_1106_:
{
if (v___y_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec_ref(v___f_1105_);
lean_dec(v_tail_1104_);
lean_dec(v_toBind_1099_);
lean_dec(v_set_1098_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_apply_2(v_toPure_1096_, lean_box(0), v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v_toPure_1096_);
v___x_1110_ = lean_apply_1(v_set_1098_, v_tail_1104_);
v___x_1111_ = lean_apply_4(v_toBind_1099_, lean_box(0), lean_box(0), v___x_1110_, v___f_1105_);
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_handle_1125_){
_start:
{
lean_object* v_toApplicative_1126_; lean_object* v_toBind_1127_; lean_object* v_get_1128_; lean_object* v_set_1129_; lean_object* v_toPure_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v_toApplicative_1126_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc_ref(v_toApplicative_1126_);
v_toBind_1127_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1127_, 2);
lean_dec_ref(v_inst_1123_);
v_get_1128_ = lean_ctor_get(v_inst_1124_, 0);
lean_inc(v_get_1128_);
v_set_1129_ = lean_ctor_get(v_inst_1124_, 1);
lean_inc(v_set_1129_);
lean_dec_ref(v_inst_1124_);
v_toPure_1130_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_inc(v_toPure_1130_);
lean_dec_ref(v_toApplicative_1126_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1131_, 0, v_toPure_1130_);
lean_closure_set(v___f_1131_, 1, v_handle_1125_);
lean_closure_set(v___f_1131_, 2, v_set_1129_);
lean_closure_set(v___f_1131_, 3, v_toBind_1127_);
v___x_1132_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v_get_1128_, v___f_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object* v_m_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_handle_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lake_processLeadingOption___redArg(v_inst_1134_, v_inst_1135_, v_handle_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object* v___x_1138_, lean_object* v_head_1139_, lean_object* v_it_1140_, lean_object* v_acc_1141_, lean_object* v_hP_1142_, lean_object* v_recur_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_nat_dec_eq(v_it_1140_, v___x_1138_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_string_utf8_next_fast(v_head_1139_, v_it_1140_);
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_nat_add(v_acc_1141_, v___x_1146_);
v___x_1148_ = lean_apply_4(v_recur_1143_, v___x_1145_, v___x_1147_, lean_box(0), lean_box(0));
return v___x_1148_;
}
else
{
lean_dec_ref(v_recur_1143_);
lean_inc(v_acc_1141_);
return v_acc_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1___boxed(lean_object* v___x_1149_, lean_object* v_head_1150_, lean_object* v_it_1151_, lean_object* v_acc_1152_, lean_object* v_hP_1153_, lean_object* v_recur_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lake_processLeadingOptions___redArg___lam__1(v___x_1149_, v_head_1150_, v_it_1151_, v_acc_1152_, v_hP_1153_, v_recur_1154_);
lean_dec(v_acc_1152_);
lean_dec(v_it_1151_);
lean_dec_ref(v_head_1150_);
lean_dec(v___x_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object* v_handle_1156_, lean_object* v_head_1157_, lean_object* v_toBind_1158_, lean_object* v___f_1159_, lean_object* v_____r_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_apply_1(v_handle_1156_, v_head_1157_);
v___x_1162_ = lean_apply_4(v_toBind_1158_, lean_box(0), lean_box(0), v___x_1161_, v___f_1159_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__3(lean_object* v_handle_1163_, lean_object* v_toBind_1164_, lean_object* v___f_1165_, lean_object* v_toPure_1166_, lean_object* v_set_1167_, lean_object* v___f_1168_, lean_object* v_____do__lift_1169_){
_start:
{
if (lean_obj_tag(v_____do__lift_1169_) == 1)
{
lean_object* v_head_1170_; lean_object* v_tail_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_len_1178_; uint8_t v___y_1180_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_head_1170_ = lean_ctor_get(v_____do__lift_1169_, 0);
lean_inc_n(v_head_1170_, 4);
v_tail_1171_ = lean_ctor_get(v_____do__lift_1169_, 1);
lean_inc(v_tail_1171_);
lean_dec_ref_known(v_____do__lift_1169_, 2);
lean_inc(v_toBind_1164_);
v___f_1172_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1172_, 0, v_handle_1163_);
lean_closure_set(v___f_1172_, 1, v_head_1170_);
lean_closure_set(v___f_1172_, 2, v_toBind_1164_);
lean_closure_set(v___f_1172_, 3, v___f_1165_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_string_utf8_byte_size(v_head_1170_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_1175_, 0, v___x_1174_);
lean_closure_set(v___f_1175_, 1, v_head_1170_);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v_head_1170_);
lean_ctor_set(v___x_1176_, 1, v___x_1173_);
lean_ctor_set(v___x_1176_, 2, v___x_1174_);
v___x_1177_ = l_String_Slice_positions(v___x_1176_);
lean_dec_ref_known(v___x_1176_, 3);
v_len_1178_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1175_, v___x_1177_, v___x_1173_, lean_box(0));
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_dec_lt(v___x_1188_, v_len_1178_);
if (v___x_1189_ == 0)
{
lean_dec(v_head_1170_);
v___y_1180_ = v___x_1189_;
goto v___jp_1179_;
}
else
{
uint32_t v___x_1190_; uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_string_utf8_get(v_head_1170_, v___x_1173_);
lean_dec(v_head_1170_);
v___x_1191_ = 45;
v___x_1192_ = lean_uint32_dec_eq(v___x_1190_, v___x_1191_);
v___y_1180_ = v___x_1192_;
goto v___jp_1179_;
}
v___jp_1179_:
{
if (v___y_1180_ == 0)
{
uint8_t v___x_1181_; 
lean_dec_ref(v___f_1172_);
v___x_1181_ = lean_nat_dec_eq(v_len_1178_, v___x_1173_);
lean_dec(v_len_1178_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_tail_1171_);
lean_dec(v___f_1168_);
lean_dec(v_set_1167_);
lean_dec(v_toBind_1164_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_apply_2(v_toPure_1166_, lean_box(0), v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_toPure_1166_);
v___x_1184_ = lean_apply_1(v_set_1167_, v_tail_1171_);
v___x_1185_ = lean_apply_4(v_toBind_1164_, lean_box(0), lean_box(0), v___x_1184_, v___f_1168_);
return v___x_1185_;
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec(v_len_1178_);
lean_dec(v___f_1168_);
lean_dec(v_toPure_1166_);
v___x_1186_ = lean_apply_1(v_set_1167_, v_tail_1171_);
v___x_1187_ = lean_apply_4(v_toBind_1164_, lean_box(0), lean_box(0), v___x_1186_, v___f_1172_);
return v___x_1187_;
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_____do__lift_1169_);
lean_dec(v___f_1168_);
lean_dec(v_set_1167_);
lean_dec(v___f_1165_);
lean_dec(v_toBind_1164_);
lean_dec(v_handle_1163_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_apply_2(v_toPure_1166_, lean_box(0), v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_handle_1197_){
_start:
{
lean_object* v_toApplicative_1198_; lean_object* v_toBind_1199_; lean_object* v_get_1200_; lean_object* v_set_1201_; lean_object* v_toPure_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; 
v_toApplicative_1198_ = lean_ctor_get(v_inst_1195_, 0);
v_toBind_1199_ = lean_ctor_get(v_inst_1195_, 1);
lean_inc_n(v_toBind_1199_, 2);
v_get_1200_ = lean_ctor_get(v_inst_1196_, 0);
lean_inc(v_get_1200_);
v_set_1201_ = lean_ctor_get(v_inst_1196_, 1);
lean_inc(v_set_1201_);
v_toPure_1202_ = lean_ctor_get(v_toApplicative_1198_, 1);
lean_inc(v_toPure_1202_);
lean_inc(v_handle_1197_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1203_, 0, v_inst_1195_);
lean_closure_set(v___f_1203_, 1, v_inst_1196_);
lean_closure_set(v___f_1203_, 2, v_handle_1197_);
lean_inc_ref(v___f_1203_);
v___f_1204_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1204_, 0, v_handle_1197_);
lean_closure_set(v___f_1204_, 1, v_toBind_1199_);
lean_closure_set(v___f_1204_, 2, v___f_1203_);
lean_closure_set(v___f_1204_, 3, v_toPure_1202_);
lean_closure_set(v___f_1204_, 4, v_set_1201_);
lean_closure_set(v___f_1204_, 5, v___f_1203_);
v___x_1205_ = lean_apply_4(v_toBind_1199_, lean_box(0), lean_box(0), v_get_1200_, v___f_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_handle_1208_, lean_object* v_____r_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lake_processLeadingOptions___redArg(v_inst_1206_, v_inst_1207_, v_handle_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object* v_m_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_handle_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lake_processLeadingOptions___redArg(v_inst_1212_, v_inst_1213_, v_handle_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object* v_x_1216_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_x_1216_);
return v___x_1218_;
}
else
{
lean_object* v_head_1219_; lean_object* v_tail_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1228_; 
v_head_1219_ = lean_ctor_get(v_x_1216_, 0);
v_tail_1220_ = lean_ctor_get(v_x_1216_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_1216_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1222_ = v_x_1216_;
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_tail_1220_);
lean_inc(v_head_1219_);
lean_dec(v_x_1216_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_head_1219_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_tail_1220_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object* v___x_1229_, lean_object* v_val_1230_, lean_object* v_it_1231_, lean_object* v_acc_1232_, lean_object* v_hP_1233_, lean_object* v_recur_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_eq(v_it_1231_, v___x_1229_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = lean_string_utf8_next_fast(v_val_1230_, v_it_1231_);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_acc_1232_, v___x_1237_);
v___x_1239_ = lean_apply_4(v_recur_1234_, v___x_1236_, v___x_1238_, lean_box(0), lean_box(0));
return v___x_1239_;
}
else
{
lean_dec_ref(v_recur_1234_);
lean_inc(v_acc_1232_);
return v_acc_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2___boxed(lean_object* v___x_1240_, lean_object* v_val_1241_, lean_object* v_it_1242_, lean_object* v_acc_1243_, lean_object* v_hP_1244_, lean_object* v_recur_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lake_collectArgs___redArg___lam__2(v___x_1240_, v_val_1241_, v_it_1242_, v_acc_1243_, v_hP_1244_, v_recur_1245_);
lean_dec(v_acc_1243_);
lean_dec(v_it_1242_);
lean_dec_ref(v_val_1241_);
lean_dec(v___x_1240_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__3(lean_object* v_args_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_option_1251_, lean_object* v_toBind_1252_, lean_object* v___f_1253_, lean_object* v_toPure_1254_, lean_object* v_____do__lift_1255_){
_start:
{
if (lean_obj_tag(v_____do__lift_1255_) == 1)
{
lean_object* v_val_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_len_1262_; uint8_t v___y_1264_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
lean_dec(v_toPure_1254_);
v_val_1256_ = lean_ctor_get(v_____do__lift_1255_, 0);
lean_inc_n(v_val_1256_, 3);
lean_dec_ref_known(v_____do__lift_1255_, 1);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = lean_string_utf8_byte_size(v_val_1256_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__2___boxed), 6, 2);
lean_closure_set(v___f_1259_, 0, v___x_1258_);
lean_closure_set(v___f_1259_, 1, v_val_1256_);
v___x_1260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1260_, 0, v_val_1256_);
lean_ctor_set(v___x_1260_, 1, v___x_1257_);
lean_ctor_set(v___x_1260_, 2, v___x_1258_);
v___x_1261_ = l_String_Slice_positions(v___x_1260_);
lean_dec_ref_known(v___x_1260_, 3);
v_len_1262_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1259_, v___x_1261_, v___x_1257_, lean_box(0));
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_dec_lt(v___x_1271_, v_len_1262_);
if (v___x_1272_ == 0)
{
v___y_1264_ = v___x_1272_;
goto v___jp_1263_;
}
else
{
uint32_t v___x_1273_; uint32_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_string_utf8_get(v_val_1256_, v___x_1257_);
v___x_1274_ = 45;
v___x_1275_ = lean_uint32_dec_eq(v___x_1273_, v___x_1274_);
v___y_1264_ = v___x_1275_;
goto v___jp_1263_;
}
v___jp_1263_:
{
if (v___y_1264_ == 0)
{
uint8_t v___x_1265_; 
lean_dec(v___f_1253_);
lean_dec(v_toBind_1252_);
v___x_1265_ = lean_nat_dec_eq(v_len_1262_, v___x_1257_);
lean_dec(v_len_1262_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_array_push(v_args_1248_, v_val_1256_);
v___x_1267_ = l_Lake_collectArgs___redArg(v_inst_1249_, v_inst_1250_, v_option_1251_, v___x_1266_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
lean_dec(v_val_1256_);
v___x_1268_ = l_Lake_collectArgs___redArg(v_inst_1249_, v_inst_1250_, v_option_1251_, v_args_1248_);
return v___x_1268_;
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_len_1262_);
lean_dec_ref(v_inst_1250_);
lean_dec_ref(v_inst_1249_);
lean_dec_ref(v_args_1248_);
v___x_1269_ = lean_apply_1(v_option_1251_, v_val_1256_);
v___x_1270_ = lean_apply_4(v_toBind_1252_, lean_box(0), lean_box(0), v___x_1269_, v___f_1253_);
return v___x_1270_;
}
}
}
else
{
lean_object* v___x_1276_; 
lean_dec(v_____do__lift_1255_);
lean_dec(v___f_1253_);
lean_dec(v_toBind_1252_);
lean_dec(v_option_1251_);
lean_dec_ref(v_inst_1250_);
lean_dec_ref(v_inst_1249_);
v___x_1276_ = lean_apply_2(v_toPure_1254_, lean_box(0), v_args_1248_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_option_1279_, lean_object* v_args_1280_){
_start:
{
lean_object* v_toApplicative_1281_; lean_object* v_toBind_1282_; lean_object* v_modifyGet_1283_; lean_object* v_toPure_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; 
v_toApplicative_1281_ = lean_ctor_get(v_inst_1277_, 0);
v_toBind_1282_ = lean_ctor_get(v_inst_1277_, 1);
lean_inc_n(v_toBind_1282_, 2);
v_modifyGet_1283_ = lean_ctor_get(v_inst_1278_, 2);
v_toPure_1284_ = lean_ctor_get(v_toApplicative_1281_, 1);
lean_inc(v_toPure_1284_);
v___f_1285_ = ((lean_object*)(l_Lake_collectArgs___redArg___closed__0));
lean_inc_ref(v_args_1280_);
lean_inc(v_option_1279_);
lean_inc_ref(v_inst_1278_);
lean_inc_ref(v_inst_1277_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1286_, 0, v_inst_1277_);
lean_closure_set(v___f_1286_, 1, v_inst_1278_);
lean_closure_set(v___f_1286_, 2, v_option_1279_);
lean_closure_set(v___f_1286_, 3, v_args_1280_);
lean_inc(v_modifyGet_1283_);
v___x_1287_ = lean_apply_2(v_modifyGet_1283_, lean_box(0), v___f_1285_);
v___f_1288_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1288_, 0, v_args_1280_);
lean_closure_set(v___f_1288_, 1, v_inst_1277_);
lean_closure_set(v___f_1288_, 2, v_inst_1278_);
lean_closure_set(v___f_1288_, 3, v_option_1279_);
lean_closure_set(v___f_1288_, 4, v_toBind_1282_);
lean_closure_set(v___f_1288_, 5, v___f_1286_);
lean_closure_set(v___f_1288_, 6, v_toPure_1284_);
v___x_1289_ = lean_apply_4(v_toBind_1282_, lean_box(0), lean_box(0), v___x_1287_, v___f_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_option_1292_, lean_object* v_args_1293_, lean_object* v_____r_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lake_collectArgs___redArg(v_inst_1290_, v_inst_1291_, v_option_1292_, v_args_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object* v_m_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_option_1299_, lean_object* v_args_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lake_collectArgs___redArg(v_inst_1297_, v_inst_1298_, v_option_1299_, v_args_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object* v_inst_1302_, lean_object* v_____do__lift_1303_){
_start:
{
lean_object* v_set_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_set_1304_ = lean_ctor_get(v_inst_1302_, 1);
lean_inc(v_set_1304_);
lean_dec_ref(v_inst_1302_);
v___x_1305_ = lean_array_to_list(v_____do__lift_1303_);
v___x_1306_ = lean_apply_1(v_set_1304_, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_handle_1311_){
_start:
{
lean_object* v_toBind_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_toBind_1312_ = lean_ctor_get(v_inst_1309_, 1);
lean_inc(v_toBind_1312_);
lean_inc_ref(v_inst_1310_);
v___f_1313_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1313_, 0, v_inst_1310_);
v___x_1314_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1315_ = l_Lake_collectArgs___redArg(v_inst_1309_, v_inst_1310_, v_handle_1311_, v___x_1314_);
v___x_1316_ = lean_apply_4(v_toBind_1312_, lean_box(0), lean_box(0), v___x_1315_, v___f_1313_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object* v_m_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_handle_1320_){
_start:
{
lean_object* v_toBind_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_toBind_1321_ = lean_ctor_get(v_inst_1318_, 1);
lean_inc(v_toBind_1321_);
lean_inc_ref(v_inst_1319_);
v___f_1322_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1322_, 0, v_inst_1319_);
v___x_1323_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1324_ = l_Lake_collectArgs___redArg(v_inst_1318_, v_inst_1319_, v_handle_1320_, v___x_1323_);
v___x_1325_ = lean_apply_4(v_toBind_1321_, lean_box(0), lean_box(0), v___x_1324_, v___f_1322_);
return v___x_1325_;
}
}
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Cli(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
