// Lean compiler output
// Module: Lake.Util.Cli
// Imports: public import Init.Data.String.TakeDrop public import Init.Data.String.Search
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
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_collectArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_collectArgs___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_collectArgs___redArg___closed__0 = (const lean_object*)&l_Lake_collectArgs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toBind_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_str_210_; lean_object* v_startInclusive_211_; lean_object* v_endExclusive_212_; lean_object* v_modifyGet_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_toBind_200_ = lean_ctor_get(v_inst_196_, 1);
lean_inc(v_toBind_200_);
lean_dec_ref(v_inst_196_);
v___x_201_ = lean_unsigned_to_nat(2u);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_string_utf8_byte_size(v_opt_199_);
lean_inc_ref(v_opt_199_);
v___x_204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_204_, 0, v_opt_199_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
v___x_205_ = l_String_Slice_Pos_nextn(v___x_204_, v___x_202_, v___x_201_);
lean_dec_ref(v___x_204_);
lean_inc_ref(v_opt_199_);
v___x_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_206_, 0, v_opt_199_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
lean_ctor_set(v___x_206_, 2, v___x_203_);
v___x_207_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_208_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v___x_209_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_206_, v___x_207_, v___x_208_, v___x_202_);
lean_dec_ref(v___x_206_);
v_str_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_str_210_);
v_startInclusive_211_ = lean_ctor_get(v___x_209_, 1);
lean_inc(v_startInclusive_211_);
v_endExclusive_212_ = lean_ctor_get(v___x_209_, 2);
lean_inc(v_endExclusive_212_);
lean_dec_ref(v___x_209_);
v_modifyGet_213_ = lean_ctor_get(v_inst_197_, 2);
lean_inc(v_modifyGet_213_);
lean_dec_ref(v_inst_197_);
v___f_214_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_214_, 0, v_opt_199_);
lean_closure_set(v___f_214_, 1, v_handle_198_);
v___x_215_ = lean_string_utf8_extract(v_str_210_, v_startInclusive_211_, v_endExclusive_212_);
lean_dec(v_endExclusive_212_);
lean_dec(v_startInclusive_211_);
lean_dec_ref(v_str_210_);
v___f_216_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_216_, 0, v___x_215_);
v___x_217_ = lean_apply_2(v_modifyGet_213_, lean_box(0), v___f_216_);
v___x_218_ = lean_apply_4(v_toBind_200_, lean_box(0), lean_box(0), v___x_217_, v___f_214_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object* v_m_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_00_u03b1_222_, lean_object* v_handle_223_, lean_object* v_opt_224_){
_start:
{
lean_object* v_toBind_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_str_235_; lean_object* v_startInclusive_236_; lean_object* v_endExclusive_237_; lean_object* v_modifyGet_238_; lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_toBind_225_ = lean_ctor_get(v_inst_220_, 1);
lean_inc(v_toBind_225_);
lean_dec_ref(v_inst_220_);
v___x_226_ = lean_unsigned_to_nat(2u);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_string_utf8_byte_size(v_opt_224_);
lean_inc_ref(v_opt_224_);
v___x_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_229_, 0, v_opt_224_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
v___x_230_ = l_String_Slice_Pos_nextn(v___x_229_, v___x_227_, v___x_226_);
lean_dec_ref(v___x_229_);
lean_inc_ref(v_opt_224_);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v_opt_224_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
lean_ctor_set(v___x_231_, 2, v___x_228_);
v___x_232_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_233_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v___x_234_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_231_, v___x_232_, v___x_233_, v___x_227_);
lean_dec_ref(v___x_231_);
v_str_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_str_235_);
v_startInclusive_236_ = lean_ctor_get(v___x_234_, 1);
lean_inc(v_startInclusive_236_);
v_endExclusive_237_ = lean_ctor_get(v___x_234_, 2);
lean_inc(v_endExclusive_237_);
lean_dec_ref(v___x_234_);
v_modifyGet_238_ = lean_ctor_get(v_inst_221_, 2);
lean_inc(v_modifyGet_238_);
lean_dec_ref(v_inst_221_);
v___f_239_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_239_, 0, v_opt_224_);
lean_closure_set(v___f_239_, 1, v_handle_223_);
v___x_240_ = lean_string_utf8_extract(v_str_235_, v_startInclusive_236_, v_endExclusive_237_);
lean_dec(v_endExclusive_237_);
lean_dec(v_startInclusive_236_);
lean_dec_ref(v_str_235_);
v___f_241_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_241_, 0, v___x_240_);
v___x_242_ = lean_apply_2(v_modifyGet_238_, lean_box(0), v___f_241_);
v___x_243_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v___x_242_, v___f_239_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_handle_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_toBind_248_; lean_object* v___x_249_; lean_object* v_modifyGet_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_265_; 
v_toBind_248_ = lean_ctor_get(v_inst_244_, 1);
lean_inc(v_toBind_248_);
lean_dec_ref(v_inst_244_);
v___x_249_ = lean_string_utf8_byte_size(v_opt_247_);
v_modifyGet_250_ = lean_ctor_get(v_inst_245_, 2);
v_isSharedCheck_265_ = !lean_is_exclusive(v_inst_245_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; 
v_unused_266_ = lean_ctor_get(v_inst_245_, 1);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_inst_245_, 0);
lean_dec(v_unused_267_);
v___x_252_ = v_inst_245_;
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_modifyGet_250_);
lean_dec(v_inst_245_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_247_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 2, v___x_249_);
lean_ctor_set(v___x_252_, 1, v___x_254_);
lean_ctor_set(v___x_252_, 0, v_opt_247_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_opt_247_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v___x_249_);
v___x_256_ = v_reuseFailAlloc_264_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc_ref(v_opt_247_);
v___f_257_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_257_, 0, v_opt_247_);
lean_closure_set(v___f_257_, 1, v_handle_246_);
v___x_258_ = lean_unsigned_to_nat(2u);
v___x_259_ = l_String_Slice_Pos_nextn(v___x_256_, v___x_254_, v___x_258_);
lean_dec_ref(v___x_256_);
v___x_260_ = lean_string_utf8_extract(v_opt_247_, v___x_259_, v___x_249_);
lean_dec(v___x_259_);
lean_dec_ref(v_opt_247_);
v___f_261_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_261_, 0, v___x_260_);
v___x_262_ = lean_apply_2(v_modifyGet_250_, lean_box(0), v___f_261_);
v___x_263_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v___x_262_, v___f_257_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object* v_m_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_00_u03b1_271_, lean_object* v_handle_272_, lean_object* v_opt_273_){
_start:
{
lean_object* v_toBind_274_; lean_object* v___x_275_; lean_object* v_modifyGet_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_291_; 
v_toBind_274_ = lean_ctor_get(v_inst_269_, 1);
lean_inc(v_toBind_274_);
lean_dec_ref(v_inst_269_);
v___x_275_ = lean_string_utf8_byte_size(v_opt_273_);
v_modifyGet_276_ = lean_ctor_get(v_inst_270_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v_inst_270_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_292_ = lean_ctor_get(v_inst_270_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_inst_270_, 0);
lean_dec(v_unused_293_);
v___x_278_ = v_inst_270_;
v_isShared_279_ = v_isSharedCheck_291_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_modifyGet_276_);
lean_dec(v_inst_270_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_291_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_273_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 2, v___x_275_);
lean_ctor_set(v___x_278_, 1, v___x_280_);
lean_ctor_set(v___x_278_, 0, v_opt_273_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_opt_273_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_275_);
v___x_282_ = v_reuseFailAlloc_290_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_inc_ref(v_opt_273_);
v___f_283_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_283_, 0, v_opt_273_);
lean_closure_set(v___f_283_, 1, v_handle_272_);
v___x_284_ = lean_unsigned_to_nat(2u);
v___x_285_ = l_String_Slice_Pos_nextn(v___x_282_, v___x_280_, v___x_284_);
lean_dec_ref(v___x_282_);
v___x_286_ = lean_string_utf8_extract(v_opt_273_, v___x_285_, v___x_275_);
lean_dec(v___x_285_);
lean_dec_ref(v_opt_273_);
v___f_287_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_287_, 0, v___x_286_);
v___x_288_ = lean_apply_2(v_modifyGet_276_, lean_box(0), v___f_287_);
v___x_289_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_288_, v___f_283_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object* v_opt_294_, lean_object* v_p_295_, lean_object* v_inst_296_, lean_object* v_handle_297_, lean_object* v_____r_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(v_opt_294_, v_p_295_, v_inst_296_, v_handle_297_, v_____r_298_);
lean_dec(v_p_295_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(lean_object* v_inst_300_, lean_object* v_handle_301_, lean_object* v_opt_302_, lean_object* v_p_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_string_utf8_at_end(v_opt_302_, v_p_303_);
if (v___x_304_ == 0)
{
lean_object* v_toBind_305_; lean_object* v___f_306_; uint32_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_toBind_305_ = lean_ctor_get(v_inst_300_, 1);
lean_inc(v_toBind_305_);
lean_inc(v_handle_301_);
lean_inc(v_p_303_);
lean_inc_ref(v_opt_302_);
v___f_306_ = lean_alloc_closure((void*)(l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_306_, 0, v_opt_302_);
lean_closure_set(v___f_306_, 1, v_p_303_);
lean_closure_set(v___f_306_, 2, v_inst_300_);
lean_closure_set(v___f_306_, 3, v_handle_301_);
v___x_307_ = lean_string_utf8_get_fast(v_opt_302_, v_p_303_);
lean_dec(v_p_303_);
lean_dec_ref(v_opt_302_);
v___x_308_ = lean_box_uint32(v___x_307_);
v___x_309_ = lean_apply_1(v_handle_301_, v___x_308_);
v___x_310_ = lean_apply_4(v_toBind_305_, lean_box(0), lean_box(0), v___x_309_, v___f_306_);
return v___x_310_;
}
else
{
lean_object* v_toApplicative_311_; lean_object* v_toPure_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_p_303_);
lean_dec_ref(v_opt_302_);
lean_dec(v_handle_301_);
v_toApplicative_311_ = lean_ctor_get(v_inst_300_, 0);
lean_inc_ref(v_toApplicative_311_);
lean_dec_ref(v_inst_300_);
v_toPure_312_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_inc(v_toPure_312_);
lean_dec_ref(v_toApplicative_311_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_apply_2(v_toPure_312_, lean_box(0), v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(lean_object* v_opt_315_, lean_object* v_p_316_, lean_object* v_inst_317_, lean_object* v_handle_318_, lean_object* v_____r_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_string_utf8_next_fast(v_opt_315_, v_p_316_);
v___x_321_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_317_, v_handle_318_, v_opt_315_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop(lean_object* v_m_322_, lean_object* v_inst_323_, lean_object* v_handle_324_, lean_object* v_opt_325_, lean_object* v_p_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_323_, v_handle_324_, v_opt_325_, v_p_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object* v_inst_328_, lean_object* v_handle_329_, lean_object* v_opt_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_328_, v_handle_329_, v_opt_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object* v_m_333_, lean_object* v_inst_334_, lean_object* v_handle_335_, lean_object* v_opt_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(v_inst_334_, v_handle_335_, v_opt_336_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object* v_opt_339_, lean_object* v___y_340_, lean_object* v_handle_341_, lean_object* v_____r_342_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_string_utf8_extract(v_opt_339_, v___x_343_, v___y_340_);
v___x_345_ = lean_apply_1(v_handle_341_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object* v_opt_346_, lean_object* v___y_347_, lean_object* v_handle_348_, lean_object* v_____r_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lake_longOptionOrSpace___redArg___lam__0(v_opt_346_, v___y_347_, v_handle_348_, v_____r_349_);
lean_dec(v___y_347_);
lean_dec_ref(v_opt_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__2(lean_object* v___x_351_, lean_object* v_opt_352_, lean_object* v___x_353_, lean_object* v_it_354_, lean_object* v_acc_355_, lean_object* v_hP_356_, lean_object* v_recur_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_eq(v_it_354_, v___x_351_);
if (v___x_358_ == 0)
{
uint32_t v___x_359_; uint32_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_string_utf8_get_fast(v_opt_352_, v_it_354_);
v___x_360_ = 32;
v___x_361_ = lean_uint32_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_string_utf8_next_fast(v_opt_352_, v_it_354_);
lean_dec(v_it_354_);
v___x_363_ = lean_apply_4(v_recur_357_, v___x_362_, v___x_353_, lean_box(0), lean_box(0));
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_dec_ref(v_recur_357_);
lean_dec(v___x_353_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_it_354_);
return v___x_364_;
}
}
else
{
lean_dec_ref(v_recur_357_);
lean_dec(v_it_354_);
lean_dec(v___x_353_);
lean_inc(v_acc_355_);
return v_acc_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__2___boxed(lean_object* v___x_365_, lean_object* v_opt_366_, lean_object* v___x_367_, lean_object* v_it_368_, lean_object* v_acc_369_, lean_object* v_hP_370_, lean_object* v_recur_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lake_longOptionOrSpace___redArg___lam__2(v___x_365_, v_opt_366_, v___x_367_, v_it_368_, v_acc_369_, v_hP_370_, v_recur_371_);
lean_dec(v_acc_369_);
lean_dec_ref(v_opt_366_);
lean_dec(v___x_365_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_handle_375_, lean_object* v_opt_376_){
_start:
{
lean_object* v___y_378_; lean_object* v_searcher_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___x_394_; 
v_searcher_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_string_utf8_byte_size(v_opt_376_);
v___x_392_ = lean_box(0);
lean_inc_ref(v_opt_376_);
v___f_393_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_393_, 0, v___x_391_);
lean_closure_set(v___f_393_, 1, v_opt_376_);
lean_closure_set(v___f_393_, 2, v___x_392_);
v___x_394_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_393_, v_searcher_390_, v___x_392_, lean_box(0));
if (lean_obj_tag(v___x_394_) == 0)
{
v___y_378_ = v___x_391_;
goto v___jp_377_;
}
else
{
lean_object* v_val_395_; 
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref(v___x_394_);
v___y_378_ = v_val_395_;
goto v___jp_377_;
}
v___jp_377_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_string_utf8_byte_size(v_opt_376_);
v___x_380_ = lean_nat_dec_eq(v___y_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v_toBind_381_; lean_object* v_modifyGet_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_toBind_381_ = lean_ctor_get(v_inst_373_, 1);
lean_inc(v_toBind_381_);
lean_dec_ref(v_inst_373_);
v_modifyGet_382_ = lean_ctor_get(v_inst_374_, 2);
lean_inc(v_modifyGet_382_);
lean_dec_ref(v_inst_374_);
lean_inc(v___y_378_);
lean_inc_ref(v_opt_376_);
v___f_383_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_383_, 0, v_opt_376_);
lean_closure_set(v___f_383_, 1, v___y_378_);
lean_closure_set(v___f_383_, 2, v_handle_375_);
v___x_384_ = lean_string_utf8_next_fast(v_opt_376_, v___y_378_);
lean_dec(v___y_378_);
v___x_385_ = lean_string_utf8_extract(v_opt_376_, v___x_384_, v___x_379_);
lean_dec_ref(v_opt_376_);
v___f_386_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_386_, 0, v___x_385_);
v___x_387_ = lean_apply_2(v_modifyGet_382_, lean_box(0), v___f_386_);
v___x_388_ = lean_apply_4(v_toBind_381_, lean_box(0), lean_box(0), v___x_387_, v___f_383_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; 
lean_dec(v___y_378_);
lean_dec_ref(v_inst_374_);
lean_dec_ref(v_inst_373_);
v___x_389_ = lean_apply_1(v_handle_375_, v_opt_376_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object* v_m_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_00_u03b1_399_, lean_object* v_handle_400_, lean_object* v_opt_401_){
_start:
{
lean_object* v___y_403_; lean_object* v_searcher_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___f_418_; lean_object* v___x_419_; 
v_searcher_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_string_utf8_byte_size(v_opt_401_);
v___x_417_ = lean_box(0);
lean_inc_ref(v_opt_401_);
v___f_418_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_418_, 0, v___x_416_);
lean_closure_set(v___f_418_, 1, v_opt_401_);
lean_closure_set(v___f_418_, 2, v___x_417_);
v___x_419_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_418_, v_searcher_415_, v___x_417_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
v___y_403_ = v___x_416_;
goto v___jp_402_;
}
else
{
lean_object* v_val_420_; 
v_val_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v___x_419_);
v___y_403_ = v_val_420_;
goto v___jp_402_;
}
v___jp_402_:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_string_utf8_byte_size(v_opt_401_);
v___x_405_ = lean_nat_dec_eq(v___y_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v_toBind_406_; lean_object* v_modifyGet_407_; lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_toBind_406_ = lean_ctor_get(v_inst_397_, 1);
lean_inc(v_toBind_406_);
lean_dec_ref(v_inst_397_);
v_modifyGet_407_ = lean_ctor_get(v_inst_398_, 2);
lean_inc(v_modifyGet_407_);
lean_dec_ref(v_inst_398_);
lean_inc(v___y_403_);
lean_inc_ref(v_opt_401_);
v___f_408_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_408_, 0, v_opt_401_);
lean_closure_set(v___f_408_, 1, v___y_403_);
lean_closure_set(v___f_408_, 2, v_handle_400_);
v___x_409_ = lean_string_utf8_next_fast(v_opt_401_, v___y_403_);
lean_dec(v___y_403_);
v___x_410_ = lean_string_utf8_extract(v_opt_401_, v___x_409_, v___x_404_);
lean_dec_ref(v_opt_401_);
v___f_411_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_411_, 0, v___x_410_);
v___x_412_ = lean_apply_2(v_modifyGet_407_, lean_box(0), v___f_411_);
v___x_413_ = lean_apply_4(v_toBind_406_, lean_box(0), lean_box(0), v___x_412_, v___f_408_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; 
lean_dec(v___y_403_);
lean_dec_ref(v_inst_398_);
lean_dec_ref(v_inst_397_);
v___x_414_ = lean_apply_1(v_handle_400_, v_opt_401_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2(lean_object* v___x_421_, lean_object* v_opt_422_, lean_object* v___x_423_, lean_object* v_it_424_, lean_object* v_acc_425_, lean_object* v_hP_426_, lean_object* v_recur_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_eq(v_it_424_, v___x_421_);
if (v___x_428_ == 0)
{
uint32_t v___x_429_; uint32_t v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_string_utf8_get_fast(v_opt_422_, v_it_424_);
v___x_430_ = 61;
v___x_431_ = lean_uint32_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_string_utf8_next_fast(v_opt_422_, v_it_424_);
lean_dec(v_it_424_);
v___x_433_ = lean_apply_4(v_recur_427_, v___x_432_, v___x_423_, lean_box(0), lean_box(0));
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
lean_dec_ref(v_recur_427_);
lean_dec(v___x_423_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_it_424_);
return v___x_434_;
}
}
else
{
lean_dec_ref(v_recur_427_);
lean_dec(v_it_424_);
lean_dec(v___x_423_);
lean_inc(v_acc_425_);
return v_acc_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg___lam__2___boxed(lean_object* v___x_435_, lean_object* v_opt_436_, lean_object* v___x_437_, lean_object* v_it_438_, lean_object* v_acc_439_, lean_object* v_hP_440_, lean_object* v_recur_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lake_longOptionOrEq___redArg___lam__2(v___x_435_, v_opt_436_, v___x_437_, v_it_438_, v_acc_439_, v_hP_440_, v_recur_441_);
lean_dec(v_acc_439_);
lean_dec_ref(v_opt_436_);
lean_dec(v___x_435_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_handle_445_, lean_object* v_opt_446_){
_start:
{
lean_object* v___y_448_; lean_object* v_searcher_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___x_464_; 
v_searcher_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_string_utf8_byte_size(v_opt_446_);
v___x_462_ = lean_box(0);
lean_inc_ref(v_opt_446_);
v___f_463_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_463_, 0, v___x_461_);
lean_closure_set(v___f_463_, 1, v_opt_446_);
lean_closure_set(v___f_463_, 2, v___x_462_);
v___x_464_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_463_, v_searcher_460_, v___x_462_, lean_box(0));
if (lean_obj_tag(v___x_464_) == 0)
{
v___y_448_ = v___x_461_;
goto v___jp_447_;
}
else
{
lean_object* v_val_465_; 
v_val_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref(v___x_464_);
v___y_448_ = v_val_465_;
goto v___jp_447_;
}
v___jp_447_:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_string_utf8_byte_size(v_opt_446_);
v___x_450_ = lean_nat_dec_eq(v___y_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v_toBind_451_; lean_object* v_modifyGet_452_; lean_object* v___f_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_toBind_451_ = lean_ctor_get(v_inst_443_, 1);
lean_inc(v_toBind_451_);
lean_dec_ref(v_inst_443_);
v_modifyGet_452_ = lean_ctor_get(v_inst_444_, 2);
lean_inc(v_modifyGet_452_);
lean_dec_ref(v_inst_444_);
lean_inc(v___y_448_);
lean_inc_ref(v_opt_446_);
v___f_453_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_453_, 0, v_opt_446_);
lean_closure_set(v___f_453_, 1, v___y_448_);
lean_closure_set(v___f_453_, 2, v_handle_445_);
v___x_454_ = lean_string_utf8_next_fast(v_opt_446_, v___y_448_);
lean_dec(v___y_448_);
v___x_455_ = lean_string_utf8_extract(v_opt_446_, v___x_454_, v___x_449_);
lean_dec_ref(v_opt_446_);
v___f_456_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_456_, 0, v___x_455_);
v___x_457_ = lean_apply_2(v_modifyGet_452_, lean_box(0), v___f_456_);
v___x_458_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v___x_457_, v___f_453_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; 
lean_dec(v___y_448_);
lean_dec_ref(v_inst_444_);
lean_dec_ref(v_inst_443_);
v___x_459_ = lean_apply_1(v_handle_445_, v_opt_446_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object* v_m_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_00_u03b1_469_, lean_object* v_handle_470_, lean_object* v_opt_471_){
_start:
{
lean_object* v___y_473_; lean_object* v_searcher_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___f_488_; lean_object* v___x_489_; 
v_searcher_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_string_utf8_byte_size(v_opt_471_);
v___x_487_ = lean_box(0);
lean_inc_ref(v_opt_471_);
v___f_488_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_488_, 0, v___x_486_);
lean_closure_set(v___f_488_, 1, v_opt_471_);
lean_closure_set(v___f_488_, 2, v___x_487_);
v___x_489_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_488_, v_searcher_485_, v___x_487_, lean_box(0));
if (lean_obj_tag(v___x_489_) == 0)
{
v___y_473_ = v___x_486_;
goto v___jp_472_;
}
else
{
lean_object* v_val_490_; 
v_val_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_val_490_);
lean_dec_ref(v___x_489_);
v___y_473_ = v_val_490_;
goto v___jp_472_;
}
v___jp_472_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_string_utf8_byte_size(v_opt_471_);
v___x_475_ = lean_nat_dec_eq(v___y_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v_toBind_476_; lean_object* v_modifyGet_477_; lean_object* v___f_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_toBind_476_ = lean_ctor_get(v_inst_467_, 1);
lean_inc(v_toBind_476_);
lean_dec_ref(v_inst_467_);
v_modifyGet_477_ = lean_ctor_get(v_inst_468_, 2);
lean_inc(v_modifyGet_477_);
lean_dec_ref(v_inst_468_);
lean_inc(v___y_473_);
lean_inc_ref(v_opt_471_);
v___f_478_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_478_, 0, v_opt_471_);
lean_closure_set(v___f_478_, 1, v___y_473_);
lean_closure_set(v___f_478_, 2, v_handle_470_);
v___x_479_ = lean_string_utf8_next_fast(v_opt_471_, v___y_473_);
lean_dec(v___y_473_);
v___x_480_ = lean_string_utf8_extract(v_opt_471_, v___x_479_, v___x_474_);
lean_dec_ref(v_opt_471_);
v___f_481_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_481_, 0, v___x_480_);
v___x_482_ = lean_apply_2(v_modifyGet_477_, lean_box(0), v___f_481_);
v___x_483_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v___x_482_, v___f_478_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; 
lean_dec(v___y_473_);
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_inst_467_);
v___x_484_ = lean_apply_1(v_handle_470_, v_opt_471_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object* v___x_491_, lean_object* v_searcher_492_, lean_object* v___y_493_, lean_object* v_handle_494_, lean_object* v_____r_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_string_utf8_extract(v___x_491_, v_searcher_492_, v___y_493_);
v___x_497_ = lean_apply_1(v_handle_494_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object* v___x_498_, lean_object* v_searcher_499_, lean_object* v___y_500_, lean_object* v_handle_501_, lean_object* v_____r_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_longOption___redArg___lam__2(v___x_498_, v_searcher_499_, v___y_500_, v_handle_501_, v_____r_502_);
lean_dec(v___y_500_);
lean_dec(v_searcher_499_);
lean_dec_ref(v___x_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__1(lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v_it_507_, lean_object* v_acc_508_, lean_object* v_hP_509_, lean_object* v_recur_510_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = lean_nat_dec_eq(v_it_507_, v___x_504_);
if (v___x_511_ == 0)
{
uint32_t v___x_512_; uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_string_utf8_get_fast(v___x_505_, v_it_507_);
v___x_513_ = 32;
v___x_514_ = lean_uint32_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_string_utf8_next_fast(v___x_505_, v_it_507_);
lean_dec(v_it_507_);
v___x_516_ = lean_apply_4(v_recur_510_, v___x_515_, v___x_506_, lean_box(0), lean_box(0));
return v___x_516_;
}
else
{
lean_object* v___x_517_; 
lean_dec_ref(v_recur_510_);
lean_dec(v___x_506_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v_it_507_);
return v___x_517_;
}
}
else
{
lean_dec_ref(v_recur_510_);
lean_dec(v_it_507_);
lean_dec(v___x_506_);
lean_inc(v_acc_508_);
return v_acc_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__1___boxed(lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_it_521_, lean_object* v_acc_522_, lean_object* v_hP_523_, lean_object* v_recur_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_longOption___redArg___lam__1(v___x_518_, v___x_519_, v___x_520_, v_it_521_, v_acc_522_, v_hP_523_, v_recur_524_);
lean_dec(v_acc_522_);
lean_dec_ref(v___x_519_);
lean_dec(v___x_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object* v_opt_526_, lean_object* v___y_527_, lean_object* v_handle_528_, lean_object* v_modifyGet_529_, lean_object* v_toBind_530_, lean_object* v_____r_531_){
_start:
{
lean_object* v_searcher_532_; lean_object* v___x_533_; lean_object* v___y_535_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
v_searcher_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_string_utf8_extract(v_opt_526_, v_searcher_532_, v___y_527_);
v___x_545_ = lean_string_utf8_byte_size(v___x_533_);
v___x_546_ = lean_box(0);
lean_inc_ref(v___x_533_);
v___f_547_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_547_, 0, v___x_545_);
lean_closure_set(v___f_547_, 1, v___x_533_);
lean_closure_set(v___f_547_, 2, v___x_546_);
v___x_548_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_547_, v_searcher_532_, v___x_546_, lean_box(0));
if (lean_obj_tag(v___x_548_) == 0)
{
v___y_535_ = v___x_545_;
goto v___jp_534_;
}
else
{
lean_object* v_val_549_; 
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref(v___x_548_);
v___y_535_ = v_val_549_;
goto v___jp_534_;
}
v___jp_534_:
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_string_utf8_byte_size(v___x_533_);
v___x_537_ = lean_nat_dec_eq(v___y_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc(v___y_535_);
lean_inc_ref(v___x_533_);
v___f_538_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_538_, 0, v___x_533_);
lean_closure_set(v___f_538_, 1, v_searcher_532_);
lean_closure_set(v___f_538_, 2, v___y_535_);
lean_closure_set(v___f_538_, 3, v_handle_528_);
v___x_539_ = lean_string_utf8_next_fast(v___x_533_, v___y_535_);
lean_dec(v___y_535_);
v___x_540_ = lean_string_utf8_extract(v___x_533_, v___x_539_, v___x_536_);
lean_dec_ref(v___x_533_);
v___f_541_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_541_, 0, v___x_540_);
v___x_542_ = lean_apply_2(v_modifyGet_529_, lean_box(0), v___f_541_);
v___x_543_ = lean_apply_4(v_toBind_530_, lean_box(0), lean_box(0), v___x_542_, v___f_538_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; 
lean_dec(v___y_535_);
lean_dec(v_toBind_530_);
lean_dec(v_modifyGet_529_);
v___x_544_ = lean_apply_1(v_handle_528_, v___x_533_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object* v_opt_550_, lean_object* v___y_551_, lean_object* v_handle_552_, lean_object* v_modifyGet_553_, lean_object* v_toBind_554_, lean_object* v_____r_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lake_longOption___redArg___lam__0(v_opt_550_, v___y_551_, v_handle_552_, v_modifyGet_553_, v_toBind_554_, v_____r_555_);
lean_dec(v___y_551_);
lean_dec_ref(v_opt_550_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_handle_559_, lean_object* v_opt_560_){
_start:
{
lean_object* v___y_562_; lean_object* v___y_575_; lean_object* v_searcher_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___x_595_; 
v_searcher_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_string_utf8_byte_size(v_opt_560_);
v___x_593_ = lean_box(0);
lean_inc_ref(v_opt_560_);
v___f_594_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_594_, 0, v___x_592_);
lean_closure_set(v___f_594_, 1, v_opt_560_);
lean_closure_set(v___f_594_, 2, v___x_593_);
v___x_595_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_594_, v_searcher_591_, v___x_593_, lean_box(0));
if (lean_obj_tag(v___x_595_) == 0)
{
v___y_575_ = v___x_592_;
goto v___jp_574_;
}
else
{
lean_object* v_val_596_; 
v_val_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v___x_595_);
v___y_575_ = v_val_596_;
goto v___jp_574_;
}
v___jp_561_:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_string_utf8_byte_size(v_opt_560_);
v___x_564_ = lean_nat_dec_eq(v___y_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v_toBind_565_; lean_object* v_modifyGet_566_; lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_toBind_565_ = lean_ctor_get(v_inst_557_, 1);
lean_inc(v_toBind_565_);
lean_dec_ref(v_inst_557_);
v_modifyGet_566_ = lean_ctor_get(v_inst_558_, 2);
lean_inc(v_modifyGet_566_);
lean_dec_ref(v_inst_558_);
lean_inc(v___y_562_);
lean_inc_ref(v_opt_560_);
v___f_567_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_567_, 0, v_opt_560_);
lean_closure_set(v___f_567_, 1, v___y_562_);
lean_closure_set(v___f_567_, 2, v_handle_559_);
v___x_568_ = lean_string_utf8_next_fast(v_opt_560_, v___y_562_);
lean_dec(v___y_562_);
v___x_569_ = lean_string_utf8_extract(v_opt_560_, v___x_568_, v___x_563_);
lean_dec_ref(v_opt_560_);
v___f_570_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_570_, 0, v___x_569_);
v___x_571_ = lean_apply_2(v_modifyGet_566_, lean_box(0), v___f_570_);
v___x_572_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_571_, v___f_567_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
lean_dec(v___y_562_);
lean_dec_ref(v_inst_558_);
lean_dec_ref(v_inst_557_);
v___x_573_ = lean_apply_1(v_handle_559_, v_opt_560_);
return v___x_573_;
}
}
v___jp_574_:
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_string_utf8_byte_size(v_opt_560_);
v___x_577_ = lean_nat_dec_eq(v___y_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v_toBind_578_; lean_object* v_modifyGet_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_toBind_578_ = lean_ctor_get(v_inst_557_, 1);
lean_inc(v_toBind_578_);
lean_dec_ref(v_inst_557_);
v_modifyGet_579_ = lean_ctor_get(v_inst_558_, 2);
lean_inc(v_modifyGet_579_);
lean_dec_ref(v_inst_558_);
lean_inc(v_toBind_578_);
lean_inc(v_modifyGet_579_);
lean_inc(v___y_575_);
lean_inc_ref(v_opt_560_);
v___f_580_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_580_, 0, v_opt_560_);
lean_closure_set(v___f_580_, 1, v___y_575_);
lean_closure_set(v___f_580_, 2, v_handle_559_);
lean_closure_set(v___f_580_, 3, v_modifyGet_579_);
lean_closure_set(v___f_580_, 4, v_toBind_578_);
v___x_581_ = lean_string_utf8_next_fast(v_opt_560_, v___y_575_);
lean_dec(v___y_575_);
v___x_582_ = lean_string_utf8_extract(v_opt_560_, v___x_581_, v___x_576_);
lean_dec_ref(v_opt_560_);
v___f_583_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_583_, 0, v___x_582_);
v___x_584_ = lean_apply_2(v_modifyGet_579_, lean_box(0), v___f_583_);
v___x_585_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_584_, v___f_580_);
return v___x_585_;
}
else
{
lean_object* v_searcher_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___x_589_; 
lean_dec(v___y_575_);
v_searcher_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_box(0);
lean_inc_ref(v_opt_560_);
v___f_588_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_588_, 0, v___x_576_);
lean_closure_set(v___f_588_, 1, v_opt_560_);
lean_closure_set(v___f_588_, 2, v___x_587_);
v___x_589_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_588_, v_searcher_586_, v___x_587_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
v___y_562_ = v___x_576_;
goto v___jp_561_;
}
else
{
lean_object* v_val_590_; 
v_val_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v___x_589_);
v___y_562_ = v_val_590_;
goto v___jp_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object* v_m_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_00_u03b1_600_, lean_object* v_handle_601_, lean_object* v_opt_602_){
_start:
{
lean_object* v___y_604_; lean_object* v___y_617_; lean_object* v_searcher_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; 
v_searcher_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_string_utf8_byte_size(v_opt_602_);
v___x_635_ = lean_box(0);
lean_inc_ref(v_opt_602_);
v___f_636_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_636_, 0, v___x_634_);
lean_closure_set(v___f_636_, 1, v_opt_602_);
lean_closure_set(v___f_636_, 2, v___x_635_);
v___x_637_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_636_, v_searcher_633_, v___x_635_, lean_box(0));
if (lean_obj_tag(v___x_637_) == 0)
{
v___y_617_ = v___x_634_;
goto v___jp_616_;
}
else
{
lean_object* v_val_638_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref(v___x_637_);
v___y_617_ = v_val_638_;
goto v___jp_616_;
}
v___jp_603_:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_string_utf8_byte_size(v_opt_602_);
v___x_606_ = lean_nat_dec_eq(v___y_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v_toBind_607_; lean_object* v_modifyGet_608_; lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toBind_607_ = lean_ctor_get(v_inst_598_, 1);
lean_inc(v_toBind_607_);
lean_dec_ref(v_inst_598_);
v_modifyGet_608_ = lean_ctor_get(v_inst_599_, 2);
lean_inc(v_modifyGet_608_);
lean_dec_ref(v_inst_599_);
lean_inc(v___y_604_);
lean_inc_ref(v_opt_602_);
v___f_609_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_609_, 0, v_opt_602_);
lean_closure_set(v___f_609_, 1, v___y_604_);
lean_closure_set(v___f_609_, 2, v_handle_601_);
v___x_610_ = lean_string_utf8_next_fast(v_opt_602_, v___y_604_);
lean_dec(v___y_604_);
v___x_611_ = lean_string_utf8_extract(v_opt_602_, v___x_610_, v___x_605_);
lean_dec_ref(v_opt_602_);
v___f_612_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_612_, 0, v___x_611_);
v___x_613_ = lean_apply_2(v_modifyGet_608_, lean_box(0), v___f_612_);
v___x_614_ = lean_apply_4(v_toBind_607_, lean_box(0), lean_box(0), v___x_613_, v___f_609_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
lean_dec(v___y_604_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_inst_598_);
v___x_615_ = lean_apply_1(v_handle_601_, v_opt_602_);
return v___x_615_;
}
}
v___jp_616_:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_string_utf8_byte_size(v_opt_602_);
v___x_619_ = lean_nat_dec_eq(v___y_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v_toBind_620_; lean_object* v_modifyGet_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_toBind_620_ = lean_ctor_get(v_inst_598_, 1);
lean_inc(v_toBind_620_);
lean_dec_ref(v_inst_598_);
v_modifyGet_621_ = lean_ctor_get(v_inst_599_, 2);
lean_inc(v_modifyGet_621_);
lean_dec_ref(v_inst_599_);
lean_inc(v_toBind_620_);
lean_inc(v_modifyGet_621_);
lean_inc(v___y_617_);
lean_inc_ref(v_opt_602_);
v___f_622_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_622_, 0, v_opt_602_);
lean_closure_set(v___f_622_, 1, v___y_617_);
lean_closure_set(v___f_622_, 2, v_handle_601_);
lean_closure_set(v___f_622_, 3, v_modifyGet_621_);
lean_closure_set(v___f_622_, 4, v_toBind_620_);
v___x_623_ = lean_string_utf8_next_fast(v_opt_602_, v___y_617_);
lean_dec(v___y_617_);
v___x_624_ = lean_string_utf8_extract(v_opt_602_, v___x_623_, v___x_618_);
lean_dec_ref(v_opt_602_);
v___f_625_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_625_, 0, v___x_624_);
v___x_626_ = lean_apply_2(v_modifyGet_621_, lean_box(0), v___f_625_);
v___x_627_ = lean_apply_4(v_toBind_620_, lean_box(0), lean_box(0), v___x_626_, v___f_622_);
return v___x_627_;
}
else
{
lean_object* v_searcher_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
lean_dec(v___y_617_);
v_searcher_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_box(0);
lean_inc_ref(v_opt_602_);
v___f_630_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_630_, 0, v___x_618_);
lean_closure_set(v___f_630_, 1, v_opt_602_);
lean_closure_set(v___f_630_, 2, v___x_629_);
v___x_631_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_630_, v_searcher_628_, v___x_629_, lean_box(0));
if (lean_obj_tag(v___x_631_) == 0)
{
v___y_604_ = v___x_618_;
goto v___jp_603_;
}
else
{
lean_object* v_val_632_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v___x_631_);
v___y_604_ = v_val_632_;
goto v___jp_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object* v_opt_639_, lean_object* v_shortHandle_640_, lean_object* v_____r_641_){
_start:
{
lean_object* v___x_642_; uint32_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_string_utf8_get(v_opt_639_, v___x_642_);
v___x_644_ = lean_box_uint32(v___x_643_);
v___x_645_ = lean_apply_1(v_shortHandle_640_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object* v_opt_646_, lean_object* v_shortHandle_647_, lean_object* v_____r_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lake_shortOption___redArg___lam__0(v_opt_646_, v_shortHandle_647_, v_____r_648_);
lean_dec_ref(v_opt_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_shortHandle_652_, lean_object* v_longHandle_653_, lean_object* v_opt_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_string_length(v_opt_654_);
v___x_656_ = lean_unsigned_to_nat(2u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
uint32_t v___x_658_; uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_string_utf8_get(v_opt_654_, v___x_656_);
v___x_659_ = 61;
v___x_660_ = lean_uint32_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 32;
v___x_662_ = lean_uint32_dec_eq(v___x_658_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec(v_shortHandle_652_);
lean_dec_ref(v_inst_651_);
lean_dec_ref(v_inst_650_);
v___x_663_ = lean_apply_1(v_longHandle_653_, v_opt_654_);
return v___x_663_;
}
else
{
lean_object* v_toBind_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_str_673_; lean_object* v_startInclusive_674_; lean_object* v_endExclusive_675_; lean_object* v_modifyGet_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___f_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v_longHandle_653_);
v_toBind_664_ = lean_ctor_get(v_inst_650_, 1);
lean_inc(v_toBind_664_);
lean_dec_ref(v_inst_650_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_string_utf8_byte_size(v_opt_654_);
lean_inc_ref(v_opt_654_);
v___x_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_667_, 0, v_opt_654_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
lean_ctor_set(v___x_667_, 2, v___x_666_);
v___x_668_ = l_String_Slice_Pos_nextn(v___x_667_, v___x_665_, v___x_656_);
lean_dec_ref(v___x_667_);
lean_inc_ref(v_opt_654_);
v___x_669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_669_, 0, v_opt_654_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_ctor_set(v___x_669_, 2, v___x_666_);
v___x_670_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_671_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v___x_672_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_669_, v___x_670_, v___x_671_, v___x_665_);
lean_dec_ref(v___x_669_);
v_str_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_str_673_);
v_startInclusive_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_startInclusive_674_);
v_endExclusive_675_ = lean_ctor_get(v___x_672_, 2);
lean_inc(v_endExclusive_675_);
lean_dec_ref(v___x_672_);
v_modifyGet_676_ = lean_ctor_get(v_inst_651_, 2);
lean_inc(v_modifyGet_676_);
lean_dec_ref(v_inst_651_);
v___f_677_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_677_, 0, v_opt_654_);
lean_closure_set(v___f_677_, 1, v_shortHandle_652_);
v___x_678_ = lean_string_utf8_extract(v_str_673_, v_startInclusive_674_, v_endExclusive_675_);
lean_dec(v_endExclusive_675_);
lean_dec(v_startInclusive_674_);
lean_dec_ref(v_str_673_);
v___f_679_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_679_, 0, v___x_678_);
v___x_680_ = lean_apply_2(v_modifyGet_676_, lean_box(0), v___f_679_);
v___x_681_ = lean_apply_4(v_toBind_664_, lean_box(0), lean_box(0), v___x_680_, v___f_677_);
return v___x_681_;
}
}
else
{
lean_object* v_toBind_682_; lean_object* v___x_683_; lean_object* v_modifyGet_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_longHandle_653_);
v_toBind_682_ = lean_ctor_get(v_inst_650_, 1);
lean_inc(v_toBind_682_);
lean_dec_ref(v_inst_650_);
v___x_683_ = lean_string_utf8_byte_size(v_opt_654_);
v_modifyGet_684_ = lean_ctor_get(v_inst_651_, 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_inst_651_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_700_ = lean_ctor_get(v_inst_651_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_inst_651_, 0);
lean_dec(v_unused_701_);
v___x_686_ = v_inst_651_;
v_isShared_687_ = v_isSharedCheck_699_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_modifyGet_684_);
lean_dec(v_inst_651_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_699_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_654_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 2, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_688_);
lean_ctor_set(v___x_686_, 0, v_opt_654_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_opt_654_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v___x_683_);
v___x_690_ = v_reuseFailAlloc_698_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___f_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc_ref(v_opt_654_);
v___f_691_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_691_, 0, v_opt_654_);
lean_closure_set(v___f_691_, 1, v_shortHandle_652_);
v___x_692_ = lean_unsigned_to_nat(3u);
v___x_693_ = l_String_Slice_Pos_nextn(v___x_690_, v___x_688_, v___x_692_);
lean_dec_ref(v___x_690_);
v___x_694_ = lean_string_utf8_extract(v_opt_654_, v___x_693_, v___x_683_);
lean_dec(v___x_693_);
lean_dec_ref(v_opt_654_);
v___f_695_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_695_, 0, v___x_694_);
v___x_696_ = lean_apply_2(v_modifyGet_684_, lean_box(0), v___f_695_);
v___x_697_ = lean_apply_4(v_toBind_682_, lean_box(0), lean_box(0), v___x_696_, v___f_691_);
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_702_; uint32_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_longHandle_653_);
lean_dec_ref(v_inst_651_);
lean_dec_ref(v_inst_650_);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_string_utf8_get(v_opt_654_, v___x_702_);
lean_dec_ref(v_opt_654_);
v___x_704_ = lean_box_uint32(v___x_703_);
v___x_705_ = lean_apply_1(v_shortHandle_652_, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object* v_m_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_00_u03b1_709_, lean_object* v_shortHandle_710_, lean_object* v_longHandle_711_, lean_object* v_opt_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_string_length(v_opt_712_);
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = lean_nat_dec_eq(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
uint32_t v___x_716_; uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_string_utf8_get(v_opt_712_, v___x_714_);
v___x_717_ = 61;
v___x_718_ = lean_uint32_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 32;
v___x_720_ = lean_uint32_dec_eq(v___x_716_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v_shortHandle_710_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_inst_707_);
v___x_721_ = lean_apply_1(v_longHandle_711_, v_opt_712_);
return v___x_721_;
}
else
{
lean_object* v_toBind_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_str_731_; lean_object* v_startInclusive_732_; lean_object* v_endExclusive_733_; lean_object* v_modifyGet_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_longHandle_711_);
v_toBind_722_ = lean_ctor_get(v_inst_707_, 1);
lean_inc(v_toBind_722_);
lean_dec_ref(v_inst_707_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_string_utf8_byte_size(v_opt_712_);
lean_inc_ref(v_opt_712_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v_opt_712_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = l_String_Slice_Pos_nextn(v___x_725_, v___x_723_, v___x_714_);
lean_dec_ref(v___x_725_);
lean_inc_ref(v_opt_712_);
v___x_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_727_, 0, v_opt_712_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_ctor_set(v___x_727_, 2, v___x_724_);
v___x_728_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_729_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v___x_730_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_727_, v___x_728_, v___x_729_, v___x_723_);
lean_dec_ref(v___x_727_);
v_str_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_str_731_);
v_startInclusive_732_ = lean_ctor_get(v___x_730_, 1);
lean_inc(v_startInclusive_732_);
v_endExclusive_733_ = lean_ctor_get(v___x_730_, 2);
lean_inc(v_endExclusive_733_);
lean_dec_ref(v___x_730_);
v_modifyGet_734_ = lean_ctor_get(v_inst_708_, 2);
lean_inc(v_modifyGet_734_);
lean_dec_ref(v_inst_708_);
v___f_735_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_735_, 0, v_opt_712_);
lean_closure_set(v___f_735_, 1, v_shortHandle_710_);
v___x_736_ = lean_string_utf8_extract(v_str_731_, v_startInclusive_732_, v_endExclusive_733_);
lean_dec(v_endExclusive_733_);
lean_dec(v_startInclusive_732_);
lean_dec_ref(v_str_731_);
v___f_737_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_737_, 0, v___x_736_);
v___x_738_ = lean_apply_2(v_modifyGet_734_, lean_box(0), v___f_737_);
v___x_739_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_738_, v___f_735_);
return v___x_739_;
}
}
else
{
lean_object* v_toBind_740_; lean_object* v___x_741_; lean_object* v_modifyGet_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_longHandle_711_);
v_toBind_740_ = lean_ctor_get(v_inst_707_, 1);
lean_inc(v_toBind_740_);
lean_dec_ref(v_inst_707_);
v___x_741_ = lean_string_utf8_byte_size(v_opt_712_);
v_modifyGet_742_ = lean_ctor_get(v_inst_708_, 2);
v_isSharedCheck_757_ = !lean_is_exclusive(v_inst_708_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; 
v_unused_758_ = lean_ctor_get(v_inst_708_, 1);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_inst_708_, 0);
lean_dec(v_unused_759_);
v___x_744_ = v_inst_708_;
v_isShared_745_ = v_isSharedCheck_757_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_modifyGet_742_);
lean_dec(v_inst_708_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_757_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_712_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 2, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_746_);
lean_ctor_set(v___x_744_, 0, v_opt_712_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_opt_712_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v___x_741_);
v___x_748_ = v_reuseFailAlloc_756_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_inc_ref(v_opt_712_);
v___f_749_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_749_, 0, v_opt_712_);
lean_closure_set(v___f_749_, 1, v_shortHandle_710_);
v___x_750_ = lean_unsigned_to_nat(3u);
v___x_751_ = l_String_Slice_Pos_nextn(v___x_748_, v___x_746_, v___x_750_);
lean_dec_ref(v___x_748_);
v___x_752_ = lean_string_utf8_extract(v_opt_712_, v___x_751_, v___x_741_);
lean_dec(v___x_751_);
lean_dec_ref(v_opt_712_);
v___f_753_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_753_, 0, v___x_752_);
v___x_754_ = lean_apply_2(v_modifyGet_742_, lean_box(0), v___f_753_);
v___x_755_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_754_, v___f_749_);
return v___x_755_;
}
}
}
}
else
{
lean_object* v___x_760_; uint32_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec(v_longHandle_711_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_inst_707_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_string_utf8_get(v_opt_712_, v___x_760_);
lean_dec_ref(v_opt_712_);
v___x_762_ = lean_box_uint32(v___x_761_);
v___x_763_ = lean_apply_1(v_shortHandle_710_, v___x_762_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object* v_short_764_, uint32_t v___x_765_, lean_object* v_____r_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_box_uint32(v___x_765_);
v___x_768_ = lean_apply_1(v_short_764_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object* v_short_769_, lean_object* v___x_770_, lean_object* v_____r_771_){
_start:
{
uint32_t v___x_1244__boxed_772_; lean_object* v_res_773_; 
v___x_1244__boxed_772_ = lean_unbox_uint32(v___x_770_);
lean_dec(v___x_770_);
v_res_773_ = l_Lake_option___redArg___lam__0(v_short_769_, v___x_1244__boxed_772_, v_____r_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object* v_opt_774_, lean_object* v___y_775_, lean_object* v_long_776_, lean_object* v_____r_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_string_utf8_extract(v_opt_774_, v___x_778_, v___y_775_);
v___x_780_ = lean_apply_1(v_long_776_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object* v_opt_781_, lean_object* v___y_782_, lean_object* v_long_783_, lean_object* v_____r_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_option___redArg___lam__4(v_opt_781_, v___y_782_, v_long_783_, v_____r_784_);
lean_dec(v___y_782_);
lean_dec_ref(v_opt_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object* v___x_786_, lean_object* v_searcher_787_, lean_object* v___y_788_, lean_object* v_long_789_, lean_object* v_____r_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_string_utf8_extract(v___x_786_, v_searcher_787_, v___y_788_);
v___x_792_ = lean_apply_1(v_long_789_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object* v___x_793_, lean_object* v_searcher_794_, lean_object* v___y_795_, lean_object* v_long_796_, lean_object* v_____r_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_option___redArg___lam__2(v___x_793_, v_searcher_794_, v___y_795_, v_long_796_, v_____r_797_);
lean_dec(v___y_795_);
lean_dec(v_searcher_794_);
lean_dec_ref(v___x_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5(lean_object* v_opt_799_, lean_object* v___y_800_, lean_object* v_long_801_, lean_object* v_modifyGet_802_, lean_object* v_toBind_803_, lean_object* v_____r_804_){
_start:
{
lean_object* v_searcher_805_; lean_object* v___x_806_; lean_object* v___y_808_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; 
v_searcher_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_string_utf8_extract(v_opt_799_, v_searcher_805_, v___y_800_);
v___x_818_ = lean_string_utf8_byte_size(v___x_806_);
v___x_819_ = lean_box(0);
lean_inc_ref(v___x_806_);
v___f_820_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_820_, 0, v___x_818_);
lean_closure_set(v___f_820_, 1, v___x_806_);
lean_closure_set(v___f_820_, 2, v___x_819_);
v___x_821_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_820_, v_searcher_805_, v___x_819_, lean_box(0));
if (lean_obj_tag(v___x_821_) == 0)
{
v___y_808_ = v___x_818_;
goto v___jp_807_;
}
else
{
lean_object* v_val_822_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v___x_821_);
v___y_808_ = v_val_822_;
goto v___jp_807_;
}
v___jp_807_:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_string_utf8_byte_size(v___x_806_);
v___x_810_ = lean_nat_dec_eq(v___y_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc(v___y_808_);
lean_inc_ref(v___x_806_);
v___f_811_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_811_, 0, v___x_806_);
lean_closure_set(v___f_811_, 1, v_searcher_805_);
lean_closure_set(v___f_811_, 2, v___y_808_);
lean_closure_set(v___f_811_, 3, v_long_801_);
v___x_812_ = lean_string_utf8_next_fast(v___x_806_, v___y_808_);
lean_dec(v___y_808_);
v___x_813_ = lean_string_utf8_extract(v___x_806_, v___x_812_, v___x_809_);
lean_dec_ref(v___x_806_);
v___f_814_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_814_, 0, v___x_813_);
v___x_815_ = lean_apply_2(v_modifyGet_802_, lean_box(0), v___f_814_);
v___x_816_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_815_, v___f_811_);
return v___x_816_;
}
else
{
lean_object* v___x_817_; 
lean_dec(v___y_808_);
lean_dec(v_toBind_803_);
lean_dec(v_modifyGet_802_);
v___x_817_ = lean_apply_1(v_long_801_, v___x_806_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5___boxed(lean_object* v_opt_823_, lean_object* v___y_824_, lean_object* v_long_825_, lean_object* v_modifyGet_826_, lean_object* v_toBind_827_, lean_object* v_____r_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lake_option___redArg___lam__5(v_opt_823_, v___y_824_, v_long_825_, v_modifyGet_826_, v_toBind_827_, v_____r_828_);
lean_dec(v___y_824_);
lean_dec_ref(v_opt_823_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_handlers_832_, lean_object* v_opt_833_){
_start:
{
lean_object* v___x_834_; uint32_t v___x_835_; uint32_t v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_unsigned_to_nat(1u);
v___x_835_ = lean_string_utf8_get(v_opt_833_, v___x_834_);
v___x_836_ = 45;
v___x_837_ = lean_uint32_dec_eq(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v_short_838_; lean_object* v_longShort_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_896_; 
v_short_838_ = lean_ctor_get(v_handlers_832_, 1);
v_longShort_839_ = lean_ctor_get(v_handlers_832_, 2);
v_isSharedCheck_896_ = !lean_is_exclusive(v_handlers_832_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_handlers_832_, 0);
lean_dec(v_unused_897_);
v___x_841_ = v_handlers_832_;
v_isShared_842_ = v_isSharedCheck_896_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_longShort_839_);
lean_inc(v_short_838_);
lean_dec(v_handlers_832_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_896_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = lean_string_length(v_opt_833_);
v___x_844_ = lean_unsigned_to_nat(2u);
v___x_845_ = lean_nat_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
uint32_t v___x_846_; uint32_t v___x_847_; uint8_t v___x_848_; 
v___x_846_ = lean_string_utf8_get(v_opt_833_, v___x_844_);
v___x_847_ = 61;
v___x_848_ = lean_uint32_dec_eq(v___x_846_, v___x_847_);
if (v___x_848_ == 0)
{
uint32_t v___x_849_; uint8_t v___x_850_; 
v___x_849_ = 32;
v___x_850_ = lean_uint32_dec_eq(v___x_846_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_del_object(v___x_841_);
lean_dec(v_short_838_);
lean_dec_ref(v_inst_831_);
lean_dec_ref(v_inst_830_);
v___x_851_ = lean_apply_1(v_longShort_839_, v_opt_833_);
return v___x_851_;
}
else
{
lean_object* v_toBind_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_longShort_839_);
v_toBind_852_ = lean_ctor_get(v_inst_830_, 1);
lean_inc(v_toBind_852_);
lean_dec_ref(v_inst_830_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_string_utf8_byte_size(v_opt_833_);
lean_inc_ref(v_opt_833_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 2, v___x_854_);
lean_ctor_set(v___x_841_, 1, v___x_853_);
lean_ctor_set(v___x_841_, 0, v_opt_833_);
v___x_856_ = v___x_841_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_opt_833_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v___x_854_);
v___x_856_ = v_reuseFailAlloc_872_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_str_862_; lean_object* v_startInclusive_863_; lean_object* v_endExclusive_864_; lean_object* v_modifyGet_865_; lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_857_ = l_String_Slice_Pos_nextn(v___x_856_, v___x_853_, v___x_844_);
lean_dec_ref(v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v_opt_833_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
lean_ctor_set(v___x_858_, 2, v___x_854_);
v___x_859_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_860_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v___x_861_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_858_, v___x_859_, v___x_860_, v___x_853_);
lean_dec_ref(v___x_858_);
v_str_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_str_862_);
v_startInclusive_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_startInclusive_863_);
v_endExclusive_864_ = lean_ctor_get(v___x_861_, 2);
lean_inc(v_endExclusive_864_);
lean_dec_ref(v___x_861_);
v_modifyGet_865_ = lean_ctor_get(v_inst_831_, 2);
lean_inc(v_modifyGet_865_);
lean_dec_ref(v_inst_831_);
v___x_866_ = lean_box_uint32(v___x_835_);
v___f_867_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_867_, 0, v_short_838_);
lean_closure_set(v___f_867_, 1, v___x_866_);
v___x_868_ = lean_string_utf8_extract(v_str_862_, v_startInclusive_863_, v_endExclusive_864_);
lean_dec(v_endExclusive_864_);
lean_dec(v_startInclusive_863_);
lean_dec_ref(v_str_862_);
v___f_869_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_869_, 0, v___x_868_);
v___x_870_ = lean_apply_2(v_modifyGet_865_, lean_box(0), v___f_869_);
v___x_871_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v___x_870_, v___f_867_);
return v___x_871_;
}
}
}
else
{
lean_object* v_toBind_873_; lean_object* v___x_874_; lean_object* v_modifyGet_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_841_);
lean_dec(v_longShort_839_);
v_toBind_873_ = lean_ctor_get(v_inst_830_, 1);
lean_inc(v_toBind_873_);
lean_dec_ref(v_inst_830_);
v___x_874_ = lean_string_utf8_byte_size(v_opt_833_);
v_modifyGet_875_ = lean_ctor_get(v_inst_831_, 2);
v_isSharedCheck_891_ = !lean_is_exclusive(v_inst_831_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_892_ = lean_ctor_get(v_inst_831_, 1);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_inst_831_, 0);
lean_dec(v_unused_893_);
v___x_877_ = v_inst_831_;
v_isShared_878_ = v_isSharedCheck_891_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_modifyGet_875_);
lean_dec(v_inst_831_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_891_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_833_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 2, v___x_874_);
lean_ctor_set(v___x_877_, 1, v___x_879_);
lean_ctor_set(v___x_877_, 0, v_opt_833_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_opt_833_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v___x_874_);
v___x_881_ = v_reuseFailAlloc_890_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_882_ = lean_box_uint32(v___x_835_);
v___f_883_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_883_, 0, v_short_838_);
lean_closure_set(v___f_883_, 1, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(3u);
v___x_885_ = l_String_Slice_Pos_nextn(v___x_881_, v___x_879_, v___x_884_);
lean_dec_ref(v___x_881_);
v___x_886_ = lean_string_utf8_extract(v_opt_833_, v___x_885_, v___x_874_);
lean_dec(v___x_885_);
lean_dec_ref(v_opt_833_);
v___f_887_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_887_, 0, v___x_886_);
v___x_888_ = lean_apply_2(v_modifyGet_875_, lean_box(0), v___f_887_);
v___x_889_ = lean_apply_4(v_toBind_873_, lean_box(0), lean_box(0), v___x_888_, v___f_883_);
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_841_);
lean_dec(v_longShort_839_);
lean_dec_ref(v_opt_833_);
lean_dec_ref(v_inst_831_);
lean_dec_ref(v_inst_830_);
v___x_894_ = lean_box_uint32(v___x_835_);
v___x_895_ = lean_apply_1(v_short_838_, v___x_894_);
return v___x_895_;
}
}
}
else
{
lean_object* v_long_898_; lean_object* v___y_900_; lean_object* v___y_913_; lean_object* v_searcher_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___f_932_; lean_object* v___x_933_; 
v_long_898_ = lean_ctor_get(v_handlers_832_, 0);
lean_inc(v_long_898_);
lean_dec_ref(v_handlers_832_);
v_searcher_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_string_utf8_byte_size(v_opt_833_);
v___x_931_ = lean_box(0);
lean_inc_ref(v_opt_833_);
v___f_932_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_932_, 0, v___x_930_);
lean_closure_set(v___f_932_, 1, v_opt_833_);
lean_closure_set(v___f_932_, 2, v___x_931_);
v___x_933_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_932_, v_searcher_929_, v___x_931_, lean_box(0));
if (lean_obj_tag(v___x_933_) == 0)
{
v___y_913_ = v___x_930_;
goto v___jp_912_;
}
else
{
lean_object* v_val_934_; 
v_val_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_val_934_);
lean_dec_ref(v___x_933_);
v___y_913_ = v_val_934_;
goto v___jp_912_;
}
v___jp_899_:
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_string_utf8_byte_size(v_opt_833_);
v___x_902_ = lean_nat_dec_eq(v___y_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v_toBind_903_; lean_object* v_modifyGet_904_; lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_toBind_903_ = lean_ctor_get(v_inst_830_, 1);
lean_inc(v_toBind_903_);
lean_dec_ref(v_inst_830_);
v_modifyGet_904_ = lean_ctor_get(v_inst_831_, 2);
lean_inc(v_modifyGet_904_);
lean_dec_ref(v_inst_831_);
lean_inc(v___y_900_);
lean_inc_ref(v_opt_833_);
v___f_905_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_905_, 0, v_opt_833_);
lean_closure_set(v___f_905_, 1, v___y_900_);
lean_closure_set(v___f_905_, 2, v_long_898_);
v___x_906_ = lean_string_utf8_next_fast(v_opt_833_, v___y_900_);
lean_dec(v___y_900_);
v___x_907_ = lean_string_utf8_extract(v_opt_833_, v___x_906_, v___x_901_);
lean_dec_ref(v_opt_833_);
v___f_908_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_908_, 0, v___x_907_);
v___x_909_ = lean_apply_2(v_modifyGet_904_, lean_box(0), v___f_908_);
v___x_910_ = lean_apply_4(v_toBind_903_, lean_box(0), lean_box(0), v___x_909_, v___f_905_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; 
lean_dec(v___y_900_);
lean_dec_ref(v_inst_831_);
lean_dec_ref(v_inst_830_);
v___x_911_ = lean_apply_1(v_long_898_, v_opt_833_);
return v___x_911_;
}
}
v___jp_912_:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_string_utf8_byte_size(v_opt_833_);
v___x_915_ = lean_nat_dec_eq(v___y_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v_toBind_916_; lean_object* v_modifyGet_917_; lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_toBind_916_ = lean_ctor_get(v_inst_830_, 1);
lean_inc(v_toBind_916_);
lean_dec_ref(v_inst_830_);
v_modifyGet_917_ = lean_ctor_get(v_inst_831_, 2);
lean_inc(v_modifyGet_917_);
lean_dec_ref(v_inst_831_);
lean_inc(v_toBind_916_);
lean_inc(v_modifyGet_917_);
lean_inc(v___y_913_);
lean_inc_ref(v_opt_833_);
v___f_918_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_918_, 0, v_opt_833_);
lean_closure_set(v___f_918_, 1, v___y_913_);
lean_closure_set(v___f_918_, 2, v_long_898_);
lean_closure_set(v___f_918_, 3, v_modifyGet_917_);
lean_closure_set(v___f_918_, 4, v_toBind_916_);
v___x_919_ = lean_string_utf8_next_fast(v_opt_833_, v___y_913_);
lean_dec(v___y_913_);
v___x_920_ = lean_string_utf8_extract(v_opt_833_, v___x_919_, v___x_914_);
lean_dec_ref(v_opt_833_);
v___f_921_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_921_, 0, v___x_920_);
v___x_922_ = lean_apply_2(v_modifyGet_917_, lean_box(0), v___f_921_);
v___x_923_ = lean_apply_4(v_toBind_916_, lean_box(0), lean_box(0), v___x_922_, v___f_918_);
return v___x_923_;
}
else
{
lean_object* v_searcher_924_; lean_object* v___x_925_; lean_object* v___f_926_; lean_object* v___x_927_; 
lean_dec(v___y_913_);
v_searcher_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_box(0);
lean_inc_ref(v_opt_833_);
v___f_926_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_926_, 0, v___x_914_);
lean_closure_set(v___f_926_, 1, v_opt_833_);
lean_closure_set(v___f_926_, 2, v___x_925_);
v___x_927_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_926_, v_searcher_924_, v___x_925_, lean_box(0));
if (lean_obj_tag(v___x_927_) == 0)
{
v___y_900_ = v___x_914_;
goto v___jp_899_;
}
else
{
lean_object* v_val_928_; 
v_val_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_val_928_);
lean_dec_ref(v___x_927_);
v___y_900_ = v_val_928_;
goto v___jp_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option(lean_object* v_m_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_00_u03b1_938_, lean_object* v_handlers_939_, lean_object* v_opt_940_){
_start:
{
lean_object* v___x_941_; uint32_t v___x_942_; uint32_t v___x_943_; uint8_t v___x_944_; 
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_string_utf8_get(v_opt_940_, v___x_941_);
v___x_943_ = 45;
v___x_944_ = lean_uint32_dec_eq(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v_short_945_; lean_object* v_longShort_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1003_; 
v_short_945_ = lean_ctor_get(v_handlers_939_, 1);
v_longShort_946_ = lean_ctor_get(v_handlers_939_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_handlers_939_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_handlers_939_, 0);
lean_dec(v_unused_1004_);
v___x_948_ = v_handlers_939_;
v_isShared_949_ = v_isSharedCheck_1003_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_longShort_946_);
lean_inc(v_short_945_);
lean_dec(v_handlers_939_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1003_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_string_length(v_opt_940_);
v___x_951_ = lean_unsigned_to_nat(2u);
v___x_952_ = lean_nat_dec_eq(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
uint32_t v___x_953_; uint32_t v___x_954_; uint8_t v___x_955_; 
v___x_953_ = lean_string_utf8_get(v_opt_940_, v___x_951_);
v___x_954_ = 61;
v___x_955_ = lean_uint32_dec_eq(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
uint32_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = 32;
v___x_957_ = lean_uint32_dec_eq(v___x_953_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_del_object(v___x_948_);
lean_dec(v_short_945_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
v___x_958_ = lean_apply_1(v_longShort_946_, v_opt_940_);
return v___x_958_;
}
else
{
lean_object* v_toBind_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v_longShort_946_);
v_toBind_959_ = lean_ctor_get(v_inst_936_, 1);
lean_inc(v_toBind_959_);
lean_dec_ref(v_inst_936_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_string_utf8_byte_size(v_opt_940_);
lean_inc_ref(v_opt_940_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v___x_961_);
lean_ctor_set(v___x_948_, 1, v___x_960_);
lean_ctor_set(v___x_948_, 0, v_opt_940_);
v___x_963_ = v___x_948_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_opt_940_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v___x_961_);
v___x_963_ = v_reuseFailAlloc_979_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_str_969_; lean_object* v_startInclusive_970_; lean_object* v_endExclusive_971_; lean_object* v_modifyGet_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_964_ = l_String_Slice_Pos_nextn(v___x_963_, v___x_960_, v___x_951_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_965_, 0, v_opt_940_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
lean_ctor_set(v___x_965_, 2, v___x_961_);
v___x_966_ = ((lean_object*)(l_Lake_shortOptionWithSpace___redArg___closed__0));
v___x_967_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v___x_968_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_965_, v___x_966_, v___x_967_, v___x_960_);
lean_dec_ref(v___x_965_);
v_str_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc_ref(v_str_969_);
v_startInclusive_970_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_startInclusive_970_);
v_endExclusive_971_ = lean_ctor_get(v___x_968_, 2);
lean_inc(v_endExclusive_971_);
lean_dec_ref(v___x_968_);
v_modifyGet_972_ = lean_ctor_get(v_inst_937_, 2);
lean_inc(v_modifyGet_972_);
lean_dec_ref(v_inst_937_);
v___x_973_ = lean_box_uint32(v___x_942_);
v___f_974_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_974_, 0, v_short_945_);
lean_closure_set(v___f_974_, 1, v___x_973_);
v___x_975_ = lean_string_utf8_extract(v_str_969_, v_startInclusive_970_, v_endExclusive_971_);
lean_dec(v_endExclusive_971_);
lean_dec(v_startInclusive_970_);
lean_dec_ref(v_str_969_);
v___f_976_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_976_, 0, v___x_975_);
v___x_977_ = lean_apply_2(v_modifyGet_972_, lean_box(0), v___f_976_);
v___x_978_ = lean_apply_4(v_toBind_959_, lean_box(0), lean_box(0), v___x_977_, v___f_974_);
return v___x_978_;
}
}
}
else
{
lean_object* v_toBind_980_; lean_object* v___x_981_; lean_object* v_modifyGet_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_948_);
lean_dec(v_longShort_946_);
v_toBind_980_ = lean_ctor_get(v_inst_936_, 1);
lean_inc(v_toBind_980_);
lean_dec_ref(v_inst_936_);
v___x_981_ = lean_string_utf8_byte_size(v_opt_940_);
v_modifyGet_982_ = lean_ctor_get(v_inst_937_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_inst_937_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_999_ = lean_ctor_get(v_inst_937_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_inst_937_, 0);
lean_dec(v_unused_1000_);
v___x_984_ = v_inst_937_;
v_isShared_985_ = v_isSharedCheck_998_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_modifyGet_982_);
lean_dec(v_inst_937_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_998_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_940_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 2, v___x_981_);
lean_ctor_set(v___x_984_, 1, v___x_986_);
lean_ctor_set(v___x_984_, 0, v_opt_940_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_opt_940_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_981_);
v___x_988_ = v_reuseFailAlloc_997_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___f_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_989_ = lean_box_uint32(v___x_942_);
v___f_990_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_990_, 0, v_short_945_);
lean_closure_set(v___f_990_, 1, v___x_989_);
v___x_991_ = lean_unsigned_to_nat(3u);
v___x_992_ = l_String_Slice_Pos_nextn(v___x_988_, v___x_986_, v___x_991_);
lean_dec_ref(v___x_988_);
v___x_993_ = lean_string_utf8_extract(v_opt_940_, v___x_992_, v___x_981_);
lean_dec(v___x_992_);
lean_dec_ref(v_opt_940_);
v___f_994_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_994_, 0, v___x_993_);
v___x_995_ = lean_apply_2(v_modifyGet_982_, lean_box(0), v___f_994_);
v___x_996_ = lean_apply_4(v_toBind_980_, lean_box(0), lean_box(0), v___x_995_, v___f_990_);
return v___x_996_;
}
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_948_);
lean_dec(v_longShort_946_);
lean_dec_ref(v_opt_940_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
v___x_1001_ = lean_box_uint32(v___x_942_);
v___x_1002_ = lean_apply_1(v_short_945_, v___x_1001_);
return v___x_1002_;
}
}
}
else
{
lean_object* v_long_1005_; lean_object* v___y_1007_; lean_object* v___y_1020_; lean_object* v_searcher_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; 
v_long_1005_ = lean_ctor_get(v_handlers_939_, 0);
lean_inc(v_long_1005_);
lean_dec_ref(v_handlers_939_);
v_searcher_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_string_utf8_byte_size(v_opt_940_);
v___x_1038_ = lean_box(0);
lean_inc_ref(v_opt_940_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1039_, 0, v___x_1037_);
lean_closure_set(v___f_1039_, 1, v_opt_940_);
lean_closure_set(v___f_1039_, 2, v___x_1038_);
v___x_1040_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1039_, v_searcher_1036_, v___x_1038_, lean_box(0));
if (lean_obj_tag(v___x_1040_) == 0)
{
v___y_1020_ = v___x_1037_;
goto v___jp_1019_;
}
else
{
lean_object* v_val_1041_; 
v_val_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_val_1041_);
lean_dec_ref(v___x_1040_);
v___y_1020_ = v_val_1041_;
goto v___jp_1019_;
}
v___jp_1006_:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_string_utf8_byte_size(v_opt_940_);
v___x_1009_ = lean_nat_dec_eq(v___y_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v_toBind_1010_; lean_object* v_modifyGet_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_toBind_1010_ = lean_ctor_get(v_inst_936_, 1);
lean_inc(v_toBind_1010_);
lean_dec_ref(v_inst_936_);
v_modifyGet_1011_ = lean_ctor_get(v_inst_937_, 2);
lean_inc(v_modifyGet_1011_);
lean_dec_ref(v_inst_937_);
lean_inc(v___y_1007_);
lean_inc_ref(v_opt_940_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_1012_, 0, v_opt_940_);
lean_closure_set(v___f_1012_, 1, v___y_1007_);
lean_closure_set(v___f_1012_, 2, v_long_1005_);
v___x_1013_ = lean_string_utf8_next_fast(v_opt_940_, v___y_1007_);
lean_dec(v___y_1007_);
v___x_1014_ = lean_string_utf8_extract(v_opt_940_, v___x_1013_, v___x_1008_);
lean_dec_ref(v_opt_940_);
v___f_1015_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1015_, 0, v___x_1014_);
v___x_1016_ = lean_apply_2(v_modifyGet_1011_, lean_box(0), v___f_1015_);
v___x_1017_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v___x_1016_, v___f_1012_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; 
lean_dec(v___y_1007_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
v___x_1018_ = lean_apply_1(v_long_1005_, v_opt_940_);
return v___x_1018_;
}
}
v___jp_1019_:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_string_utf8_byte_size(v_opt_940_);
v___x_1022_ = lean_nat_dec_eq(v___y_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v_toBind_1023_; lean_object* v_modifyGet_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_toBind_1023_ = lean_ctor_get(v_inst_936_, 1);
lean_inc(v_toBind_1023_);
lean_dec_ref(v_inst_936_);
v_modifyGet_1024_ = lean_ctor_get(v_inst_937_, 2);
lean_inc(v_modifyGet_1024_);
lean_dec_ref(v_inst_937_);
lean_inc(v_toBind_1023_);
lean_inc(v_modifyGet_1024_);
lean_inc(v___y_1020_);
lean_inc_ref(v_opt_940_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1025_, 0, v_opt_940_);
lean_closure_set(v___f_1025_, 1, v___y_1020_);
lean_closure_set(v___f_1025_, 2, v_long_1005_);
lean_closure_set(v___f_1025_, 3, v_modifyGet_1024_);
lean_closure_set(v___f_1025_, 4, v_toBind_1023_);
v___x_1026_ = lean_string_utf8_next_fast(v_opt_940_, v___y_1020_);
lean_dec(v___y_1020_);
v___x_1027_ = lean_string_utf8_extract(v_opt_940_, v___x_1026_, v___x_1021_);
lean_dec_ref(v_opt_940_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
v___x_1029_ = lean_apply_2(v_modifyGet_1024_, lean_box(0), v___f_1028_);
v___x_1030_ = lean_apply_4(v_toBind_1023_, lean_box(0), lean_box(0), v___x_1029_, v___f_1025_);
return v___x_1030_;
}
else
{
lean_object* v_searcher_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
lean_dec(v___y_1020_);
v_searcher_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_box(0);
lean_inc_ref(v_opt_940_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1033_, 0, v___x_1021_);
lean_closure_set(v___f_1033_, 1, v_opt_940_);
lean_closure_set(v___f_1033_, 2, v___x_1032_);
v___x_1034_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1033_, v_searcher_1031_, v___x_1032_, lean_box(0));
if (lean_obj_tag(v___x_1034_) == 0)
{
v___y_1007_ = v___x_1021_;
goto v___jp_1006_;
}
else
{
lean_object* v_val_1035_; 
v_val_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_val_1035_);
lean_dec_ref(v___x_1034_);
v___y_1007_ = v_val_1035_;
goto v___jp_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object* v_handle_1042_, lean_object* v_head_1043_, lean_object* v_____r_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_apply_1(v_handle_1042_, v_head_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object* v_toPure_1046_, lean_object* v_handle_1047_, lean_object* v_set_1048_, lean_object* v_toBind_1049_, lean_object* v_____do__lift_1050_){
_start:
{
if (lean_obj_tag(v_____do__lift_1050_) == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec(v_toBind_1049_);
lean_dec(v_set_1048_);
lean_dec(v_handle_1047_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_apply_2(v_toPure_1046_, lean_box(0), v___x_1051_);
return v___x_1052_;
}
else
{
lean_object* v_head_1053_; lean_object* v_tail_1054_; lean_object* v___f_1055_; uint8_t v___y_1057_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_head_1053_ = lean_ctor_get(v_____do__lift_1050_, 0);
lean_inc(v_head_1053_);
v_tail_1054_ = lean_ctor_get(v_____do__lift_1050_, 1);
lean_inc(v_tail_1054_);
lean_dec_ref(v_____do__lift_1050_);
lean_inc(v_head_1053_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1055_, 0, v_handle_1047_);
lean_closure_set(v___f_1055_, 1, v_head_1053_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_string_length(v_head_1053_);
v___x_1064_ = lean_nat_dec_lt(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_dec(v_head_1053_);
v___y_1057_ = v___x_1064_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1065_; uint32_t v___x_1066_; uint32_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_string_utf8_get(v_head_1053_, v___x_1065_);
lean_dec(v_head_1053_);
v___x_1067_ = 45;
v___x_1068_ = lean_uint32_dec_eq(v___x_1066_, v___x_1067_);
v___y_1057_ = v___x_1068_;
goto v___jp_1056_;
}
v___jp_1056_:
{
if (v___y_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v___f_1055_);
lean_dec(v_tail_1054_);
lean_dec(v_toBind_1049_);
lean_dec(v_set_1048_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_apply_2(v_toPure_1046_, lean_box(0), v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec(v_toPure_1046_);
v___x_1060_ = lean_apply_1(v_set_1048_, v_tail_1054_);
v___x_1061_ = lean_apply_4(v_toBind_1049_, lean_box(0), lean_box(0), v___x_1060_, v___f_1055_);
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_handle_1071_){
_start:
{
lean_object* v_toApplicative_1072_; lean_object* v_toBind_1073_; lean_object* v_get_1074_; lean_object* v_set_1075_; lean_object* v_toPure_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
v_toApplicative_1072_ = lean_ctor_get(v_inst_1069_, 0);
lean_inc_ref(v_toApplicative_1072_);
v_toBind_1073_ = lean_ctor_get(v_inst_1069_, 1);
lean_inc(v_toBind_1073_);
lean_dec_ref(v_inst_1069_);
v_get_1074_ = lean_ctor_get(v_inst_1070_, 0);
lean_inc(v_get_1074_);
v_set_1075_ = lean_ctor_get(v_inst_1070_, 1);
lean_inc(v_set_1075_);
lean_dec_ref(v_inst_1070_);
v_toPure_1076_ = lean_ctor_get(v_toApplicative_1072_, 1);
lean_inc(v_toPure_1076_);
lean_dec_ref(v_toApplicative_1072_);
lean_inc(v_toBind_1073_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1077_, 0, v_toPure_1076_);
lean_closure_set(v___f_1077_, 1, v_handle_1071_);
lean_closure_set(v___f_1077_, 2, v_set_1075_);
lean_closure_set(v___f_1077_, 3, v_toBind_1073_);
v___x_1078_ = lean_apply_4(v_toBind_1073_, lean_box(0), lean_box(0), v_get_1074_, v___f_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object* v_m_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_handle_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lake_processLeadingOption___redArg(v_inst_1080_, v_inst_1081_, v_handle_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object* v_handle_1084_, lean_object* v_head_1085_, lean_object* v_toBind_1086_, lean_object* v___f_1087_, lean_object* v_____r_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_apply_1(v_handle_1084_, v_head_1085_);
v___x_1090_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v___x_1089_, v___f_1087_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object* v_handle_1091_, lean_object* v_toBind_1092_, lean_object* v___f_1093_, lean_object* v_toPure_1094_, lean_object* v_set_1095_, lean_object* v___f_1096_, lean_object* v_____do__lift_1097_){
_start:
{
if (lean_obj_tag(v_____do__lift_1097_) == 1)
{
lean_object* v_head_1098_; lean_object* v_tail_1099_; lean_object* v___f_1100_; lean_object* v_len_1101_; uint8_t v___y_1103_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_head_1098_ = lean_ctor_get(v_____do__lift_1097_, 0);
lean_inc(v_head_1098_);
v_tail_1099_ = lean_ctor_get(v_____do__lift_1097_, 1);
lean_inc(v_tail_1099_);
lean_dec_ref(v_____do__lift_1097_);
lean_inc(v_toBind_1092_);
lean_inc(v_head_1098_);
v___f_1100_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1100_, 0, v_handle_1091_);
lean_closure_set(v___f_1100_, 1, v_head_1098_);
lean_closure_set(v___f_1100_, 2, v_toBind_1092_);
lean_closure_set(v___f_1100_, 3, v___f_1093_);
v_len_1101_ = lean_string_length(v_head_1098_);
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_dec_lt(v___x_1112_, v_len_1101_);
if (v___x_1113_ == 0)
{
lean_dec(v_head_1098_);
v___y_1103_ = v___x_1113_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1114_; uint32_t v___x_1115_; uint32_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_string_utf8_get(v_head_1098_, v___x_1114_);
lean_dec(v_head_1098_);
v___x_1116_ = 45;
v___x_1117_ = lean_uint32_dec_eq(v___x_1115_, v___x_1116_);
v___y_1103_ = v___x_1117_;
goto v___jp_1102_;
}
v___jp_1102_:
{
if (v___y_1103_ == 0)
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
lean_dec_ref(v___f_1100_);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_nat_dec_eq(v_len_1101_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec(v_tail_1099_);
lean_dec(v___f_1096_);
lean_dec(v_set_1095_);
lean_dec(v_toBind_1092_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_apply_2(v_toPure_1094_, lean_box(0), v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec(v_toPure_1094_);
v___x_1108_ = lean_apply_1(v_set_1095_, v_tail_1099_);
v___x_1109_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1108_, v___f_1096_);
return v___x_1109_;
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v___f_1096_);
lean_dec(v_toPure_1094_);
v___x_1110_ = lean_apply_1(v_set_1095_, v_tail_1099_);
v___x_1111_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1110_, v___f_1100_);
return v___x_1111_;
}
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v_____do__lift_1097_);
lean_dec(v___f_1096_);
lean_dec(v_set_1095_);
lean_dec(v___f_1093_);
lean_dec(v_toBind_1092_);
lean_dec(v_handle_1091_);
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_apply_2(v_toPure_1094_, lean_box(0), v___x_1118_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_handle_1122_){
_start:
{
lean_object* v_toApplicative_1123_; lean_object* v_toBind_1124_; lean_object* v_get_1125_; lean_object* v_set_1126_; lean_object* v_toPure_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v_toApplicative_1123_ = lean_ctor_get(v_inst_1120_, 0);
v_toBind_1124_ = lean_ctor_get(v_inst_1120_, 1);
lean_inc(v_toBind_1124_);
v_get_1125_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc(v_get_1125_);
v_set_1126_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc(v_set_1126_);
v_toPure_1127_ = lean_ctor_get(v_toApplicative_1123_, 1);
lean_inc(v_toPure_1127_);
lean_inc(v_handle_1122_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1128_, 0, v_inst_1120_);
lean_closure_set(v___f_1128_, 1, v_inst_1121_);
lean_closure_set(v___f_1128_, 2, v_handle_1122_);
lean_inc_ref(v___f_1128_);
lean_inc(v_toBind_1124_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1129_, 0, v_handle_1122_);
lean_closure_set(v___f_1129_, 1, v_toBind_1124_);
lean_closure_set(v___f_1129_, 2, v___f_1128_);
lean_closure_set(v___f_1129_, 3, v_toPure_1127_);
lean_closure_set(v___f_1129_, 4, v_set_1126_);
lean_closure_set(v___f_1129_, 5, v___f_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1124_, lean_box(0), lean_box(0), v_get_1125_, v___f_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_handle_1133_, lean_object* v_____r_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lake_processLeadingOptions___redArg(v_inst_1131_, v_inst_1132_, v_handle_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_handle_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lake_processLeadingOptions___redArg(v_inst_1137_, v_inst_1138_, v_handle_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_x_1141_);
return v___x_1143_;
}
else
{
lean_object* v_head_1144_; lean_object* v_tail_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v_head_1144_ = lean_ctor_get(v_x_1141_, 0);
v_tail_1145_ = lean_ctor_get(v_x_1141_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v_x_1141_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_tail_1145_);
lean_inc(v_head_1144_);
lean_dec(v_x_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_head_1144_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_tail_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object* v_args_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_option_1158_, lean_object* v_toBind_1159_, lean_object* v___f_1160_, lean_object* v_toPure_1161_, lean_object* v_____do__lift_1162_){
_start:
{
if (lean_obj_tag(v_____do__lift_1162_) == 1)
{
lean_object* v_val_1163_; lean_object* v_len_1164_; uint8_t v___y_1166_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
lean_dec(v_toPure_1161_);
v_val_1163_ = lean_ctor_get(v_____do__lift_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref(v_____do__lift_1162_);
v_len_1164_ = lean_string_length(v_val_1163_);
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_dec_lt(v___x_1174_, v_len_1164_);
if (v___x_1175_ == 0)
{
v___y_1166_ = v___x_1175_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1176_; uint32_t v___x_1177_; uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_string_utf8_get(v_val_1163_, v___x_1176_);
v___x_1178_ = 45;
v___x_1179_ = lean_uint32_dec_eq(v___x_1177_, v___x_1178_);
v___y_1166_ = v___x_1179_;
goto v___jp_1165_;
}
v___jp_1165_:
{
if (v___y_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
lean_dec(v___f_1160_);
lean_dec(v_toBind_1159_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_nat_dec_eq(v_len_1164_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_array_push(v_args_1155_, v_val_1163_);
v___x_1170_ = l_Lake_collectArgs___redArg(v_inst_1156_, v_inst_1157_, v_option_1158_, v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_val_1163_);
v___x_1171_ = l_Lake_collectArgs___redArg(v_inst_1156_, v_inst_1157_, v_option_1158_, v_args_1155_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v_inst_1157_);
lean_dec_ref(v_inst_1156_);
lean_dec_ref(v_args_1155_);
v___x_1172_ = lean_apply_1(v_option_1158_, v_val_1163_);
v___x_1173_ = lean_apply_4(v_toBind_1159_, lean_box(0), lean_box(0), v___x_1172_, v___f_1160_);
return v___x_1173_;
}
}
}
else
{
lean_object* v___x_1180_; 
lean_dec(v_____do__lift_1162_);
lean_dec(v___f_1160_);
lean_dec(v_toBind_1159_);
lean_dec(v_option_1158_);
lean_dec_ref(v_inst_1157_);
lean_dec_ref(v_inst_1156_);
v___x_1180_ = lean_apply_2(v_toPure_1161_, lean_box(0), v_args_1155_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_option_1183_, lean_object* v_args_1184_){
_start:
{
lean_object* v_toApplicative_1185_; lean_object* v_toBind_1186_; lean_object* v_modifyGet_1187_; lean_object* v_toPure_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; 
v_toApplicative_1185_ = lean_ctor_get(v_inst_1181_, 0);
v_toBind_1186_ = lean_ctor_get(v_inst_1181_, 1);
lean_inc(v_toBind_1186_);
v_modifyGet_1187_ = lean_ctor_get(v_inst_1182_, 2);
v_toPure_1188_ = lean_ctor_get(v_toApplicative_1185_, 1);
lean_inc(v_toPure_1188_);
v___f_1189_ = ((lean_object*)(l_Lake_collectArgs___redArg___closed__0));
lean_inc_ref(v_args_1184_);
lean_inc(v_option_1183_);
lean_inc_ref(v_inst_1182_);
lean_inc_ref(v_inst_1181_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1190_, 0, v_inst_1181_);
lean_closure_set(v___f_1190_, 1, v_inst_1182_);
lean_closure_set(v___f_1190_, 2, v_option_1183_);
lean_closure_set(v___f_1190_, 3, v_args_1184_);
lean_inc(v_modifyGet_1187_);
v___x_1191_ = lean_apply_2(v_modifyGet_1187_, lean_box(0), v___f_1189_);
lean_inc(v_toBind_1186_);
v___f_1192_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1192_, 0, v_args_1184_);
lean_closure_set(v___f_1192_, 1, v_inst_1181_);
lean_closure_set(v___f_1192_, 2, v_inst_1182_);
lean_closure_set(v___f_1192_, 3, v_option_1183_);
lean_closure_set(v___f_1192_, 4, v_toBind_1186_);
lean_closure_set(v___f_1192_, 5, v___f_1190_);
lean_closure_set(v___f_1192_, 6, v_toPure_1188_);
v___x_1193_ = lean_apply_4(v_toBind_1186_, lean_box(0), lean_box(0), v___x_1191_, v___f_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_option_1196_, lean_object* v_args_1197_, lean_object* v_____r_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lake_collectArgs___redArg(v_inst_1194_, v_inst_1195_, v_option_1196_, v_args_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object* v_m_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_option_1203_, lean_object* v_args_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lake_collectArgs___redArg(v_inst_1201_, v_inst_1202_, v_option_1203_, v_args_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object* v_inst_1206_, lean_object* v_____do__lift_1207_){
_start:
{
lean_object* v_set_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_set_1208_ = lean_ctor_get(v_inst_1206_, 1);
lean_inc(v_set_1208_);
lean_dec_ref(v_inst_1206_);
v___x_1209_ = lean_array_to_list(v_____do__lift_1207_);
v___x_1210_ = lean_apply_1(v_set_1208_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_handle_1215_){
_start:
{
lean_object* v_toBind_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_toBind_1216_ = lean_ctor_get(v_inst_1213_, 1);
lean_inc(v_toBind_1216_);
lean_inc_ref(v_inst_1214_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1217_, 0, v_inst_1214_);
v___x_1218_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1219_ = l_Lake_collectArgs___redArg(v_inst_1213_, v_inst_1214_, v_handle_1215_, v___x_1218_);
v___x_1220_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v___x_1219_, v___f_1217_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object* v_m_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_handle_1224_){
_start:
{
lean_object* v_toBind_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_toBind_1225_ = lean_ctor_get(v_inst_1222_, 1);
lean_inc(v_toBind_1225_);
lean_inc_ref(v_inst_1223_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1226_, 0, v_inst_1223_);
v___x_1227_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1228_ = l_Lake_collectArgs___redArg(v_inst_1222_, v_inst_1223_, v_handle_1224_, v___x_1227_);
v___x_1229_ = lean_apply_4(v_toBind_1225_, lean_box(0), lean_box(0), v___x_1228_, v___f_1226_);
return v___x_1229_;
}
}
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
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
