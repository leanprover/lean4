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
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_dec_ref(v___x_203_);
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
lean_dec_ref(v___x_233_);
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
lean_dec_ref(v___x_404_);
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
lean_dec_ref(v___x_429_);
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
lean_dec_ref(v___x_474_);
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
lean_dec_ref(v___x_499_);
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
lean_dec_ref(v___x_558_);
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
lean_dec_ref(v___x_605_);
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
lean_dec_ref(v___x_599_);
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
lean_dec_ref(v___x_647_);
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
lean_dec_ref(v___x_641_);
v___y_614_ = v_val_642_;
goto v___jp_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object* v_opt_649_, lean_object* v_shortHandle_650_, lean_object* v_____r_651_){
_start:
{
lean_object* v___x_652_; uint32_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_string_utf8_get(v_opt_649_, v___x_652_);
v___x_654_ = lean_box_uint32(v___x_653_);
v___x_655_ = lean_apply_1(v_shortHandle_650_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object* v_opt_656_, lean_object* v_shortHandle_657_, lean_object* v_____r_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_shortOption___redArg___lam__0(v_opt_656_, v_shortHandle_657_, v_____r_658_);
lean_dec_ref(v_opt_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_shortHandle_662_, lean_object* v_longHandle_663_, lean_object* v_opt_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_string_length(v_opt_664_);
v___x_666_ = lean_unsigned_to_nat(2u);
v___x_667_ = lean_nat_dec_eq(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint32_t v___x_669_; uint8_t v___x_670_; 
v___x_668_ = lean_string_utf8_get(v_opt_664_, v___x_666_);
v___x_669_ = 61;
v___x_670_ = lean_uint32_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
uint32_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 32;
v___x_672_ = lean_uint32_dec_eq(v___x_668_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v_shortHandle_662_);
lean_dec_ref(v_inst_661_);
lean_dec_ref(v_inst_660_);
v___x_673_ = lean_apply_1(v_longHandle_663_, v_opt_664_);
return v___x_673_;
}
else
{
lean_object* v_toBind_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_modifyGet_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_694_; 
lean_dec(v_longHandle_663_);
v_toBind_674_ = lean_ctor_get(v_inst_660_, 1);
lean_inc(v_toBind_674_);
lean_dec_ref(v_inst_660_);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_string_utf8_byte_size(v_opt_664_);
lean_inc_ref(v_opt_664_);
v___x_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_677_, 0, v_opt_664_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
v___x_678_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_679_ = lean_ctor_get(v_inst_661_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_inst_661_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_695_ = lean_ctor_get(v_inst_661_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_inst_661_, 0);
lean_dec(v_unused_696_);
v___x_681_ = v_inst_661_;
v_isShared_682_ = v_isSharedCheck_694_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_modifyGet_679_);
lean_dec(v_inst_661_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_694_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_686_; 
v___x_683_ = l_String_Slice_Pos_nextn(v___x_677_, v___x_675_, v___x_666_);
lean_dec_ref(v___x_677_);
lean_inc_ref_n(v_opt_664_, 2);
v___f_684_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_684_, 0, v_opt_664_);
lean_closure_set(v___f_684_, 1, v_shortHandle_662_);
lean_inc(v___x_683_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v___x_676_);
lean_ctor_set(v___x_681_, 1, v___x_683_);
lean_ctor_set(v___x_681_, 0, v_opt_664_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_opt_664_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v___x_676_);
v___x_686_ = v_reuseFailAlloc_693_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_687_ = l_String_Slice_Pos_skipWhile___redArg(v___x_686_, v___x_675_, v___x_678_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_nat_add(v___x_683_, v___x_687_);
lean_dec(v___x_687_);
lean_dec(v___x_683_);
v___x_689_ = lean_string_utf8_extract(v_opt_664_, v___x_688_, v___x_676_);
lean_dec(v___x_688_);
lean_dec_ref(v_opt_664_);
v___f_690_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_690_, 0, v___x_689_);
v___x_691_ = lean_apply_2(v_modifyGet_679_, lean_box(0), v___f_690_);
v___x_692_ = lean_apply_4(v_toBind_674_, lean_box(0), lean_box(0), v___x_691_, v___f_684_);
return v___x_692_;
}
}
}
}
else
{
lean_object* v_toBind_697_; lean_object* v___x_698_; lean_object* v_modifyGet_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_longHandle_663_);
v_toBind_697_ = lean_ctor_get(v_inst_660_, 1);
lean_inc(v_toBind_697_);
lean_dec_ref(v_inst_660_);
v___x_698_ = lean_string_utf8_byte_size(v_opt_664_);
v_modifyGet_699_ = lean_ctor_get(v_inst_661_, 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_inst_661_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_inst_661_, 1);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_inst_661_, 0);
lean_dec(v_unused_716_);
v___x_701_ = v_inst_661_;
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_modifyGet_699_);
lean_dec(v_inst_661_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_714_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_664_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 2, v___x_698_);
lean_ctor_set(v___x_701_, 1, v___x_703_);
lean_ctor_set(v___x_701_, 0, v_opt_664_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_opt_664_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v___x_698_);
v___x_705_ = v_reuseFailAlloc_713_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc_ref(v_opt_664_);
v___f_706_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_706_, 0, v_opt_664_);
lean_closure_set(v___f_706_, 1, v_shortHandle_662_);
v___x_707_ = lean_unsigned_to_nat(3u);
v___x_708_ = l_String_Slice_Pos_nextn(v___x_705_, v___x_703_, v___x_707_);
lean_dec_ref(v___x_705_);
v___x_709_ = lean_string_utf8_extract(v_opt_664_, v___x_708_, v___x_698_);
lean_dec(v___x_708_);
lean_dec_ref(v_opt_664_);
v___f_710_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_710_, 0, v___x_709_);
v___x_711_ = lean_apply_2(v_modifyGet_699_, lean_box(0), v___f_710_);
v___x_712_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v___x_711_, v___f_706_);
return v___x_712_;
}
}
}
}
else
{
lean_object* v___x_717_; uint32_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v_longHandle_663_);
lean_dec_ref(v_inst_661_);
lean_dec_ref(v_inst_660_);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_string_utf8_get(v_opt_664_, v___x_717_);
lean_dec_ref(v_opt_664_);
v___x_719_ = lean_box_uint32(v___x_718_);
v___x_720_ = lean_apply_1(v_shortHandle_662_, v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object* v_m_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_00_u03b1_724_, lean_object* v_shortHandle_725_, lean_object* v_longHandle_726_, lean_object* v_opt_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = lean_string_length(v_opt_727_);
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_nat_dec_eq(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
uint32_t v___x_731_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_string_utf8_get(v_opt_727_, v___x_729_);
v___x_732_ = 61;
v___x_733_ = lean_uint32_dec_eq(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 32;
v___x_735_ = lean_uint32_dec_eq(v___x_731_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v_shortHandle_725_);
lean_dec_ref(v_inst_723_);
lean_dec_ref(v_inst_722_);
v___x_736_ = lean_apply_1(v_longHandle_726_, v_opt_727_);
return v___x_736_;
}
else
{
lean_object* v_toBind_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_modifyGet_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_longHandle_726_);
v_toBind_737_ = lean_ctor_get(v_inst_722_, 1);
lean_inc(v_toBind_737_);
lean_dec_ref(v_inst_722_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_string_utf8_byte_size(v_opt_727_);
lean_inc_ref(v_opt_727_);
v___x_740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_740_, 0, v_opt_727_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_742_ = lean_ctor_get(v_inst_723_, 2);
v_isSharedCheck_757_ = !lean_is_exclusive(v_inst_723_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; 
v_unused_758_ = lean_ctor_get(v_inst_723_, 1);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_inst_723_, 0);
lean_dec(v_unused_759_);
v___x_744_ = v_inst_723_;
v_isShared_745_ = v_isSharedCheck_757_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_modifyGet_742_);
lean_dec(v_inst_723_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_757_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_749_; 
v___x_746_ = l_String_Slice_Pos_nextn(v___x_740_, v___x_738_, v___x_729_);
lean_dec_ref(v___x_740_);
lean_inc_ref_n(v_opt_727_, 2);
v___f_747_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_747_, 0, v_opt_727_);
lean_closure_set(v___f_747_, 1, v_shortHandle_725_);
lean_inc(v___x_746_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 2, v___x_739_);
lean_ctor_set(v___x_744_, 1, v___x_746_);
lean_ctor_set(v___x_744_, 0, v_opt_727_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_opt_727_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v___x_739_);
v___x_749_ = v_reuseFailAlloc_756_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_750_ = l_String_Slice_Pos_skipWhile___redArg(v___x_749_, v___x_738_, v___x_741_);
lean_dec_ref(v___x_749_);
v___x_751_ = lean_nat_add(v___x_746_, v___x_750_);
lean_dec(v___x_750_);
lean_dec(v___x_746_);
v___x_752_ = lean_string_utf8_extract(v_opt_727_, v___x_751_, v___x_739_);
lean_dec(v___x_751_);
lean_dec_ref(v_opt_727_);
v___f_753_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_753_, 0, v___x_752_);
v___x_754_ = lean_apply_2(v_modifyGet_742_, lean_box(0), v___f_753_);
v___x_755_ = lean_apply_4(v_toBind_737_, lean_box(0), lean_box(0), v___x_754_, v___f_747_);
return v___x_755_;
}
}
}
}
else
{
lean_object* v_toBind_760_; lean_object* v___x_761_; lean_object* v_modifyGet_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_longHandle_726_);
v_toBind_760_ = lean_ctor_get(v_inst_722_, 1);
lean_inc(v_toBind_760_);
lean_dec_ref(v_inst_722_);
v___x_761_ = lean_string_utf8_byte_size(v_opt_727_);
v_modifyGet_762_ = lean_ctor_get(v_inst_723_, 2);
v_isSharedCheck_777_ = !lean_is_exclusive(v_inst_723_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_778_ = lean_ctor_get(v_inst_723_, 1);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_inst_723_, 0);
lean_dec(v_unused_779_);
v___x_764_ = v_inst_723_;
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_modifyGet_762_);
lean_dec(v_inst_723_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_727_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 2, v___x_761_);
lean_ctor_set(v___x_764_, 1, v___x_766_);
lean_ctor_set(v___x_764_, 0, v_opt_727_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_opt_727_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_761_);
v___x_768_ = v_reuseFailAlloc_776_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_inc_ref(v_opt_727_);
v___f_769_ = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_769_, 0, v_opt_727_);
lean_closure_set(v___f_769_, 1, v_shortHandle_725_);
v___x_770_ = lean_unsigned_to_nat(3u);
v___x_771_ = l_String_Slice_Pos_nextn(v___x_768_, v___x_766_, v___x_770_);
lean_dec_ref(v___x_768_);
v___x_772_ = lean_string_utf8_extract(v_opt_727_, v___x_771_, v___x_761_);
lean_dec(v___x_771_);
lean_dec_ref(v_opt_727_);
v___f_773_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_773_, 0, v___x_772_);
v___x_774_ = lean_apply_2(v_modifyGet_762_, lean_box(0), v___f_773_);
v___x_775_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_774_, v___f_769_);
return v___x_775_;
}
}
}
}
else
{
lean_object* v___x_780_; uint32_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_longHandle_726_);
lean_dec_ref(v_inst_723_);
lean_dec_ref(v_inst_722_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_string_utf8_get(v_opt_727_, v___x_780_);
lean_dec_ref(v_opt_727_);
v___x_782_ = lean_box_uint32(v___x_781_);
v___x_783_ = lean_apply_1(v_shortHandle_725_, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object* v_short_784_, uint32_t v___x_785_, lean_object* v_____r_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_box_uint32(v___x_785_);
v___x_788_ = lean_apply_1(v_short_784_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object* v_short_789_, lean_object* v___x_790_, lean_object* v_____r_791_){
_start:
{
uint32_t v___x_1251__boxed_792_; lean_object* v_res_793_; 
v___x_1251__boxed_792_ = lean_unbox_uint32(v___x_790_);
lean_dec(v___x_790_);
v_res_793_ = l_Lake_option___redArg___lam__0(v_short_789_, v___x_1251__boxed_792_, v_____r_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object* v_opt_794_, lean_object* v___y_795_, lean_object* v_long_796_, lean_object* v_____r_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_string_utf8_extract(v_opt_794_, v___x_798_, v___y_795_);
v___x_800_ = lean_apply_1(v_long_796_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object* v_opt_801_, lean_object* v___y_802_, lean_object* v_long_803_, lean_object* v_____r_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lake_option___redArg___lam__4(v_opt_801_, v___y_802_, v_long_803_, v_____r_804_);
lean_dec(v___y_802_);
lean_dec_ref(v_opt_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object* v___x_806_, lean_object* v_searcher_807_, lean_object* v___y_808_, lean_object* v_long_809_, lean_object* v_____r_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_string_utf8_extract(v___x_806_, v_searcher_807_, v___y_808_);
v___x_812_ = lean_apply_1(v_long_809_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object* v___x_813_, lean_object* v_searcher_814_, lean_object* v___y_815_, lean_object* v_long_816_, lean_object* v_____r_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lake_option___redArg___lam__2(v___x_813_, v_searcher_814_, v___y_815_, v_long_816_, v_____r_817_);
lean_dec(v___y_815_);
lean_dec(v_searcher_814_);
lean_dec_ref(v___x_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5(lean_object* v_opt_819_, lean_object* v___y_820_, lean_object* v_long_821_, lean_object* v_modifyGet_822_, lean_object* v_toBind_823_, lean_object* v_____r_824_){
_start:
{
lean_object* v_searcher_825_; lean_object* v___x_826_; lean_object* v___y_828_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___f_840_; lean_object* v___x_841_; 
v_searcher_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_string_utf8_extract(v_opt_819_, v_searcher_825_, v___y_820_);
v___x_838_ = lean_string_utf8_byte_size(v___x_826_);
v___x_839_ = lean_box(0);
lean_inc_ref(v___x_826_);
v___f_840_ = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_840_, 0, v___x_838_);
lean_closure_set(v___f_840_, 1, v___x_826_);
lean_closure_set(v___f_840_, 2, v___x_839_);
v___x_841_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_840_, v_searcher_825_, v___x_839_, lean_box(0));
if (lean_obj_tag(v___x_841_) == 0)
{
v___y_828_ = v___x_838_;
goto v___jp_827_;
}
else
{
lean_object* v_val_842_; 
v_val_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_val_842_);
lean_dec_ref(v___x_841_);
v___y_828_ = v_val_842_;
goto v___jp_827_;
}
v___jp_827_:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_string_utf8_byte_size(v___x_826_);
v___x_830_ = lean_nat_dec_eq(v___y_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc(v___y_828_);
lean_inc_ref(v___x_826_);
v___f_831_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_831_, 0, v___x_826_);
lean_closure_set(v___f_831_, 1, v_searcher_825_);
lean_closure_set(v___f_831_, 2, v___y_828_);
lean_closure_set(v___f_831_, 3, v_long_821_);
v___x_832_ = lean_string_utf8_next_fast(v___x_826_, v___y_828_);
lean_dec(v___y_828_);
v___x_833_ = lean_string_utf8_extract(v___x_826_, v___x_832_, v___x_829_);
lean_dec_ref(v___x_826_);
v___f_834_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_834_, 0, v___x_833_);
v___x_835_ = lean_apply_2(v_modifyGet_822_, lean_box(0), v___f_834_);
v___x_836_ = lean_apply_4(v_toBind_823_, lean_box(0), lean_box(0), v___x_835_, v___f_831_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
lean_dec(v___y_828_);
lean_dec(v_toBind_823_);
lean_dec(v_modifyGet_822_);
v___x_837_ = lean_apply_1(v_long_821_, v___x_826_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__5___boxed(lean_object* v_opt_843_, lean_object* v___y_844_, lean_object* v_long_845_, lean_object* v_modifyGet_846_, lean_object* v_toBind_847_, lean_object* v_____r_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lake_option___redArg___lam__5(v_opt_843_, v___y_844_, v_long_845_, v_modifyGet_846_, v_toBind_847_, v_____r_848_);
lean_dec(v___y_844_);
lean_dec_ref(v_opt_843_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_handlers_852_, lean_object* v_opt_853_){
_start:
{
lean_object* v___x_854_; uint32_t v___x_855_; uint32_t v___x_856_; uint8_t v___x_857_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_string_utf8_get(v_opt_853_, v___x_854_);
v___x_856_ = 45;
v___x_857_ = lean_uint32_dec_eq(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v_short_858_; lean_object* v_longShort_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_921_; 
v_short_858_ = lean_ctor_get(v_handlers_852_, 1);
v_longShort_859_ = lean_ctor_get(v_handlers_852_, 2);
v_isSharedCheck_921_ = !lean_is_exclusive(v_handlers_852_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_handlers_852_, 0);
lean_dec(v_unused_922_);
v___x_861_ = v_handlers_852_;
v_isShared_862_ = v_isSharedCheck_921_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_longShort_859_);
lean_inc(v_short_858_);
lean_dec(v_handlers_852_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_921_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_863_ = lean_string_length(v_opt_853_);
v___x_864_ = lean_unsigned_to_nat(2u);
v___x_865_ = lean_nat_dec_eq(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
uint32_t v___x_866_; uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_866_ = lean_string_utf8_get(v_opt_853_, v___x_864_);
v___x_867_ = 61;
v___x_868_ = lean_uint32_dec_eq(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
uint32_t v___x_869_; uint8_t v___x_870_; 
v___x_869_ = 32;
v___x_870_ = lean_uint32_dec_eq(v___x_866_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_del_object(v___x_861_);
lean_dec(v_short_858_);
lean_dec_ref(v_inst_851_);
lean_dec_ref(v_inst_850_);
v___x_871_ = lean_apply_1(v_longShort_859_, v_opt_853_);
return v___x_871_;
}
else
{
lean_object* v_toBind_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v_longShort_859_);
v_toBind_872_ = lean_ctor_get(v_inst_850_, 1);
lean_inc(v_toBind_872_);
lean_dec_ref(v_inst_850_);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_string_utf8_byte_size(v_opt_853_);
lean_inc_ref(v_opt_853_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 2, v___x_874_);
lean_ctor_set(v___x_861_, 1, v___x_873_);
lean_ctor_set(v___x_861_, 0, v_opt_853_);
v___x_876_ = v___x_861_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_opt_853_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v___x_874_);
v___x_876_ = v_reuseFailAlloc_897_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v_modifyGet_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_894_; 
v___x_877_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_878_ = lean_ctor_get(v_inst_851_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v_inst_851_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; lean_object* v_unused_896_; 
v_unused_895_ = lean_ctor_get(v_inst_851_, 1);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_inst_851_, 0);
lean_dec(v_unused_896_);
v___x_880_ = v_inst_851_;
v_isShared_881_ = v_isSharedCheck_894_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_modifyGet_878_);
lean_dec(v_inst_851_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_894_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___f_884_; lean_object* v___x_886_; 
v___x_882_ = l_String_Slice_Pos_nextn(v___x_876_, v___x_873_, v___x_864_);
lean_dec_ref(v___x_876_);
v___x_883_ = lean_box_uint32(v___x_855_);
v___f_884_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_884_, 0, v_short_858_);
lean_closure_set(v___f_884_, 1, v___x_883_);
lean_inc(v___x_882_);
lean_inc_ref(v_opt_853_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v___x_874_);
lean_ctor_set(v___x_880_, 1, v___x_882_);
lean_ctor_set(v___x_880_, 0, v_opt_853_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_opt_853_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v___x_874_);
v___x_886_ = v_reuseFailAlloc_893_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_887_ = l_String_Slice_Pos_skipWhile___redArg(v___x_886_, v___x_873_, v___x_877_);
lean_dec_ref(v___x_886_);
v___x_888_ = lean_nat_add(v___x_882_, v___x_887_);
lean_dec(v___x_887_);
lean_dec(v___x_882_);
v___x_889_ = lean_string_utf8_extract(v_opt_853_, v___x_888_, v___x_874_);
lean_dec(v___x_888_);
lean_dec_ref(v_opt_853_);
v___f_890_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_890_, 0, v___x_889_);
v___x_891_ = lean_apply_2(v_modifyGet_878_, lean_box(0), v___f_890_);
v___x_892_ = lean_apply_4(v_toBind_872_, lean_box(0), lean_box(0), v___x_891_, v___f_884_);
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v_toBind_898_; lean_object* v___x_899_; lean_object* v_modifyGet_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_916_; 
lean_del_object(v___x_861_);
lean_dec(v_longShort_859_);
v_toBind_898_ = lean_ctor_get(v_inst_850_, 1);
lean_inc(v_toBind_898_);
lean_dec_ref(v_inst_850_);
v___x_899_ = lean_string_utf8_byte_size(v_opt_853_);
v_modifyGet_900_ = lean_ctor_get(v_inst_851_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_inst_851_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_917_ = lean_ctor_get(v_inst_851_, 1);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_inst_851_, 0);
lean_dec(v_unused_918_);
v___x_902_ = v_inst_851_;
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_modifyGet_900_);
lean_dec(v_inst_851_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_916_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_853_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_904_);
lean_ctor_set(v___x_902_, 0, v_opt_853_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_opt_853_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v___x_899_);
v___x_906_ = v_reuseFailAlloc_915_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_907_ = lean_box_uint32(v___x_855_);
v___f_908_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_908_, 0, v_short_858_);
lean_closure_set(v___f_908_, 1, v___x_907_);
v___x_909_ = lean_unsigned_to_nat(3u);
v___x_910_ = l_String_Slice_Pos_nextn(v___x_906_, v___x_904_, v___x_909_);
lean_dec_ref(v___x_906_);
v___x_911_ = lean_string_utf8_extract(v_opt_853_, v___x_910_, v___x_899_);
lean_dec(v___x_910_);
lean_dec_ref(v_opt_853_);
v___f_912_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_912_, 0, v___x_911_);
v___x_913_ = lean_apply_2(v_modifyGet_900_, lean_box(0), v___f_912_);
v___x_914_ = lean_apply_4(v_toBind_898_, lean_box(0), lean_box(0), v___x_913_, v___f_908_);
return v___x_914_;
}
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_del_object(v___x_861_);
lean_dec(v_longShort_859_);
lean_dec_ref(v_opt_853_);
lean_dec_ref(v_inst_851_);
lean_dec_ref(v_inst_850_);
v___x_919_ = lean_box_uint32(v___x_855_);
v___x_920_ = lean_apply_1(v_short_858_, v___x_919_);
return v___x_920_;
}
}
}
else
{
lean_object* v_long_923_; lean_object* v___y_925_; lean_object* v___y_938_; lean_object* v_searcher_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_958_; 
v_long_923_ = lean_ctor_get(v_handlers_852_, 0);
lean_inc(v_long_923_);
lean_dec_ref(v_handlers_852_);
v_searcher_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_string_utf8_byte_size(v_opt_853_);
v___x_956_ = lean_box(0);
lean_inc_ref(v_opt_853_);
v___f_957_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_957_, 0, v___x_955_);
lean_closure_set(v___f_957_, 1, v_opt_853_);
lean_closure_set(v___f_957_, 2, v___x_956_);
v___x_958_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_957_, v_searcher_954_, v___x_956_, lean_box(0));
if (lean_obj_tag(v___x_958_) == 0)
{
v___y_938_ = v___x_955_;
goto v___jp_937_;
}
else
{
lean_object* v_val_959_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref(v___x_958_);
v___y_938_ = v_val_959_;
goto v___jp_937_;
}
v___jp_924_:
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_string_utf8_byte_size(v_opt_853_);
v___x_927_ = lean_nat_dec_eq(v___y_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v_toBind_928_; lean_object* v_modifyGet_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_toBind_928_ = lean_ctor_get(v_inst_850_, 1);
lean_inc(v_toBind_928_);
lean_dec_ref(v_inst_850_);
v_modifyGet_929_ = lean_ctor_get(v_inst_851_, 2);
lean_inc(v_modifyGet_929_);
lean_dec_ref(v_inst_851_);
lean_inc(v___y_925_);
lean_inc_ref(v_opt_853_);
v___f_930_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_930_, 0, v_opt_853_);
lean_closure_set(v___f_930_, 1, v___y_925_);
lean_closure_set(v___f_930_, 2, v_long_923_);
v___x_931_ = lean_string_utf8_next_fast(v_opt_853_, v___y_925_);
lean_dec(v___y_925_);
v___x_932_ = lean_string_utf8_extract(v_opt_853_, v___x_931_, v___x_926_);
lean_dec_ref(v_opt_853_);
v___f_933_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_933_, 0, v___x_932_);
v___x_934_ = lean_apply_2(v_modifyGet_929_, lean_box(0), v___f_933_);
v___x_935_ = lean_apply_4(v_toBind_928_, lean_box(0), lean_box(0), v___x_934_, v___f_930_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; 
lean_dec(v___y_925_);
lean_dec_ref(v_inst_851_);
lean_dec_ref(v_inst_850_);
v___x_936_ = lean_apply_1(v_long_923_, v_opt_853_);
return v___x_936_;
}
}
v___jp_937_:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_string_utf8_byte_size(v_opt_853_);
v___x_940_ = lean_nat_dec_eq(v___y_938_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v_toBind_941_; lean_object* v_modifyGet_942_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_toBind_941_ = lean_ctor_get(v_inst_850_, 1);
lean_inc_n(v_toBind_941_, 2);
lean_dec_ref(v_inst_850_);
v_modifyGet_942_ = lean_ctor_get(v_inst_851_, 2);
lean_inc_n(v_modifyGet_942_, 2);
lean_dec_ref(v_inst_851_);
lean_inc(v___y_938_);
lean_inc_ref(v_opt_853_);
v___f_943_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_943_, 0, v_opt_853_);
lean_closure_set(v___f_943_, 1, v___y_938_);
lean_closure_set(v___f_943_, 2, v_long_923_);
lean_closure_set(v___f_943_, 3, v_modifyGet_942_);
lean_closure_set(v___f_943_, 4, v_toBind_941_);
v___x_944_ = lean_string_utf8_next_fast(v_opt_853_, v___y_938_);
lean_dec(v___y_938_);
v___x_945_ = lean_string_utf8_extract(v_opt_853_, v___x_944_, v___x_939_);
lean_dec_ref(v_opt_853_);
v___f_946_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_946_, 0, v___x_945_);
v___x_947_ = lean_apply_2(v_modifyGet_942_, lean_box(0), v___f_946_);
v___x_948_ = lean_apply_4(v_toBind_941_, lean_box(0), lean_box(0), v___x_947_, v___f_943_);
return v___x_948_;
}
else
{
lean_object* v_searcher_949_; lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___x_952_; 
lean_dec(v___y_938_);
v_searcher_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_box(0);
lean_inc_ref(v_opt_853_);
v___f_951_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_951_, 0, v___x_939_);
lean_closure_set(v___f_951_, 1, v_opt_853_);
lean_closure_set(v___f_951_, 2, v___x_950_);
v___x_952_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_951_, v_searcher_949_, v___x_950_, lean_box(0));
if (lean_obj_tag(v___x_952_) == 0)
{
v___y_925_ = v___x_939_;
goto v___jp_924_;
}
else
{
lean_object* v_val_953_; 
v_val_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v___x_952_);
v___y_925_ = v_val_953_;
goto v___jp_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option(lean_object* v_m_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_00_u03b1_963_, lean_object* v_handlers_964_, lean_object* v_opt_965_){
_start:
{
lean_object* v___x_966_; uint32_t v___x_967_; uint32_t v___x_968_; uint8_t v___x_969_; 
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_string_utf8_get(v_opt_965_, v___x_966_);
v___x_968_ = 45;
v___x_969_ = lean_uint32_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v_short_970_; lean_object* v_longShort_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1033_; 
v_short_970_ = lean_ctor_get(v_handlers_964_, 1);
v_longShort_971_ = lean_ctor_get(v_handlers_964_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_handlers_964_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_handlers_964_, 0);
lean_dec(v_unused_1034_);
v___x_973_ = v_handlers_964_;
v_isShared_974_ = v_isSharedCheck_1033_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_longShort_971_);
lean_inc(v_short_970_);
lean_dec(v_handlers_964_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1033_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_string_length(v_opt_965_);
v___x_976_ = lean_unsigned_to_nat(2u);
v___x_977_ = lean_nat_dec_eq(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
uint32_t v___x_978_; uint32_t v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_string_utf8_get(v_opt_965_, v___x_976_);
v___x_979_ = 61;
v___x_980_ = lean_uint32_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
uint32_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = 32;
v___x_982_ = lean_uint32_dec_eq(v___x_978_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_del_object(v___x_973_);
lean_dec(v_short_970_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_inst_961_);
v___x_983_ = lean_apply_1(v_longShort_971_, v_opt_965_);
return v___x_983_;
}
else
{
lean_object* v_toBind_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
lean_dec(v_longShort_971_);
v_toBind_984_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_984_);
lean_dec_ref(v_inst_961_);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_string_utf8_byte_size(v_opt_965_);
lean_inc_ref(v_opt_965_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_986_);
lean_ctor_set(v___x_973_, 1, v___x_985_);
lean_ctor_set(v___x_973_, 0, v_opt_965_);
v___x_988_ = v___x_973_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_opt_965_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v___x_986_);
v___x_988_ = v_reuseFailAlloc_1009_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v_modifyGet_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1006_; 
v___x_989_ = lean_obj_once(&l_Lake_shortOptionWithSpace___redArg___closed__1, &l_Lake_shortOptionWithSpace___redArg___closed__1_once, _init_l_Lake_shortOptionWithSpace___redArg___closed__1);
v_modifyGet_990_ = lean_ctor_get(v_inst_962_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_inst_962_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; lean_object* v_unused_1008_; 
v_unused_1007_ = lean_ctor_get(v_inst_962_, 1);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_inst_962_, 0);
lean_dec(v_unused_1008_);
v___x_992_ = v_inst_962_;
v_isShared_993_ = v_isSharedCheck_1006_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_modifyGet_990_);
lean_dec(v_inst_962_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1006_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v___x_998_; 
v___x_994_ = l_String_Slice_Pos_nextn(v___x_988_, v___x_985_, v___x_976_);
lean_dec_ref(v___x_988_);
v___x_995_ = lean_box_uint32(v___x_967_);
v___f_996_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_996_, 0, v_short_970_);
lean_closure_set(v___f_996_, 1, v___x_995_);
lean_inc(v___x_994_);
lean_inc_ref(v_opt_965_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v___x_986_);
lean_ctor_set(v___x_992_, 1, v___x_994_);
lean_ctor_set(v___x_992_, 0, v_opt_965_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_opt_965_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v___x_986_);
v___x_998_ = v_reuseFailAlloc_1005_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_999_ = l_String_Slice_Pos_skipWhile___redArg(v___x_998_, v___x_985_, v___x_989_);
lean_dec_ref(v___x_998_);
v___x_1000_ = lean_nat_add(v___x_994_, v___x_999_);
lean_dec(v___x_999_);
lean_dec(v___x_994_);
v___x_1001_ = lean_string_utf8_extract(v_opt_965_, v___x_1000_, v___x_986_);
lean_dec(v___x_1000_);
lean_dec_ref(v_opt_965_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1002_, 0, v___x_1001_);
v___x_1003_ = lean_apply_2(v_modifyGet_990_, lean_box(0), v___f_1002_);
v___x_1004_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v___x_1003_, v___f_996_);
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v_toBind_1010_; lean_object* v___x_1011_; lean_object* v_modifyGet_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_973_);
lean_dec(v_longShort_971_);
v_toBind_1010_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_1010_);
lean_dec_ref(v_inst_961_);
v___x_1011_ = lean_string_utf8_byte_size(v_opt_965_);
v_modifyGet_1012_ = lean_ctor_get(v_inst_962_, 2);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_inst_962_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; lean_object* v_unused_1030_; 
v_unused_1029_ = lean_ctor_get(v_inst_962_, 1);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_inst_962_, 0);
lean_dec(v_unused_1030_);
v___x_1014_ = v_inst_962_;
v_isShared_1015_ = v_isSharedCheck_1028_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_modifyGet_1012_);
lean_dec(v_inst_962_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1028_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_opt_965_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 2, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1016_);
lean_ctor_set(v___x_1014_, 0, v_opt_965_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_opt_965_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v___x_1011_);
v___x_1018_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1019_ = lean_box_uint32(v___x_967_);
v___f_1020_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1020_, 0, v_short_970_);
lean_closure_set(v___f_1020_, 1, v___x_1019_);
v___x_1021_ = lean_unsigned_to_nat(3u);
v___x_1022_ = l_String_Slice_Pos_nextn(v___x_1018_, v___x_1016_, v___x_1021_);
lean_dec_ref(v___x_1018_);
v___x_1023_ = lean_string_utf8_extract(v_opt_965_, v___x_1022_, v___x_1011_);
lean_dec(v___x_1022_);
lean_dec_ref(v_opt_965_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
v___x_1025_ = lean_apply_2(v_modifyGet_1012_, lean_box(0), v___f_1024_);
v___x_1026_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v___x_1025_, v___f_1020_);
return v___x_1026_;
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_del_object(v___x_973_);
lean_dec(v_longShort_971_);
lean_dec_ref(v_opt_965_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_inst_961_);
v___x_1031_ = lean_box_uint32(v___x_967_);
v___x_1032_ = lean_apply_1(v_short_970_, v___x_1031_);
return v___x_1032_;
}
}
}
else
{
lean_object* v_long_1035_; lean_object* v___y_1037_; lean_object* v___y_1050_; lean_object* v_searcher_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
v_long_1035_ = lean_ctor_get(v_handlers_964_, 0);
lean_inc(v_long_1035_);
lean_dec_ref(v_handlers_964_);
v_searcher_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_string_utf8_byte_size(v_opt_965_);
v___x_1068_ = lean_box(0);
lean_inc_ref(v_opt_965_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lake_longOptionOrEq___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1069_, 0, v___x_1067_);
lean_closure_set(v___f_1069_, 1, v_opt_965_);
lean_closure_set(v___f_1069_, 2, v___x_1068_);
v___x_1070_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1069_, v_searcher_1066_, v___x_1068_, lean_box(0));
if (lean_obj_tag(v___x_1070_) == 0)
{
v___y_1050_ = v___x_1067_;
goto v___jp_1049_;
}
else
{
lean_object* v_val_1071_; 
v_val_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_val_1071_);
lean_dec_ref(v___x_1070_);
v___y_1050_ = v_val_1071_;
goto v___jp_1049_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_string_utf8_byte_size(v_opt_965_);
v___x_1039_ = lean_nat_dec_eq(v___y_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v_toBind_1040_; lean_object* v_modifyGet_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_toBind_1040_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_1040_);
lean_dec_ref(v_inst_961_);
v_modifyGet_1041_ = lean_ctor_get(v_inst_962_, 2);
lean_inc(v_modifyGet_1041_);
lean_dec_ref(v_inst_962_);
lean_inc(v___y_1037_);
lean_inc_ref(v_opt_965_);
v___f_1042_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_1042_, 0, v_opt_965_);
lean_closure_set(v___f_1042_, 1, v___y_1037_);
lean_closure_set(v___f_1042_, 2, v_long_1035_);
v___x_1043_ = lean_string_utf8_next_fast(v_opt_965_, v___y_1037_);
lean_dec(v___y_1037_);
v___x_1044_ = lean_string_utf8_extract(v_opt_965_, v___x_1043_, v___x_1038_);
lean_dec_ref(v_opt_965_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1045_, 0, v___x_1044_);
v___x_1046_ = lean_apply_2(v_modifyGet_1041_, lean_box(0), v___f_1045_);
v___x_1047_ = lean_apply_4(v_toBind_1040_, lean_box(0), lean_box(0), v___x_1046_, v___f_1042_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v___y_1037_);
lean_dec_ref(v_inst_962_);
lean_dec_ref(v_inst_961_);
v___x_1048_ = lean_apply_1(v_long_1035_, v_opt_965_);
return v___x_1048_;
}
}
v___jp_1049_:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_string_utf8_byte_size(v_opt_965_);
v___x_1052_ = lean_nat_dec_eq(v___y_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v_toBind_1053_; lean_object* v_modifyGet_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_toBind_1053_ = lean_ctor_get(v_inst_961_, 1);
lean_inc_n(v_toBind_1053_, 2);
lean_dec_ref(v_inst_961_);
v_modifyGet_1054_ = lean_ctor_get(v_inst_962_, 2);
lean_inc_n(v_modifyGet_1054_, 2);
lean_dec_ref(v_inst_962_);
lean_inc(v___y_1050_);
lean_inc_ref(v_opt_965_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1055_, 0, v_opt_965_);
lean_closure_set(v___f_1055_, 1, v___y_1050_);
lean_closure_set(v___f_1055_, 2, v_long_1035_);
lean_closure_set(v___f_1055_, 3, v_modifyGet_1054_);
lean_closure_set(v___f_1055_, 4, v_toBind_1053_);
v___x_1056_ = lean_string_utf8_next_fast(v_opt_965_, v___y_1050_);
lean_dec(v___y_1050_);
v___x_1057_ = lean_string_utf8_extract(v_opt_965_, v___x_1056_, v___x_1051_);
lean_dec_ref(v_opt_965_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1058_, 0, v___x_1057_);
v___x_1059_ = lean_apply_2(v_modifyGet_1054_, lean_box(0), v___f_1058_);
v___x_1060_ = lean_apply_4(v_toBind_1053_, lean_box(0), lean_box(0), v___x_1059_, v___f_1055_);
return v___x_1060_;
}
else
{
lean_object* v_searcher_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
lean_dec(v___y_1050_);
v_searcher_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_box(0);
lean_inc_ref(v_opt_965_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_1063_, 0, v___x_1051_);
lean_closure_set(v___f_1063_, 1, v_opt_965_);
lean_closure_set(v___f_1063_, 2, v___x_1062_);
v___x_1064_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1063_, v_searcher_1061_, v___x_1062_, lean_box(0));
if (lean_obj_tag(v___x_1064_) == 0)
{
v___y_1037_ = v___x_1051_;
goto v___jp_1036_;
}
else
{
lean_object* v_val_1065_; 
v_val_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref(v___x_1064_);
v___y_1037_ = v_val_1065_;
goto v___jp_1036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object* v_handle_1072_, lean_object* v_head_1073_, lean_object* v_____r_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_apply_1(v_handle_1072_, v_head_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object* v_toPure_1076_, lean_object* v_handle_1077_, lean_object* v_set_1078_, lean_object* v_toBind_1079_, lean_object* v_____do__lift_1080_){
_start:
{
if (lean_obj_tag(v_____do__lift_1080_) == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v_toBind_1079_);
lean_dec(v_set_1078_);
lean_dec(v_handle_1077_);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_apply_2(v_toPure_1076_, lean_box(0), v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v_head_1083_; lean_object* v_tail_1084_; lean_object* v___f_1085_; uint8_t v___y_1087_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_head_1083_ = lean_ctor_get(v_____do__lift_1080_, 0);
lean_inc_n(v_head_1083_, 2);
v_tail_1084_ = lean_ctor_get(v_____do__lift_1080_, 1);
lean_inc(v_tail_1084_);
lean_dec_ref(v_____do__lift_1080_);
v___f_1085_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1085_, 0, v_handle_1077_);
lean_closure_set(v___f_1085_, 1, v_head_1083_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_string_length(v_head_1083_);
v___x_1094_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_dec(v_head_1083_);
v___y_1087_ = v___x_1094_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1095_; uint32_t v___x_1096_; uint32_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_string_utf8_get(v_head_1083_, v___x_1095_);
lean_dec(v_head_1083_);
v___x_1097_ = 45;
v___x_1098_ = lean_uint32_dec_eq(v___x_1096_, v___x_1097_);
v___y_1087_ = v___x_1098_;
goto v___jp_1086_;
}
v___jp_1086_:
{
if (v___y_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v___f_1085_);
lean_dec(v_tail_1084_);
lean_dec(v_toBind_1079_);
lean_dec(v_set_1078_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_apply_2(v_toPure_1076_, lean_box(0), v___x_1088_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_toPure_1076_);
v___x_1090_ = lean_apply_1(v_set_1078_, v_tail_1084_);
v___x_1091_ = lean_apply_4(v_toBind_1079_, lean_box(0), lean_box(0), v___x_1090_, v___f_1085_);
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_handle_1101_){
_start:
{
lean_object* v_toApplicative_1102_; lean_object* v_toBind_1103_; lean_object* v_get_1104_; lean_object* v_set_1105_; lean_object* v_toPure_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
v_toApplicative_1102_ = lean_ctor_get(v_inst_1099_, 0);
lean_inc_ref(v_toApplicative_1102_);
v_toBind_1103_ = lean_ctor_get(v_inst_1099_, 1);
lean_inc_n(v_toBind_1103_, 2);
lean_dec_ref(v_inst_1099_);
v_get_1104_ = lean_ctor_get(v_inst_1100_, 0);
lean_inc(v_get_1104_);
v_set_1105_ = lean_ctor_get(v_inst_1100_, 1);
lean_inc(v_set_1105_);
lean_dec_ref(v_inst_1100_);
v_toPure_1106_ = lean_ctor_get(v_toApplicative_1102_, 1);
lean_inc(v_toPure_1106_);
lean_dec_ref(v_toApplicative_1102_);
v___f_1107_ = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1107_, 0, v_toPure_1106_);
lean_closure_set(v___f_1107_, 1, v_handle_1101_);
lean_closure_set(v___f_1107_, 2, v_set_1105_);
lean_closure_set(v___f_1107_, 3, v_toBind_1103_);
v___x_1108_ = lean_apply_4(v_toBind_1103_, lean_box(0), lean_box(0), v_get_1104_, v___f_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object* v_m_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_handle_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lake_processLeadingOption___redArg(v_inst_1110_, v_inst_1111_, v_handle_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object* v_handle_1114_, lean_object* v_head_1115_, lean_object* v_toBind_1116_, lean_object* v___f_1117_, lean_object* v_____r_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_apply_1(v_handle_1114_, v_head_1115_);
v___x_1120_ = lean_apply_4(v_toBind_1116_, lean_box(0), lean_box(0), v___x_1119_, v___f_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object* v_handle_1121_, lean_object* v_toBind_1122_, lean_object* v___f_1123_, lean_object* v_toPure_1124_, lean_object* v_set_1125_, lean_object* v___f_1126_, lean_object* v_____do__lift_1127_){
_start:
{
if (lean_obj_tag(v_____do__lift_1127_) == 1)
{
lean_object* v_head_1128_; lean_object* v_tail_1129_; lean_object* v___f_1130_; lean_object* v_len_1131_; uint8_t v___y_1133_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v_head_1128_ = lean_ctor_get(v_____do__lift_1127_, 0);
lean_inc_n(v_head_1128_, 2);
v_tail_1129_ = lean_ctor_get(v_____do__lift_1127_, 1);
lean_inc(v_tail_1129_);
lean_dec_ref(v_____do__lift_1127_);
lean_inc(v_toBind_1122_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1130_, 0, v_handle_1121_);
lean_closure_set(v___f_1130_, 1, v_head_1128_);
lean_closure_set(v___f_1130_, 2, v_toBind_1122_);
lean_closure_set(v___f_1130_, 3, v___f_1123_);
v_len_1131_ = lean_string_length(v_head_1128_);
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_dec_lt(v___x_1142_, v_len_1131_);
if (v___x_1143_ == 0)
{
lean_dec(v_head_1128_);
v___y_1133_ = v___x_1143_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1144_; uint32_t v___x_1145_; uint32_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_string_utf8_get(v_head_1128_, v___x_1144_);
lean_dec(v_head_1128_);
v___x_1146_ = 45;
v___x_1147_ = lean_uint32_dec_eq(v___x_1145_, v___x_1146_);
v___y_1133_ = v___x_1147_;
goto v___jp_1132_;
}
v___jp_1132_:
{
if (v___y_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
lean_dec_ref(v___f_1130_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_nat_dec_eq(v_len_1131_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v_tail_1129_);
lean_dec(v___f_1126_);
lean_dec(v_set_1125_);
lean_dec(v_toBind_1122_);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_apply_2(v_toPure_1124_, lean_box(0), v___x_1136_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_toPure_1124_);
v___x_1138_ = lean_apply_1(v_set_1125_, v_tail_1129_);
v___x_1139_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v___x_1138_, v___f_1126_);
return v___x_1139_;
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v___f_1126_);
lean_dec(v_toPure_1124_);
v___x_1140_ = lean_apply_1(v_set_1125_, v_tail_1129_);
v___x_1141_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v___x_1140_, v___f_1130_);
return v___x_1141_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec(v_____do__lift_1127_);
lean_dec(v___f_1126_);
lean_dec(v_set_1125_);
lean_dec(v___f_1123_);
lean_dec(v_toBind_1122_);
lean_dec(v_handle_1121_);
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_apply_2(v_toPure_1124_, lean_box(0), v___x_1148_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_handle_1152_){
_start:
{
lean_object* v_toApplicative_1153_; lean_object* v_toBind_1154_; lean_object* v_get_1155_; lean_object* v_set_1156_; lean_object* v_toPure_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; 
v_toApplicative_1153_ = lean_ctor_get(v_inst_1150_, 0);
v_toBind_1154_ = lean_ctor_get(v_inst_1150_, 1);
lean_inc_n(v_toBind_1154_, 2);
v_get_1155_ = lean_ctor_get(v_inst_1151_, 0);
lean_inc(v_get_1155_);
v_set_1156_ = lean_ctor_get(v_inst_1151_, 1);
lean_inc(v_set_1156_);
v_toPure_1157_ = lean_ctor_get(v_toApplicative_1153_, 1);
lean_inc(v_toPure_1157_);
lean_inc(v_handle_1152_);
v___f_1158_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1158_, 0, v_inst_1150_);
lean_closure_set(v___f_1158_, 1, v_inst_1151_);
lean_closure_set(v___f_1158_, 2, v_handle_1152_);
lean_inc_ref(v___f_1158_);
v___f_1159_ = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1159_, 0, v_handle_1152_);
lean_closure_set(v___f_1159_, 1, v_toBind_1154_);
lean_closure_set(v___f_1159_, 2, v___f_1158_);
lean_closure_set(v___f_1159_, 3, v_toPure_1157_);
lean_closure_set(v___f_1159_, 4, v_set_1156_);
lean_closure_set(v___f_1159_, 5, v___f_1158_);
v___x_1160_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v_get_1155_, v___f_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_handle_1163_, lean_object* v_____r_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lake_processLeadingOptions___redArg(v_inst_1161_, v_inst_1162_, v_handle_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object* v_m_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_handle_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lake_processLeadingOptions___redArg(v_inst_1167_, v_inst_1168_, v_handle_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object* v_x_1171_){
_start:
{
if (lean_obj_tag(v_x_1171_) == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_x_1171_);
return v___x_1173_;
}
else
{
lean_object* v_head_1174_; lean_object* v_tail_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_head_1174_ = lean_ctor_get(v_x_1171_, 0);
v_tail_1175_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v_x_1171_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_tail_1175_);
lean_inc(v_head_1174_);
lean_dec(v_x_1171_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_head_1174_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_tail_1175_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object* v_args_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_option_1188_, lean_object* v_toBind_1189_, lean_object* v___f_1190_, lean_object* v_toPure_1191_, lean_object* v_____do__lift_1192_){
_start:
{
if (lean_obj_tag(v_____do__lift_1192_) == 1)
{
lean_object* v_val_1193_; lean_object* v_len_1194_; uint8_t v___y_1196_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
lean_dec(v_toPure_1191_);
v_val_1193_ = lean_ctor_get(v_____do__lift_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref(v_____do__lift_1192_);
v_len_1194_ = lean_string_length(v_val_1193_);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_dec_lt(v___x_1204_, v_len_1194_);
if (v___x_1205_ == 0)
{
v___y_1196_ = v___x_1205_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1206_; uint32_t v___x_1207_; uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_string_utf8_get(v_val_1193_, v___x_1206_);
v___x_1208_ = 45;
v___x_1209_ = lean_uint32_dec_eq(v___x_1207_, v___x_1208_);
v___y_1196_ = v___x_1209_;
goto v___jp_1195_;
}
v___jp_1195_:
{
if (v___y_1196_ == 0)
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
lean_dec(v___f_1190_);
lean_dec(v_toBind_1189_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_nat_dec_eq(v_len_1194_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_array_push(v_args_1185_, v_val_1193_);
v___x_1200_ = l_Lake_collectArgs___redArg(v_inst_1186_, v_inst_1187_, v_option_1188_, v___x_1199_);
return v___x_1200_;
}
else
{
lean_object* v___x_1201_; 
lean_dec(v_val_1193_);
v___x_1201_ = l_Lake_collectArgs___redArg(v_inst_1186_, v_inst_1187_, v_option_1188_, v_args_1185_);
return v___x_1201_;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
lean_dec_ref(v_args_1185_);
v___x_1202_ = lean_apply_1(v_option_1188_, v_val_1193_);
v___x_1203_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1202_, v___f_1190_);
return v___x_1203_;
}
}
}
else
{
lean_object* v___x_1210_; 
lean_dec(v_____do__lift_1192_);
lean_dec(v___f_1190_);
lean_dec(v_toBind_1189_);
lean_dec(v_option_1188_);
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
v___x_1210_ = lean_apply_2(v_toPure_1191_, lean_box(0), v_args_1185_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_option_1213_, lean_object* v_args_1214_){
_start:
{
lean_object* v_toApplicative_1215_; lean_object* v_toBind_1216_; lean_object* v_modifyGet_1217_; lean_object* v_toPure_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
v_toApplicative_1215_ = lean_ctor_get(v_inst_1211_, 0);
v_toBind_1216_ = lean_ctor_get(v_inst_1211_, 1);
lean_inc_n(v_toBind_1216_, 2);
v_modifyGet_1217_ = lean_ctor_get(v_inst_1212_, 2);
v_toPure_1218_ = lean_ctor_get(v_toApplicative_1215_, 1);
lean_inc(v_toPure_1218_);
v___f_1219_ = ((lean_object*)(l_Lake_collectArgs___redArg___closed__0));
lean_inc_ref(v_args_1214_);
lean_inc(v_option_1213_);
lean_inc_ref(v_inst_1212_);
lean_inc_ref(v_inst_1211_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1220_, 0, v_inst_1211_);
lean_closure_set(v___f_1220_, 1, v_inst_1212_);
lean_closure_set(v___f_1220_, 2, v_option_1213_);
lean_closure_set(v___f_1220_, 3, v_args_1214_);
lean_inc(v_modifyGet_1217_);
v___x_1221_ = lean_apply_2(v_modifyGet_1217_, lean_box(0), v___f_1219_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1222_, 0, v_args_1214_);
lean_closure_set(v___f_1222_, 1, v_inst_1211_);
lean_closure_set(v___f_1222_, 2, v_inst_1212_);
lean_closure_set(v___f_1222_, 3, v_option_1213_);
lean_closure_set(v___f_1222_, 4, v_toBind_1216_);
lean_closure_set(v___f_1222_, 5, v___f_1220_);
lean_closure_set(v___f_1222_, 6, v_toPure_1218_);
v___x_1223_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v___x_1221_, v___f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_option_1226_, lean_object* v_args_1227_, lean_object* v_____r_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lake_collectArgs___redArg(v_inst_1224_, v_inst_1225_, v_option_1226_, v_args_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object* v_m_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_option_1233_, lean_object* v_args_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lake_collectArgs___redArg(v_inst_1231_, v_inst_1232_, v_option_1233_, v_args_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object* v_inst_1236_, lean_object* v_____do__lift_1237_){
_start:
{
lean_object* v_set_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_set_1238_ = lean_ctor_get(v_inst_1236_, 1);
lean_inc(v_set_1238_);
lean_dec_ref(v_inst_1236_);
v___x_1239_ = lean_array_to_list(v_____do__lift_1237_);
v___x_1240_ = lean_apply_1(v_set_1238_, v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_handle_1245_){
_start:
{
lean_object* v_toBind_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_toBind_1246_ = lean_ctor_get(v_inst_1243_, 1);
lean_inc(v_toBind_1246_);
lean_inc_ref(v_inst_1244_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1247_, 0, v_inst_1244_);
v___x_1248_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1249_ = l_Lake_collectArgs___redArg(v_inst_1243_, v_inst_1244_, v_handle_1245_, v___x_1248_);
v___x_1250_ = lean_apply_4(v_toBind_1246_, lean_box(0), lean_box(0), v___x_1249_, v___f_1247_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object* v_m_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_handle_1254_){
_start:
{
lean_object* v_toBind_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_toBind_1255_ = lean_ctor_get(v_inst_1252_, 1);
lean_inc(v_toBind_1255_);
lean_inc_ref(v_inst_1253_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1256_, 0, v_inst_1253_);
v___x_1257_ = ((lean_object*)(l_Lake_processOptions___redArg___closed__0));
v___x_1258_ = l_Lake_collectArgs___redArg(v_inst_1252_, v_inst_1253_, v_handle_1254_, v___x_1257_);
v___x_1259_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v___x_1258_, v___f_1256_);
return v___x_1259_;
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
