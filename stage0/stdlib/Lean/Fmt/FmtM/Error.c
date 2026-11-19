// Lean compiler output
// Module: Lean.Fmt.FmtM.Error
// Imports: public import Init.Data.ToString public import Lean.Fmt.Core.Basic public import Init.Data.Format.Syntax public import Lean.Fmt.Core.Formatter
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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedInternalError_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedInternalError;
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_parseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_parseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_earlyTerminationCommand_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_earlyTerminationCommand_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_importError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_importError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instInhabitedInputError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_instInhabitedInputError_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedInputError_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instInhabitedInputError_default___closed__1 = (const lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedInputError_default = (const lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedInputError = (const lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringInputError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringInputError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringInputError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instToStringInputError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringInputError___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringInputError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringInputError = (const lean_object*)&l_Lean_Fmt_instToStringInputError___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ref_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ref_x3f___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_instInhabitedElaborationError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__0_value),((lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instInhabitedElaborationError_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedElaborationError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedElaborationError_default = (const lean_object*)&l_Lean_Fmt_instInhabitedElaborationError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedElaborationError = (const lean_object*)&l_Lean_Fmt_instInhabitedElaborationError_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringElaborationError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringElaborationError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringElaborationError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instToStringElaborationError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringElaborationError___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringElaborationError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringElaborationError = (const lean_object*)&l_Lean_Fmt_instToStringElaborationError___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ref___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_formattingFailure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_formattingFailure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseFailure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseFailure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStopMismatch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStopMismatch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStructureMismatch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStructureMismatch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_taintedFormatting_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_taintedFormatting_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_instInhabitedFmtError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instInhabitedInputError_default___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instInhabitedFmtError_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedFmtError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedFmtError_default = (const lean_object*)&l_Lean_Fmt_instInhabitedFmtError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedFmtError = (const lean_object*)&l_Lean_Fmt_instInhabitedFmtError_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringFmtError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringFmtError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringFmtError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instToStringFmtError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringFmtError___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringFmtError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringFmtError = (const lean_object*)&l_Lean_Fmt_instToStringFmtError___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ref___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_internal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_internal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_input_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_input_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_elaboration_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_elaboration_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_fmt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_fmt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_instInhabitedError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_instInhabitedError_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedError_default = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedError = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Error_partialFormatter = (const lean_object*)&l_Lean_Fmt_instInhabitedError_default___closed__0_value;
static const lean_string_object l_Lean_Fmt_instToStringError___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Internal error."};
static const lean_object* l_Lean_Fmt_instToStringError___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringError___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instToStringError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringError___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringError = (const lean_object*)&l_Lean_Fmt_instToStringError___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ref_x3f(lean_object*);
static const lean_string_object l_Lean_Fmt_Error_ofFormattingError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 527, .m_capacity = 527, .m_length = 526, .m_data = "Formatting of the document produced by the current set of `[fmt]` annotations contains a part that always exceeds the maximum column width within which the formatter attempts to find optimal configurations (200). This issue is commonly caused by syntax in the document that is not formatted (e.g. because there is no `[fmt]` attribute for it) and is also very long in the input document. To format the parts of the document that are formatteable, either break up the document that is not formatted or write a formatter for it."};
static const lean_object* l_Lean_Fmt_Error_ofFormattingError___closed__0 = (const lean_object*)&l_Lean_Fmt_Error_ofFormattingError___closed__0_value;
static const lean_string_object l_Lean_Fmt_Error_ofFormattingError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 193, .m_capacity = 193, .m_length = 192, .m_data = "Formatting of the document produced by the current set of `[fmt]` annotations has failed. This issue is commonly caused by `Doc.failure` or attempting to flatten a document with hard newlines."};
static const lean_object* l_Lean_Fmt_Error_ofFormattingError___closed__1 = (const lean_object*)&l_Lean_Fmt_Error_ofFormattingError___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Fmt_InternalError_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Fmt_InternalError_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Fmt_InternalError_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim___redArg(lean_object* v_partialFormatter_22_){
_start:
{
lean_inc(v_partialFormatter_22_);
return v_partialFormatter_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim___redArg___boxed(lean_object* v_partialFormatter_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Fmt_InternalError_partialFormatter_elim___redArg(v_partialFormatter_23_);
lean_dec(v_partialFormatter_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_partialFormatter_28_){
_start:
{
lean_inc(v_partialFormatter_28_);
return v_partialFormatter_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_partialFormatter_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_partialFormatter_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Fmt_InternalError_partialFormatter_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_partialFormatter_32_);
lean_dec(v_partialFormatter_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim___redArg(lean_object* v_cancelled_35_){
_start:
{
lean_inc(v_cancelled_35_);
return v_cancelled_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim___redArg___boxed(lean_object* v_cancelled_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Fmt_InternalError_cancelled_elim___redArg(v_cancelled_36_);
lean_dec(v_cancelled_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_cancelled_41_){
_start:
{
lean_inc(v_cancelled_41_);
return v_cancelled_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InternalError_cancelled_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_cancelled_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Fmt_InternalError_cancelled_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_cancelled_45_);
lean_dec(v_cancelled_45_);
return v_res_47_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInternalError_default(void){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInternalError(void){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorIdx___impl(lean_object* v_x_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_tag_nat(v_x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorIdx___impl___boxed(lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Fmt_InputError_ctorIdx___impl(v_x_52_);
lean_dec_ref(v_x_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorElim___redArg(lean_object* v_t_54_, lean_object* v_k_55_){
_start:
{
if (lean_obj_tag(v_t_54_) == 0)
{
lean_object* v_msg_56_; lean_object* v___x_57_; 
v_msg_56_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_msg_56_);
lean_dec_ref_known(v_t_54_, 1);
v___x_57_ = lean_apply_1(v_k_55_, v_msg_56_);
return v___x_57_;
}
else
{
lean_object* v_stx_58_; lean_object* v_msg_59_; lean_object* v___x_60_; 
v_stx_58_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_stx_58_);
v_msg_59_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_msg_59_);
lean_dec_ref(v_t_54_);
v___x_60_ = lean_apply_2(v_k_55_, v_stx_58_, v_msg_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorElim(lean_object* v_motive_61_, lean_object* v_ctorIdx_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_k_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_63_, v_k_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ctorElim___boxed(lean_object* v_motive_67_, lean_object* v_ctorIdx_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_k_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Fmt_InputError_ctorElim(v_motive_67_, v_ctorIdx_68_, v_t_69_, v_h_70_, v_k_71_);
lean_dec(v_ctorIdx_68_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_parseError_elim___redArg(lean_object* v_t_73_, lean_object* v_parseError_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_73_, v_parseError_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_parseError_elim(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_parseError_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_77_, v_parseError_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_earlyTerminationCommand_elim___redArg(lean_object* v_t_81_, lean_object* v_earlyTerminationCommand_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_81_, v_earlyTerminationCommand_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_earlyTerminationCommand_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_earlyTerminationCommand_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_85_, v_earlyTerminationCommand_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_importError_elim___redArg(lean_object* v_t_89_, lean_object* v_importError_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_89_, v_importError_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_importError_elim(lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_importError_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Fmt_InputError_ctorElim___redArg(v_t_93_, v_importError_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringInputError___lam__0(lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_msg_103_; 
v_msg_103_ = lean_ctor_get(v_x_102_, 0);
lean_inc_ref(v_msg_103_);
return v_msg_103_;
}
else
{
lean_object* v_msg_104_; 
v_msg_104_ = lean_ctor_get(v_x_102_, 1);
lean_inc_ref(v_msg_104_);
return v_msg_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringInputError___lam__0___boxed(lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Fmt_instToStringInputError___lam__0(v_x_105_);
lean_dec_ref(v_x_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ref_x3f(lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v_stx_111_; lean_object* v___x_112_; 
v_stx_111_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_stx_111_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_stx_111_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InputError_ref_x3f___boxed(lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Fmt_InputError_ref_x3f(v_x_113_);
lean_dec_ref(v_x_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringElaborationError___lam__0(lean_object* v_x_120_){
_start:
{
lean_object* v_msg_121_; 
v_msg_121_ = lean_ctor_get(v_x_120_, 2);
lean_inc_ref(v_msg_121_);
return v_msg_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringElaborationError___lam__0___boxed(lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Fmt_instToStringElaborationError___lam__0(v_x_122_);
lean_dec_ref(v_x_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ref(lean_object* v_x_126_){
_start:
{
lean_object* v_stx_127_; 
v_stx_127_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_stx_127_);
return v_stx_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ref___boxed(lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Fmt_ElaborationError_ref(v_x_128_);
lean_dec_ref(v_x_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorIdx___impl(lean_object* v_x_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_tag_nat(v_x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorIdx___impl___boxed(lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Fmt_FmtError_ctorIdx___impl(v_x_132_);
lean_dec_ref(v_x_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim___redArg(lean_object* v_t_134_, lean_object* v_k_135_){
_start:
{
lean_object* v_stx_136_; lean_object* v_msg_137_; lean_object* v___x_138_; 
v_stx_136_ = lean_ctor_get(v_t_134_, 0);
lean_inc(v_stx_136_);
v_msg_137_ = lean_ctor_get(v_t_134_, 1);
lean_inc_ref(v_msg_137_);
lean_dec_ref(v_t_134_);
v___x_138_ = lean_apply_2(v_k_135_, v_stx_136_, v_msg_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim(lean_object* v_motive_139_, lean_object* v_ctorIdx_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_k_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_141_, v_k_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim___boxed(lean_object* v_motive_145_, lean_object* v_ctorIdx_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_k_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Fmt_FmtError_ctorElim(v_motive_145_, v_ctorIdx_146_, v_t_147_, v_h_148_, v_k_149_);
lean_dec(v_ctorIdx_146_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_formattingFailure_elim___redArg(lean_object* v_t_151_, lean_object* v_formattingFailure_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_151_, v_formattingFailure_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_formattingFailure_elim(lean_object* v_motive_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_formattingFailure_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_155_, v_formattingFailure_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseFailure_elim___redArg(lean_object* v_t_159_, lean_object* v_reparseFailure_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_159_, v_reparseFailure_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseFailure_elim(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_reparseFailure_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_163_, v_reparseFailure_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStopMismatch_elim___redArg(lean_object* v_t_167_, lean_object* v_reparseStopMismatch_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_167_, v_reparseStopMismatch_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStopMismatch_elim(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_reparseStopMismatch_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_171_, v_reparseStopMismatch_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStructureMismatch_elim___redArg(lean_object* v_t_175_, lean_object* v_reparseStructureMismatch_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_175_, v_reparseStructureMismatch_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseStructureMismatch_elim(lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_reparseStructureMismatch_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_179_, v_reparseStructureMismatch_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_taintedFormatting_elim___redArg(lean_object* v_t_183_, lean_object* v_taintedFormatting_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_183_, v_taintedFormatting_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_taintedFormatting_elim(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_taintedFormatting_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_187_, v_taintedFormatting_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringFmtError___lam__0(lean_object* v_x_196_){
_start:
{
lean_object* v_msg_197_; 
v_msg_197_ = lean_ctor_get(v_x_196_, 1);
lean_inc_ref(v_msg_197_);
return v_msg_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringFmtError___lam__0___boxed(lean_object* v_x_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Fmt_instToStringFmtError___lam__0(v_x_198_);
lean_dec_ref(v_x_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ref(lean_object* v_x_202_){
_start:
{
lean_object* v_stx_203_; 
v_stx_203_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_stx_203_);
return v_stx_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ref___boxed(lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Fmt_FmtError_ref(v_x_204_);
lean_dec_ref(v_x_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___impl(lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_tag_nat(v_x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___impl___boxed(lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Fmt_Error_ctorIdx___impl(v_x_208_);
lean_dec_ref(v_x_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___redArg(lean_object* v_t_210_, lean_object* v_k_211_){
_start:
{
if (lean_obj_tag(v_t_210_) == 0)
{
uint8_t v_err_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_err_212_ = lean_ctor_get_uint8(v_t_210_, 0);
lean_dec_ref_known(v_t_210_, 0);
v___x_213_ = lean_box(v_err_212_);
v___x_214_ = lean_apply_1(v_k_211_, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v_err_215_; lean_object* v___x_216_; 
v_err_215_ = lean_ctor_get(v_t_210_, 0);
lean_inc_ref(v_err_215_);
lean_dec_ref(v_t_210_);
v___x_216_ = lean_apply_1(v_k_211_, v_err_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim(lean_object* v_motive_217_, lean_object* v_ctorIdx_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_219_, v_k_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___boxed(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Fmt_Error_ctorElim(v_motive_223_, v_ctorIdx_224_, v_t_225_, v_h_226_, v_k_227_);
lean_dec(v_ctorIdx_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_internal_elim___redArg(lean_object* v_t_229_, lean_object* v_internal_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_229_, v_internal_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_internal_elim(lean_object* v_motive_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_internal_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_233_, v_internal_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_input_elim___redArg(lean_object* v_t_237_, lean_object* v_input_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_237_, v_input_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_input_elim(lean_object* v_motive_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_input_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_241_, v_input_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_elaboration_elim___redArg(lean_object* v_t_245_, lean_object* v_elaboration_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_245_, v_elaboration_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_elaboration_elim(lean_object* v_motive_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_elaboration_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_249_, v_elaboration_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_fmt_elim___redArg(lean_object* v_t_253_, lean_object* v_fmt_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_253_, v_fmt_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_fmt_elim(lean_object* v_motive_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_fmt_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_257_, v_fmt_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0(lean_object* v_x_267_){
_start:
{
switch(lean_obj_tag(v_x_267_))
{
case 0:
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Lean_Fmt_instToStringError___lam__0___closed__0));
return v___x_268_;
}
case 1:
{
lean_object* v_err_269_; 
v_err_269_ = lean_ctor_get(v_x_267_, 0);
if (lean_obj_tag(v_err_269_) == 0)
{
lean_object* v_msg_270_; 
v_msg_270_ = lean_ctor_get(v_err_269_, 0);
lean_inc_ref(v_msg_270_);
return v_msg_270_;
}
else
{
lean_object* v_msg_271_; 
v_msg_271_ = lean_ctor_get(v_err_269_, 1);
lean_inc_ref(v_msg_271_);
return v_msg_271_;
}
}
case 2:
{
lean_object* v_err_272_; lean_object* v_msg_273_; 
v_err_272_ = lean_ctor_get(v_x_267_, 0);
v_msg_273_ = lean_ctor_get(v_err_272_, 2);
lean_inc_ref(v_msg_273_);
return v_msg_273_;
}
default: 
{
lean_object* v_err_274_; lean_object* v_msg_275_; 
v_err_274_ = lean_ctor_get(v_x_267_, 0);
v_msg_275_ = lean_ctor_get(v_err_274_, 1);
lean_inc_ref(v_msg_275_);
return v_msg_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0___boxed(lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Fmt_instToStringError___lam__0(v_x_276_);
lean_dec_ref(v_x_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ref_x3f(lean_object* v_x_280_){
_start:
{
switch(lean_obj_tag(v_x_280_))
{
case 0:
{
lean_object* v___x_281_; 
lean_dec_ref_known(v_x_280_, 0);
v___x_281_ = lean_box(0);
return v___x_281_;
}
case 1:
{
lean_object* v_err_282_; lean_object* v___x_283_; 
v_err_282_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_err_282_);
lean_dec_ref_known(v_x_280_, 1);
v___x_283_ = l_Lean_Fmt_InputError_ref_x3f(v_err_282_);
lean_dec_ref(v_err_282_);
return v___x_283_;
}
default: 
{
lean_object* v_err_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v_err_284_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_292_ == 0)
{
v___x_286_ = v_x_280_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_err_284_);
lean_dec(v_x_280_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_stx_288_; lean_object* v___x_290_; 
v_stx_288_ = lean_ctor_get(v_err_284_, 0);
lean_inc(v_stx_288_);
lean_dec_ref(v_err_284_);
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 1);
lean_ctor_set(v___x_286_, 0, v_stx_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_stx_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError(lean_object* v_stx_295_, uint8_t v_x_296_){
_start:
{
if (v_x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = ((lean_object*)(l_Lean_Fmt_Error_ofFormattingError___closed__0));
v___x_298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_298_, 0, v_stx_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((lean_object*)(l_Lean_Fmt_Error_ofFormattingError___closed__1));
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_stx_295_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError___boxed(lean_object* v_stx_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_x_30__boxed_305_; lean_object* v_res_306_; 
v_x_30__boxed_305_ = lean_unbox(v_x_304_);
v_res_306_ = l_Lean_Fmt_Error_ofFormattingError(v_stx_303_, v_x_30__boxed_305_);
return v_res_306_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Core_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedInternalError_default = _init_l_Lean_Fmt_instInhabitedInternalError_default();
l_Lean_Fmt_instInhabitedInternalError = _init_l_Lean_Fmt_instInhabitedInternalError();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Core_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Error(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Error(builtin);
}
#ifdef __cplusplus
}
#endif
