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
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_malformedInputSyntax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_malformedInputSyntax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ambiguousChoiceNode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ambiguousChoiceNode_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorIdx___impl(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_tag_nat(v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorIdx___impl___boxed(lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Fmt_ElaborationError_ctorIdx___impl(v_x_117_);
lean_dec_ref(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorElim___redArg(lean_object* v_t_119_, lean_object* v_k_120_){
_start:
{
if (lean_obj_tag(v_t_119_) == 0)
{
lean_object* v_stx_121_; lean_object* v_reason_122_; lean_object* v_msg_123_; lean_object* v___x_124_; 
v_stx_121_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_stx_121_);
v_reason_122_ = lean_ctor_get(v_t_119_, 1);
lean_inc_ref(v_reason_122_);
v_msg_123_ = lean_ctor_get(v_t_119_, 2);
lean_inc_ref(v_msg_123_);
lean_dec_ref_known(v_t_119_, 3);
v___x_124_ = lean_apply_3(v_k_120_, v_stx_121_, v_reason_122_, v_msg_123_);
return v___x_124_;
}
else
{
lean_object* v_stx_125_; lean_object* v_msg_126_; lean_object* v___x_127_; 
v_stx_125_ = lean_ctor_get(v_t_119_, 0);
lean_inc(v_stx_125_);
v_msg_126_ = lean_ctor_get(v_t_119_, 1);
lean_inc_ref(v_msg_126_);
lean_dec_ref_known(v_t_119_, 2);
v___x_127_ = lean_apply_2(v_k_120_, v_stx_125_, v_msg_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorElim(lean_object* v_motive_128_, lean_object* v_ctorIdx_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_k_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Fmt_ElaborationError_ctorElim___redArg(v_t_130_, v_k_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ctorElim___boxed(lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Fmt_ElaborationError_ctorElim(v_motive_134_, v_ctorIdx_135_, v_t_136_, v_h_137_, v_k_138_);
lean_dec(v_ctorIdx_135_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_malformedInputSyntax_elim___redArg(lean_object* v_t_140_, lean_object* v_malformedInputSyntax_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Fmt_ElaborationError_ctorElim___redArg(v_t_140_, v_malformedInputSyntax_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_malformedInputSyntax_elim(lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_malformedInputSyntax_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Fmt_ElaborationError_ctorElim___redArg(v_t_144_, v_malformedInputSyntax_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ambiguousChoiceNode_elim___redArg(lean_object* v_t_148_, lean_object* v_ambiguousChoiceNode_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Fmt_ElaborationError_ctorElim___redArg(v_t_148_, v_ambiguousChoiceNode_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ambiguousChoiceNode_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_ambiguousChoiceNode_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Fmt_ElaborationError_ctorElim___redArg(v_t_152_, v_ambiguousChoiceNode_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringElaborationError___lam__0(lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v_msg_162_; 
v_msg_162_ = lean_ctor_get(v_x_161_, 2);
lean_inc_ref(v_msg_162_);
return v_msg_162_;
}
else
{
lean_object* v_msg_163_; 
v_msg_163_ = lean_ctor_get(v_x_161_, 1);
lean_inc_ref(v_msg_163_);
return v_msg_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringElaborationError___lam__0___boxed(lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Fmt_instToStringElaborationError___lam__0(v_x_164_);
lean_dec_ref(v_x_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ref(lean_object* v_x_168_){
_start:
{
lean_object* v_stx_169_; 
v_stx_169_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_stx_169_);
return v_stx_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_ElaborationError_ref___boxed(lean_object* v_x_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Fmt_ElaborationError_ref(v_x_170_);
lean_dec_ref(v_x_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorIdx___impl(lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_tag_nat(v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorIdx___impl___boxed(lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Fmt_FmtError_ctorIdx___impl(v_x_174_);
lean_dec_ref(v_x_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim___redArg(lean_object* v_t_176_, lean_object* v_k_177_){
_start:
{
lean_object* v_stx_178_; lean_object* v_msg_179_; lean_object* v___x_180_; 
v_stx_178_ = lean_ctor_get(v_t_176_, 0);
lean_inc(v_stx_178_);
v_msg_179_ = lean_ctor_get(v_t_176_, 1);
lean_inc_ref(v_msg_179_);
lean_dec_ref(v_t_176_);
v___x_180_ = lean_apply_2(v_k_177_, v_stx_178_, v_msg_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim(lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ctorElim___boxed(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Fmt_FmtError_ctorElim(v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_formattingFailure_elim___redArg(lean_object* v_t_193_, lean_object* v_formattingFailure_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_193_, v_formattingFailure_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_formattingFailure_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_formattingFailure_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_197_, v_formattingFailure_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseFailure_elim___redArg(lean_object* v_t_201_, lean_object* v_reparseFailure_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_201_, v_reparseFailure_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_reparseFailure_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_reparseFailure_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_205_, v_reparseFailure_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_taintedFormatting_elim___redArg(lean_object* v_t_209_, lean_object* v_taintedFormatting_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_209_, v_taintedFormatting_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_taintedFormatting_elim(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_taintedFormatting_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Fmt_FmtError_ctorElim___redArg(v_t_213_, v_taintedFormatting_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringFmtError___lam__0(lean_object* v_x_222_){
_start:
{
lean_object* v_msg_223_; 
v_msg_223_ = lean_ctor_get(v_x_222_, 1);
lean_inc_ref(v_msg_223_);
return v_msg_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringFmtError___lam__0___boxed(lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Fmt_instToStringFmtError___lam__0(v_x_224_);
lean_dec_ref(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ref(lean_object* v_x_228_){
_start:
{
lean_object* v_stx_229_; 
v_stx_229_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_stx_229_);
return v_stx_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FmtError_ref___boxed(lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Fmt_FmtError_ref(v_x_230_);
lean_dec_ref(v_x_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___impl(lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_tag_nat(v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorIdx___impl___boxed(lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Fmt_Error_ctorIdx___impl(v_x_234_);
lean_dec_ref(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___redArg(lean_object* v_t_236_, lean_object* v_k_237_){
_start:
{
if (lean_obj_tag(v_t_236_) == 0)
{
uint8_t v_err_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_err_238_ = lean_ctor_get_uint8(v_t_236_, 0);
lean_dec_ref_known(v_t_236_, 0);
v___x_239_ = lean_box(v_err_238_);
v___x_240_ = lean_apply_1(v_k_237_, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v_err_241_; lean_object* v___x_242_; 
v_err_241_ = lean_ctor_get(v_t_236_, 0);
lean_inc_ref(v_err_241_);
lean_dec_ref(v_t_236_);
v___x_242_ = lean_apply_1(v_k_237_, v_err_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_245_, v_k_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ctorElim___boxed(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Fmt_Error_ctorElim(v_motive_249_, v_ctorIdx_250_, v_t_251_, v_h_252_, v_k_253_);
lean_dec(v_ctorIdx_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_internal_elim___redArg(lean_object* v_t_255_, lean_object* v_internal_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_255_, v_internal_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_internal_elim(lean_object* v_motive_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_internal_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_259_, v_internal_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_input_elim___redArg(lean_object* v_t_263_, lean_object* v_input_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_263_, v_input_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_input_elim(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_input_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_267_, v_input_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_elaboration_elim___redArg(lean_object* v_t_271_, lean_object* v_elaboration_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_271_, v_elaboration_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_elaboration_elim(lean_object* v_motive_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_elaboration_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_275_, v_elaboration_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_fmt_elim___redArg(lean_object* v_t_279_, lean_object* v_fmt_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_279_, v_fmt_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_fmt_elim(lean_object* v_motive_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_fmt_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Fmt_Error_ctorElim___redArg(v_t_283_, v_fmt_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0(lean_object* v_x_293_){
_start:
{
switch(lean_obj_tag(v_x_293_))
{
case 0:
{
lean_object* v___x_294_; 
v___x_294_ = ((lean_object*)(l_Lean_Fmt_instToStringError___lam__0___closed__0));
return v___x_294_;
}
case 1:
{
lean_object* v_err_295_; 
v_err_295_ = lean_ctor_get(v_x_293_, 0);
if (lean_obj_tag(v_err_295_) == 0)
{
lean_object* v_msg_296_; 
v_msg_296_ = lean_ctor_get(v_err_295_, 0);
lean_inc_ref(v_msg_296_);
return v_msg_296_;
}
else
{
lean_object* v_msg_297_; 
v_msg_297_ = lean_ctor_get(v_err_295_, 1);
lean_inc_ref(v_msg_297_);
return v_msg_297_;
}
}
case 2:
{
lean_object* v_err_298_; 
v_err_298_ = lean_ctor_get(v_x_293_, 0);
if (lean_obj_tag(v_err_298_) == 0)
{
lean_object* v_msg_299_; 
v_msg_299_ = lean_ctor_get(v_err_298_, 2);
lean_inc_ref(v_msg_299_);
return v_msg_299_;
}
else
{
lean_object* v_msg_300_; 
v_msg_300_ = lean_ctor_get(v_err_298_, 1);
lean_inc_ref(v_msg_300_);
return v_msg_300_;
}
}
default: 
{
lean_object* v_err_301_; lean_object* v_msg_302_; 
v_err_301_ = lean_ctor_get(v_x_293_, 0);
v_msg_302_ = lean_ctor_get(v_err_301_, 1);
lean_inc_ref(v_msg_302_);
return v_msg_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringError___lam__0___boxed(lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Fmt_instToStringError___lam__0(v_x_303_);
lean_dec_ref(v_x_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ref_x3f(lean_object* v_x_307_){
_start:
{
switch(lean_obj_tag(v_x_307_))
{
case 0:
{
lean_object* v___x_308_; 
lean_dec_ref_known(v_x_307_, 0);
v___x_308_ = lean_box(0);
return v___x_308_;
}
case 1:
{
lean_object* v_err_309_; lean_object* v___x_310_; 
v_err_309_ = lean_ctor_get(v_x_307_, 0);
lean_inc_ref(v_err_309_);
lean_dec_ref_known(v_x_307_, 1);
v___x_310_ = l_Lean_Fmt_InputError_ref_x3f(v_err_309_);
lean_dec_ref(v_err_309_);
return v___x_310_;
}
default: 
{
lean_object* v_err_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_err_311_ = lean_ctor_get(v_x_307_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v_x_307_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_err_311_);
lean_dec(v_x_307_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_stx_315_; lean_object* v___x_317_; 
v_stx_315_ = lean_ctor_get(v_err_311_, 0);
lean_inc(v_stx_315_);
lean_dec_ref(v_err_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 1);
lean_ctor_set(v___x_313_, 0, v_stx_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_stx_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError(lean_object* v_stx_322_, uint8_t v_x_323_){
_start:
{
if (v_x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((lean_object*)(l_Lean_Fmt_Error_ofFormattingError___closed__0));
v___x_325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_325_, 0, v_stx_322_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((lean_object*)(l_Lean_Fmt_Error_ofFormattingError___closed__1));
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_stx_322_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Error_ofFormattingError___boxed(lean_object* v_stx_330_, lean_object* v_x_331_){
_start:
{
uint8_t v_x_30__boxed_332_; lean_object* v_res_333_; 
v_x_30__boxed_332_ = lean_unbox(v_x_331_);
v_res_333_ = l_Lean_Fmt_Error_ofFormattingError(v_stx_330_, v_x_30__boxed_332_);
return v_res_333_;
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
