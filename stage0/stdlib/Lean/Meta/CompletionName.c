// Lean compiler output
// Module: Lean.Meta.CompletionName
// Imports: public import Lean.Meta.Match.MatcherInfo
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
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Lean_privateHeader;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "completionBlackListExt"};
static const lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 136, 117, 241, 251, 167, 79, 178)}};
static const lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_completionBlackListExt;
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; 
v___x_9_ = ((lean_object*)(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_));
v___x_10_ = lean_box(2);
v___x_11_ = 0;
v___x_12_ = l_Lean_mkTagDeclarationExtension(v___x_9_, v___x_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_13_;
v_res_13_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2____boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object* v_env_16_, lean_object* v_declName_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = l_Lean_Meta_completionBlackListExt;
v___x_19_ = l_Lean_TagDeclarationExtension_tag(v___x_18_, v_env_16_, v_declName_17_);
return v___x_19_;
}
}
uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object* v_x_20_){
_start:
{
switch(lean_obj_tag(v_x_20_))
{
case 1:
{
lean_object* v_pre_21_; lean_object* v_str_22_; uint32_t v___y_24_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_pre_21_ = lean_ctor_get(v_x_20_, 0);
v_str_22_ = lean_ctor_get(v_x_20_, 1);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_string_utf8_byte_size(v_str_22_);
lean_inc_ref(v_str_22_);
v___x_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_33_, 0, v_str_22_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
v___x_34_ = l_String_Slice_Pos_get_x3f(v___x_33_, v___x_31_);
lean_dec_ref_known(v___x_33_, 3);
if (lean_obj_tag(v___x_34_) == 0)
{
uint32_t v___x_35_; 
v___x_35_ = 65;
v___y_24_ = v___x_35_;
goto v___jp_23_;
}
else
{
lean_object* v_val_36_; uint32_t v___x_37_; 
v_val_36_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_36_);
lean_dec_ref_known(v___x_34_, 1);
v___x_37_ = lean_unbox_uint32(v_val_36_);
lean_dec(v_val_36_);
v___y_24_ = v___x_37_;
goto v___jp_23_;
}
v___jp_23_:
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 95;
v___x_26_ = lean_uint32_dec_eq(v___y_24_, v___x_25_);
if (v___x_26_ == 0)
{
v_x_20_ = v_pre_21_;
goto _start;
}
else
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = l_Lean_privateHeader;
v___x_29_ = lean_name_eq(v_x_20_, v___x_28_);
if (v___x_29_ == 0)
{
return v___x_26_;
}
else
{
v_x_20_ = v_pre_21_;
goto _start;
}
}
}
}
case 2:
{
lean_object* v_pre_38_; 
v_pre_38_ = lean_ctor_get(v_x_20_, 0);
v_x_20_ = v_pre_38_;
goto _start;
}
default: 
{
uint8_t v___x_40_; 
v___x_40_ = 0;
return v___x_40_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_20_ = stack[0].m_obj;
uint8_t v_res_41_;
v_res_41_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(v_x_20_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(v_x_42_);
lean_dec(v_x_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object* v_env_45_, lean_object* v_declName_46_){
_start:
{
uint8_t v___y_48_; uint8_t v___x_56_; 
v___x_56_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(v_declName_46_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
lean_inc(v_declName_46_);
lean_inc_ref(v_env_45_);
v___x_57_ = l_Lean_isAuxRecursor(v_env_45_, v_declName_46_);
v___y_48_ = v___x_57_;
goto v___jp_47_;
}
else
{
v___y_48_ = v___x_56_;
goto v___jp_47_;
}
v___jp_47_:
{
if (v___y_48_ == 0)
{
uint8_t v___x_49_; 
lean_inc(v_declName_46_);
lean_inc_ref(v_env_45_);
v___x_49_ = l_Lean_isNoConfusion(v_env_45_, v_declName_46_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
lean_inc(v_declName_46_);
lean_inc_ref(v_env_45_);
v___x_50_ = l_Lean_isRecCore(v_env_45_, v_declName_46_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v_toEnvExtension_52_; lean_object* v_asyncMode_53_; uint8_t v___x_54_; 
v___x_51_ = l_Lean_Meta_completionBlackListExt;
v_toEnvExtension_52_ = lean_ctor_get(v___x_51_, 0);
v_asyncMode_53_ = lean_ctor_get(v_toEnvExtension_52_, 2);
lean_inc(v_declName_46_);
lean_inc_ref(v_env_45_);
v___x_54_ = l_Lean_TagDeclarationExtension_isTagged(v___x_51_, v_env_45_, v_declName_46_, v_asyncMode_53_);
if (v___x_54_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = l_Lean_Meta_isMatcherCore(v_env_45_, v_declName_46_);
return v___x_55_;
}
else
{
lean_dec(v_declName_46_);
lean_dec_ref(v_env_45_);
return v___x_54_;
}
}
else
{
lean_dec(v_declName_46_);
lean_dec_ref(v_env_45_);
return v___x_50_;
}
}
else
{
lean_dec(v_declName_46_);
lean_dec_ref(v_env_45_);
return v___x_49_;
}
}
else
{
lean_dec(v_declName_46_);
lean_dec_ref(v_env_45_);
return v___y_48_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_45_ = stack[0].m_obj;
lean_object* v_declName_46_ = stack[1].m_obj;
uint8_t v_res_58_;
v_res_58_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(v_env_45_, v_declName_46_);
stack->m_num = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(lean_object* v_env_59_, lean_object* v_declName_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(v_env_59_, v_declName_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
uint8_t l_Lean_Meta_allowCompletion(lean_object* v_env_63_, lean_object* v_declName_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(v_env_63_, v_declName_64_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 1;
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_allowCompletion_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_63_ = stack[0].m_obj;
lean_object* v_declName_64_ = stack[1].m_obj;
uint8_t v_res_68_;
v_res_68_ = l_Lean_Meta_allowCompletion(v_env_63_, v_declName_64_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object* v_env_69_, lean_object* v_declName_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Meta_allowCompletion(v_env_69_, v_declName_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_completionBlackListExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CompletionName(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CompletionName(builtin);
}
#ifdef __cplusplus
}
#endif
