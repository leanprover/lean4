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
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_));
v___x_10_ = lean_box(2);
v___x_11_ = l_Lean_mkTagDeclarationExtension(v___x_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2____boxed(lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object* v_env_14_, lean_object* v_declName_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = l_Lean_Meta_completionBlackListExt;
v___x_17_ = l_Lean_TagDeclarationExtension_tag(v___x_16_, v_env_14_, v_declName_15_);
return v___x_17_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object* v_x_18_){
_start:
{
switch(lean_obj_tag(v_x_18_))
{
case 1:
{
lean_object* v_pre_19_; lean_object* v_str_20_; uint32_t v___y_22_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_pre_19_ = lean_ctor_get(v_x_18_, 0);
v_str_20_ = lean_ctor_get(v_x_18_, 1);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_string_utf8_byte_size(v_str_20_);
lean_inc_ref(v_str_20_);
v___x_31_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_31_, 0, v_str_20_);
lean_ctor_set(v___x_31_, 1, v___x_29_);
lean_ctor_set(v___x_31_, 2, v___x_30_);
v___x_32_ = l_String_Slice_Pos_get_x3f(v___x_31_, v___x_29_);
lean_dec_ref_known(v___x_31_, 3);
if (lean_obj_tag(v___x_32_) == 0)
{
uint32_t v___x_33_; 
v___x_33_ = 65;
v___y_22_ = v___x_33_;
goto v___jp_21_;
}
else
{
lean_object* v_val_34_; uint32_t v___x_35_; 
v_val_34_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v___x_32_, 1);
v___x_35_ = lean_unbox_uint32(v_val_34_);
lean_dec(v_val_34_);
v___y_22_ = v___x_35_;
goto v___jp_21_;
}
v___jp_21_:
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 95;
v___x_24_ = lean_uint32_dec_eq(v___y_22_, v___x_23_);
if (v___x_24_ == 0)
{
v_x_18_ = v_pre_19_;
goto _start;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = l_Lean_privateHeader;
v___x_27_ = lean_name_eq(v_x_18_, v___x_26_);
if (v___x_27_ == 0)
{
return v___x_24_;
}
else
{
v_x_18_ = v_pre_19_;
goto _start;
}
}
}
}
case 2:
{
lean_object* v_pre_36_; 
v_pre_36_ = lean_ctor_get(v_x_18_, 0);
v_x_18_ = v_pre_36_;
goto _start;
}
default: 
{
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object* v_x_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(v_x_39_);
lean_dec(v_x_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object* v_env_42_, lean_object* v_declName_43_){
_start:
{
uint8_t v___y_45_; uint8_t v___x_53_; 
v___x_53_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(v_declName_43_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
lean_inc(v_declName_43_);
lean_inc_ref(v_env_42_);
v___x_54_ = l_Lean_isAuxRecursor(v_env_42_, v_declName_43_);
v___y_45_ = v___x_54_;
goto v___jp_44_;
}
else
{
v___y_45_ = v___x_53_;
goto v___jp_44_;
}
v___jp_44_:
{
if (v___y_45_ == 0)
{
uint8_t v___x_46_; 
lean_inc(v_declName_43_);
lean_inc_ref(v_env_42_);
v___x_46_ = l_Lean_isNoConfusion(v_env_42_, v_declName_43_);
if (v___x_46_ == 0)
{
uint8_t v___x_47_; 
lean_inc(v_declName_43_);
lean_inc_ref(v_env_42_);
v___x_47_ = l_Lean_isRecCore(v_env_42_, v_declName_43_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v_toEnvExtension_49_; lean_object* v_asyncMode_50_; uint8_t v___x_51_; 
v___x_48_ = l_Lean_Meta_completionBlackListExt;
v_toEnvExtension_49_ = lean_ctor_get(v___x_48_, 0);
v_asyncMode_50_ = lean_ctor_get(v_toEnvExtension_49_, 2);
lean_inc(v_declName_43_);
lean_inc_ref(v_env_42_);
v___x_51_ = l_Lean_TagDeclarationExtension_isTagged(v___x_48_, v_env_42_, v_declName_43_, v_asyncMode_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = l_Lean_Meta_isMatcherCore(v_env_42_, v_declName_43_);
return v___x_52_;
}
else
{
lean_dec(v_declName_43_);
lean_dec_ref(v_env_42_);
return v___x_51_;
}
}
else
{
lean_dec(v_declName_43_);
lean_dec_ref(v_env_42_);
return v___x_47_;
}
}
else
{
lean_dec(v_declName_43_);
lean_dec_ref(v_env_42_);
return v___x_46_;
}
}
else
{
lean_dec(v_declName_43_);
lean_dec_ref(v_env_42_);
return v___y_45_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(lean_object* v_env_55_, lean_object* v_declName_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(v_env_55_, v_declName_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object* v_env_59_, lean_object* v_declName_60_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(v_env_59_, v_declName_60_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; 
v___x_62_ = 1;
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object* v_env_64_, lean_object* v_declName_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_Meta_allowCompletion(v_env_64_, v_declName_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
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
