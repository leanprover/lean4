// Lean compiler output
// Module: Lake.Util.Reservoir
// Imports: public import Lake.Util.JsonObject
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
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Lake_Reservoir_lakeHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "X-Reservoir-Api-Version:1.0.0"};
static const lean_object* l_Lake_Reservoir_lakeHeaders___closed__0 = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__0_value;
static const lean_string_object l_Lake_Reservoir_lakeHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "X-Lake-Registry-Api-Version:0.1.0"};
static const lean_object* l_Lake_Reservoir_lakeHeaders___closed__1 = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__1_value;
static const lean_array_object l_Lake_Reservoir_lakeHeaders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__0_value),((lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__1_value)}};
static const lean_object* l_Lake_Reservoir_lakeHeaders___closed__2 = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_Reservoir_lakeHeaders = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "data: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_JsonObject_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "property not found: status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "status: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "message: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl___redArg(lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_tag_nat(v_x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl___redArg___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lake_ReservoirResp_ctorIdx___impl___redArg(v_x_12_);
lean_dec_ref(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl(lean_object* v_00_u03b1_14_, lean_object* v_x_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_tag_nat(v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___impl___boxed(lean_object* v_00_u03b1_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_ReservoirResp_ctorIdx___impl(v_00_u03b1_17_, v_x_18_);
lean_dec_ref(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___redArg(lean_object* v_t_20_, lean_object* v_k_21_){
_start:
{
if (lean_obj_tag(v_t_20_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_22_ = lean_ctor_get(v_t_20_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v_t_20_, 1);
v___x_23_ = lean_apply_1(v_k_21_, v_a_22_);
return v___x_23_;
}
else
{
lean_object* v_status_24_; lean_object* v_message_25_; lean_object* v___x_26_; 
v_status_24_ = lean_ctor_get(v_t_20_, 0);
lean_inc(v_status_24_);
v_message_25_ = lean_ctor_get(v_t_20_, 1);
lean_inc_ref(v_message_25_);
lean_dec_ref_known(v_t_20_, 2);
v___x_26_ = lean_apply_2(v_k_21_, v_status_24_, v_message_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim(lean_object* v_00_u03b1_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_30_, v_k_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___boxed(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_ReservoirResp_ctorElim(v_00_u03b1_34_, v_motive_35_, v_ctorIdx_36_, v_t_37_, v_h_38_, v_k_39_);
lean_dec(v_ctorIdx_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim___redArg(lean_object* v_t_41_, lean_object* v_data_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_41_, v_data_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_data_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_46_, v_data_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim___redArg(lean_object* v_t_50_, lean_object* v_error_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_50_, v_error_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim(lean_object* v_00_u03b1_53_, lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_error_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_55_, v_error_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object* v_inst_75_, lean_object* v_val_76_){
_start:
{
lean_object* v_a_78_; lean_object* v___x_122_; 
lean_inc(v_val_76_);
v___x_122_ = l_Lean_Json_getObj_x3f(v_val_76_);
if (lean_obj_tag(v___x_122_) == 1)
{
lean_object* v_a_123_; lean_object* v___f_124_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___f_124_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0));
v___x_149_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3));
v___x_150_ = l_Lake_JsonObject_getJson_x3f(v_a_123_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
goto v___jp_125_;
}
else
{
lean_object* v_val_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_val_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4));
v___x_153_ = l_Lean_Option_fromJson_x3f___redArg(v___x_152_, v_val_151_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_123_);
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_163_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_163_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_163_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_158_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5));
v___x_159_ = lean_string_append(v___x_158_, v_a_154_);
lean_dec(v_a_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_159_);
v___x_161_ = v___x_156_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_123_);
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_a_164_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_153_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_153_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set_tag(v___x_166_, 0);
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; 
v_a_172_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_153_, 1);
if (lean_obj_tag(v_a_172_) == 1)
{
lean_object* v_val_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_a_123_);
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_val_173_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_val_173_);
lean_dec_ref_known(v_a_172_, 1);
v___x_174_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6));
v___x_175_ = l_Lake_JsonObject_getJson_x3f(v_val_173_, v___x_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; 
lean_dec(v_val_173_);
v___x_176_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8));
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_175_, 1);
v___x_178_ = l_Lean_Json_getNat_x3f(v_val_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_val_173_);
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_188_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9));
v___x_184_ = lean_string_append(v___x_183_, v_a_179_);
lean_dec(v_a_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_val_173_);
v_a_189_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_178_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_178_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 0);
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_a_197_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_178_, 1);
v___x_198_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10));
v___x_199_ = l_Lake_JsonObject_getJson_x3f(v_val_173_, v___x_198_);
lean_dec(v_val_173_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
lean_dec(v_a_197_);
v___x_200_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12));
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_199_, 1);
v___x_202_ = l_Lean_Json_getStr_x3f(v_val_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_a_197_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_212_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_207_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13));
v___x_208_ = lean_string_append(v___x_207_, v_a_203_);
lean_dec(v_a_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_197_);
v_a_213_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_202_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_202_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 0);
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_a_221_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v___x_202_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_202_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v_a_197_);
lean_ctor_set(v___x_225_, 1, v_a_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v_a_172_);
goto v___jp_125_;
}
}
}
}
v___jp_125_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1));
v___x_127_ = l_Lake_JsonObject_getJson_x3f(v_a_123_, v___x_126_);
lean_dec(v_a_123_);
if (lean_obj_tag(v___x_127_) == 0)
{
v_a_78_ = v___x_127_;
goto v___jp_77_;
}
else
{
lean_object* v_val_128_; lean_object* v___x_129_; 
v_val_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v___x_127_, 1);
v___x_129_ = l_Lean_Option_fromJson_x3f___redArg(v___f_124_, v_val_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_139_; 
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_139_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2));
v___x_135_ = lean_string_append(v___x_134_, v_a_130_);
lean_dec(v_a_130_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_135_);
v___x_137_ = v___x_132_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_a_140_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_129_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_129_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 0);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_148_; 
v_a_148_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_129_, 1);
v_a_78_ = v_a_148_;
goto v___jp_77_;
}
}
}
}
}
else
{
lean_object* v___x_230_; 
lean_dec_ref(v___x_122_);
v___x_230_ = lean_apply_1(v_inst_75_, v_val_76_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_a_239_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v___x_230_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_230_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_a_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
v___jp_77_:
{
if (lean_obj_tag(v_a_78_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_val_76_);
v_val_79_ = lean_ctor_get(v_a_78_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_103_ == 0)
{
v___x_81_ = v_a_78_;
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v_a_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; 
v___x_83_ = lean_apply_1(v_inst_75_, v_val_79_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_del_object(v___x_81_);
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_102_; 
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_102_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_102_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_102_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 0);
lean_ctor_set(v___x_81_, 0, v_a_92_);
v___x_97_ = v___x_81_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_97_);
v___x_99_ = v___x_94_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v_a_78_);
v___x_104_ = lean_apply_1(v_inst_75_, v_val_76_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
v_a_113_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v___x_104_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_104_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_a_113_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_117_);
v___x_119_ = v___x_115_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_val_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lake_ReservoirResp_fromJson_x3f___redArg(v_inst_249_, v_val_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object* v_inst_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_253_, 0, lean_box(0));
lean_closure_set(v___x_253_, 1, v_inst_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_256_, 0, lean_box(0));
lean_closure_set(v___x_256_, 1, v_inst_255_);
return v___x_256_;
}
}
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Reservoir(builtin);
}
#ifdef __cplusplus
}
#endif
