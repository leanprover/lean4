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
lean_object* v___x_96_; 
lean_inc(v_val_76_);
v___x_96_ = l_Lean_Json_getObj_x3f(v_val_76_);
if (lean_obj_tag(v___x_96_) == 1)
{
lean_object* v_a_97_; lean_object* v___f_98_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_96_, 1);
v___f_98_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0));
v___x_140_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3));
v___x_141_ = l_Lake_JsonObject_getJson_x3f(v_a_97_, v___x_140_);
if (lean_obj_tag(v___x_141_) == 0)
{
goto v___jp_99_;
}
else
{
lean_object* v_val_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_val_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v___x_141_, 1);
v___x_143_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4));
v___x_144_ = l_Lean_Option_fromJson_x3f___redArg(v___x_143_, v_val_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_a_97_);
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_154_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_149_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5));
v___x_150_ = lean_string_append(v___x_149_, v_a_145_);
lean_dec(v_a_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_150_);
v___x_152_ = v___x_147_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v_a_155_; 
v_a_155_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_144_, 1);
if (lean_obj_tag(v_a_155_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_a_97_);
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_val_156_ = lean_ctor_get(v_a_155_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v_a_155_, 1);
v___x_157_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6));
v___x_158_ = l_Lake_JsonObject_getJson_x3f(v_val_156_, v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_val_156_);
v___x_159_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8));
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_161_; 
v_val_160_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v___x_158_, 1);
v___x_161_ = l_Lean_Json_getNat_x3f(v_val_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_val_156_);
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_171_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9));
v___x_167_ = lean_string_append(v___x_166_, v_a_162_);
lean_dec(v_a_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_167_);
v___x_169_ = v___x_164_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
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
lean_object* v_a_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_a_172_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_161_, 1);
v___x_173_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10));
v___x_174_ = l_Lake_JsonObject_getJson_x3f(v_val_156_, v___x_173_);
lean_dec(v_val_156_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v___x_175_; 
lean_dec(v_a_172_);
v___x_175_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12));
return v___x_175_;
}
else
{
lean_object* v_val_176_; lean_object* v___x_177_; 
v_val_176_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_174_, 1);
v___x_177_ = l_Lean_Json_getStr_x3f(v_val_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_a_172_);
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13));
v___x_183_ = lean_string_append(v___x_182_, v_a_178_);
lean_dec(v_a_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v_a_188_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_196_ == 0)
{
v___x_190_ = v___x_177_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_177_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v_a_172_);
lean_ctor_set(v___x_192_, 1, v_a_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_155_);
goto v___jp_99_;
}
}
}
v___jp_99_:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1));
v___x_101_ = l_Lake_JsonObject_getJson_x3f(v_a_97_, v___x_100_);
lean_dec(v_a_97_);
if (lean_obj_tag(v___x_101_) == 0)
{
goto v___jp_77_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; 
v_val_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = l_Lean_Option_fromJson_x3f___redArg(v___f_98_, v_val_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_113_; 
lean_dec(v_val_76_);
lean_dec_ref(v_inst_75_);
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_113_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2));
v___x_109_ = lean_string_append(v___x_108_, v_a_104_);
lean_dec(v_a_104_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; 
v_a_114_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_103_, 1);
if (lean_obj_tag(v_a_114_) == 1)
{
lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_139_; 
lean_dec(v_val_76_);
v_val_115_ = lean_ctor_get(v_a_114_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_139_ == 0)
{
v___x_117_ = v_a_114_;
v_isShared_118_ = v_isSharedCheck_139_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v_a_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_139_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_apply_1(v_inst_75_, v_val_115_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_del_object(v___x_117_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
v_a_128_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_138_ == 0)
{
v___x_130_ = v___x_119_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_119_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 0);
lean_ctor_set(v___x_117_, 0, v_a_128_);
v___x_133_ = v___x_117_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_133_);
v___x_135_ = v___x_130_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
else
{
lean_dec(v_a_114_);
goto v___jp_77_;
}
}
}
}
}
else
{
lean_object* v___x_197_; 
lean_dec_ref(v___x_96_);
v___x_197_ = lean_apply_1(v_inst_75_, v_val_76_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_214_; 
v_a_206_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_214_ == 0)
{
v___x_208_ = v___x_197_;
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_197_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_a_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_210_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
v___jp_77_:
{
lean_object* v___x_78_; 
v___x_78_ = lean_apply_1(v_inst_75_, v_val_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_a_87_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_val_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lake_ReservoirResp_fromJson_x3f___redArg(v_inst_216_, v_val_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object* v_inst_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_220_, 0, lean_box(0));
lean_closure_set(v___x_220_, 1, v_inst_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object* v_00_u03b1_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, v_inst_222_);
return v___x_223_;
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
