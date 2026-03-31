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
lean_object* l_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Lake_Reservoir_lakeHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "X-Reservoir-Api-Version:1.0.0"};
static const lean_object* l_Lake_Reservoir_lakeHeaders___closed__0 = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__0_value;
static const lean_string_object l_Lake_Reservoir_lakeHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "X-Lake-Registry-Api-Version:0.1.0"};
static const lean_object* l_Lake_Reservoir_lakeHeaders___closed__1 = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__1_value;
static const lean_array_object l_Lake_Reservoir_lakeHeaders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__0_value),((lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__1_value)}};
static const lean_object* l_Lake_Reservoir_lakeHeaders___closed__2 = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_Reservoir_lakeHeaders = (const lean_object*)&l_Lake_Reservoir_lakeHeaders___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg(lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(0u);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(1u);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___redArg___boxed(lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_13_);
lean_dec_ref(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx(lean_object* v_00_u03b1_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorIdx___boxed(lean_object* v_00_u03b1_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_ReservoirResp_ctorIdx(v_00_u03b1_18_, v_x_19_);
lean_dec_ref(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___redArg(lean_object* v_t_21_, lean_object* v_k_22_){
_start:
{
if (lean_obj_tag(v_t_21_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_23_ = lean_ctor_get(v_t_21_, 0);
lean_inc(v_a_23_);
lean_dec_ref(v_t_21_);
v___x_24_ = lean_apply_1(v_k_22_, v_a_23_);
return v___x_24_;
}
else
{
lean_object* v_status_25_; lean_object* v_message_26_; lean_object* v___x_27_; 
v_status_25_ = lean_ctor_get(v_t_21_, 0);
lean_inc(v_status_25_);
v_message_26_ = lean_ctor_get(v_t_21_, 1);
lean_inc_ref(v_message_26_);
lean_dec_ref(v_t_21_);
v___x_27_ = lean_apply_2(v_k_22_, v_status_25_, v_message_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim(lean_object* v_00_u03b1_28_, lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_31_, v_k_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_ctorElim___boxed(lean_object* v_00_u03b1_35_, lean_object* v_motive_36_, lean_object* v_ctorIdx_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_k_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lake_ReservoirResp_ctorElim(v_00_u03b1_35_, v_motive_36_, v_ctorIdx_37_, v_t_38_, v_h_39_, v_k_40_);
lean_dec(v_ctorIdx_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim___redArg(lean_object* v_t_42_, lean_object* v_data_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_42_, v_data_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_data_elim(lean_object* v_00_u03b1_45_, lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_data_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_47_, v_data_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim___redArg(lean_object* v_t_51_, lean_object* v_error_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_51_, v_error_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_error_elim(lean_object* v_00_u03b1_54_, lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_error_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_56_, v_error_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___redArg(lean_object* v_inst_76_, lean_object* v_val_77_){
_start:
{
lean_object* v_a_79_; lean_object* v___x_123_; 
lean_inc(v_val_77_);
v___x_123_ = l_Lean_Json_getObj_x3f(v_val_77_);
if (lean_obj_tag(v___x_123_) == 1)
{
lean_object* v_a_124_; lean_object* v___f_125_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref(v___x_123_);
v___f_125_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0));
v___x_150_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3));
v___x_151_ = l_Lake_JsonObject_getJson_x3f(v_a_124_, v___x_150_);
if (lean_obj_tag(v___x_151_) == 0)
{
goto v___jp_126_;
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_val_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_val_152_);
lean_dec_ref(v___x_151_);
v___x_153_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4));
v___x_154_ = l_Option_fromJson_x3f___redArg(v___x_153_, v_val_152_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_a_124_);
lean_dec(v_val_77_);
lean_dec_ref(v_inst_76_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5));
v___x_160_ = lean_string_append(v___x_159_, v_a_155_);
lean_dec(v_a_155_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_124_);
lean_dec(v_val_77_);
lean_dec_ref(v_inst_76_);
v_a_165_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_154_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_154_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 0);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v_a_173_; 
v_a_173_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_173_);
lean_dec_ref(v___x_154_);
if (lean_obj_tag(v_a_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_a_124_);
lean_dec(v_val_77_);
lean_dec_ref(v_inst_76_);
v_val_174_ = lean_ctor_get(v_a_173_, 0);
lean_inc(v_val_174_);
lean_dec_ref(v_a_173_);
v___x_175_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6));
v___x_176_ = l_Lake_JsonObject_getJson_x3f(v_val_174_, v___x_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; 
lean_dec(v_val_174_);
v___x_177_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8));
return v___x_177_;
}
else
{
lean_object* v_val_178_; lean_object* v___x_179_; 
v_val_178_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_val_178_);
lean_dec_ref(v___x_176_);
v___x_179_ = l_Lean_Json_getNat_x3f(v_val_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_val_174_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_189_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9));
v___x_185_ = lean_string_append(v___x_184_, v_a_180_);
lean_dec(v_a_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_val_174_);
v_a_190_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_179_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_179_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 0);
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_a_198_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_179_);
v___x_199_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10));
v___x_200_ = l_Lake_JsonObject_getJson_x3f(v_val_174_, v___x_199_);
lean_dec(v_val_174_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
lean_dec(v_a_198_);
v___x_201_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12));
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_202_);
lean_dec_ref(v___x_200_);
v___x_203_ = l_Lean_Json_getStr_x3f(v_val_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_198_);
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13));
v___x_209_ = lean_string_append(v___x_208_, v_a_204_);
lean_dec(v_a_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_209_);
v___x_211_ = v___x_206_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_198_);
v_a_214_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_203_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_203_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set_tag(v___x_216_, 0);
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_a_222_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_203_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_203_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_198_);
lean_ctor_set(v___x_226_, 1, v_a_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
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
lean_dec(v_a_173_);
goto v___jp_126_;
}
}
}
}
v___jp_126_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1));
v___x_128_ = l_Lake_JsonObject_getJson_x3f(v_a_124_, v___x_127_);
lean_dec(v_a_124_);
if (lean_obj_tag(v___x_128_) == 0)
{
v_a_79_ = v___x_128_;
goto v___jp_78_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; 
v_val_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_val_129_);
lean_dec_ref(v___x_128_);
v___x_130_ = l_Option_fromJson_x3f___redArg(v___f_125_, v_val_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_val_77_);
lean_dec_ref(v_inst_76_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_140_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_140_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_140_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2));
v___x_136_ = lean_string_append(v___x_135_, v_a_131_);
lean_dec(v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_136_);
v___x_138_ = v___x_133_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_val_77_);
lean_dec_ref(v_inst_76_);
v_a_141_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_130_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_130_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 0);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; 
v_a_149_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_149_);
lean_dec_ref(v___x_130_);
v_a_79_ = v_a_149_;
goto v___jp_78_;
}
}
}
}
}
else
{
lean_object* v___x_231_; 
lean_dec_ref(v___x_123_);
v___x_231_ = lean_apply_1(v_inst_76_, v_val_77_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_a_240_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_248_ == 0)
{
v___x_242_ = v___x_231_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_231_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v_a_240_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
v___jp_78_:
{
if (lean_obj_tag(v_a_79_) == 1)
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_104_; 
lean_dec(v_val_77_);
v_val_80_ = lean_ctor_get(v_a_79_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_a_79_);
if (v_isSharedCheck_104_ == 0)
{
v___x_82_ = v_a_79_;
v_isShared_83_ = v_isSharedCheck_104_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v_a_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_104_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_1(v_inst_76_, v_val_80_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
lean_del_object(v___x_82_);
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_103_; 
v_a_93_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_103_ == 0)
{
v___x_95_ = v___x_84_;
v_isShared_96_ = v_isSharedCheck_103_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_84_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_103_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 0);
lean_ctor_set(v___x_82_, 0, v_a_93_);
v___x_98_ = v___x_82_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_102_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
else
{
lean_object* v___x_105_; 
lean_dec(v_a_79_);
v___x_105_ = lean_apply_1(v_inst_76_, v_val_77_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
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
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_a_114_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v___x_105_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_105_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v_a_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f(lean_object* v_00_u03b1_249_, lean_object* v_inst_250_, lean_object* v_val_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lake_ReservoirResp_fromJson_x3f___redArg(v_inst_250_, v_val_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp___redArg(lean_object* v_inst_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_254_, 0, lean_box(0));
lean_closure_set(v___x_254_, 1, v_inst_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonReservoirResp(lean_object* v_00_u03b1_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_closure((void*)(l_Lake_ReservoirResp_fromJson_x3f), 3, 2);
lean_closure_set(v___x_257_, 0, lean_box(0));
lean_closure_set(v___x_257_, 1, v_inst_256_);
return v___x_257_;
}
}
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Reservoir(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
