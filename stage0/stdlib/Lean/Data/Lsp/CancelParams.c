// Lean compiler output
// Module: Lean.Data.Lsp.CancelParams
// Imports: public import Lean.Data.JsonRpc
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
uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedCancelParams_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedCancelParams;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqCancelParams_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqCancelParams_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqCancelParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqCancelParams_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqCancelParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqCancelParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqCancelParams = (const lean_object*)&l_Lean_Lsp_instBEqCancelParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0_value;
static const lean_array_object l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCancelParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonCancelParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonCancelParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonCancelParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCancelParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonCancelParams = (const lean_object*)&l_Lean_Lsp_instToJsonCancelParams___closed__0_value;
static const lean_string_object l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "a request id needs to be a number or a string"};
static const lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0 = (const lean_object*)&l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0_value)}};
static const lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1 = (const lean_object*)&l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CancelParams"};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 166, 156, 47, 233, 242, 65, 233)}};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonCancelParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonCancelParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonCancelParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonCancelParams = (const lean_object*)&l_Lean_Lsp_instFromJsonCancelParams___closed__0_value;
static lean_object* _init_l_Lean_Lsp_instInhabitedCancelParams_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_JsonRpc_instInhabitedRequestID_default;
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedCancelParams(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Lean_JsonRpc_instInhabitedRequestID_default;
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqCancelParams_beq(lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqCancelParams_beq___boxed(lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Lsp_instBEqCancelParams_beq(v_x_6_, v_x_7_);
lean_dec(v_x_7_);
lean_dec(v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
if (lean_obj_tag(v_a_12_) == 0)
{
lean_object* v___x_14_; 
v___x_14_ = lean_array_to_list(v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_head_15_; lean_object* v_tail_16_; lean_object* v___x_17_; 
v_head_15_ = lean_ctor_get(v_a_12_, 0);
lean_inc(v_head_15_);
v_tail_16_ = lean_ctor_get(v_a_12_, 1);
lean_inc(v_tail_16_);
lean_dec_ref(v_a_12_);
v___x_17_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_13_, v_head_15_);
v_a_12_ = v_tail_16_;
v_a_13_ = v___x_17_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCancelParams_toJson(lean_object* v_x_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___y_25_; 
v___x_23_ = ((lean_object*)(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0));
switch(lean_obj_tag(v_x_22_))
{
case 0:
{
lean_object* v_s_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
v_s_33_ = lean_ctor_get(v_x_22_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v_x_22_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_s_33_);
lean_dec(v_x_22_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 3);
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_s_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
v___y_25_ = v___x_38_;
goto v___jp_24_;
}
}
}
case 1:
{
lean_object* v_n_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_n_41_ = lean_ctor_get(v_x_22_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v_x_22_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_n_41_);
lean_dec(v_x_22_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set_tag(v___x_43_, 2);
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_n_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
v___y_25_ = v___x_46_;
goto v___jp_24_;
}
}
}
default: 
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
v___y_25_ = v___x_49_;
goto v___jp_24_;
}
}
v___jp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_23_);
lean_ctor_set(v___x_26_, 1, v___y_25_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
v___x_30_ = ((lean_object*)(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1));
v___x_31_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(v___x_29_, v___x_30_);
v___x_32_ = l_Lean_Json_mkObj(v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(lean_object* v_j_55_, lean_object* v_k_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Json_getObjValD(v_j_55_, v_k_56_);
switch(lean_obj_tag(v___x_57_))
{
case 3:
{
lean_object* v_s_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_66_; 
v_s_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_66_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_s_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 0);
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_s_58_);
v___x_63_ = v_reuseFailAlloc_65_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; 
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
}
case 2:
{
lean_object* v_n_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_n_67_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v___x_57_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_n_67_);
lean_dec(v___x_57_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 1);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_n_67_);
v___x_72_ = v_reuseFailAlloc_74_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
}
default: 
{
lean_object* v___x_76_; 
lean_dec(v___x_57_);
v___x_76_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1));
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___boxed(lean_object* v_j_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(v_j_77_, v_k_78_);
lean_dec_ref(v_k_78_);
return v_res_79_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4(void){
_start:
{
uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = 1;
v___x_88_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3));
v___x_89_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5));
v___x_92_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4);
v___x_93_ = lean_string_append(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = 1;
v___x_97_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7));
v___x_98_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8);
v___x_100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6);
v___x_101_ = lean_string_append(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10));
v___x_104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9);
v___x_105_ = lean_string_append(v___x_104_, v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson(lean_object* v_json_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0));
v___x_108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(v_json_106_, v___x_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_118_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_118_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11);
v___x_114_ = lean_string_append(v___x_113_, v_a_109_);
lean_dec(v_a_109_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_108_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_108_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 0);
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_a_127_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_108_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_108_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_CancelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedCancelParams_default = _init_l_Lean_Lsp_instInhabitedCancelParams_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedCancelParams_default);
l_Lean_Lsp_instInhabitedCancelParams = _init_l_Lean_Lsp_instInhabitedCancelParams();
lean_mark_persistent(l_Lean_Lsp_instInhabitedCancelParams);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_CancelParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_CancelParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_CancelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_CancelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_CancelParams(builtin);
}
#ifdef __cplusplus
}
#endif
