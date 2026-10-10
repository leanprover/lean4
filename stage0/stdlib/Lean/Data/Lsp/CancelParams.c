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
uint8_t l_Lean_Lsp_instBEqCancelParams_beq(lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instBEqCancelParams_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
lean_object* v_x_4_ = stack[1].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Lean_Lsp_instBEqCancelParams_beq(v_x_3_, v_x_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqCancelParams_beq___boxed(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Lean_Lsp_instBEqCancelParams_beq(v_x_7_, v_x_8_);
lean_dec(v_x_8_);
lean_dec(v_x_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
if (lean_obj_tag(v_a_13_) == 0)
{
lean_object* v___x_15_; 
v___x_15_ = lean_array_to_list(v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___x_18_; 
v_head_16_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_tail_17_);
lean_dec_ref_known(v_a_13_, 2);
v___x_18_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_14_, v_head_16_);
v_a_13_ = v_tail_17_;
v_a_14_ = v___x_18_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCancelParams_toJson(lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___y_26_; 
v___x_24_ = ((lean_object*)(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0));
switch(lean_obj_tag(v_x_23_))
{
case 0:
{
lean_object* v_s_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
v_s_34_ = lean_ctor_get(v_x_23_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v_x_23_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_s_34_);
lean_dec(v_x_23_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 3);
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_s_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
v___y_26_ = v___x_39_;
goto v___jp_25_;
}
}
}
case 1:
{
lean_object* v_n_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_n_42_ = lean_ctor_get(v_x_23_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v_x_23_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_n_42_);
lean_dec(v_x_23_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 2);
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_n_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
v___y_26_ = v___x_47_;
goto v___jp_25_;
}
}
}
default: 
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
v___y_26_ = v___x_50_;
goto v___jp_25_;
}
}
v___jp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_24_);
lean_ctor_set(v___x_27_, 1, v___y_26_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
v___x_31_ = ((lean_object*)(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1));
v___x_32_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(v___x_30_, v___x_31_);
v___x_33_ = l_Lean_Json_mkObj(v___x_32_);
lean_dec(v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(lean_object* v_j_56_, lean_object* v_k_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Json_getObjValD(v_j_56_, v_k_57_);
switch(lean_obj_tag(v___x_58_))
{
case 3:
{
lean_object* v_s_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
v_s_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_67_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_s_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 0);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_s_59_);
v___x_64_ = v_reuseFailAlloc_66_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
}
case 2:
{
lean_object* v_n_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_n_68_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v___x_58_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_n_68_);
lean_dec(v___x_58_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set_tag(v___x_70_, 1);
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_n_68_);
v___x_73_ = v_reuseFailAlloc_75_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
default: 
{
lean_object* v___x_77_; 
lean_dec(v___x_58_);
v___x_77_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1));
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___boxed(lean_object* v_j_78_, lean_object* v_k_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(v_j_78_, v_k_79_);
lean_dec_ref(v_k_79_);
return v_res_80_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4(void){
_start:
{
uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = 1;
v___x_89_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3));
v___x_90_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5));
v___x_93_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4);
v___x_94_ = lean_string_append(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = 1;
v___x_98_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7));
v___x_99_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8);
v___x_101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6);
v___x_102_ = lean_string_append(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10));
v___x_105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9);
v___x_106_ = lean_string_append(v___x_105_, v___x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCancelParams_fromJson(lean_object* v_json_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0));
v___x_109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(v_json_107_, v___x_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_119_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_119_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_119_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_119_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11);
v___x_115_ = lean_string_append(v___x_114_, v_a_110_);
lean_dec(v_a_110_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_115_);
v___x_117_ = v___x_112_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_109_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_109_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 0);
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
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
v_a_128_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_109_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_109_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_CancelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
