// Lean compiler output
// Module: Lake.Build.ModuleArtifacts
// Imports: public import Lake.Config.Artifact import Lake.Util.JsonObject
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
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_oleanParts(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(lean_object*);
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "l"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__0 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__0_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__1 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__1_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__2 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__2_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__3 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__3_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__4 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__4_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__5 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__5_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__6 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__6_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rs"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__7 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object*);
static const lean_closure_object l_Lake_instToJsonModuleOutputDescrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ModuleOutputDescrs_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonModuleOutputDescrs___closed__0 = (const lean_object*)&l_Lake_instToJsonModuleOutputDescrs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonModuleOutputDescrs = (const lean_object*)&l_Lake_instToJsonModuleOutputDescrs___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object*);
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: o"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "o: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "expected a least one 'o' (.olean) hash"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "l: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: c"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "c: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "b: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "r: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: i"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "i: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "rs: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "m: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__15 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__15_value;
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_instFromJsonModuleOutputDescrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ModuleOutputDescrs_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonModuleOutputDescrs___closed__0 = (const lean_object*)&l_Lake_instFromJsonModuleOutputDescrs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonModuleOutputDescrs = (const lean_object*)&l_Lake_instFromJsonModuleOutputDescrs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_oleanParts(lean_object* v_self_1_){
_start:
{
lean_object* v_olean_2_; lean_object* v_oleanServer_x3f_3_; lean_object* v_oleanPrivate_x3f_4_; lean_object* v_descrs_6_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_descrs_11_; 
v_olean_2_ = lean_ctor_get(v_self_1_, 0);
lean_inc_ref(v_olean_2_);
v_oleanServer_x3f_3_ = lean_ctor_get(v_self_1_, 1);
lean_inc(v_oleanServer_x3f_3_);
v_oleanPrivate_x3f_4_ = lean_ctor_get(v_self_1_, 2);
lean_inc(v_oleanPrivate_x3f_4_);
lean_dec_ref(v_self_1_);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_mk_empty_array_with_capacity(v___x_9_);
v_descrs_11_ = lean_array_push(v___x_10_, v_olean_2_);
if (lean_obj_tag(v_oleanServer_x3f_3_) == 1)
{
lean_object* v_val_12_; lean_object* v_descrs_13_; 
v_val_12_ = lean_ctor_get(v_oleanServer_x3f_3_, 0);
lean_inc(v_val_12_);
lean_dec_ref_known(v_oleanServer_x3f_3_, 1);
v_descrs_13_ = lean_array_push(v_descrs_11_, v_val_12_);
v_descrs_6_ = v_descrs_13_;
goto v___jp_5_;
}
else
{
lean_dec(v_oleanServer_x3f_3_);
v_descrs_6_ = v_descrs_11_;
goto v___jp_5_;
}
v___jp_5_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_4_) == 1)
{
lean_object* v_val_7_; lean_object* v_descrs_8_; 
v_val_7_ = lean_ctor_get(v_oleanPrivate_x3f_4_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_oleanPrivate_x3f_4_, 1);
v_descrs_8_ = lean_array_push(v_descrs_6_, v_val_7_);
return v_descrs_8_;
}
else
{
lean_dec(v_oleanPrivate_x3f_4_);
return v_descrs_6_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(size_t v_sz_15_, size_t v_i_16_, lean_object* v_bs_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_lt(v_i_16_, v_sz_15_);
if (v___x_18_ == 0)
{
return v_bs_17_;
}
else
{
lean_object* v_v_19_; uint64_t v_hash_20_; lean_object* v_ext_21_; lean_object* v___x_22_; lean_object* v_bs_x27_23_; lean_object* v___y_25_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_v_19_ = lean_array_uget_borrowed(v_bs_17_, v_i_16_);
v_hash_20_ = lean_ctor_get_uint64(v_v_19_, sizeof(void*)*1);
v_ext_21_ = lean_ctor_get(v_v_19_, 0);
lean_inc_ref(v_ext_21_);
v___x_22_ = lean_unsigned_to_nat(0u);
v_bs_x27_23_ = lean_array_uset(v_bs_17_, v_i_16_, v___x_22_);
v___x_31_ = lean_string_utf8_byte_size(v_ext_21_);
v___x_32_ = lean_nat_dec_eq(v___x_31_, v___x_22_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_33_ = l_Lake_lowerHexUInt64(v_hash_20_);
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_35_ = lean_string_append(v___x_33_, v___x_34_);
v___x_36_ = lean_string_append(v___x_35_, v_ext_21_);
lean_dec_ref(v_ext_21_);
v___y_25_ = v___x_36_;
goto v___jp_24_;
}
else
{
lean_object* v___x_37_; 
lean_dec_ref(v_ext_21_);
v___x_37_ = l_Lake_lowerHexUInt64(v_hash_20_);
v___y_25_ = v___x_37_;
goto v___jp_24_;
}
v___jp_24_:
{
lean_object* v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; 
v___x_26_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_26_, 0, v___y_25_);
v___x_27_ = ((size_t)1ULL);
v___x_28_ = lean_usize_add(v_i_16_, v___x_27_);
v___x_29_ = lean_array_uset(v_bs_x27_23_, v_i_16_, v___x_26_);
v_i_16_ = v___x_28_;
v_bs_17_ = v___x_29_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(lean_object* v_sz_38_, lean_object* v_i_39_, lean_object* v_bs_40_){
_start:
{
size_t v_sz_boxed_41_; size_t v_i_boxed_42_; lean_object* v_res_43_; 
v_sz_boxed_41_ = lean_unbox_usize(v_sz_38_);
lean_dec(v_sz_38_);
v_i_boxed_42_ = lean_unbox_usize(v_i_39_);
lean_dec(v_i_39_);
v_res_43_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_boxed_41_, v_i_boxed_42_, v_bs_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(lean_object* v_a_44_){
_start:
{
size_t v_sz_45_; size_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_sz_45_ = lean_array_size(v_a_44_);
v___x_46_ = ((size_t)0ULL);
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_45_, v___x_46_, v_a_44_);
v___x_48_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object* v_self_57_){
_start:
{
lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; uint8_t v_isModule_65_; lean_object* v_ilean_66_; lean_object* v_irSig_x3f_67_; lean_object* v_ir_x3f_68_; lean_object* v_c_69_; lean_object* v_bc_x3f_70_; lean_object* v_ltar_x3f_71_; lean_object* v_obj_73_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v_obj_112_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v_obj_131_; lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; uint64_t v_hash_150_; lean_object* v_ext_151_; lean_object* v_obj_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_obj_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_obj_159_; lean_object* v___x_160_; lean_object* v___y_162_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_isModule_65_ = lean_ctor_get_uint8(v_self_57_, sizeof(void*)*9);
v_ilean_66_ = lean_ctor_get(v_self_57_, 3);
v_irSig_x3f_67_ = lean_ctor_get(v_self_57_, 4);
lean_inc(v_irSig_x3f_67_);
v_ir_x3f_68_ = lean_ctor_get(v_self_57_, 5);
lean_inc(v_ir_x3f_68_);
v_c_69_ = lean_ctor_get(v_self_57_, 6);
lean_inc_ref(v_c_69_);
v_bc_x3f_70_ = lean_ctor_get(v_self_57_, 7);
lean_inc(v_bc_x3f_70_);
v_ltar_x3f_71_ = lean_ctor_get(v_self_57_, 8);
lean_inc(v_ltar_x3f_71_);
v_hash_150_ = lean_ctor_get_uint64(v_ilean_66_, sizeof(void*)*1);
v_ext_151_ = lean_ctor_get(v_ilean_66_, 0);
lean_inc_ref(v_ext_151_);
v_obj_152_ = lean_box(1);
v___x_153_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_154_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_154_, 0, v_isModule_65_);
v_obj_155_ = l_Lake_JsonObject_insertJson(v_obj_152_, v___x_153_, v___x_154_);
v___x_156_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_157_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_57_);
v___x_158_ = l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_157_);
v_obj_159_ = l_Lake_JsonObject_insertJson(v_obj_155_, v___x_156_, v___x_158_);
v___x_160_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_177_ = lean_string_utf8_byte_size(v_ext_151_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_nat_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = l_Lake_lowerHexUInt64(v_hash_150_);
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_182_ = lean_string_append(v___x_180_, v___x_181_);
v___x_183_ = lean_string_append(v___x_182_, v_ext_151_);
lean_dec_ref(v_ext_151_);
v___y_162_ = v___x_183_;
goto v___jp_161_;
}
else
{
lean_object* v___x_184_; 
lean_dec_ref(v_ext_151_);
v___x_184_ = l_Lake_lowerHexUInt64(v_hash_150_);
v___y_162_ = v___x_184_;
goto v___jp_161_;
}
v___jp_58_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_62_, 0, v___y_61_);
lean_inc_ref(v___y_59_);
v___x_63_ = l_Lake_JsonObject_insertJson(v___y_60_, v___y_59_, v___x_62_);
v___x_64_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
v___jp_72_:
{
if (lean_obj_tag(v_ltar_x3f_71_) == 1)
{
lean_object* v_val_74_; uint64_t v_hash_75_; lean_object* v_ext_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_val_74_ = lean_ctor_get(v_ltar_x3f_71_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v_ltar_x3f_71_, 1);
v_hash_75_ = lean_ctor_get_uint64(v_val_74_, sizeof(void*)*1);
v_ext_76_ = lean_ctor_get(v_val_74_, 0);
lean_inc_ref(v_ext_76_);
lean_dec(v_val_74_);
v___x_77_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_78_ = lean_string_utf8_byte_size(v_ext_76_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_nat_dec_eq(v___x_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = l_Lake_lowerHexUInt64(v_hash_75_);
v___x_82_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_83_ = lean_string_append(v___x_81_, v___x_82_);
v___x_84_ = lean_string_append(v___x_83_, v_ext_76_);
lean_dec_ref(v_ext_76_);
v___y_59_ = v___x_77_;
v___y_60_ = v_obj_73_;
v___y_61_ = v___x_84_;
goto v___jp_58_;
}
else
{
lean_object* v___x_85_; 
lean_dec_ref(v_ext_76_);
v___x_85_ = l_Lake_lowerHexUInt64(v_hash_75_);
v___y_59_ = v___x_77_;
v___y_60_ = v_obj_73_;
v___y_61_ = v___x_85_;
goto v___jp_58_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v_ltar_x3f_71_);
v___x_86_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_86_, 0, v_obj_73_);
return v___x_86_;
}
}
v___jp_87_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_91_, 0, v___y_90_);
lean_inc_ref(v___y_88_);
v___x_92_ = l_Lake_JsonObject_insertJson(v___y_89_, v___y_88_, v___x_91_);
v_obj_73_ = v___x_92_;
goto v___jp_72_;
}
v___jp_93_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_97_, 0, v___y_96_);
lean_inc_ref(v___y_94_);
v___x_98_ = l_Lake_JsonObject_insertJson(v___y_95_, v___y_94_, v___x_97_);
if (lean_obj_tag(v_bc_x3f_70_) == 1)
{
lean_object* v_val_99_; uint64_t v_hash_100_; lean_object* v_ext_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_val_99_ = lean_ctor_get(v_bc_x3f_70_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v_bc_x3f_70_, 1);
v_hash_100_ = lean_ctor_get_uint64(v_val_99_, sizeof(void*)*1);
v_ext_101_ = lean_ctor_get(v_val_99_, 0);
lean_inc_ref(v_ext_101_);
lean_dec(v_val_99_);
v___x_102_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_103_ = lean_string_utf8_byte_size(v_ext_101_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = l_Lake_lowerHexUInt64(v_hash_100_);
v___x_107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_108_ = lean_string_append(v___x_106_, v___x_107_);
v___x_109_ = lean_string_append(v___x_108_, v_ext_101_);
lean_dec_ref(v_ext_101_);
v___y_88_ = v___x_102_;
v___y_89_ = v___x_98_;
v___y_90_ = v___x_109_;
goto v___jp_87_;
}
else
{
lean_object* v___x_110_; 
lean_dec_ref(v_ext_101_);
v___x_110_ = l_Lake_lowerHexUInt64(v_hash_100_);
v___y_88_ = v___x_102_;
v___y_89_ = v___x_98_;
v___y_90_ = v___x_110_;
goto v___jp_87_;
}
}
else
{
lean_dec(v_bc_x3f_70_);
v_obj_73_ = v___x_98_;
goto v___jp_72_;
}
}
v___jp_111_:
{
uint64_t v_hash_113_; lean_object* v_ext_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_hash_113_ = lean_ctor_get_uint64(v_c_69_, sizeof(void*)*1);
v_ext_114_ = lean_ctor_get(v_c_69_, 0);
lean_inc_ref(v_ext_114_);
lean_dec_ref(v_c_69_);
v___x_115_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_116_ = lean_string_utf8_byte_size(v_ext_114_);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_dec_eq(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = l_Lake_lowerHexUInt64(v_hash_113_);
v___x_120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_121_ = lean_string_append(v___x_119_, v___x_120_);
v___x_122_ = lean_string_append(v___x_121_, v_ext_114_);
lean_dec_ref(v_ext_114_);
v___y_94_ = v___x_115_;
v___y_95_ = v_obj_112_;
v___y_96_ = v___x_122_;
goto v___jp_93_;
}
else
{
lean_object* v___x_123_; 
lean_dec_ref(v_ext_114_);
v___x_123_ = l_Lake_lowerHexUInt64(v_hash_113_);
v___y_94_ = v___x_115_;
v___y_95_ = v_obj_112_;
v___y_96_ = v___x_123_;
goto v___jp_93_;
}
}
v___jp_124_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_128_, 0, v___y_127_);
lean_inc_ref(v___y_126_);
v___x_129_ = l_Lake_JsonObject_insertJson(v___y_125_, v___y_126_, v___x_128_);
v_obj_112_ = v___x_129_;
goto v___jp_111_;
}
v___jp_130_:
{
if (lean_obj_tag(v_ir_x3f_68_) == 1)
{
lean_object* v_val_132_; uint64_t v_hash_133_; lean_object* v_ext_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_val_132_ = lean_ctor_get(v_ir_x3f_68_, 0);
lean_inc(v_val_132_);
lean_dec_ref_known(v_ir_x3f_68_, 1);
v_hash_133_ = lean_ctor_get_uint64(v_val_132_, sizeof(void*)*1);
v_ext_134_ = lean_ctor_get(v_val_132_, 0);
lean_inc_ref(v_ext_134_);
lean_dec(v_val_132_);
v___x_135_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_136_ = lean_string_utf8_byte_size(v_ext_134_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_139_ = l_Lake_lowerHexUInt64(v_hash_133_);
v___x_140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_141_ = lean_string_append(v___x_139_, v___x_140_);
v___x_142_ = lean_string_append(v___x_141_, v_ext_134_);
lean_dec_ref(v_ext_134_);
v___y_125_ = v_obj_131_;
v___y_126_ = v___x_135_;
v___y_127_ = v___x_142_;
goto v___jp_124_;
}
else
{
lean_object* v___x_143_; 
lean_dec_ref(v_ext_134_);
v___x_143_ = l_Lake_lowerHexUInt64(v_hash_133_);
v___y_125_ = v_obj_131_;
v___y_126_ = v___x_135_;
v___y_127_ = v___x_143_;
goto v___jp_124_;
}
}
else
{
lean_dec(v_ir_x3f_68_);
v_obj_112_ = v_obj_131_;
goto v___jp_111_;
}
}
v___jp_144_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_148_, 0, v___y_147_);
lean_inc_ref(v___y_145_);
v___x_149_ = l_Lake_JsonObject_insertJson(v___y_146_, v___y_145_, v___x_148_);
v_obj_131_ = v___x_149_;
goto v___jp_130_;
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v___y_162_);
v___x_164_ = l_Lake_JsonObject_insertJson(v_obj_159_, v___x_160_, v___x_163_);
if (lean_obj_tag(v_irSig_x3f_67_) == 1)
{
lean_object* v_val_165_; uint64_t v_hash_166_; lean_object* v_ext_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_val_165_ = lean_ctor_get(v_irSig_x3f_67_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v_irSig_x3f_67_, 1);
v_hash_166_ = lean_ctor_get_uint64(v_val_165_, sizeof(void*)*1);
v_ext_167_ = lean_ctor_get(v_val_165_, 0);
lean_inc_ref(v_ext_167_);
lean_dec(v_val_165_);
v___x_168_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_169_ = lean_string_utf8_byte_size(v_ext_167_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_nat_dec_eq(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = l_Lake_lowerHexUInt64(v_hash_166_);
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
v___x_175_ = lean_string_append(v___x_174_, v_ext_167_);
lean_dec_ref(v_ext_167_);
v___y_145_ = v___x_168_;
v___y_146_ = v___x_164_;
v___y_147_ = v___x_175_;
goto v___jp_144_;
}
else
{
lean_object* v___x_176_; 
lean_dec_ref(v_ext_167_);
v___x_176_ = l_Lake_lowerHexUInt64(v_hash_166_);
v___y_145_ = v___x_168_;
v___y_146_ = v___x_164_;
v___y_147_ = v___x_176_;
goto v___jp_144_;
}
}
else
{
lean_dec(v_irSig_x3f_67_);
v_obj_131_ = v___x_164_;
goto v___jp_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0));
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_a_200_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v___x_191_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_191_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_a_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0));
return v___x_212_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Json_getBool_x3f(v_x_211_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
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
v_a_222_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_213_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_213_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_a_222_);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_x_231_);
lean_dec(v_x_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t v_sz_233_, size_t v_i_234_, lean_object* v_bs_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_bs_235_);
return v___x_237_;
}
else
{
lean_object* v_v_238_; lean_object* v___x_239_; 
v_v_238_ = lean_array_uget_borrowed(v_bs_235_, v_i_234_);
lean_inc(v_v_238_);
v___x_239_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_bs_235_);
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v_bs_x27_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
v_a_248_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_239_, 1);
v___x_249_ = lean_unsigned_to_nat(0u);
v_bs_x27_250_ = lean_array_uset(v_bs_235_, v_i_234_, v___x_249_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_234_, v___x_251_);
v___x_253_ = lean_array_uset(v_bs_x27_250_, v_i_234_, v_a_248_);
v_i_234_ = v___x_252_;
v_bs_235_ = v___x_253_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object* v_sz_255_, lean_object* v_i_256_, lean_object* v_bs_257_){
_start:
{
size_t v_sz_boxed_258_; size_t v_i_boxed_259_; lean_object* v_res_260_; 
v_sz_boxed_258_ = lean_unbox_usize(v_sz_255_);
lean_dec(v_sz_255_);
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_258_, v_i_boxed_259_, v_bs_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 4)
{
lean_object* v_elems_264_; size_t v_sz_265_; size_t v___x_266_; lean_object* v___x_267_; 
v_elems_264_ = lean_ctor_get(v_x_263_, 0);
lean_inc_ref(v_elems_264_);
lean_dec_ref_known(v_x_263_, 1);
v_sz_265_ = lean_array_size(v_elems_264_);
v___x_266_ = ((size_t)0ULL);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_265_, v___x_266_, v_elems_264_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_268_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0));
v___x_269_ = lean_unsigned_to_nat(80u);
v___x_270_ = l_Lean_Json_pretty(v_x_263_, v___x_269_);
v___x_271_ = lean_string_append(v___x_268_, v___x_270_);
lean_dec_ref(v___x_270_);
v___x_272_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1));
v___x_273_ = lean_string_append(v___x_271_, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f(lean_object* v_val_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Json_getObj_x3f(v_val_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_a_305_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_296_, 1);
v___x_306_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_307_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec(v_a_305_);
v___x_308_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1));
return v___x_308_;
}
else
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_583_; 
v_val_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_583_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_583_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_583_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; 
v___x_313_ = l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(v_val_309_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_323_; 
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_323_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_323_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_323_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_318_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2));
v___x_319_ = lean_string_append(v___x_318_, v_a_314_);
lean_dec(v_a_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_321_ = v___x_316_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_324_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_313_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_313_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 0);
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_582_; 
v_a_332_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_582_ == 0)
{
v___x_334_ = v___x_313_;
v_isShared_335_ = v_isSharedCheck_582_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_313_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_582_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_array_get_size(v_a_332_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v___x_339_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4));
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; uint8_t v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v_a_391_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_a_402_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v_a_431_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v_a_483_; lean_object* v_a_509_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_340_ = lean_array_fget(v_a_332_, v___x_336_);
v___x_558_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_559_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_558_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_box(0);
v_a_509_ = v___x_560_;
goto v___jp_508_;
}
else
{
lean_object* v_val_561_; lean_object* v___x_562_; 
v_val_561_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v___x_559_, 1);
v___x_562_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_561_);
lean_dec(v_val_561_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_572_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__15));
v___x_568_ = lean_string_append(v___x_567_, v_a_563_);
lean_dec(v_a_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_573_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_562_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_562_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 0);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; 
v_a_581_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_562_, 1);
v_a_509_ = v_a_581_;
goto v___jp_508_;
}
}
}
v___jp_341_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_351_, 0, v___x_340_);
lean_ctor_set(v___x_351_, 1, v___y_344_);
lean_ctor_set(v___x_351_, 2, v___y_350_);
lean_ctor_set(v___x_351_, 3, v___y_348_);
lean_ctor_set(v___x_351_, 4, v___y_346_);
lean_ctor_set(v___x_351_, 5, v___y_343_);
lean_ctor_set(v___x_351_, 6, v___y_347_);
lean_ctor_set(v___x_351_, 7, v___y_349_);
lean_ctor_set(v___x_351_, 8, v___y_342_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*9, v___y_345_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_351_);
v___x_353_ = v___x_334_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
v___jp_355_:
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(2u);
v___x_365_ = lean_nat_dec_lt(v___x_364_, v___x_337_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
v___x_366_ = lean_box(0);
v___y_342_ = v___y_356_;
v___y_343_ = v___y_357_;
v___y_344_ = v___y_363_;
v___y_345_ = v___y_358_;
v___y_346_ = v___y_359_;
v___y_347_ = v___y_360_;
v___y_348_ = v___y_361_;
v___y_349_ = v___y_362_;
v___y_350_ = v___x_366_;
goto v___jp_341_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_array_fget(v_a_332_, v___x_364_);
lean_dec(v_a_332_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_367_);
v___x_369_ = v___x_311_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v___y_342_ = v___y_356_;
v___y_343_ = v___y_357_;
v___y_344_ = v___y_363_;
v___y_345_ = v___y_358_;
v___y_346_ = v___y_359_;
v___y_347_ = v___y_360_;
v___y_348_ = v___y_361_;
v___y_349_ = v___y_362_;
v___y_350_ = v___x_369_;
goto v___jp_341_;
}
}
}
v___jp_371_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_dec_lt(v___x_379_, v___x_337_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
v___y_356_ = v___y_372_;
v___y_357_ = v___y_373_;
v___y_358_ = v___y_378_;
v___y_359_ = v___y_374_;
v___y_360_ = v___y_375_;
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___x_381_;
goto v___jp_355_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_array_fget_borrowed(v_a_332_, v___x_379_);
lean_inc(v___x_382_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___y_356_ = v___y_372_;
v___y_357_ = v___y_373_;
v___y_358_ = v___y_378_;
v___y_359_ = v___y_374_;
v___y_360_ = v___y_375_;
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___x_383_;
goto v___jp_355_;
}
}
v___jp_384_:
{
if (lean_obj_tag(v___y_389_) == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_dec_lt(v___x_392_, v___x_337_);
v___y_372_ = v_a_391_;
v___y_373_ = v___y_385_;
v___y_374_ = v___y_386_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_390_;
v___y_378_ = v___x_393_;
goto v___jp_371_;
}
else
{
lean_object* v_val_394_; uint8_t v___x_395_; 
v_val_394_ = lean_ctor_get(v___y_389_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___y_389_, 1);
v___x_395_ = lean_unbox(v_val_394_);
lean_dec(v_val_394_);
v___y_372_ = v_a_391_;
v___y_373_ = v___y_385_;
v___y_374_ = v___y_386_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_390_;
v___y_378_ = v___x_395_;
goto v___jp_371_;
}
}
v___jp_396_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_404_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_403_);
lean_dec(v_a_305_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
v___x_405_ = lean_box(0);
v___y_385_ = v___y_397_;
v___y_386_ = v___y_398_;
v___y_387_ = v___y_399_;
v___y_388_ = v___y_400_;
v___y_389_ = v___y_401_;
v___y_390_ = v_a_402_;
v_a_391_ = v___x_405_;
goto v___jp_384_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; 
v_val_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v___x_404_, 1);
v___x_407_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec(v___y_397_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_417_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5));
v___x_413_ = lean_string_append(v___x_412_, v_a_408_);
lean_dec(v_a_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec(v___y_397_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
v_a_418_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_407_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 0);
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; 
v_a_426_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_407_, 1);
v___y_385_ = v___y_397_;
v___y_386_ = v___y_398_;
v___y_387_ = v___y_399_;
v___y_388_ = v___y_400_;
v___y_389_ = v___y_401_;
v___y_390_ = v_a_402_;
v_a_391_ = v_a_426_;
goto v___jp_384_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_433_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; 
lean_dec(v_a_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v___x_434_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7));
return v___x_434_;
}
else
{
lean_object* v_val_435_; lean_object* v___x_436_; 
v_val_435_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_435_);
lean_dec_ref_known(v___x_433_, 1);
v___x_436_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8));
v___x_442_ = lean_string_append(v___x_441_, v_a_437_);
lean_dec(v_a_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_a_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_447_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_436_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_436_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 0);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_a_455_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_436_, 1);
v___x_456_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_457_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
v___y_397_ = v_a_431_;
v___y_398_ = v___y_428_;
v___y_399_ = v_a_455_;
v___y_400_ = v___y_429_;
v___y_401_ = v___y_430_;
v_a_402_ = v___x_458_;
goto v___jp_396_;
}
else
{
lean_object* v_val_459_; lean_object* v___x_460_; 
v_val_459_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v___x_457_, 1);
v___x_460_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_455_);
lean_dec(v_a_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9));
v___x_466_ = lean_string_append(v___x_465_, v_a_461_);
lean_dec(v_a_461_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v_a_455_);
lean_dec(v_a_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_471_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_460_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_460_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 0);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_479_; 
v_a_479_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_460_, 1);
v___y_397_ = v_a_431_;
v___y_398_ = v___y_428_;
v___y_399_ = v_a_455_;
v___y_400_ = v___y_429_;
v___y_401_ = v___y_430_;
v_a_402_ = v_a_479_;
goto v___jp_396_;
}
}
}
}
}
}
}
v___jp_480_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_485_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_484_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_box(0);
v___y_428_ = v_a_483_;
v___y_429_ = v___y_481_;
v___y_430_ = v___y_482_;
v_a_431_ = v___x_486_;
goto v___jp_427_;
}
else
{
lean_object* v_val_487_; lean_object* v___x_488_; 
v_val_487_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_485_, 1);
v___x_488_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_a_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_498_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10));
v___x_494_ = lean_string_append(v___x_493_, v_a_489_);
lean_dec(v_a_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_494_);
v___x_496_ = v___x_491_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_499_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_488_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_488_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 0);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; 
v_a_507_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_488_, 1);
v___y_428_ = v_a_483_;
v___y_429_ = v___y_481_;
v___y_430_ = v___y_482_;
v_a_431_ = v_a_507_;
goto v___jp_427_;
}
}
}
}
v___jp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_511_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_512_; 
lean_dec(v_a_509_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v___x_512_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12));
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_514_; 
v_val_513_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v___x_511_, 1);
v___x_514_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_a_509_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_524_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13));
v___x_520_ = lean_string_append(v___x_519_, v_a_515_);
lean_dec(v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_509_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_525_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_514_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_514_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 0);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_514_, 1);
v___x_534_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_535_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(0);
v___y_481_ = v_a_533_;
v___y_482_ = v_a_509_;
v_a_483_ = v___x_536_;
goto v___jp_480_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; 
v_val_537_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v___x_535_, 1);
v___x_538_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_533_);
lean_dec(v_a_509_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14));
v___x_544_ = lean_string_append(v___x_543_, v_a_539_);
lean_dec(v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_533_);
lean_dec(v_a_509_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_549_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_538_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_538_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 0);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v_a_557_; 
v_a_557_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_538_, 1);
v___y_481_ = v_a_533_;
v___y_482_ = v_a_509_;
v_a_483_ = v_a_557_;
goto v___jp_480_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object* v_arts_586_){
_start:
{
lean_object* v_olean_587_; uint8_t v_isModule_588_; lean_object* v_oleanServer_x3f_589_; lean_object* v_oleanPrivate_x3f_590_; lean_object* v_ilean_591_; lean_object* v_irSig_x3f_592_; lean_object* v_ir_x3f_593_; lean_object* v_c_594_; lean_object* v_bc_x3f_595_; lean_object* v_ltar_x3f_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_695_; 
v_olean_587_ = lean_ctor_get(v_arts_586_, 0);
v_isModule_588_ = lean_ctor_get_uint8(v_arts_586_, sizeof(void*)*9);
v_oleanServer_x3f_589_ = lean_ctor_get(v_arts_586_, 1);
v_oleanPrivate_x3f_590_ = lean_ctor_get(v_arts_586_, 2);
v_ilean_591_ = lean_ctor_get(v_arts_586_, 3);
v_irSig_x3f_592_ = lean_ctor_get(v_arts_586_, 4);
v_ir_x3f_593_ = lean_ctor_get(v_arts_586_, 5);
v_c_594_ = lean_ctor_get(v_arts_586_, 6);
v_bc_x3f_595_ = lean_ctor_get(v_arts_586_, 7);
v_ltar_x3f_596_ = lean_ctor_get(v_arts_586_, 8);
v_isSharedCheck_695_ = !lean_is_exclusive(v_arts_586_);
if (v_isSharedCheck_695_ == 0)
{
v___x_598_ = v_arts_586_;
v_isShared_599_ = v_isSharedCheck_695_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_ltar_x3f_596_);
lean_inc(v_bc_x3f_595_);
lean_inc(v_c_594_);
lean_inc(v_ir_x3f_593_);
lean_inc(v_irSig_x3f_592_);
lean_inc(v_ilean_591_);
lean_inc(v_oleanPrivate_x3f_590_);
lean_inc(v_oleanServer_x3f_589_);
lean_inc(v_olean_587_);
lean_dec(v_arts_586_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_695_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_descr_600_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_674_; 
v_descr_600_ = lean_ctor_get(v_olean_587_, 0);
lean_inc_ref(v_descr_600_);
lean_dec_ref(v_olean_587_);
if (lean_obj_tag(v_oleanServer_x3f_589_) == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_box(0);
v___y_674_ = v___x_685_;
goto v___jp_673_;
}
else
{
lean_object* v_val_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_694_; 
v_val_686_ = lean_ctor_get(v_oleanServer_x3f_589_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_oleanServer_x3f_589_);
if (v_isSharedCheck_694_ == 0)
{
v___x_688_ = v_oleanServer_x3f_589_;
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_val_686_);
lean_dec(v_oleanServer_x3f_589_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_descr_690_; lean_object* v___x_692_; 
v_descr_690_ = lean_ctor_get(v_val_686_, 0);
lean_inc_ref(v_descr_690_);
lean_dec(v_val_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_descr_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_descr_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v___y_674_ = v___x_692_;
goto v___jp_673_;
}
}
}
v___jp_601_:
{
if (lean_obj_tag(v_ltar_x3f_596_) == 0)
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 8, v___x_609_);
lean_ctor_set(v___x_598_, 7, v___y_608_);
lean_ctor_set(v___x_598_, 6, v___y_602_);
lean_ctor_set(v___x_598_, 5, v___y_607_);
lean_ctor_set(v___x_598_, 4, v___y_605_);
lean_ctor_set(v___x_598_, 3, v___y_603_);
lean_ctor_set(v___x_598_, 2, v___y_604_);
lean_ctor_set(v___x_598_, 1, v___y_606_);
lean_ctor_set(v___x_598_, 0, v_descr_600_);
v___x_611_ = v___x_598_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_descr_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___y_606_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v___y_603_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v___y_605_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v___y_607_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v___y_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v___y_608_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v___x_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_612_, sizeof(void*)*9, v_isModule_588_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_624_; 
v_val_613_ = lean_ctor_get(v_ltar_x3f_596_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_ltar_x3f_596_);
if (v_isSharedCheck_624_ == 0)
{
v___x_615_ = v_ltar_x3f_596_;
v_isShared_616_ = v_isSharedCheck_624_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v_ltar_x3f_596_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_624_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_descr_617_; lean_object* v___x_619_; 
v_descr_617_ = lean_ctor_get(v_val_613_, 0);
lean_inc_ref(v_descr_617_);
lean_dec(v_val_613_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_descr_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_descr_617_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 8, v___x_619_);
lean_ctor_set(v___x_598_, 7, v___y_608_);
lean_ctor_set(v___x_598_, 6, v___y_602_);
lean_ctor_set(v___x_598_, 5, v___y_607_);
lean_ctor_set(v___x_598_, 4, v___y_605_);
lean_ctor_set(v___x_598_, 3, v___y_603_);
lean_ctor_set(v___x_598_, 2, v___y_604_);
lean_ctor_set(v___x_598_, 1, v___y_606_);
lean_ctor_set(v___x_598_, 0, v_descr_600_);
v___x_621_ = v___x_598_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_descr_600_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___y_606_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v___y_603_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___y_605_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v___y_607_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v___y_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v___y_608_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v___x_619_);
lean_ctor_set_uint8(v_reuseFailAlloc_622_, sizeof(void*)*9, v_isModule_588_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
v___jp_625_:
{
if (lean_obj_tag(v_bc_x3f_595_) == 0)
{
lean_object* v_descr_631_; lean_object* v___x_632_; 
v_descr_631_ = lean_ctor_get(v_c_594_, 0);
lean_inc_ref(v_descr_631_);
lean_dec_ref(v_c_594_);
v___x_632_ = lean_box(0);
v___y_602_ = v_descr_631_;
v___y_603_ = v___y_626_;
v___y_604_ = v___y_627_;
v___y_605_ = v___y_629_;
v___y_606_ = v___y_628_;
v___y_607_ = v___y_630_;
v___y_608_ = v___x_632_;
goto v___jp_601_;
}
else
{
lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_642_; 
v_val_633_ = lean_ctor_get(v_bc_x3f_595_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_bc_x3f_595_);
if (v_isSharedCheck_642_ == 0)
{
v___x_635_ = v_bc_x3f_595_;
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_dec(v_bc_x3f_595_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_descr_637_; lean_object* v_descr_638_; lean_object* v___x_640_; 
v_descr_637_ = lean_ctor_get(v_c_594_, 0);
lean_inc_ref(v_descr_637_);
lean_dec_ref(v_c_594_);
v_descr_638_ = lean_ctor_get(v_val_633_, 0);
lean_inc_ref(v_descr_638_);
lean_dec(v_val_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_descr_638_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_descr_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v___y_602_ = v_descr_637_;
v___y_603_ = v___y_626_;
v___y_604_ = v___y_627_;
v___y_605_ = v___y_629_;
v___y_606_ = v___y_628_;
v___y_607_ = v___y_630_;
v___y_608_ = v___x_640_;
goto v___jp_601_;
}
}
}
}
v___jp_643_:
{
if (lean_obj_tag(v_ir_x3f_593_) == 0)
{
lean_object* v___x_648_; 
v___x_648_ = lean_box(0);
v___y_626_ = v___y_644_;
v___y_627_ = v___y_645_;
v___y_628_ = v___y_646_;
v___y_629_ = v___y_647_;
v___y_630_ = v___x_648_;
goto v___jp_625_;
}
else
{
lean_object* v_val_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
v_val_649_ = lean_ctor_get(v_ir_x3f_593_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_ir_x3f_593_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_ir_x3f_593_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_val_649_);
lean_dec(v_ir_x3f_593_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_descr_653_; lean_object* v___x_655_; 
v_descr_653_ = lean_ctor_get(v_val_649_, 0);
lean_inc_ref(v_descr_653_);
lean_dec(v_val_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_descr_653_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_descr_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
v___y_626_ = v___y_644_;
v___y_627_ = v___y_645_;
v___y_628_ = v___y_646_;
v___y_629_ = v___y_647_;
v___y_630_ = v___x_655_;
goto v___jp_625_;
}
}
}
}
v___jp_658_:
{
if (lean_obj_tag(v_irSig_x3f_592_) == 0)
{
lean_object* v_descr_661_; lean_object* v___x_662_; 
v_descr_661_ = lean_ctor_get(v_ilean_591_, 0);
lean_inc_ref(v_descr_661_);
lean_dec_ref(v_ilean_591_);
v___x_662_ = lean_box(0);
v___y_644_ = v_descr_661_;
v___y_645_ = v___y_660_;
v___y_646_ = v___y_659_;
v___y_647_ = v___x_662_;
goto v___jp_643_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_672_; 
v_val_663_ = lean_ctor_get(v_irSig_x3f_592_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_irSig_x3f_592_);
if (v_isSharedCheck_672_ == 0)
{
v___x_665_ = v_irSig_x3f_592_;
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_dec(v_irSig_x3f_592_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_descr_667_; lean_object* v_descr_668_; lean_object* v___x_670_; 
v_descr_667_ = lean_ctor_get(v_ilean_591_, 0);
lean_inc_ref(v_descr_667_);
lean_dec_ref(v_ilean_591_);
v_descr_668_ = lean_ctor_get(v_val_663_, 0);
lean_inc_ref(v_descr_668_);
lean_dec(v_val_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_descr_668_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_descr_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
v___y_644_ = v_descr_667_;
v___y_645_ = v___y_660_;
v___y_646_ = v___y_659_;
v___y_647_ = v___x_670_;
goto v___jp_643_;
}
}
}
}
v___jp_673_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_590_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
v___y_659_ = v___y_674_;
v___y_660_ = v___x_675_;
goto v___jp_658_;
}
else
{
lean_object* v_val_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_val_676_ = lean_ctor_get(v_oleanPrivate_x3f_590_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_oleanPrivate_x3f_590_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_oleanPrivate_x3f_590_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_val_676_);
lean_dec(v_oleanPrivate_x3f_590_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_descr_680_; lean_object* v___x_682_; 
v_descr_680_ = lean_ctor_get(v_val_676_, 0);
lean_inc_ref(v_descr_680_);
lean_dec(v_val_676_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_descr_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_descr_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
v___y_659_ = v___y_674_;
v___y_660_ = v___x_682_;
goto v___jp_658_;
}
}
}
}
}
}
}
lean_object* runtime_initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_ModuleArtifacts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_ModuleArtifacts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_ModuleArtifacts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_ModuleArtifacts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_ModuleArtifacts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_ModuleArtifacts(builtin);
}
#ifdef __cplusplus
}
#endif
