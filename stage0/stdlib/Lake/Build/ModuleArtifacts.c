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
lean_object* l_Lake_Hash_hex(uint64_t);
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
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__3 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__3_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__4 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__4_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__5 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__5_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__6 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__6_value;
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
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: i"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "i: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "r: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "m: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value;
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
lean_dec_ref(v_oleanServer_x3f_3_);
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
lean_object* v_val_7_; lean_object* v___x_8_; 
v_val_7_ = lean_ctor_get(v_oleanPrivate_x3f_4_, 0);
lean_inc(v_val_7_);
lean_dec_ref(v_oleanPrivate_x3f_4_);
v___x_8_ = lean_array_push(v_descrs_6_, v_val_7_);
return v___x_8_;
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
v___x_33_ = l_Lake_Hash_hex(v_hash_20_);
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
v___x_37_ = l_Lake_Hash_hex(v_hash_20_);
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
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object* v_self_56_){
_start:
{
lean_object* v___y_58_; lean_object* v___y_59_; lean_object* v___y_60_; uint8_t v_isModule_64_; lean_object* v_ilean_65_; lean_object* v_ir_x3f_66_; lean_object* v_c_67_; lean_object* v_bc_x3f_68_; lean_object* v_ltar_x3f_69_; lean_object* v_obj_71_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_92_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v_obj_110_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; uint64_t v_hash_128_; lean_object* v_ext_129_; lean_object* v_obj_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_obj_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_obj_137_; lean_object* v___x_138_; lean_object* v___y_140_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_isModule_64_ = lean_ctor_get_uint8(v_self_56_, sizeof(void*)*8);
v_ilean_65_ = lean_ctor_get(v_self_56_, 3);
v_ir_x3f_66_ = lean_ctor_get(v_self_56_, 4);
lean_inc(v_ir_x3f_66_);
v_c_67_ = lean_ctor_get(v_self_56_, 5);
lean_inc_ref(v_c_67_);
v_bc_x3f_68_ = lean_ctor_get(v_self_56_, 6);
lean_inc(v_bc_x3f_68_);
v_ltar_x3f_69_ = lean_ctor_get(v_self_56_, 7);
lean_inc(v_ltar_x3f_69_);
v_hash_128_ = lean_ctor_get_uint64(v_ilean_65_, sizeof(void*)*1);
v_ext_129_ = lean_ctor_get(v_ilean_65_, 0);
lean_inc_ref(v_ext_129_);
v_obj_130_ = lean_box(1);
v___x_131_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_132_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_132_, 0, v_isModule_64_);
v_obj_133_ = l_Lake_JsonObject_insertJson(v_obj_130_, v___x_131_, v___x_132_);
v___x_134_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_135_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_56_);
v___x_136_ = l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_135_);
v_obj_137_ = l_Lake_JsonObject_insertJson(v_obj_133_, v___x_134_, v___x_136_);
v___x_138_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_155_ = lean_string_utf8_byte_size(v_ext_129_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_nat_dec_eq(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = l_Lake_Hash_hex(v_hash_128_);
v___x_159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_160_ = lean_string_append(v___x_158_, v___x_159_);
v___x_161_ = lean_string_append(v___x_160_, v_ext_129_);
lean_dec_ref(v_ext_129_);
v___y_140_ = v___x_161_;
goto v___jp_139_;
}
else
{
lean_object* v___x_162_; 
lean_dec_ref(v_ext_129_);
v___x_162_ = l_Lake_Hash_hex(v_hash_128_);
v___y_140_ = v___x_162_;
goto v___jp_139_;
}
v___jp_57_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_61_, 0, v___y_60_);
lean_inc_ref(v___y_58_);
v___x_62_ = l_Lake_JsonObject_insertJson(v___y_59_, v___y_58_, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
v___jp_70_:
{
if (lean_obj_tag(v_ltar_x3f_69_) == 1)
{
lean_object* v_val_72_; uint64_t v_hash_73_; lean_object* v_ext_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_val_72_ = lean_ctor_get(v_ltar_x3f_69_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v_ltar_x3f_69_);
v_hash_73_ = lean_ctor_get_uint64(v_val_72_, sizeof(void*)*1);
v_ext_74_ = lean_ctor_get(v_val_72_, 0);
lean_inc_ref(v_ext_74_);
lean_dec(v_val_72_);
v___x_75_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_76_ = lean_string_utf8_byte_size(v_ext_74_);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_nat_dec_eq(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = l_Lake_Hash_hex(v_hash_73_);
v___x_80_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_81_ = lean_string_append(v___x_79_, v___x_80_);
v___x_82_ = lean_string_append(v___x_81_, v_ext_74_);
lean_dec_ref(v_ext_74_);
v___y_58_ = v___x_75_;
v___y_59_ = v_obj_71_;
v___y_60_ = v___x_82_;
goto v___jp_57_;
}
else
{
lean_object* v___x_83_; 
lean_dec_ref(v_ext_74_);
v___x_83_ = l_Lake_Hash_hex(v_hash_73_);
v___y_58_ = v___x_75_;
v___y_59_ = v_obj_71_;
v___y_60_ = v___x_83_;
goto v___jp_57_;
}
}
else
{
lean_object* v___x_84_; 
lean_dec(v_ltar_x3f_69_);
v___x_84_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_84_, 0, v_obj_71_);
return v___x_84_;
}
}
v___jp_85_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_89_, 0, v___y_88_);
lean_inc_ref(v___y_87_);
v___x_90_ = l_Lake_JsonObject_insertJson(v___y_86_, v___y_87_, v___x_89_);
v_obj_71_ = v___x_90_;
goto v___jp_70_;
}
v___jp_91_:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_95_, 0, v___y_94_);
lean_inc_ref(v___y_93_);
v___x_96_ = l_Lake_JsonObject_insertJson(v___y_92_, v___y_93_, v___x_95_);
if (lean_obj_tag(v_bc_x3f_68_) == 1)
{
lean_object* v_val_97_; uint64_t v_hash_98_; lean_object* v_ext_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_val_97_ = lean_ctor_get(v_bc_x3f_68_, 0);
lean_inc(v_val_97_);
lean_dec_ref(v_bc_x3f_68_);
v_hash_98_ = lean_ctor_get_uint64(v_val_97_, sizeof(void*)*1);
v_ext_99_ = lean_ctor_get(v_val_97_, 0);
lean_inc_ref(v_ext_99_);
lean_dec(v_val_97_);
v___x_100_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_101_ = lean_string_utf8_byte_size(v_ext_99_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_nat_dec_eq(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = l_Lake_Hash_hex(v_hash_98_);
v___x_105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_106_ = lean_string_append(v___x_104_, v___x_105_);
v___x_107_ = lean_string_append(v___x_106_, v_ext_99_);
lean_dec_ref(v_ext_99_);
v___y_86_ = v___x_96_;
v___y_87_ = v___x_100_;
v___y_88_ = v___x_107_;
goto v___jp_85_;
}
else
{
lean_object* v___x_108_; 
lean_dec_ref(v_ext_99_);
v___x_108_ = l_Lake_Hash_hex(v_hash_98_);
v___y_86_ = v___x_96_;
v___y_87_ = v___x_100_;
v___y_88_ = v___x_108_;
goto v___jp_85_;
}
}
else
{
lean_dec(v_bc_x3f_68_);
v_obj_71_ = v___x_96_;
goto v___jp_70_;
}
}
v___jp_109_:
{
uint64_t v_hash_111_; lean_object* v_ext_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_hash_111_ = lean_ctor_get_uint64(v_c_67_, sizeof(void*)*1);
v_ext_112_ = lean_ctor_get(v_c_67_, 0);
lean_inc_ref(v_ext_112_);
lean_dec_ref(v_c_67_);
v___x_113_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_114_ = lean_string_utf8_byte_size(v_ext_112_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_dec_eq(v___x_114_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = l_Lake_Hash_hex(v_hash_111_);
v___x_118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
v___x_120_ = lean_string_append(v___x_119_, v_ext_112_);
lean_dec_ref(v_ext_112_);
v___y_92_ = v_obj_110_;
v___y_93_ = v___x_113_;
v___y_94_ = v___x_120_;
goto v___jp_91_;
}
else
{
lean_object* v___x_121_; 
lean_dec_ref(v_ext_112_);
v___x_121_ = l_Lake_Hash_hex(v_hash_111_);
v___y_92_ = v_obj_110_;
v___y_93_ = v___x_113_;
v___y_94_ = v___x_121_;
goto v___jp_91_;
}
}
v___jp_122_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_126_, 0, v___y_125_);
lean_inc_ref(v___y_123_);
v___x_127_ = l_Lake_JsonObject_insertJson(v___y_124_, v___y_123_, v___x_126_);
v_obj_110_ = v___x_127_;
goto v___jp_109_;
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___y_140_);
v___x_142_ = l_Lake_JsonObject_insertJson(v_obj_137_, v___x_138_, v___x_141_);
if (lean_obj_tag(v_ir_x3f_66_) == 1)
{
lean_object* v_val_143_; uint64_t v_hash_144_; lean_object* v_ext_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_val_143_ = lean_ctor_get(v_ir_x3f_66_, 0);
lean_inc(v_val_143_);
lean_dec_ref(v_ir_x3f_66_);
v_hash_144_ = lean_ctor_get_uint64(v_val_143_, sizeof(void*)*1);
v_ext_145_ = lean_ctor_get(v_val_143_, 0);
lean_inc_ref(v_ext_145_);
lean_dec(v_val_143_);
v___x_146_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_147_ = lean_string_utf8_byte_size(v_ext_145_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_nat_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = l_Lake_Hash_hex(v_hash_144_);
v___x_151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_152_ = lean_string_append(v___x_150_, v___x_151_);
v___x_153_ = lean_string_append(v___x_152_, v_ext_145_);
lean_dec_ref(v_ext_145_);
v___y_123_ = v___x_146_;
v___y_124_ = v___x_142_;
v___y_125_ = v___x_153_;
goto v___jp_122_;
}
else
{
lean_object* v___x_154_; 
lean_dec_ref(v_ext_145_);
v___x_154_ = l_Lake_Hash_hex(v_hash_144_);
v___y_123_ = v___x_146_;
v___y_124_ = v___x_142_;
v___y_125_ = v___x_154_;
goto v___jp_122_;
}
}
else
{
lean_dec(v_ir_x3f_66_);
v_obj_110_ = v___x_142_;
goto v___jp_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0));
return v___x_168_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_186_; 
v_a_178_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_186_ == 0)
{
v___x_180_ = v___x_169_;
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_169_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_a_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0));
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Json_getBool_x3f(v_x_189_);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_x_209_);
lean_dec(v_x_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t v_sz_211_, size_t v_i_212_, lean_object* v_bs_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = lean_usize_dec_lt(v_i_212_, v_sz_211_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_bs_213_);
return v___x_215_;
}
else
{
lean_object* v_v_216_; lean_object* v___x_217_; 
v_v_216_ = lean_array_uget_borrowed(v_bs_213_, v_i_212_);
lean_inc(v_v_216_);
v___x_217_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v_bs_213_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v_bs_x27_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; 
v_a_226_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_217_);
v___x_227_ = lean_unsigned_to_nat(0u);
v_bs_x27_228_ = lean_array_uset(v_bs_213_, v_i_212_, v___x_227_);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_212_, v___x_229_);
v___x_231_ = lean_array_uset(v_bs_x27_228_, v_i_212_, v_a_226_);
v_i_212_ = v___x_230_;
v_bs_213_ = v___x_231_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object* v_sz_233_, lean_object* v_i_234_, lean_object* v_bs_235_){
_start:
{
size_t v_sz_boxed_236_; size_t v_i_boxed_237_; lean_object* v_res_238_; 
v_sz_boxed_236_ = lean_unbox_usize(v_sz_233_);
lean_dec(v_sz_233_);
v_i_boxed_237_ = lean_unbox_usize(v_i_234_);
lean_dec(v_i_234_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_236_, v_i_boxed_237_, v_bs_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 4)
{
lean_object* v_elems_242_; size_t v_sz_243_; size_t v___x_244_; lean_object* v___x_245_; 
v_elems_242_ = lean_ctor_get(v_x_241_, 0);
lean_inc_ref(v_elems_242_);
lean_dec_ref(v_x_241_);
v_sz_243_ = lean_array_size(v_elems_242_);
v___x_244_ = ((size_t)0ULL);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_243_, v___x_244_, v_elems_242_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_246_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0));
v___x_247_ = lean_unsigned_to_nat(80u);
v___x_248_ = l_Lean_Json_pretty(v_x_241_, v___x_247_);
v___x_249_ = lean_string_append(v___x_246_, v___x_248_);
lean_dec_ref(v___x_248_);
v___x_250_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1));
v___x_251_ = lean_string_append(v___x_249_, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f(lean_object* v_val_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Json_getObj_x3f(v_val_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_a_282_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_282_);
lean_dec_ref(v___x_273_);
v___x_283_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_284_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_283_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; 
lean_dec(v_a_282_);
v___x_285_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1));
return v___x_285_;
}
else
{
lean_object* v_val_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_526_; 
v_val_286_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_526_ == 0)
{
v___x_288_ = v___x_284_;
v_isShared_289_ = v_isSharedCheck_526_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_val_286_);
lean_dec(v___x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_526_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; 
v___x_290_ = l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(v_val_286_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_300_; 
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_300_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2));
v___x_296_ = lean_string_append(v___x_295_, v_a_291_);
lean_dec(v_a_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_301_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_290_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_290_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 0);
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_525_; 
v_a_309_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_525_ == 0)
{
v___x_311_ = v___x_290_;
v_isShared_312_ = v_isSharedCheck_525_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_290_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_525_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_a_309_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v___x_316_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4));
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___y_319_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; uint8_t v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_352_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_a_364_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v_a_374_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_a_402_; lean_object* v_a_452_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_317_ = lean_array_fget(v_a_309_, v___x_313_);
v___x_501_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_502_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_501_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
v_a_452_ = v___x_503_;
goto v___jp_451_;
}
else
{
lean_object* v_val_504_; lean_object* v___x_505_; 
v_val_504_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_val_504_);
lean_dec_ref(v___x_502_);
v___x_505_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_504_);
lean_dec(v_val_504_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_515_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14));
v___x_511_ = lean_string_append(v___x_510_, v_a_506_);
lean_dec(v_a_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_516_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_505_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_505_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 0);
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v_a_524_; 
v_a_524_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v___x_505_);
v_a_452_ = v_a_524_;
goto v___jp_451_;
}
}
}
v___jp_318_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_327_, 0, v___x_317_);
lean_ctor_set(v___x_327_, 1, v___y_322_);
lean_ctor_set(v___x_327_, 2, v___y_326_);
lean_ctor_set(v___x_327_, 3, v___y_321_);
lean_ctor_set(v___x_327_, 4, v___y_323_);
lean_ctor_set(v___x_327_, 5, v___y_325_);
lean_ctor_set(v___x_327_, 6, v___y_324_);
lean_ctor_set(v___x_327_, 7, v___y_319_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*8, v___y_320_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_327_);
v___x_329_ = v___x_311_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
v___jp_331_:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_nat_dec_lt(v___x_339_, v___x_314_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
v___x_341_ = lean_box(0);
v___y_319_ = v___y_333_;
v___y_320_ = v___y_332_;
v___y_321_ = v___y_334_;
v___y_322_ = v___y_338_;
v___y_323_ = v___y_335_;
v___y_324_ = v___y_337_;
v___y_325_ = v___y_336_;
v___y_326_ = v___x_341_;
goto v___jp_318_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_array_fget(v_a_309_, v___x_339_);
lean_dec(v_a_309_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_342_);
v___x_344_ = v___x_288_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
v___y_319_ = v___y_333_;
v___y_320_ = v___y_332_;
v___y_321_ = v___y_334_;
v___y_322_ = v___y_338_;
v___y_323_ = v___y_335_;
v___y_324_ = v___y_337_;
v___y_325_ = v___y_336_;
v___y_326_ = v___x_344_;
goto v___jp_318_;
}
}
}
v___jp_346_:
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_dec_lt(v___x_353_, v___x_314_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_box(0);
v___y_332_ = v___y_352_;
v___y_333_ = v___y_347_;
v___y_334_ = v___y_348_;
v___y_335_ = v___y_349_;
v___y_336_ = v___y_351_;
v___y_337_ = v___y_350_;
v___y_338_ = v___x_355_;
goto v___jp_331_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_array_fget_borrowed(v_a_309_, v___x_353_);
lean_inc(v___x_356_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___y_332_ = v___y_352_;
v___y_333_ = v___y_347_;
v___y_334_ = v___y_348_;
v___y_335_ = v___y_349_;
v___y_336_ = v___y_351_;
v___y_337_ = v___y_350_;
v___y_338_ = v___x_357_;
goto v___jp_331_;
}
}
v___jp_358_:
{
if (lean_obj_tag(v___y_360_) == 0)
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_dec_lt(v___x_365_, v___x_314_);
v___y_347_ = v_a_364_;
v___y_348_ = v___y_359_;
v___y_349_ = v___y_361_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_362_;
v___y_352_ = v___x_366_;
goto v___jp_346_;
}
else
{
lean_object* v_val_367_; uint8_t v___x_368_; 
v_val_367_ = lean_ctor_get(v___y_360_, 0);
lean_inc(v_val_367_);
lean_dec_ref(v___y_360_);
v___x_368_ = lean_unbox(v_val_367_);
lean_dec(v_val_367_);
v___y_347_ = v_a_364_;
v___y_348_ = v___y_359_;
v___y_349_ = v___y_361_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_362_;
v___y_352_ = v___x_368_;
goto v___jp_346_;
}
}
v___jp_369_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_376_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_375_);
lean_dec(v_a_282_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
v___y_359_ = v___y_370_;
v___y_360_ = v___y_372_;
v___y_361_ = v___y_371_;
v___y_362_ = v___y_373_;
v___y_363_ = v_a_374_;
v_a_364_ = v___x_377_;
goto v___jp_358_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_379_; 
v_val_378_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_val_378_);
lean_dec_ref(v___x_376_);
v___x_379_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_a_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_389_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_384_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5));
v___x_385_ = lean_string_append(v___x_384_, v_a_380_);
lean_dec(v_a_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_a_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
v_a_390_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_379_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_379_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 0);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; 
v_a_398_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_379_);
v___y_359_ = v___y_370_;
v___y_360_ = v___y_372_;
v___y_361_ = v___y_371_;
v___y_362_ = v___y_373_;
v___y_363_ = v_a_374_;
v_a_364_ = v_a_398_;
goto v___jp_358_;
}
}
}
}
v___jp_399_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_404_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_403_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v___x_405_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7));
return v___x_405_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; 
v_val_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v___x_404_);
v___x_407_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
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
v___x_412_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8));
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
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
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
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_a_426_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_407_);
v___x_427_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_428_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
v___y_370_ = v___y_400_;
v___y_371_ = v_a_402_;
v___y_372_ = v___y_401_;
v___y_373_ = v_a_426_;
v_a_374_ = v___x_429_;
goto v___jp_369_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_431_; 
v_val_430_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_430_);
lean_dec_ref(v___x_428_);
v___x_431_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_a_426_);
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9));
v___x_437_ = lean_string_append(v___x_436_, v_a_432_);
lean_dec(v_a_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_a_426_);
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_442_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_431_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_431_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 0);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_431_);
v___y_370_ = v___y_400_;
v___y_371_ = v_a_402_;
v___y_372_ = v___y_401_;
v___y_373_ = v_a_426_;
v_a_374_ = v_a_450_;
goto v___jp_369_;
}
}
}
}
}
}
}
v___jp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_454_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_453_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_455_; 
lean_dec(v_a_452_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v___x_455_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11));
return v___x_455_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_457_; 
v_val_456_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_val_456_);
lean_dec_ref(v___x_454_);
v___x_457_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
lean_dec(v_a_452_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_467_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12));
v___x_463_ = lean_string_append(v___x_462_, v_a_458_);
lean_dec(v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v_a_452_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_468_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_457_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_457_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 0);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_a_476_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_476_);
lean_dec_ref(v___x_457_);
v___x_477_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_478_ = l_Lake_JsonObject_getJson_x3f(v_a_282_, v___x_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_box(0);
v___y_400_ = v_a_476_;
v___y_401_ = v_a_452_;
v_a_402_ = v___x_479_;
goto v___jp_399_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; 
v_val_480_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_480_);
lean_dec_ref(v___x_478_);
v___x_481_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_a_476_);
lean_dec(v_a_452_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_491_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_486_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13));
v___x_487_ = lean_string_append(v___x_486_, v_a_482_);
lean_dec(v_a_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_a_476_);
lean_dec(v_a_452_);
lean_dec(v___x_317_);
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
lean_del_object(v___x_288_);
lean_dec(v_a_282_);
v_a_492_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_481_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_481_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set_tag(v___x_494_, 0);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_481_);
v___y_400_ = v_a_476_;
v___y_401_ = v_a_452_;
v_a_402_ = v_a_500_;
goto v___jp_399_;
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
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object* v_arts_529_){
_start:
{
lean_object* v_olean_530_; uint8_t v_isModule_531_; lean_object* v_oleanServer_x3f_532_; lean_object* v_oleanPrivate_x3f_533_; lean_object* v_ilean_534_; lean_object* v_ir_x3f_535_; lean_object* v_c_536_; lean_object* v_bc_x3f_537_; lean_object* v_ltar_x3f_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_620_; 
v_olean_530_ = lean_ctor_get(v_arts_529_, 0);
v_isModule_531_ = lean_ctor_get_uint8(v_arts_529_, sizeof(void*)*8);
v_oleanServer_x3f_532_ = lean_ctor_get(v_arts_529_, 1);
v_oleanPrivate_x3f_533_ = lean_ctor_get(v_arts_529_, 2);
v_ilean_534_ = lean_ctor_get(v_arts_529_, 3);
v_ir_x3f_535_ = lean_ctor_get(v_arts_529_, 4);
v_c_536_ = lean_ctor_get(v_arts_529_, 5);
v_bc_x3f_537_ = lean_ctor_get(v_arts_529_, 6);
v_ltar_x3f_538_ = lean_ctor_get(v_arts_529_, 7);
v_isSharedCheck_620_ = !lean_is_exclusive(v_arts_529_);
if (v_isSharedCheck_620_ == 0)
{
v___x_540_ = v_arts_529_;
v_isShared_541_ = v_isSharedCheck_620_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_ltar_x3f_538_);
lean_inc(v_bc_x3f_537_);
lean_inc(v_c_536_);
lean_inc(v_ir_x3f_535_);
lean_inc(v_ilean_534_);
lean_inc(v_oleanPrivate_x3f_533_);
lean_inc(v_oleanServer_x3f_532_);
lean_inc(v_olean_530_);
lean_dec(v_arts_529_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_620_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_descr_542_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_599_; 
v_descr_542_ = lean_ctor_get(v_olean_530_, 0);
lean_inc_ref(v_descr_542_);
lean_dec_ref(v_olean_530_);
if (lean_obj_tag(v_oleanServer_x3f_532_) == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_box(0);
v___y_599_ = v___x_610_;
goto v___jp_598_;
}
else
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_619_; 
v_val_611_ = lean_ctor_get(v_oleanServer_x3f_532_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_oleanServer_x3f_532_);
if (v_isSharedCheck_619_ == 0)
{
v___x_613_ = v_oleanServer_x3f_532_;
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v_oleanServer_x3f_532_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_619_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_descr_615_; lean_object* v___x_617_; 
v_descr_615_ = lean_ctor_get(v_val_611_, 0);
lean_inc_ref(v_descr_615_);
lean_dec(v_val_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_descr_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_descr_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v___y_599_ = v___x_617_;
goto v___jp_598_;
}
}
}
v___jp_543_:
{
if (lean_obj_tag(v_ltar_x3f_538_) == 0)
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 7, v___x_550_);
lean_ctor_set(v___x_540_, 6, v___y_549_);
lean_ctor_set(v___x_540_, 5, v___y_545_);
lean_ctor_set(v___x_540_, 4, v___y_548_);
lean_ctor_set(v___x_540_, 3, v___y_547_);
lean_ctor_set(v___x_540_, 2, v___y_546_);
lean_ctor_set(v___x_540_, 1, v___y_544_);
lean_ctor_set(v___x_540_, 0, v_descr_542_);
v___x_552_ = v___x_540_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_descr_542_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v___y_546_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v___y_548_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v___y_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v___y_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v___x_550_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*8, v_isModule_531_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_565_; 
v_val_554_ = lean_ctor_get(v_ltar_x3f_538_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_ltar_x3f_538_);
if (v_isSharedCheck_565_ == 0)
{
v___x_556_ = v_ltar_x3f_538_;
v_isShared_557_ = v_isSharedCheck_565_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v_ltar_x3f_538_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_565_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_descr_558_; lean_object* v___x_560_; 
v_descr_558_ = lean_ctor_get(v_val_554_, 0);
lean_inc_ref(v_descr_558_);
lean_dec(v_val_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_descr_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_descr_558_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 7, v___x_560_);
lean_ctor_set(v___x_540_, 6, v___y_549_);
lean_ctor_set(v___x_540_, 5, v___y_545_);
lean_ctor_set(v___x_540_, 4, v___y_548_);
lean_ctor_set(v___x_540_, 3, v___y_547_);
lean_ctor_set(v___x_540_, 2, v___y_546_);
lean_ctor_set(v___x_540_, 1, v___y_544_);
lean_ctor_set(v___x_540_, 0, v_descr_542_);
v___x_562_ = v___x_540_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_descr_542_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v___y_546_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v___y_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v___y_545_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v___y_549_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v___x_560_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*8, v_isModule_531_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
v___jp_566_:
{
if (lean_obj_tag(v_bc_x3f_537_) == 0)
{
lean_object* v_descr_571_; lean_object* v___x_572_; 
v_descr_571_ = lean_ctor_get(v_c_536_, 0);
lean_inc_ref(v_descr_571_);
lean_dec_ref(v_c_536_);
v___x_572_ = lean_box(0);
v___y_544_ = v___y_567_;
v___y_545_ = v_descr_571_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_569_;
v___y_548_ = v___y_570_;
v___y_549_ = v___x_572_;
goto v___jp_543_;
}
else
{
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
v_val_573_ = lean_ctor_get(v_bc_x3f_537_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_bc_x3f_537_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v_bc_x3f_537_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v_bc_x3f_537_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_descr_577_; lean_object* v_descr_578_; lean_object* v___x_580_; 
v_descr_577_ = lean_ctor_get(v_c_536_, 0);
lean_inc_ref(v_descr_577_);
lean_dec_ref(v_c_536_);
v_descr_578_ = lean_ctor_get(v_val_573_, 0);
lean_inc_ref(v_descr_578_);
lean_dec(v_val_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_descr_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_descr_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
v___y_544_ = v___y_567_;
v___y_545_ = v_descr_577_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_569_;
v___y_548_ = v___y_570_;
v___y_549_ = v___x_580_;
goto v___jp_543_;
}
}
}
}
v___jp_583_:
{
if (lean_obj_tag(v_ir_x3f_535_) == 0)
{
lean_object* v_descr_586_; lean_object* v___x_587_; 
v_descr_586_ = lean_ctor_get(v_ilean_534_, 0);
lean_inc_ref(v_descr_586_);
lean_dec_ref(v_ilean_534_);
v___x_587_ = lean_box(0);
v___y_567_ = v___y_584_;
v___y_568_ = v___y_585_;
v___y_569_ = v_descr_586_;
v___y_570_ = v___x_587_;
goto v___jp_566_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_597_; 
v_val_588_ = lean_ctor_get(v_ir_x3f_535_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_ir_x3f_535_);
if (v_isSharedCheck_597_ == 0)
{
v___x_590_ = v_ir_x3f_535_;
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_dec(v_ir_x3f_535_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_descr_592_; lean_object* v_descr_593_; lean_object* v___x_595_; 
v_descr_592_ = lean_ctor_get(v_ilean_534_, 0);
lean_inc_ref(v_descr_592_);
lean_dec_ref(v_ilean_534_);
v_descr_593_ = lean_ctor_get(v_val_588_, 0);
lean_inc_ref(v_descr_593_);
lean_dec(v_val_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_descr_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_descr_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v___y_567_ = v___y_584_;
v___y_568_ = v___y_585_;
v___y_569_ = v_descr_592_;
v___y_570_ = v___x_595_;
goto v___jp_566_;
}
}
}
}
v___jp_598_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_533_) == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
v___y_584_ = v___y_599_;
v___y_585_ = v___x_600_;
goto v___jp_583_;
}
else
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_val_601_ = lean_ctor_get(v_oleanPrivate_x3f_533_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_oleanPrivate_x3f_533_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v_oleanPrivate_x3f_533_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v_oleanPrivate_x3f_533_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_descr_605_; lean_object* v___x_607_; 
v_descr_605_ = lean_ctor_get(v_val_601_, 0);
lean_inc_ref(v_descr_605_);
lean_dec(v_val_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_descr_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_descr_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v___y_584_ = v___y_599_;
v___y_585_ = v___x_607_;
goto v___jp_583_;
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
