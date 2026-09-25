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
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_oleanParts(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object*);
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: o"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "o: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "expected at least one 'o' (.olean) hash"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "l: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "b: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "c: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "r: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: i"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "i: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "rs: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "m: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(size_t v_sz_15_, size_t v_i_16_, lean_object* v_bs_17_){
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
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(lean_object* v_sz_38_, lean_object* v_i_39_, lean_object* v_bs_40_){
_start:
{
size_t v_sz_boxed_41_; size_t v_i_boxed_42_; lean_object* v_res_43_; 
v_sz_boxed_41_ = lean_unbox_usize(v_sz_38_);
lean_dec(v_sz_38_);
v_i_boxed_42_ = lean_unbox_usize(v_i_39_);
lean_dec(v_i_39_);
v_res_43_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_boxed_41_, v_i_boxed_42_, v_bs_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(lean_object* v_a_44_){
_start:
{
size_t v_sz_45_; size_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_sz_45_ = lean_array_size(v_a_44_);
v___x_46_ = ((size_t)0ULL);
v___x_47_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_45_, v___x_46_, v_a_44_);
v___x_48_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object* v_self_57_){
_start:
{
lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; uint8_t v_isModule_65_; lean_object* v_ilean_66_; lean_object* v_irSig_x3f_67_; lean_object* v_ir_x3f_68_; lean_object* v_c_x3f_69_; lean_object* v_bc_x3f_70_; lean_object* v_ltar_x3f_71_; lean_object* v_obj_73_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v_obj_94_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v_obj_114_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v_obj_134_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; uint64_t v_hash_153_; lean_object* v_ext_154_; lean_object* v_obj_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_obj_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_obj_162_; lean_object* v___x_163_; lean_object* v___y_165_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_isModule_65_ = lean_ctor_get_uint8(v_self_57_, sizeof(void*)*9);
v_ilean_66_ = lean_ctor_get(v_self_57_, 3);
v_irSig_x3f_67_ = lean_ctor_get(v_self_57_, 4);
lean_inc(v_irSig_x3f_67_);
v_ir_x3f_68_ = lean_ctor_get(v_self_57_, 5);
lean_inc(v_ir_x3f_68_);
v_c_x3f_69_ = lean_ctor_get(v_self_57_, 6);
lean_inc(v_c_x3f_69_);
v_bc_x3f_70_ = lean_ctor_get(v_self_57_, 7);
lean_inc(v_bc_x3f_70_);
v_ltar_x3f_71_ = lean_ctor_get(v_self_57_, 8);
lean_inc(v_ltar_x3f_71_);
v_hash_153_ = lean_ctor_get_uint64(v_ilean_66_, sizeof(void*)*1);
v_ext_154_ = lean_ctor_get(v_ilean_66_, 0);
lean_inc_ref(v_ext_154_);
v_obj_155_ = lean_box(1);
v___x_156_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_157_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_157_, 0, v_isModule_65_);
v_obj_158_ = l_Lake_JsonObject_insertJson(v_obj_155_, v___x_156_, v___x_157_);
v___x_159_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_160_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_57_);
v___x_161_ = l_Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_160_);
v_obj_162_ = l_Lake_JsonObject_insertJson(v_obj_158_, v___x_159_, v___x_161_);
v___x_163_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_180_ = lean_string_utf8_byte_size(v_ext_154_);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_nat_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = l_Lake_lowerHexUInt64(v_hash_153_);
v___x_184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_185_ = lean_string_append(v___x_183_, v___x_184_);
v___x_186_ = lean_string_append(v___x_185_, v_ext_154_);
lean_dec_ref(v_ext_154_);
v___y_165_ = v___x_186_;
goto v___jp_164_;
}
else
{
lean_object* v___x_187_; 
lean_dec_ref(v_ext_154_);
v___x_187_ = l_Lake_lowerHexUInt64(v_hash_153_);
v___y_165_ = v___x_187_;
goto v___jp_164_;
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
v___x_82_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
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
if (lean_obj_tag(v_bc_x3f_70_) == 1)
{
lean_object* v_val_95_; uint64_t v_hash_96_; lean_object* v_ext_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_val_95_ = lean_ctor_get(v_bc_x3f_70_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v_bc_x3f_70_, 1);
v_hash_96_ = lean_ctor_get_uint64(v_val_95_, sizeof(void*)*1);
v_ext_97_ = lean_ctor_get(v_val_95_, 0);
lean_inc_ref(v_ext_97_);
lean_dec(v_val_95_);
v___x_98_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_99_ = lean_string_utf8_byte_size(v_ext_97_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = l_Lake_lowerHexUInt64(v_hash_96_);
v___x_103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_104_ = lean_string_append(v___x_102_, v___x_103_);
v___x_105_ = lean_string_append(v___x_104_, v_ext_97_);
lean_dec_ref(v_ext_97_);
v___y_88_ = v___x_98_;
v___y_89_ = v_obj_94_;
v___y_90_ = v___x_105_;
goto v___jp_87_;
}
else
{
lean_object* v___x_106_; 
lean_dec_ref(v_ext_97_);
v___x_106_ = l_Lake_lowerHexUInt64(v_hash_96_);
v___y_88_ = v___x_98_;
v___y_89_ = v_obj_94_;
v___y_90_ = v___x_106_;
goto v___jp_87_;
}
}
else
{
lean_dec(v_bc_x3f_70_);
v_obj_73_ = v_obj_94_;
goto v___jp_72_;
}
}
v___jp_107_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_111_, 0, v___y_110_);
lean_inc_ref(v___y_109_);
v___x_112_ = l_Lake_JsonObject_insertJson(v___y_108_, v___y_109_, v___x_111_);
v_obj_94_ = v___x_112_;
goto v___jp_93_;
}
v___jp_113_:
{
if (lean_obj_tag(v_c_x3f_69_) == 1)
{
lean_object* v_val_115_; uint64_t v_hash_116_; lean_object* v_ext_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_val_115_ = lean_ctor_get(v_c_x3f_69_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v_c_x3f_69_, 1);
v_hash_116_ = lean_ctor_get_uint64(v_val_115_, sizeof(void*)*1);
v_ext_117_ = lean_ctor_get(v_val_115_, 0);
lean_inc_ref(v_ext_117_);
lean_dec(v_val_115_);
v___x_118_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_119_ = lean_string_utf8_byte_size(v_ext_117_);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_nat_dec_eq(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = l_Lake_lowerHexUInt64(v_hash_116_);
v___x_123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
v___x_125_ = lean_string_append(v___x_124_, v_ext_117_);
lean_dec_ref(v_ext_117_);
v___y_108_ = v_obj_114_;
v___y_109_ = v___x_118_;
v___y_110_ = v___x_125_;
goto v___jp_107_;
}
else
{
lean_object* v___x_126_; 
lean_dec_ref(v_ext_117_);
v___x_126_ = l_Lake_lowerHexUInt64(v_hash_116_);
v___y_108_ = v_obj_114_;
v___y_109_ = v___x_118_;
v___y_110_ = v___x_126_;
goto v___jp_107_;
}
}
else
{
lean_dec(v_c_x3f_69_);
v_obj_94_ = v_obj_114_;
goto v___jp_93_;
}
}
v___jp_127_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___y_130_);
lean_inc_ref(v___y_128_);
v___x_132_ = l_Lake_JsonObject_insertJson(v___y_129_, v___y_128_, v___x_131_);
v_obj_114_ = v___x_132_;
goto v___jp_113_;
}
v___jp_133_:
{
if (lean_obj_tag(v_ir_x3f_68_) == 1)
{
lean_object* v_val_135_; uint64_t v_hash_136_; lean_object* v_ext_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_val_135_ = lean_ctor_get(v_ir_x3f_68_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_ir_x3f_68_, 1);
v_hash_136_ = lean_ctor_get_uint64(v_val_135_, sizeof(void*)*1);
v_ext_137_ = lean_ctor_get(v_val_135_, 0);
lean_inc_ref(v_ext_137_);
lean_dec(v_val_135_);
v___x_138_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_139_ = lean_string_utf8_byte_size(v_ext_137_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_nat_dec_eq(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = l_Lake_lowerHexUInt64(v_hash_136_);
v___x_143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_144_ = lean_string_append(v___x_142_, v___x_143_);
v___x_145_ = lean_string_append(v___x_144_, v_ext_137_);
lean_dec_ref(v_ext_137_);
v___y_128_ = v___x_138_;
v___y_129_ = v_obj_134_;
v___y_130_ = v___x_145_;
goto v___jp_127_;
}
else
{
lean_object* v___x_146_; 
lean_dec_ref(v_ext_137_);
v___x_146_ = l_Lake_lowerHexUInt64(v_hash_136_);
v___y_128_ = v___x_138_;
v___y_129_ = v_obj_134_;
v___y_130_ = v___x_146_;
goto v___jp_127_;
}
}
else
{
lean_dec(v_ir_x3f_68_);
v_obj_114_ = v_obj_134_;
goto v___jp_113_;
}
}
v___jp_147_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_151_, 0, v___y_150_);
lean_inc_ref(v___y_149_);
v___x_152_ = l_Lake_JsonObject_insertJson(v___y_148_, v___y_149_, v___x_151_);
v_obj_134_ = v___x_152_;
goto v___jp_133_;
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_166_, 0, v___y_165_);
v___x_167_ = l_Lake_JsonObject_insertJson(v_obj_162_, v___x_163_, v___x_166_);
if (lean_obj_tag(v_irSig_x3f_67_) == 1)
{
lean_object* v_val_168_; uint64_t v_hash_169_; lean_object* v_ext_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_val_168_ = lean_ctor_get(v_irSig_x3f_67_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v_irSig_x3f_67_, 1);
v_hash_169_ = lean_ctor_get_uint64(v_val_168_, sizeof(void*)*1);
v_ext_170_ = lean_ctor_get(v_val_168_, 0);
lean_inc_ref(v_ext_170_);
lean_dec(v_val_168_);
v___x_171_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_172_ = lean_string_utf8_byte_size(v_ext_170_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_nat_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = l_Lake_lowerHexUInt64(v_hash_169_);
v___x_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
v___x_178_ = lean_string_append(v___x_177_, v_ext_170_);
lean_dec_ref(v_ext_170_);
v___y_148_ = v___x_167_;
v___y_149_ = v___x_171_;
v___y_150_ = v___x_178_;
goto v___jp_147_;
}
else
{
lean_object* v___x_179_; 
lean_dec_ref(v_ext_170_);
v___x_179_ = l_Lake_lowerHexUInt64(v_hash_169_);
v___y_148_ = v___x_167_;
v___y_149_ = v___x_171_;
v___y_150_ = v___x_179_;
goto v___jp_147_;
}
}
else
{
lean_dec(v_irSig_x3f_67_);
v_obj_134_ = v___x_167_;
goto v___jp_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0));
return v___x_193_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_192_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_a_203_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v___x_194_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_194_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v_a_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0));
return v___x_215_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Json_getBool_x3f(v_x_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_a_225_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v___x_216_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_216_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_a_225_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_x_234_);
lean_dec(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t v_sz_236_, size_t v_i_237_, lean_object* v_bs_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_lt(v_i_237_, v_sz_236_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_bs_238_);
return v___x_240_;
}
else
{
lean_object* v_v_241_; lean_object* v___x_242_; 
v_v_241_ = lean_array_uget_borrowed(v_bs_238_, v_i_237_);
lean_inc(v_v_241_);
v___x_242_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_bs_238_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v_bs_x27_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v_a_251_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_242_, 1);
v___x_252_ = lean_unsigned_to_nat(0u);
v_bs_x27_253_ = lean_array_uset(v_bs_238_, v_i_237_, v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_237_, v___x_254_);
v___x_256_ = lean_array_uset(v_bs_x27_253_, v_i_237_, v_a_251_);
v_i_237_ = v___x_255_;
v_bs_238_ = v___x_256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object* v_sz_258_, lean_object* v_i_259_, lean_object* v_bs_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_258_);
lean_dec(v_sz_258_);
v_i_boxed_262_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_261_, v_i_boxed_262_, v_bs_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 4)
{
lean_object* v_elems_267_; size_t v_sz_268_; size_t v___x_269_; lean_object* v___x_270_; 
v_elems_267_ = lean_ctor_get(v_x_266_, 0);
lean_inc_ref(v_elems_267_);
lean_dec_ref_known(v_x_266_, 1);
v_sz_268_ = lean_array_size(v_elems_267_);
v___x_269_ = ((size_t)0ULL);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_268_, v___x_269_, v_elems_267_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_271_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0));
v___x_272_ = lean_unsigned_to_nat(80u);
v___x_273_ = l_Lean_Json_pretty(v_x_266_, v___x_272_);
v___x_274_ = lean_string_append(v___x_271_, v___x_273_);
lean_dec_ref(v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1));
v___x_276_ = lean_string_append(v___x_274_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
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
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_589_; 
v_val_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_589_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_589_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_589_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(v_val_309_);
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
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_588_; 
v_a_332_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_588_ == 0)
{
v___x_334_ = v___x_313_;
v_isShared_335_ = v_isSharedCheck_588_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_313_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_588_;
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
lean_object* v___x_340_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; uint8_t v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v_a_391_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v_a_402_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v_a_432_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v_a_461_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v_a_489_; lean_object* v_a_515_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_340_ = lean_array_fget(v_a_332_, v___x_336_);
v___x_564_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_565_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_564_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_box(0);
v_a_515_ = v___x_566_;
goto v___jp_514_;
}
else
{
lean_object* v_val_567_; lean_object* v___x_568_; 
v_val_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_565_, 1);
v___x_568_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_567_);
lean_dec(v_val_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13));
v___x_574_ = lean_string_append(v___x_573_, v_a_569_);
lean_dec(v_a_569_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_579_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_568_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_568_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; 
v_a_587_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_568_, 1);
v_a_515_ = v_a_587_;
goto v___jp_514_;
}
}
}
v___jp_341_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_351_, 0, v___x_340_);
lean_ctor_set(v___x_351_, 1, v___y_349_);
lean_ctor_set(v___x_351_, 2, v___y_350_);
lean_ctor_set(v___x_351_, 3, v___y_345_);
lean_ctor_set(v___x_351_, 4, v___y_348_);
lean_ctor_set(v___x_351_, 5, v___y_347_);
lean_ctor_set(v___x_351_, 6, v___y_346_);
lean_ctor_set(v___x_351_, 7, v___y_343_);
lean_ctor_set(v___x_351_, 8, v___y_344_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*9, v___y_342_);
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
v___y_344_ = v___y_358_;
v___y_345_ = v___y_359_;
v___y_346_ = v___y_361_;
v___y_347_ = v___y_360_;
v___y_348_ = v___y_362_;
v___y_349_ = v___y_363_;
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
v___y_344_ = v___y_358_;
v___y_345_ = v___y_359_;
v___y_346_ = v___y_361_;
v___y_347_ = v___y_360_;
v___y_348_ = v___y_362_;
v___y_349_ = v___y_363_;
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
v___y_356_ = v___y_378_;
v___y_357_ = v___y_372_;
v___y_358_ = v___y_373_;
v___y_359_ = v___y_374_;
v___y_360_ = v___y_376_;
v___y_361_ = v___y_375_;
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
v___y_356_ = v___y_378_;
v___y_357_ = v___y_372_;
v___y_358_ = v___y_373_;
v___y_359_ = v___y_374_;
v___y_360_ = v___y_376_;
v___y_361_ = v___y_375_;
v___y_362_ = v___y_377_;
v___y_363_ = v___x_383_;
goto v___jp_355_;
}
}
v___jp_384_:
{
if (lean_obj_tag(v___y_387_) == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_dec_lt(v___x_392_, v___x_337_);
v___y_372_ = v___y_385_;
v___y_373_ = v_a_391_;
v___y_374_ = v___y_386_;
v___y_375_ = v___y_389_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_390_;
v___y_378_ = v___x_393_;
goto v___jp_371_;
}
else
{
lean_object* v_val_394_; uint8_t v___x_395_; 
v_val_394_ = lean_ctor_get(v___y_387_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___y_387_, 1);
v___x_395_ = lean_unbox(v_val_394_);
lean_dec(v_val_394_);
v___y_372_ = v___y_385_;
v___y_373_ = v_a_391_;
v___y_374_ = v___y_386_;
v___y_375_ = v___y_389_;
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
v___y_385_ = v_a_402_;
v___y_386_ = v___y_397_;
v___y_387_ = v___y_400_;
v___y_388_ = v___y_399_;
v___y_389_ = v___y_398_;
v___y_390_ = v___y_401_;
v_a_391_ = v___x_405_;
goto v___jp_384_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; 
v_val_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v___x_404_, 1);
v___x_407_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_402_);
lean_dec(v___y_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
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
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
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
v___y_385_ = v_a_402_;
v___y_386_ = v___y_397_;
v___y_387_ = v___y_400_;
v___y_388_ = v___y_399_;
v___y_389_ = v___y_398_;
v___y_390_ = v___y_401_;
v_a_391_ = v_a_426_;
goto v___jp_384_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_434_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
v___y_397_ = v___y_428_;
v___y_398_ = v_a_432_;
v___y_399_ = v___y_430_;
v___y_400_ = v___y_429_;
v___y_401_ = v___y_431_;
v_a_402_ = v___x_435_;
goto v___jp_396_;
}
else
{
lean_object* v_val_436_; lean_object* v___x_437_; 
v_val_436_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_434_, 1);
v___x_437_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_a_432_);
lean_dec(v___y_431_);
lean_dec(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_442_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6));
v___x_443_ = lean_string_append(v___x_442_, v_a_438_);
lean_dec(v_a_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_432_);
lean_dec(v___y_431_);
lean_dec(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_448_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_437_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; 
v_a_456_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_437_, 1);
v___y_397_ = v___y_428_;
v___y_398_ = v_a_432_;
v___y_399_ = v___y_430_;
v___y_400_ = v___y_429_;
v___y_401_ = v___y_431_;
v_a_402_ = v_a_456_;
goto v___jp_396_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_463_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
v___y_428_ = v___y_458_;
v___y_429_ = v___y_459_;
v___y_430_ = v_a_461_;
v___y_431_ = v___y_460_;
v_a_432_ = v___x_464_;
goto v___jp_427_;
}
else
{
lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_465_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_463_, 1);
v___x_466_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_a_461_);
lean_dec(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7));
v___x_472_ = lean_string_append(v___x_471_, v_a_467_);
lean_dec(v_a_467_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_a_461_);
lean_dec(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_477_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_466_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_466_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 0);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; 
v_a_485_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_466_, 1);
v___y_428_ = v___y_458_;
v___y_429_ = v___y_459_;
v___y_430_ = v_a_461_;
v___y_431_ = v___y_460_;
v_a_432_ = v_a_485_;
goto v___jp_427_;
}
}
}
}
v___jp_486_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_491_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
v___y_458_ = v___y_487_;
v___y_459_ = v___y_488_;
v___y_460_ = v_a_489_;
v_a_461_ = v___x_492_;
goto v___jp_457_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_494_; 
v_val_493_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v___x_491_, 1);
v___x_494_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_493_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_a_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_504_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_504_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_504_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8));
v___x_500_ = lean_string_append(v___x_499_, v_a_495_);
lean_dec(v_a_495_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_a_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_505_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_494_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_494_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 0);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; 
v_a_513_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_494_, 1);
v___y_458_ = v___y_487_;
v___y_459_ = v___y_488_;
v___y_460_ = v_a_489_;
v_a_461_ = v_a_513_;
goto v___jp_457_;
}
}
}
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_517_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; 
lean_dec(v_a_515_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v___x_518_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10));
return v___x_518_;
}
else
{
lean_object* v_val_519_; lean_object* v___x_520_; 
v_val_519_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v___x_517_, 1);
v___x_520_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_515_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_530_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_525_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11));
v___x_526_ = lean_string_append(v___x_525_, v_a_521_);
lean_dec(v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_515_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_531_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_520_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_520_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 0);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_a_539_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_520_, 1);
v___x_540_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_541_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
v___y_487_ = v_a_539_;
v___y_488_ = v_a_515_;
v_a_489_ = v___x_542_;
goto v___jp_486_;
}
else
{
lean_object* v_val_543_; lean_object* v___x_544_; 
v_val_543_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v___x_541_, 1);
v___x_544_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_539_);
lean_dec(v_a_515_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_554_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12));
v___x_550_ = lean_string_append(v___x_549_, v_a_545_);
lean_dec(v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_550_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_539_);
lean_dec(v_a_515_);
lean_dec(v___x_340_);
lean_del_object(v___x_334_);
lean_dec(v_a_332_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_555_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_544_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_544_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; 
v_a_563_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_544_, 1);
v___y_487_ = v_a_539_;
v___y_488_ = v_a_515_;
v_a_489_ = v_a_563_;
goto v___jp_486_;
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
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object* v_arts_592_){
_start:
{
lean_object* v_olean_593_; uint8_t v_isModule_594_; lean_object* v_oleanServer_x3f_595_; lean_object* v_oleanPrivate_x3f_596_; lean_object* v_ilean_597_; lean_object* v_irSig_x3f_598_; lean_object* v_ir_x3f_599_; lean_object* v_c_x3f_600_; lean_object* v_bc_x3f_601_; lean_object* v_ltar_x3f_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_716_; 
v_olean_593_ = lean_ctor_get(v_arts_592_, 0);
v_isModule_594_ = lean_ctor_get_uint8(v_arts_592_, sizeof(void*)*9);
v_oleanServer_x3f_595_ = lean_ctor_get(v_arts_592_, 1);
v_oleanPrivate_x3f_596_ = lean_ctor_get(v_arts_592_, 2);
v_ilean_597_ = lean_ctor_get(v_arts_592_, 3);
v_irSig_x3f_598_ = lean_ctor_get(v_arts_592_, 4);
v_ir_x3f_599_ = lean_ctor_get(v_arts_592_, 5);
v_c_x3f_600_ = lean_ctor_get(v_arts_592_, 6);
v_bc_x3f_601_ = lean_ctor_get(v_arts_592_, 7);
v_ltar_x3f_602_ = lean_ctor_get(v_arts_592_, 8);
v_isSharedCheck_716_ = !lean_is_exclusive(v_arts_592_);
if (v_isSharedCheck_716_ == 0)
{
v___x_604_ = v_arts_592_;
v_isShared_605_ = v_isSharedCheck_716_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_ltar_x3f_602_);
lean_inc(v_bc_x3f_601_);
lean_inc(v_c_x3f_600_);
lean_inc(v_ir_x3f_599_);
lean_inc(v_irSig_x3f_598_);
lean_inc(v_ilean_597_);
lean_inc(v_oleanPrivate_x3f_596_);
lean_inc(v_oleanServer_x3f_595_);
lean_inc(v_olean_593_);
lean_dec(v_arts_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_716_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_descr_606_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_695_; 
v_descr_606_ = lean_ctor_get(v_olean_593_, 0);
lean_inc_ref(v_descr_606_);
lean_dec_ref(v_olean_593_);
if (lean_obj_tag(v_oleanServer_x3f_595_) == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_box(0);
v___y_695_ = v___x_706_;
goto v___jp_694_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_val_707_ = lean_ctor_get(v_oleanServer_x3f_595_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v_oleanServer_x3f_595_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v_oleanServer_x3f_595_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v_oleanServer_x3f_595_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_descr_711_; lean_object* v___x_713_; 
v_descr_711_ = lean_ctor_get(v_val_707_, 0);
lean_inc_ref(v_descr_711_);
lean_dec(v_val_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_descr_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_descr_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v___y_695_ = v___x_713_;
goto v___jp_694_;
}
}
}
v___jp_607_:
{
if (lean_obj_tag(v_ltar_x3f_602_) == 0)
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_box(0);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 8, v___x_615_);
lean_ctor_set(v___x_604_, 7, v___y_614_);
lean_ctor_set(v___x_604_, 6, v___y_608_);
lean_ctor_set(v___x_604_, 5, v___y_611_);
lean_ctor_set(v___x_604_, 4, v___y_613_);
lean_ctor_set(v___x_604_, 3, v___y_609_);
lean_ctor_set(v___x_604_, 2, v___y_610_);
lean_ctor_set(v___x_604_, 1, v___y_612_);
lean_ctor_set(v___x_604_, 0, v_descr_606_);
v___x_617_ = v___x_604_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_descr_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___y_612_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___y_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v___y_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v___y_613_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v___y_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v___y_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v___y_614_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v___x_615_);
lean_ctor_set_uint8(v_reuseFailAlloc_618_, sizeof(void*)*9, v_isModule_594_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v_val_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_630_; 
v_val_619_ = lean_ctor_get(v_ltar_x3f_602_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_ltar_x3f_602_);
if (v_isSharedCheck_630_ == 0)
{
v___x_621_ = v_ltar_x3f_602_;
v_isShared_622_ = v_isSharedCheck_630_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_val_619_);
lean_dec(v_ltar_x3f_602_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_630_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_descr_623_; lean_object* v___x_625_; 
v_descr_623_ = lean_ctor_get(v_val_619_, 0);
lean_inc_ref(v_descr_623_);
lean_dec(v_val_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_descr_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_descr_623_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 8, v___x_625_);
lean_ctor_set(v___x_604_, 7, v___y_614_);
lean_ctor_set(v___x_604_, 6, v___y_608_);
lean_ctor_set(v___x_604_, 5, v___y_611_);
lean_ctor_set(v___x_604_, 4, v___y_613_);
lean_ctor_set(v___x_604_, 3, v___y_609_);
lean_ctor_set(v___x_604_, 2, v___y_610_);
lean_ctor_set(v___x_604_, 1, v___y_612_);
lean_ctor_set(v___x_604_, 0, v_descr_606_);
v___x_627_ = v___x_604_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_descr_606_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___y_612_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v___y_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v___y_609_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v___y_613_);
lean_ctor_set(v_reuseFailAlloc_628_, 5, v___y_611_);
lean_ctor_set(v_reuseFailAlloc_628_, 6, v___y_608_);
lean_ctor_set(v_reuseFailAlloc_628_, 7, v___y_614_);
lean_ctor_set(v_reuseFailAlloc_628_, 8, v___x_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_628_, sizeof(void*)*9, v_isModule_594_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
v___jp_631_:
{
if (lean_obj_tag(v_bc_x3f_601_) == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_box(0);
v___y_608_ = v___y_637_;
v___y_609_ = v___y_632_;
v___y_610_ = v___y_633_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_634_;
v___y_613_ = v___y_636_;
v___y_614_ = v___x_638_;
goto v___jp_607_;
}
else
{
lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_val_639_ = lean_ctor_get(v_bc_x3f_601_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_bc_x3f_601_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_bc_x3f_601_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_dec(v_bc_x3f_601_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_descr_643_; lean_object* v___x_645_; 
v_descr_643_ = lean_ctor_get(v_val_639_, 0);
lean_inc_ref(v_descr_643_);
lean_dec(v_val_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_descr_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_descr_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v___y_608_ = v___y_637_;
v___y_609_ = v___y_632_;
v___y_610_ = v___y_633_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_634_;
v___y_613_ = v___y_636_;
v___y_614_ = v___x_645_;
goto v___jp_607_;
}
}
}
}
v___jp_648_:
{
if (lean_obj_tag(v_c_x3f_600_) == 0)
{
lean_object* v___x_654_; 
v___x_654_ = lean_box(0);
v___y_632_ = v___y_649_;
v___y_633_ = v___y_650_;
v___y_634_ = v___y_651_;
v___y_635_ = v___y_653_;
v___y_636_ = v___y_652_;
v___y_637_ = v___x_654_;
goto v___jp_631_;
}
else
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_val_655_ = lean_ctor_get(v_c_x3f_600_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_c_x3f_600_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v_c_x3f_600_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v_c_x3f_600_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_descr_659_; lean_object* v___x_661_; 
v_descr_659_ = lean_ctor_get(v_val_655_, 0);
lean_inc_ref(v_descr_659_);
lean_dec(v_val_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_descr_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_descr_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v___y_632_ = v___y_649_;
v___y_633_ = v___y_650_;
v___y_634_ = v___y_651_;
v___y_635_ = v___y_653_;
v___y_636_ = v___y_652_;
v___y_637_ = v___x_661_;
goto v___jp_631_;
}
}
}
}
v___jp_664_:
{
if (lean_obj_tag(v_ir_x3f_599_) == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
v___y_649_ = v___y_665_;
v___y_650_ = v___y_666_;
v___y_651_ = v___y_667_;
v___y_652_ = v___y_668_;
v___y_653_ = v___x_669_;
goto v___jp_648_;
}
else
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_val_670_ = lean_ctor_get(v_ir_x3f_599_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_ir_x3f_599_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_ir_x3f_599_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v_ir_x3f_599_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_descr_674_; lean_object* v___x_676_; 
v_descr_674_ = lean_ctor_get(v_val_670_, 0);
lean_inc_ref(v_descr_674_);
lean_dec(v_val_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_descr_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_descr_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v___y_649_ = v___y_665_;
v___y_650_ = v___y_666_;
v___y_651_ = v___y_667_;
v___y_652_ = v___y_668_;
v___y_653_ = v___x_676_;
goto v___jp_648_;
}
}
}
}
v___jp_679_:
{
if (lean_obj_tag(v_irSig_x3f_598_) == 0)
{
lean_object* v_descr_682_; lean_object* v___x_683_; 
v_descr_682_ = lean_ctor_get(v_ilean_597_, 0);
lean_inc_ref(v_descr_682_);
lean_dec_ref(v_ilean_597_);
v___x_683_ = lean_box(0);
v___y_665_ = v_descr_682_;
v___y_666_ = v___y_681_;
v___y_667_ = v___y_680_;
v___y_668_ = v___x_683_;
goto v___jp_664_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_val_684_ = lean_ctor_get(v_irSig_x3f_598_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_irSig_x3f_598_);
if (v_isSharedCheck_693_ == 0)
{
v___x_686_ = v_irSig_x3f_598_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v_irSig_x3f_598_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_descr_688_; lean_object* v_descr_689_; lean_object* v___x_691_; 
v_descr_688_ = lean_ctor_get(v_ilean_597_, 0);
lean_inc_ref(v_descr_688_);
lean_dec_ref(v_ilean_597_);
v_descr_689_ = lean_ctor_get(v_val_684_, 0);
lean_inc_ref(v_descr_689_);
lean_dec(v_val_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_descr_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_descr_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v___y_665_ = v_descr_688_;
v___y_666_ = v___y_681_;
v___y_667_ = v___y_680_;
v___y_668_ = v___x_691_;
goto v___jp_664_;
}
}
}
}
v___jp_694_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_596_) == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_box(0);
v___y_680_ = v___y_695_;
v___y_681_ = v___x_696_;
goto v___jp_679_;
}
else
{
lean_object* v_val_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
v_val_697_ = lean_ctor_get(v_oleanPrivate_x3f_596_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_oleanPrivate_x3f_596_);
if (v_isSharedCheck_705_ == 0)
{
v___x_699_ = v_oleanPrivate_x3f_596_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_val_697_);
lean_dec(v_oleanPrivate_x3f_596_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_descr_701_; lean_object* v___x_703_; 
v_descr_701_ = lean_ctor_get(v_val_697_, 0);
lean_inc_ref(v_descr_701_);
lean_dec(v_val_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v_descr_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_descr_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_680_ = v___y_695_;
v___y_681_ = v___x_703_;
goto v___jp_679_;
}
}
}
}
}
}
}
lean_object* runtime_initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_ModuleArtifacts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
