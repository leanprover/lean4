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
lean_inc_ref(v___y_60_);
v___x_63_ = l_Lake_JsonObject_insertJson(v___y_59_, v___y_60_, v___x_62_);
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
v___y_59_ = v_obj_73_;
v___y_60_ = v___x_77_;
v___y_61_ = v___x_84_;
goto v___jp_58_;
}
else
{
lean_object* v___x_85_; 
lean_dec_ref(v_ext_76_);
v___x_85_ = l_Lake_lowerHexUInt64(v_hash_75_);
v___y_59_ = v_obj_73_;
v___y_60_ = v___x_77_;
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
lean_inc_ref(v___y_108_);
v___x_112_ = l_Lake_JsonObject_insertJson(v___y_109_, v___y_108_, v___x_111_);
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
v___y_108_ = v___x_118_;
v___y_109_ = v_obj_114_;
v___y_110_ = v___x_125_;
goto v___jp_107_;
}
else
{
lean_object* v___x_126_; 
lean_dec_ref(v_ext_117_);
v___x_126_ = l_Lake_lowerHexUInt64(v_hash_116_);
v___y_108_ = v___x_118_;
v___y_109_ = v_obj_114_;
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
lean_inc_ref(v___y_129_);
v___x_132_ = l_Lake_JsonObject_insertJson(v___y_128_, v___y_129_, v___x_131_);
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
v___y_128_ = v_obj_134_;
v___y_129_ = v___x_138_;
v___y_130_ = v___x_145_;
goto v___jp_127_;
}
else
{
lean_object* v___x_146_; 
lean_dec_ref(v_ext_137_);
v___x_146_ = l_Lake_lowerHexUInt64(v_hash_136_);
v___y_128_ = v_obj_134_;
v___y_129_ = v___x_138_;
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
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_525_; 
v_val_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_525_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_525_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_525_;
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
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_524_; 
v_a_324_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_524_ == 0)
{
v___x_326_ = v___x_313_;
v_isShared_327_ = v_isSharedCheck_524_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_313_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_524_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_array_get_size(v_a_324_);
v___x_330_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v___x_331_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4));
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___y_334_; lean_object* v___y_335_; uint8_t v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint8_t v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; uint8_t v___y_370_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v_a_383_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v_a_394_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v_a_416_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v_a_437_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v_a_457_; lean_object* v_a_475_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_332_ = lean_array_fget(v_a_324_, v___x_328_);
v___x_508_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_509_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(0);
v_a_475_ = v___x_510_;
goto v___jp_474_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; 
v_val_511_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v___x_509_, 1);
v___x_512_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_511_);
lean_dec(v_val_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_522_; 
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_522_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_522_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_522_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_517_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13));
v___x_518_ = lean_string_append(v___x_517_, v_a_513_);
lean_dec(v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_518_);
v___x_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_512_, 1);
v_a_475_ = v_a_523_;
goto v___jp_474_;
}
}
v___jp_333_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_343_, 0, v___x_332_);
lean_ctor_set(v___x_343_, 1, v___y_335_);
lean_ctor_set(v___x_343_, 2, v___y_342_);
lean_ctor_set(v___x_343_, 3, v___y_341_);
lean_ctor_set(v___x_343_, 4, v___y_339_);
lean_ctor_set(v___x_343_, 5, v___y_340_);
lean_ctor_set(v___x_343_, 6, v___y_338_);
lean_ctor_set(v___x_343_, 7, v___y_334_);
lean_ctor_set(v___x_343_, 8, v___y_337_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*9, v___y_336_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_343_);
v___x_345_ = v___x_326_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
v___jp_347_:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(2u);
v___x_357_ = lean_nat_dec_lt(v___x_356_, v___x_329_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
v___x_358_ = lean_box(0);
v___y_334_ = v___y_349_;
v___y_335_ = v___y_355_;
v___y_336_ = v___y_348_;
v___y_337_ = v___y_351_;
v___y_338_ = v___y_350_;
v___y_339_ = v___y_352_;
v___y_340_ = v___y_353_;
v___y_341_ = v___y_354_;
v___y_342_ = v___x_358_;
goto v___jp_333_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_array_fget(v_a_324_, v___x_356_);
lean_dec(v_a_324_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_359_);
v___x_361_ = v___x_311_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v___y_334_ = v___y_349_;
v___y_335_ = v___y_355_;
v___y_336_ = v___y_348_;
v___y_337_ = v___y_351_;
v___y_338_ = v___y_350_;
v___y_339_ = v___y_352_;
v___y_340_ = v___y_353_;
v___y_341_ = v___y_354_;
v___y_342_ = v___x_361_;
goto v___jp_333_;
}
}
}
v___jp_363_:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_dec_lt(v___x_371_, v___x_329_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
v___y_348_ = v___y_370_;
v___y_349_ = v___y_364_;
v___y_350_ = v___y_366_;
v___y_351_ = v___y_365_;
v___y_352_ = v___y_367_;
v___y_353_ = v___y_368_;
v___y_354_ = v___y_369_;
v___y_355_ = v___x_373_;
goto v___jp_347_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_array_fget_borrowed(v_a_324_, v___x_371_);
lean_inc(v___x_374_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
v___y_348_ = v___y_370_;
v___y_349_ = v___y_364_;
v___y_350_ = v___y_366_;
v___y_351_ = v___y_365_;
v___y_352_ = v___y_367_;
v___y_353_ = v___y_368_;
v___y_354_ = v___y_369_;
v___y_355_ = v___x_375_;
goto v___jp_347_;
}
}
v___jp_376_:
{
if (lean_obj_tag(v___y_379_) == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_dec_lt(v___x_384_, v___x_329_);
v___y_364_ = v___y_377_;
v___y_365_ = v_a_383_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_380_;
v___y_368_ = v___y_381_;
v___y_369_ = v___y_382_;
v___y_370_ = v___x_385_;
goto v___jp_363_;
}
else
{
lean_object* v_val_386_; uint8_t v___x_387_; 
v_val_386_ = lean_ctor_get(v___y_379_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___y_379_, 1);
v___x_387_ = lean_unbox(v_val_386_);
lean_dec(v_val_386_);
v___y_364_ = v___y_377_;
v___y_365_ = v_a_383_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_380_;
v___y_368_ = v___y_381_;
v___y_369_ = v___y_382_;
v___y_370_ = v___x_387_;
goto v___jp_363_;
}
}
v___jp_388_:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_396_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_395_);
lean_dec(v_a_305_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_box(0);
v___y_377_ = v_a_394_;
v___y_378_ = v___y_389_;
v___y_379_ = v___y_390_;
v___y_380_ = v___y_391_;
v___y_381_ = v___y_392_;
v___y_382_ = v___y_393_;
v_a_383_ = v___x_397_;
goto v___jp_376_;
}
else
{
lean_object* v_val_398_; lean_object* v___x_399_; 
v_val_398_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v___x_396_, 1);
v___x_399_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_398_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_a_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec(v___y_391_);
lean_dec(v___y_390_);
lean_dec(v___y_389_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_409_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_404_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5));
v___x_405_ = lean_string_append(v___x_404_, v_a_400_);
lean_dec(v_a_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_399_, 1);
v___y_377_ = v_a_394_;
v___y_378_ = v___y_389_;
v___y_379_ = v___y_390_;
v___y_380_ = v___y_391_;
v___y_381_ = v___y_392_;
v___y_382_ = v___y_393_;
v_a_383_ = v_a_410_;
goto v___jp_376_;
}
}
}
v___jp_411_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_418_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_box(0);
v___y_389_ = v_a_416_;
v___y_390_ = v___y_412_;
v___y_391_ = v___y_413_;
v___y_392_ = v___y_414_;
v___y_393_ = v___y_415_;
v_a_394_ = v___x_419_;
goto v___jp_388_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_421_; 
v_val_420_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v___x_418_, 1);
v___x_421_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_a_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec(v___y_413_);
lean_dec(v___y_412_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_431_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6));
v___x_427_ = lean_string_append(v___x_426_, v_a_422_);
lean_dec(v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_427_);
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; 
v_a_432_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_421_, 1);
v___y_389_ = v_a_416_;
v___y_390_ = v___y_412_;
v___y_391_ = v___y_413_;
v___y_392_ = v___y_414_;
v___y_393_ = v___y_415_;
v_a_394_ = v_a_432_;
goto v___jp_388_;
}
}
}
v___jp_433_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_439_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_box(0);
v___y_412_ = v___y_434_;
v___y_413_ = v___y_435_;
v___y_414_ = v_a_437_;
v___y_415_ = v___y_436_;
v_a_416_ = v___x_440_;
goto v___jp_411_;
}
else
{
lean_object* v_val_441_; lean_object* v___x_442_; 
v_val_441_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_441_);
lean_dec_ref_known(v___x_439_, 1);
v___x_442_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_a_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec(v___y_434_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_452_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_452_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_452_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_447_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7));
v___x_448_ = lean_string_append(v___x_447_, v_a_443_);
lean_dec(v_a_443_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_448_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
lean_object* v_a_453_; 
v_a_453_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_442_, 1);
v___y_412_ = v___y_434_;
v___y_413_ = v___y_435_;
v___y_414_ = v_a_437_;
v___y_415_ = v___y_436_;
v_a_416_ = v_a_453_;
goto v___jp_411_;
}
}
}
v___jp_454_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_459_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
v___y_434_ = v___y_455_;
v___y_435_ = v_a_457_;
v___y_436_ = v___y_456_;
v_a_437_ = v___x_460_;
goto v___jp_433_;
}
else
{
lean_object* v_val_461_; lean_object* v___x_462_; 
v_val_461_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_459_, 1);
v___x_462_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_a_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_472_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8));
v___x_468_ = lean_string_append(v___x_467_, v_a_463_);
lean_dec(v_a_463_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_462_, 1);
v___y_434_ = v___y_455_;
v___y_435_ = v_a_457_;
v___y_436_ = v___y_456_;
v_a_437_ = v_a_473_;
goto v___jp_433_;
}
}
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_477_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
lean_dec(v_a_475_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v___x_478_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10));
return v___x_478_;
}
else
{
lean_object* v_val_479_; lean_object* v___x_480_; 
v_val_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v___x_477_, 1);
v___x_480_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_a_475_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11));
v___x_486_ = lean_string_append(v___x_485_, v_a_481_);
lean_dec(v_a_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_491_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_480_, 1);
v___x_492_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_493_ = l_Lake_JsonObject_getJson_x3f(v_a_305_, v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
v___y_455_ = v_a_475_;
v___y_456_ = v_a_491_;
v_a_457_ = v___x_494_;
goto v___jp_454_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
v_val_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_493_, 1);
v___x_496_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_495_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_491_);
lean_dec(v_a_475_);
lean_dec(v___x_332_);
lean_del_object(v___x_326_);
lean_dec(v_a_324_);
lean_del_object(v___x_311_);
lean_dec(v_a_305_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_506_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12));
v___x_502_ = lean_string_append(v___x_501_, v_a_497_);
lean_dec(v_a_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
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
v_a_507_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_496_, 1);
v___y_455_ = v_a_475_;
v___y_456_ = v_a_491_;
v_a_457_ = v_a_507_;
goto v___jp_454_;
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
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object* v_arts_528_){
_start:
{
lean_object* v_olean_529_; uint8_t v_isModule_530_; lean_object* v_oleanServer_x3f_531_; lean_object* v_oleanPrivate_x3f_532_; lean_object* v_ilean_533_; lean_object* v_irSig_x3f_534_; lean_object* v_ir_x3f_535_; lean_object* v_c_x3f_536_; lean_object* v_bc_x3f_537_; lean_object* v_ltar_x3f_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_652_; 
v_olean_529_ = lean_ctor_get(v_arts_528_, 0);
v_isModule_530_ = lean_ctor_get_uint8(v_arts_528_, sizeof(void*)*9);
v_oleanServer_x3f_531_ = lean_ctor_get(v_arts_528_, 1);
v_oleanPrivate_x3f_532_ = lean_ctor_get(v_arts_528_, 2);
v_ilean_533_ = lean_ctor_get(v_arts_528_, 3);
v_irSig_x3f_534_ = lean_ctor_get(v_arts_528_, 4);
v_ir_x3f_535_ = lean_ctor_get(v_arts_528_, 5);
v_c_x3f_536_ = lean_ctor_get(v_arts_528_, 6);
v_bc_x3f_537_ = lean_ctor_get(v_arts_528_, 7);
v_ltar_x3f_538_ = lean_ctor_get(v_arts_528_, 8);
v_isSharedCheck_652_ = !lean_is_exclusive(v_arts_528_);
if (v_isSharedCheck_652_ == 0)
{
v___x_540_ = v_arts_528_;
v_isShared_541_ = v_isSharedCheck_652_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_ltar_x3f_538_);
lean_inc(v_bc_x3f_537_);
lean_inc(v_c_x3f_536_);
lean_inc(v_ir_x3f_535_);
lean_inc(v_irSig_x3f_534_);
lean_inc(v_ilean_533_);
lean_inc(v_oleanPrivate_x3f_532_);
lean_inc(v_oleanServer_x3f_531_);
lean_inc(v_olean_529_);
lean_dec(v_arts_528_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_652_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_descr_542_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_631_; 
v_descr_542_ = lean_ctor_get(v_olean_529_, 0);
lean_inc_ref(v_descr_542_);
lean_dec_ref(v_olean_529_);
if (lean_obj_tag(v_oleanServer_x3f_531_) == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_box(0);
v___y_631_ = v___x_642_;
goto v___jp_630_;
}
else
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_val_643_ = lean_ctor_get(v_oleanServer_x3f_531_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_oleanServer_x3f_531_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_oleanServer_x3f_531_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v_oleanServer_x3f_531_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_descr_647_; lean_object* v___x_649_; 
v_descr_647_ = lean_ctor_get(v_val_643_, 0);
lean_inc_ref(v_descr_647_);
lean_dec(v_val_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_descr_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_descr_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v___y_631_ = v___x_649_;
goto v___jp_630_;
}
}
}
v___jp_543_:
{
if (lean_obj_tag(v_ltar_x3f_538_) == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 8, v___x_551_);
lean_ctor_set(v___x_540_, 7, v___y_550_);
lean_ctor_set(v___x_540_, 6, v___y_549_);
lean_ctor_set(v___x_540_, 5, v___y_544_);
lean_ctor_set(v___x_540_, 4, v___y_546_);
lean_ctor_set(v___x_540_, 3, v___y_547_);
lean_ctor_set(v___x_540_, 2, v___y_545_);
lean_ctor_set(v___x_540_, 1, v___y_548_);
lean_ctor_set(v___x_540_, 0, v_descr_542_);
v___x_553_ = v___x_540_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_descr_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___y_548_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v___y_545_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v___y_546_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v___y_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v___y_550_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v___x_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*9, v_isModule_530_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_val_555_ = lean_ctor_get(v_ltar_x3f_538_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_ltar_x3f_538_);
if (v_isSharedCheck_566_ == 0)
{
v___x_557_ = v_ltar_x3f_538_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v_ltar_x3f_538_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_descr_559_; lean_object* v___x_561_; 
v_descr_559_ = lean_ctor_get(v_val_555_, 0);
lean_inc_ref(v_descr_559_);
lean_dec(v_val_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_descr_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_descr_559_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 8, v___x_561_);
lean_ctor_set(v___x_540_, 7, v___y_550_);
lean_ctor_set(v___x_540_, 6, v___y_549_);
lean_ctor_set(v___x_540_, 5, v___y_544_);
lean_ctor_set(v___x_540_, 4, v___y_546_);
lean_ctor_set(v___x_540_, 3, v___y_547_);
lean_ctor_set(v___x_540_, 2, v___y_545_);
lean_ctor_set(v___x_540_, 1, v___y_548_);
lean_ctor_set(v___x_540_, 0, v_descr_542_);
v___x_563_ = v___x_540_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_descr_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___y_548_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v___y_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v___y_546_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v___y_549_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v___y_550_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v___x_561_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*9, v_isModule_530_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
v___jp_567_:
{
if (lean_obj_tag(v_bc_x3f_537_) == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_box(0);
v___y_544_ = v___y_568_;
v___y_545_ = v___y_569_;
v___y_546_ = v___y_570_;
v___y_547_ = v___y_571_;
v___y_548_ = v___y_572_;
v___y_549_ = v___y_573_;
v___y_550_ = v___x_574_;
goto v___jp_543_;
}
else
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
v_val_575_ = lean_ctor_get(v_bc_x3f_537_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_bc_x3f_537_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v_bc_x3f_537_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v_bc_x3f_537_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_descr_579_; lean_object* v___x_581_; 
v_descr_579_ = lean_ctor_get(v_val_575_, 0);
lean_inc_ref(v_descr_579_);
lean_dec(v_val_575_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_descr_579_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_descr_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v___y_544_ = v___y_568_;
v___y_545_ = v___y_569_;
v___y_546_ = v___y_570_;
v___y_547_ = v___y_571_;
v___y_548_ = v___y_572_;
v___y_549_ = v___y_573_;
v___y_550_ = v___x_581_;
goto v___jp_543_;
}
}
}
}
v___jp_584_:
{
if (lean_obj_tag(v_c_x3f_536_) == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
v___y_568_ = v___y_589_;
v___y_569_ = v___y_585_;
v___y_570_ = v___y_586_;
v___y_571_ = v___y_587_;
v___y_572_ = v___y_588_;
v___y_573_ = v___x_590_;
goto v___jp_567_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_val_591_ = lean_ctor_get(v_c_x3f_536_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_c_x3f_536_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_c_x3f_536_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v_c_x3f_536_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_descr_595_; lean_object* v___x_597_; 
v_descr_595_ = lean_ctor_get(v_val_591_, 0);
lean_inc_ref(v_descr_595_);
lean_dec(v_val_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_descr_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_descr_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
v___y_568_ = v___y_589_;
v___y_569_ = v___y_585_;
v___y_570_ = v___y_586_;
v___y_571_ = v___y_587_;
v___y_572_ = v___y_588_;
v___y_573_ = v___x_597_;
goto v___jp_567_;
}
}
}
}
v___jp_600_:
{
if (lean_obj_tag(v_ir_x3f_535_) == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_box(0);
v___y_585_ = v___y_601_;
v___y_586_ = v___y_604_;
v___y_587_ = v___y_602_;
v___y_588_ = v___y_603_;
v___y_589_ = v___x_605_;
goto v___jp_584_;
}
else
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
v_val_606_ = lean_ctor_get(v_ir_x3f_535_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_ir_x3f_535_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v_ir_x3f_535_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v_ir_x3f_535_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_descr_610_; lean_object* v___x_612_; 
v_descr_610_ = lean_ctor_get(v_val_606_, 0);
lean_inc_ref(v_descr_610_);
lean_dec(v_val_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_descr_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_descr_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v___y_585_ = v___y_601_;
v___y_586_ = v___y_604_;
v___y_587_ = v___y_602_;
v___y_588_ = v___y_603_;
v___y_589_ = v___x_612_;
goto v___jp_584_;
}
}
}
}
v___jp_615_:
{
if (lean_obj_tag(v_irSig_x3f_534_) == 0)
{
lean_object* v_descr_618_; lean_object* v___x_619_; 
v_descr_618_ = lean_ctor_get(v_ilean_533_, 0);
lean_inc_ref(v_descr_618_);
lean_dec_ref(v_ilean_533_);
v___x_619_ = lean_box(0);
v___y_601_ = v___y_617_;
v___y_602_ = v_descr_618_;
v___y_603_ = v___y_616_;
v___y_604_ = v___x_619_;
goto v___jp_600_;
}
else
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_629_; 
v_val_620_ = lean_ctor_get(v_irSig_x3f_534_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_irSig_x3f_534_);
if (v_isSharedCheck_629_ == 0)
{
v___x_622_ = v_irSig_x3f_534_;
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v_irSig_x3f_534_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_descr_624_; lean_object* v_descr_625_; lean_object* v___x_627_; 
v_descr_624_ = lean_ctor_get(v_ilean_533_, 0);
lean_inc_ref(v_descr_624_);
lean_dec_ref(v_ilean_533_);
v_descr_625_ = lean_ctor_get(v_val_620_, 0);
lean_inc_ref(v_descr_625_);
lean_dec(v_val_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_descr_625_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_descr_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v___y_601_ = v___y_617_;
v___y_602_ = v_descr_624_;
v___y_603_ = v___y_616_;
v___y_604_ = v___x_627_;
goto v___jp_600_;
}
}
}
}
v___jp_630_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_532_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_box(0);
v___y_616_ = v___y_631_;
v___y_617_ = v___x_632_;
goto v___jp_615_;
}
else
{
lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_val_633_ = lean_ctor_get(v_oleanPrivate_x3f_532_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_oleanPrivate_x3f_532_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v_oleanPrivate_x3f_532_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_dec(v_oleanPrivate_x3f_532_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_descr_637_; lean_object* v___x_639_; 
v_descr_637_ = lean_ctor_get(v_val_633_, 0);
lean_inc_ref(v_descr_637_);
lean_dec(v_val_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v_descr_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_descr_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v___y_616_ = v___y_631_;
v___y_617_ = v___x_639_;
goto v___jp_615_;
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
