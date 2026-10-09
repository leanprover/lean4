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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(size_t v_sz_15_, size_t v_i_16_, lean_object* v_bs_17_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_15_ = stack[0].m_num;
size_t v_i_16_ = stack[1].m_num;
lean_object* v_bs_17_ = stack[2].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_15_, v_i_16_, v_bs_17_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(lean_object* v_sz_39_, lean_object* v_i_40_, lean_object* v_bs_41_){
_start:
{
size_t v_sz_boxed_42_; size_t v_i_boxed_43_; lean_object* v_res_44_; 
v_sz_boxed_42_ = lean_unbox_usize(v_sz_39_);
lean_dec(v_sz_39_);
v_i_boxed_43_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_boxed_42_, v_i_boxed_43_, v_bs_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(lean_object* v_a_45_){
_start:
{
size_t v_sz_46_; size_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_sz_46_ = lean_array_size(v_a_45_);
v___x_47_ = ((size_t)0ULL);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_46_, v___x_47_, v_a_45_);
v___x_49_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object* v_self_58_){
_start:
{
lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v___y_62_; uint8_t v_isModule_66_; lean_object* v_ilean_67_; lean_object* v_irSig_x3f_68_; lean_object* v_ir_x3f_69_; lean_object* v_c_x3f_70_; lean_object* v_bc_x3f_71_; lean_object* v_ltar_x3f_72_; lean_object* v_obj_74_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v_obj_95_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v_obj_115_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v_obj_135_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; uint64_t v_hash_154_; lean_object* v_ext_155_; lean_object* v_obj_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_obj_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_obj_163_; lean_object* v___x_164_; lean_object* v___y_166_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_isModule_66_ = lean_ctor_get_uint8(v_self_58_, sizeof(void*)*9);
v_ilean_67_ = lean_ctor_get(v_self_58_, 3);
v_irSig_x3f_68_ = lean_ctor_get(v_self_58_, 4);
lean_inc(v_irSig_x3f_68_);
v_ir_x3f_69_ = lean_ctor_get(v_self_58_, 5);
lean_inc(v_ir_x3f_69_);
v_c_x3f_70_ = lean_ctor_get(v_self_58_, 6);
lean_inc(v_c_x3f_70_);
v_bc_x3f_71_ = lean_ctor_get(v_self_58_, 7);
lean_inc(v_bc_x3f_71_);
v_ltar_x3f_72_ = lean_ctor_get(v_self_58_, 8);
lean_inc(v_ltar_x3f_72_);
v_hash_154_ = lean_ctor_get_uint64(v_ilean_67_, sizeof(void*)*1);
v_ext_155_ = lean_ctor_get(v_ilean_67_, 0);
lean_inc_ref(v_ext_155_);
v_obj_156_ = lean_box(1);
v___x_157_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_158_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_158_, 0, v_isModule_66_);
v_obj_159_ = l_Lake_JsonObject_insertJson(v_obj_156_, v___x_157_, v___x_158_);
v___x_160_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_161_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_58_);
v___x_162_ = l_Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_161_);
v_obj_163_ = l_Lake_JsonObject_insertJson(v_obj_159_, v___x_160_, v___x_162_);
v___x_164_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_181_ = lean_string_utf8_byte_size(v_ext_155_);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_nat_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_184_ = l_Lake_lowerHexUInt64(v_hash_154_);
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_186_ = lean_string_append(v___x_184_, v___x_185_);
v___x_187_ = lean_string_append(v___x_186_, v_ext_155_);
lean_dec_ref(v_ext_155_);
v___y_166_ = v___x_187_;
goto v___jp_165_;
}
else
{
lean_object* v___x_188_; 
lean_dec_ref(v_ext_155_);
v___x_188_ = l_Lake_lowerHexUInt64(v_hash_154_);
v___y_166_ = v___x_188_;
goto v___jp_165_;
}
v___jp_59_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_63_, 0, v___y_62_);
lean_inc_ref(v___y_61_);
v___x_64_ = l_Lake_JsonObject_insertJson(v___y_60_, v___y_61_, v___x_63_);
v___x_65_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
v___jp_73_:
{
if (lean_obj_tag(v_ltar_x3f_72_) == 1)
{
lean_object* v_val_75_; uint64_t v_hash_76_; lean_object* v_ext_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_val_75_ = lean_ctor_get(v_ltar_x3f_72_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v_ltar_x3f_72_, 1);
v_hash_76_ = lean_ctor_get_uint64(v_val_75_, sizeof(void*)*1);
v_ext_77_ = lean_ctor_get(v_val_75_, 0);
lean_inc_ref(v_ext_77_);
lean_dec(v_val_75_);
v___x_78_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_79_ = lean_string_utf8_byte_size(v_ext_77_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = l_Lake_lowerHexUInt64(v_hash_76_);
v___x_83_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_84_ = lean_string_append(v___x_82_, v___x_83_);
v___x_85_ = lean_string_append(v___x_84_, v_ext_77_);
lean_dec_ref(v_ext_77_);
v___y_60_ = v_obj_74_;
v___y_61_ = v___x_78_;
v___y_62_ = v___x_85_;
goto v___jp_59_;
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v_ext_77_);
v___x_86_ = l_Lake_lowerHexUInt64(v_hash_76_);
v___y_60_ = v_obj_74_;
v___y_61_ = v___x_78_;
v___y_62_ = v___x_86_;
goto v___jp_59_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_ltar_x3f_72_);
v___x_87_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_87_, 0, v_obj_74_);
return v___x_87_;
}
}
v___jp_88_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_92_, 0, v___y_91_);
lean_inc_ref(v___y_89_);
v___x_93_ = l_Lake_JsonObject_insertJson(v___y_90_, v___y_89_, v___x_92_);
v_obj_74_ = v___x_93_;
goto v___jp_73_;
}
v___jp_94_:
{
if (lean_obj_tag(v_bc_x3f_71_) == 1)
{
lean_object* v_val_96_; uint64_t v_hash_97_; lean_object* v_ext_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_val_96_ = lean_ctor_get(v_bc_x3f_71_, 0);
lean_inc(v_val_96_);
lean_dec_ref_known(v_bc_x3f_71_, 1);
v_hash_97_ = lean_ctor_get_uint64(v_val_96_, sizeof(void*)*1);
v_ext_98_ = lean_ctor_get(v_val_96_, 0);
lean_inc_ref(v_ext_98_);
lean_dec(v_val_96_);
v___x_99_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_100_ = lean_string_utf8_byte_size(v_ext_98_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_nat_dec_eq(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = l_Lake_lowerHexUInt64(v_hash_97_);
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_105_ = lean_string_append(v___x_103_, v___x_104_);
v___x_106_ = lean_string_append(v___x_105_, v_ext_98_);
lean_dec_ref(v_ext_98_);
v___y_89_ = v___x_99_;
v___y_90_ = v_obj_95_;
v___y_91_ = v___x_106_;
goto v___jp_88_;
}
else
{
lean_object* v___x_107_; 
lean_dec_ref(v_ext_98_);
v___x_107_ = l_Lake_lowerHexUInt64(v_hash_97_);
v___y_89_ = v___x_99_;
v___y_90_ = v_obj_95_;
v___y_91_ = v___x_107_;
goto v___jp_88_;
}
}
else
{
lean_dec(v_bc_x3f_71_);
v_obj_74_ = v_obj_95_;
goto v___jp_73_;
}
}
v___jp_108_:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_112_, 0, v___y_111_);
lean_inc_ref(v___y_109_);
v___x_113_ = l_Lake_JsonObject_insertJson(v___y_110_, v___y_109_, v___x_112_);
v_obj_95_ = v___x_113_;
goto v___jp_94_;
}
v___jp_114_:
{
if (lean_obj_tag(v_c_x3f_70_) == 1)
{
lean_object* v_val_116_; uint64_t v_hash_117_; lean_object* v_ext_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_val_116_ = lean_ctor_get(v_c_x3f_70_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v_c_x3f_70_, 1);
v_hash_117_ = lean_ctor_get_uint64(v_val_116_, sizeof(void*)*1);
v_ext_118_ = lean_ctor_get(v_val_116_, 0);
lean_inc_ref(v_ext_118_);
lean_dec(v_val_116_);
v___x_119_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_120_ = lean_string_utf8_byte_size(v_ext_118_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = l_Lake_lowerHexUInt64(v_hash_117_);
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
v___x_126_ = lean_string_append(v___x_125_, v_ext_118_);
lean_dec_ref(v_ext_118_);
v___y_109_ = v___x_119_;
v___y_110_ = v_obj_115_;
v___y_111_ = v___x_126_;
goto v___jp_108_;
}
else
{
lean_object* v___x_127_; 
lean_dec_ref(v_ext_118_);
v___x_127_ = l_Lake_lowerHexUInt64(v_hash_117_);
v___y_109_ = v___x_119_;
v___y_110_ = v_obj_115_;
v___y_111_ = v___x_127_;
goto v___jp_108_;
}
}
else
{
lean_dec(v_c_x3f_70_);
v_obj_95_ = v_obj_115_;
goto v___jp_94_;
}
}
v___jp_128_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_132_, 0, v___y_131_);
lean_inc_ref(v___y_130_);
v___x_133_ = l_Lake_JsonObject_insertJson(v___y_129_, v___y_130_, v___x_132_);
v_obj_115_ = v___x_133_;
goto v___jp_114_;
}
v___jp_134_:
{
if (lean_obj_tag(v_ir_x3f_69_) == 1)
{
lean_object* v_val_136_; uint64_t v_hash_137_; lean_object* v_ext_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_val_136_ = lean_ctor_get(v_ir_x3f_69_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v_ir_x3f_69_, 1);
v_hash_137_ = lean_ctor_get_uint64(v_val_136_, sizeof(void*)*1);
v_ext_138_ = lean_ctor_get(v_val_136_, 0);
lean_inc_ref(v_ext_138_);
lean_dec(v_val_136_);
v___x_139_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_140_ = lean_string_utf8_byte_size(v_ext_138_);
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = l_Lake_lowerHexUInt64(v_hash_137_);
v___x_144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_145_ = lean_string_append(v___x_143_, v___x_144_);
v___x_146_ = lean_string_append(v___x_145_, v_ext_138_);
lean_dec_ref(v_ext_138_);
v___y_129_ = v_obj_135_;
v___y_130_ = v___x_139_;
v___y_131_ = v___x_146_;
goto v___jp_128_;
}
else
{
lean_object* v___x_147_; 
lean_dec_ref(v_ext_138_);
v___x_147_ = l_Lake_lowerHexUInt64(v_hash_137_);
v___y_129_ = v_obj_135_;
v___y_130_ = v___x_139_;
v___y_131_ = v___x_147_;
goto v___jp_128_;
}
}
else
{
lean_dec(v_ir_x3f_69_);
v_obj_115_ = v_obj_135_;
goto v___jp_114_;
}
}
v___jp_148_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_152_, 0, v___y_151_);
lean_inc_ref(v___y_150_);
v___x_153_ = l_Lake_JsonObject_insertJson(v___y_149_, v___y_150_, v___x_152_);
v_obj_135_ = v___x_153_;
goto v___jp_134_;
}
v___jp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_167_, 0, v___y_166_);
v___x_168_ = l_Lake_JsonObject_insertJson(v_obj_163_, v___x_164_, v___x_167_);
if (lean_obj_tag(v_irSig_x3f_68_) == 1)
{
lean_object* v_val_169_; uint64_t v_hash_170_; lean_object* v_ext_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_val_169_ = lean_ctor_get(v_irSig_x3f_68_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v_irSig_x3f_68_, 1);
v_hash_170_ = lean_ctor_get_uint64(v_val_169_, sizeof(void*)*1);
v_ext_171_ = lean_ctor_get(v_val_169_, 0);
lean_inc_ref(v_ext_171_);
lean_dec(v_val_169_);
v___x_172_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_173_ = lean_string_utf8_byte_size(v_ext_171_);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_nat_dec_eq(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = l_Lake_lowerHexUInt64(v_hash_170_);
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = lean_string_append(v___x_178_, v_ext_171_);
lean_dec_ref(v_ext_171_);
v___y_149_ = v___x_168_;
v___y_150_ = v___x_172_;
v___y_151_ = v___x_179_;
goto v___jp_148_;
}
else
{
lean_object* v___x_180_; 
lean_dec_ref(v_ext_171_);
v___x_180_ = l_Lake_lowerHexUInt64(v_hash_170_);
v___y_149_ = v___x_168_;
v___y_150_ = v___x_172_;
v___y_151_ = v___x_180_;
goto v___jp_148_;
}
}
else
{
lean_dec(v_irSig_x3f_68_);
v_obj_135_ = v___x_168_;
goto v___jp_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0));
return v___x_194_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_193_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_a_204_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v___x_195_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_195_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_a_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0));
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Json_getBool_x3f(v_x_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
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
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_a_226_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___x_217_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_217_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_x_235_);
lean_dec(v_x_235_);
return v_res_236_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t v_sz_237_, size_t v_i_238_, lean_object* v_bs_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_lt(v_i_238_, v_sz_237_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v_bs_239_);
return v___x_241_;
}
else
{
lean_object* v_v_242_; lean_object* v___x_243_; 
v_v_242_ = lean_array_uget_borrowed(v_bs_239_, v_i_238_);
lean_inc(v_v_242_);
v___x_243_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v_bs_239_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v_bs_x27_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v_a_252_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_243_, 1);
v___x_253_ = lean_unsigned_to_nat(0u);
v_bs_x27_254_ = lean_array_uset(v_bs_239_, v_i_238_, v___x_253_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_add(v_i_238_, v___x_255_);
v___x_257_ = lean_array_uset(v_bs_x27_254_, v_i_238_, v_a_252_);
v_i_238_ = v___x_256_;
v_bs_239_ = v___x_257_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_237_ = stack[0].m_num;
size_t v_i_238_ = stack[1].m_num;
lean_object* v_bs_239_ = stack[2].m_obj;
lean_object* v_res_259_;
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_237_, v_i_238_, v_bs_239_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object* v_sz_260_, lean_object* v_i_261_, lean_object* v_bs_262_){
_start:
{
size_t v_sz_boxed_263_; size_t v_i_boxed_264_; lean_object* v_res_265_; 
v_sz_boxed_263_ = lean_unbox_usize(v_sz_260_);
lean_dec(v_sz_260_);
v_i_boxed_264_ = lean_unbox_usize(v_i_261_);
lean_dec(v_i_261_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_263_, v_i_boxed_264_, v_bs_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_268_) == 4)
{
lean_object* v_elems_269_; size_t v_sz_270_; size_t v___x_271_; lean_object* v___x_272_; 
v_elems_269_ = lean_ctor_get(v_x_268_, 0);
lean_inc_ref(v_elems_269_);
lean_dec_ref_known(v_x_268_, 1);
v_sz_270_ = lean_array_size(v_elems_269_);
v___x_271_ = ((size_t)0ULL);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_270_, v___x_271_, v_elems_269_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_273_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0));
v___x_274_ = lean_unsigned_to_nat(80u);
v___x_275_ = l_Lean_Json_pretty(v_x_268_, v___x_274_);
v___x_276_ = lean_string_append(v___x_273_, v___x_275_);
lean_dec_ref(v___x_275_);
v___x_277_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1));
v___x_278_ = lean_string_append(v___x_276_, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f(lean_object* v_val_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Json_getObj_x3f(v_val_297_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_298_, 1);
v___x_308_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__5));
v___x_309_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_308_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v___x_310_; 
lean_dec(v_a_307_);
v___x_310_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1));
return v___x_310_;
}
else
{
lean_object* v_val_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_591_; 
v_val_311_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_591_ == 0)
{
v___x_313_ = v___x_309_;
v_isShared_314_ = v_isSharedCheck_591_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_val_311_);
lean_dec(v___x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_591_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(v_val_311_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_325_; 
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_325_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2));
v___x_321_ = lean_string_append(v___x_320_, v_a_316_);
lean_dec(v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_326_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_315_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_315_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 0);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_590_; 
v_a_334_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_590_ == 0)
{
v___x_336_ = v___x_315_;
v_isShared_337_ = v_isSharedCheck_590_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_315_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_590_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_array_get_size(v_a_334_);
v___x_340_ = lean_nat_dec_lt(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v___x_341_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4));
return v___x_341_;
}
else
{
lean_object* v___x_342_; uint8_t v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v_a_393_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v_a_404_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v_a_434_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v_a_463_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v_a_491_; lean_object* v_a_517_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_342_ = lean_array_fget(v_a_334_, v___x_338_);
v___x_566_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_567_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_566_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_box(0);
v_a_517_ = v___x_568_;
goto v___jp_516_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_570_; 
v_val_569_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_569_);
lean_dec_ref_known(v___x_567_, 1);
v___x_570_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_569_);
lean_dec(v_val_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_580_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13));
v___x_576_ = lean_string_append(v___x_575_, v_a_571_);
lean_dec(v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_576_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
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
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_581_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_570_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_570_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_570_, 1);
v_a_517_ = v_a_589_;
goto v___jp_516_;
}
}
}
v___jp_343_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_353_, 0, v___x_342_);
lean_ctor_set(v___x_353_, 1, v___y_346_);
lean_ctor_set(v___x_353_, 2, v___y_352_);
lean_ctor_set(v___x_353_, 3, v___y_348_);
lean_ctor_set(v___x_353_, 4, v___y_347_);
lean_ctor_set(v___x_353_, 5, v___y_345_);
lean_ctor_set(v___x_353_, 6, v___y_351_);
lean_ctor_set(v___x_353_, 7, v___y_349_);
lean_ctor_set(v___x_353_, 8, v___y_350_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*9, v___y_344_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_353_);
v___x_355_ = v___x_336_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
v___jp_357_:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(2u);
v___x_367_ = lean_nat_dec_lt(v___x_366_, v___x_339_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
v___x_368_ = lean_box(0);
v___y_344_ = v___y_358_;
v___y_345_ = v___y_359_;
v___y_346_ = v___y_365_;
v___y_347_ = v___y_361_;
v___y_348_ = v___y_360_;
v___y_349_ = v___y_362_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_364_;
v___y_352_ = v___x_368_;
goto v___jp_343_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_array_fget(v_a_334_, v___x_366_);
lean_dec(v_a_334_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_369_);
v___x_371_ = v___x_313_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v___y_344_ = v___y_358_;
v___y_345_ = v___y_359_;
v___y_346_ = v___y_365_;
v___y_347_ = v___y_361_;
v___y_348_ = v___y_360_;
v___y_349_ = v___y_362_;
v___y_350_ = v___y_363_;
v___y_351_ = v___y_364_;
v___y_352_ = v___x_371_;
goto v___jp_343_;
}
}
}
v___jp_373_:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_dec_lt(v___x_381_, v___x_339_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
v___y_358_ = v___y_380_;
v___y_359_ = v___y_374_;
v___y_360_ = v___y_376_;
v___y_361_ = v___y_375_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_379_;
v___y_365_ = v___x_383_;
goto v___jp_357_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_array_fget_borrowed(v_a_334_, v___x_381_);
lean_inc(v___x_384_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___y_358_ = v___y_380_;
v___y_359_ = v___y_374_;
v___y_360_ = v___y_376_;
v___y_361_ = v___y_375_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_379_;
v___y_365_ = v___x_385_;
goto v___jp_357_;
}
}
v___jp_386_:
{
if (lean_obj_tag(v___y_388_) == 0)
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_dec_lt(v___x_394_, v___x_339_);
v___y_374_ = v___y_387_;
v___y_375_ = v___y_390_;
v___y_376_ = v___y_389_;
v___y_377_ = v___y_391_;
v___y_378_ = v_a_393_;
v___y_379_ = v___y_392_;
v___y_380_ = v___x_395_;
goto v___jp_373_;
}
else
{
lean_object* v_val_396_; uint8_t v___x_397_; 
v_val_396_ = lean_ctor_get(v___y_388_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___y_388_, 1);
v___x_397_ = lean_unbox(v_val_396_);
lean_dec(v_val_396_);
v___y_374_ = v___y_387_;
v___y_375_ = v___y_390_;
v___y_376_ = v___y_389_;
v___y_377_ = v___y_391_;
v___y_378_ = v_a_393_;
v___y_379_ = v___y_392_;
v___y_380_ = v___x_397_;
goto v___jp_373_;
}
}
v___jp_398_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_406_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_405_);
lean_dec(v_a_307_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
v___y_387_ = v___y_399_;
v___y_388_ = v___y_400_;
v___y_389_ = v___y_402_;
v___y_390_ = v___y_401_;
v___y_391_ = v_a_404_;
v___y_392_ = v___y_403_;
v_a_393_ = v___x_407_;
goto v___jp_386_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; 
v_val_408_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v___x_406_, 1);
v___x_409_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_419_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5));
v___x_415_ = lean_string_append(v___x_414_, v_a_410_);
lean_dec(v_a_410_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_a_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
v_a_420_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_409_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_409_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 0);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v_a_428_; 
v_a_428_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_409_, 1);
v___y_387_ = v___y_399_;
v___y_388_ = v___y_400_;
v___y_389_ = v___y_402_;
v___y_390_ = v___y_401_;
v___y_391_ = v_a_404_;
v___y_392_ = v___y_403_;
v_a_393_ = v_a_428_;
goto v___jp_386_;
}
}
}
}
v___jp_429_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_436_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v___x_437_; 
v___x_437_ = lean_box(0);
v___y_399_ = v___y_430_;
v___y_400_ = v___y_431_;
v___y_401_ = v___y_433_;
v___y_402_ = v___y_432_;
v___y_403_ = v_a_434_;
v_a_404_ = v___x_437_;
goto v___jp_398_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; 
v_val_438_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_436_, 1);
v___x_439_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_a_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v___y_430_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_449_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6));
v___x_445_ = lean_string_append(v___x_444_, v_a_440_);
lean_dec(v_a_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
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
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_a_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v___y_430_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_450_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_439_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_439_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 0);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; 
v_a_458_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_439_, 1);
v___y_399_ = v___y_430_;
v___y_400_ = v___y_431_;
v___y_401_ = v___y_433_;
v___y_402_ = v___y_432_;
v___y_403_ = v_a_434_;
v_a_404_ = v_a_458_;
goto v___jp_398_;
}
}
}
}
v___jp_459_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_465_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
v___y_430_ = v_a_463_;
v___y_431_ = v___y_460_;
v___y_432_ = v___y_462_;
v___y_433_ = v___y_461_;
v_a_434_ = v___x_466_;
goto v___jp_429_;
}
else
{
lean_object* v_val_467_; lean_object* v___x_468_; 
v_val_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_465_, 1);
v___x_468_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_478_; 
lean_dec(v_a_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v___y_460_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7));
v___x_474_ = lean_string_append(v___x_473_, v_a_469_);
lean_dec(v_a_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
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
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_a_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v___y_460_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_479_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_468_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_468_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 0);
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_468_, 1);
v___y_430_ = v_a_463_;
v___y_431_ = v___y_460_;
v___y_432_ = v___y_462_;
v___y_433_ = v___y_461_;
v_a_434_ = v_a_487_;
goto v___jp_429_;
}
}
}
}
v___jp_488_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_493_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
v___y_460_ = v___y_489_;
v___y_461_ = v_a_491_;
v___y_462_ = v___y_490_;
v_a_463_ = v___x_494_;
goto v___jp_459_;
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
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
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
v___x_501_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8));
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
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_a_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_507_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_496_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_496_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 0);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_496_, 1);
v___y_460_ = v___y_489_;
v___y_461_ = v_a_491_;
v___y_462_ = v___y_490_;
v_a_463_ = v_a_515_;
goto v___jp_459_;
}
}
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__6));
v___x_519_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_518_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
lean_dec(v_a_517_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v___x_520_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10));
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; 
v_val_521_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v___x_519_, 1);
v___x_522_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_517_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11));
v___x_528_ = lean_string_append(v___x_527_, v_a_523_);
lean_dec(v_a_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
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
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_517_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_533_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_522_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_522_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 0);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_a_541_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_522_, 1);
v___x_542_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__7));
v___x_543_ = l_Lake_JsonObject_getJson_x3f(v_a_307_, v___x_542_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_box(0);
v___y_489_ = v_a_517_;
v___y_490_ = v_a_541_;
v_a_491_ = v___x_544_;
goto v___jp_488_;
}
else
{
lean_object* v_val_545_; lean_object* v___x_546_; 
v_val_545_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_543_, 1);
v___x_546_ = l_Lean_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_541_);
lean_dec(v_a_517_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_556_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12));
v___x_552_ = lean_string_append(v___x_551_, v_a_547_);
lean_dec(v_a_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
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
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_a_541_);
lean_dec(v_a_517_);
lean_dec(v___x_342_);
lean_del_object(v___x_336_);
lean_dec(v_a_334_);
lean_del_object(v___x_313_);
lean_dec(v_a_307_);
v_a_557_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_546_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_546_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 0);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_546_, 1);
v___y_489_ = v_a_517_;
v___y_490_ = v_a_541_;
v_a_491_ = v_a_565_;
goto v___jp_488_;
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
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object* v_arts_594_){
_start:
{
lean_object* v_olean_595_; uint8_t v_isModule_596_; lean_object* v_oleanServer_x3f_597_; lean_object* v_oleanPrivate_x3f_598_; lean_object* v_ilean_599_; lean_object* v_irSig_x3f_600_; lean_object* v_ir_x3f_601_; lean_object* v_c_x3f_602_; lean_object* v_bc_x3f_603_; lean_object* v_ltar_x3f_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_718_; 
v_olean_595_ = lean_ctor_get(v_arts_594_, 0);
v_isModule_596_ = lean_ctor_get_uint8(v_arts_594_, sizeof(void*)*9);
v_oleanServer_x3f_597_ = lean_ctor_get(v_arts_594_, 1);
v_oleanPrivate_x3f_598_ = lean_ctor_get(v_arts_594_, 2);
v_ilean_599_ = lean_ctor_get(v_arts_594_, 3);
v_irSig_x3f_600_ = lean_ctor_get(v_arts_594_, 4);
v_ir_x3f_601_ = lean_ctor_get(v_arts_594_, 5);
v_c_x3f_602_ = lean_ctor_get(v_arts_594_, 6);
v_bc_x3f_603_ = lean_ctor_get(v_arts_594_, 7);
v_ltar_x3f_604_ = lean_ctor_get(v_arts_594_, 8);
v_isSharedCheck_718_ = !lean_is_exclusive(v_arts_594_);
if (v_isSharedCheck_718_ == 0)
{
v___x_606_ = v_arts_594_;
v_isShared_607_ = v_isSharedCheck_718_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_ltar_x3f_604_);
lean_inc(v_bc_x3f_603_);
lean_inc(v_c_x3f_602_);
lean_inc(v_ir_x3f_601_);
lean_inc(v_irSig_x3f_600_);
lean_inc(v_ilean_599_);
lean_inc(v_oleanPrivate_x3f_598_);
lean_inc(v_oleanServer_x3f_597_);
lean_inc(v_olean_595_);
lean_dec(v_arts_594_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_718_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_descr_608_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_697_; 
v_descr_608_ = lean_ctor_get(v_olean_595_, 0);
lean_inc_ref(v_descr_608_);
lean_dec_ref(v_olean_595_);
if (lean_obj_tag(v_oleanServer_x3f_597_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(0);
v___y_697_ = v___x_708_;
goto v___jp_696_;
}
else
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_val_709_ = lean_ctor_get(v_oleanServer_x3f_597_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_oleanServer_x3f_597_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v_oleanServer_x3f_597_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v_oleanServer_x3f_597_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_descr_713_; lean_object* v___x_715_; 
v_descr_713_ = lean_ctor_get(v_val_709_, 0);
lean_inc_ref(v_descr_713_);
lean_dec(v_val_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_descr_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_descr_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
v___y_697_ = v___x_715_;
goto v___jp_696_;
}
}
}
v___jp_609_:
{
if (lean_obj_tag(v_ltar_x3f_604_) == 0)
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 8, v___x_617_);
lean_ctor_set(v___x_606_, 7, v___y_616_);
lean_ctor_set(v___x_606_, 6, v___y_611_);
lean_ctor_set(v___x_606_, 5, v___y_615_);
lean_ctor_set(v___x_606_, 4, v___y_610_);
lean_ctor_set(v___x_606_, 3, v___y_612_);
lean_ctor_set(v___x_606_, 2, v___y_613_);
lean_ctor_set(v___x_606_, 1, v___y_614_);
lean_ctor_set(v___x_606_, 0, v_descr_608_);
v___x_619_ = v___x_606_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_descr_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___y_614_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___y_613_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v___y_612_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v___y_610_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v___y_615_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v___y_611_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v___y_616_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v___x_617_);
lean_ctor_set_uint8(v_reuseFailAlloc_620_, sizeof(void*)*9, v_isModule_596_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v_val_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_632_; 
v_val_621_ = lean_ctor_get(v_ltar_x3f_604_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_ltar_x3f_604_);
if (v_isSharedCheck_632_ == 0)
{
v___x_623_ = v_ltar_x3f_604_;
v_isShared_624_ = v_isSharedCheck_632_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_val_621_);
lean_dec(v_ltar_x3f_604_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_632_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_descr_625_; lean_object* v___x_627_; 
v_descr_625_ = lean_ctor_get(v_val_621_, 0);
lean_inc_ref(v_descr_625_);
lean_dec(v_val_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_descr_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_descr_625_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 8, v___x_627_);
lean_ctor_set(v___x_606_, 7, v___y_616_);
lean_ctor_set(v___x_606_, 6, v___y_611_);
lean_ctor_set(v___x_606_, 5, v___y_615_);
lean_ctor_set(v___x_606_, 4, v___y_610_);
lean_ctor_set(v___x_606_, 3, v___y_612_);
lean_ctor_set(v___x_606_, 2, v___y_613_);
lean_ctor_set(v___x_606_, 1, v___y_614_);
lean_ctor_set(v___x_606_, 0, v_descr_608_);
v___x_629_ = v___x_606_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_descr_608_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___y_614_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___y_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v___y_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v___y_610_);
lean_ctor_set(v_reuseFailAlloc_630_, 5, v___y_615_);
lean_ctor_set(v_reuseFailAlloc_630_, 6, v___y_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 7, v___y_616_);
lean_ctor_set(v_reuseFailAlloc_630_, 8, v___x_627_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*9, v_isModule_596_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
v___jp_633_:
{
if (lean_obj_tag(v_bc_x3f_603_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_box(0);
v___y_610_ = v___y_634_;
v___y_611_ = v___y_639_;
v___y_612_ = v___y_635_;
v___y_613_ = v___y_636_;
v___y_614_ = v___y_637_;
v___y_615_ = v___y_638_;
v___y_616_ = v___x_640_;
goto v___jp_609_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_val_641_ = lean_ctor_get(v_bc_x3f_603_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_bc_x3f_603_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v_bc_x3f_603_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v_bc_x3f_603_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_descr_645_; lean_object* v___x_647_; 
v_descr_645_ = lean_ctor_get(v_val_641_, 0);
lean_inc_ref(v_descr_645_);
lean_dec(v_val_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_descr_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_descr_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v___y_610_ = v___y_634_;
v___y_611_ = v___y_639_;
v___y_612_ = v___y_635_;
v___y_613_ = v___y_636_;
v___y_614_ = v___y_637_;
v___y_615_ = v___y_638_;
v___y_616_ = v___x_647_;
goto v___jp_609_;
}
}
}
}
v___jp_650_:
{
if (lean_obj_tag(v_c_x3f_602_) == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_box(0);
v___y_634_ = v___y_651_;
v___y_635_ = v___y_652_;
v___y_636_ = v___y_653_;
v___y_637_ = v___y_654_;
v___y_638_ = v___y_655_;
v___y_639_ = v___x_656_;
goto v___jp_633_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_val_657_ = lean_ctor_get(v_c_x3f_602_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_c_x3f_602_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v_c_x3f_602_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v_c_x3f_602_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_descr_661_; lean_object* v___x_663_; 
v_descr_661_ = lean_ctor_get(v_val_657_, 0);
lean_inc_ref(v_descr_661_);
lean_dec(v_val_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_descr_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_descr_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_634_ = v___y_651_;
v___y_635_ = v___y_652_;
v___y_636_ = v___y_653_;
v___y_637_ = v___y_654_;
v___y_638_ = v___y_655_;
v___y_639_ = v___x_663_;
goto v___jp_633_;
}
}
}
}
v___jp_666_:
{
if (lean_obj_tag(v_ir_x3f_601_) == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_box(0);
v___y_651_ = v___y_670_;
v___y_652_ = v___y_667_;
v___y_653_ = v___y_668_;
v___y_654_ = v___y_669_;
v___y_655_ = v___x_671_;
goto v___jp_650_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_val_672_ = lean_ctor_get(v_ir_x3f_601_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_ir_x3f_601_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v_ir_x3f_601_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v_ir_x3f_601_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_descr_676_; lean_object* v___x_678_; 
v_descr_676_ = lean_ctor_get(v_val_672_, 0);
lean_inc_ref(v_descr_676_);
lean_dec(v_val_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v_descr_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_descr_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v___y_651_ = v___y_670_;
v___y_652_ = v___y_667_;
v___y_653_ = v___y_668_;
v___y_654_ = v___y_669_;
v___y_655_ = v___x_678_;
goto v___jp_650_;
}
}
}
}
v___jp_681_:
{
if (lean_obj_tag(v_irSig_x3f_600_) == 0)
{
lean_object* v_descr_684_; lean_object* v___x_685_; 
v_descr_684_ = lean_ctor_get(v_ilean_599_, 0);
lean_inc_ref(v_descr_684_);
lean_dec_ref(v_ilean_599_);
v___x_685_ = lean_box(0);
v___y_667_ = v_descr_684_;
v___y_668_ = v___y_683_;
v___y_669_ = v___y_682_;
v___y_670_ = v___x_685_;
goto v___jp_666_;
}
else
{
lean_object* v_val_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_val_686_ = lean_ctor_get(v_irSig_x3f_600_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_irSig_x3f_600_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v_irSig_x3f_600_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_val_686_);
lean_dec(v_irSig_x3f_600_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_descr_690_; lean_object* v_descr_691_; lean_object* v___x_693_; 
v_descr_690_ = lean_ctor_get(v_ilean_599_, 0);
lean_inc_ref(v_descr_690_);
lean_dec_ref(v_ilean_599_);
v_descr_691_ = lean_ctor_get(v_val_686_, 0);
lean_inc_ref(v_descr_691_);
lean_dec(v_val_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_descr_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_descr_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v___y_667_ = v_descr_690_;
v___y_668_ = v___y_683_;
v___y_669_ = v___y_682_;
v___y_670_ = v___x_693_;
goto v___jp_666_;
}
}
}
}
v___jp_696_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_598_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
v___y_682_ = v___y_697_;
v___y_683_ = v___x_698_;
goto v___jp_681_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_val_699_ = lean_ctor_get(v_oleanPrivate_x3f_598_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_oleanPrivate_x3f_598_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v_oleanPrivate_x3f_598_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v_oleanPrivate_x3f_598_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_descr_703_; lean_object* v___x_705_; 
v_descr_703_ = lean_ctor_get(v_val_699_, 0);
lean_inc_ref(v_descr_703_);
lean_dec(v_val_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_descr_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_descr_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
v___y_682_ = v___y_697_;
v___y_683_ = v___x_705_;
goto v___jp_681_;
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
