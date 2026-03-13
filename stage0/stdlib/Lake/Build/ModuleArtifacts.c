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
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__0 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__0_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__1 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__1_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__2 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__2_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__3 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__3_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lake_ModuleOutputDescrs_toJson___closed__4 = (const lean_object*)&l_Lake_ModuleOutputDescrs_toJson___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object*);
static const lean_closure_object l_Lake_instToJsonModuleOutputDescrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ModuleOutputDescrs_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonModuleOutputDescrs___closed__0 = (const lean_object*)&l_Lake_instToJsonModuleOutputDescrs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonModuleOutputDescrs = (const lean_object*)&l_Lake_instToJsonModuleOutputDescrs___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object*);
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
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: i"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "i: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "property not found: c"};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value;
static const lean_ctor_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value)}};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "c: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "b: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value;
static const lean_string_object l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "r: "};
static const lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12 = (const lean_object*)&l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value;
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
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_toJson(lean_object* v_self_54_){
_start:
{
lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v_ilean_62_; lean_object* v_ir_x3f_63_; lean_object* v_c_64_; lean_object* v_bc_x3f_65_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v_obj_86_; lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; uint64_t v_hash_104_; lean_object* v_ext_105_; lean_object* v_obj_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_obj_110_; lean_object* v___x_111_; lean_object* v___y_113_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_ilean_62_ = lean_ctor_get(v_self_54_, 3);
v_ir_x3f_63_ = lean_ctor_get(v_self_54_, 4);
lean_inc(v_ir_x3f_63_);
v_c_64_ = lean_ctor_get(v_self_54_, 5);
lean_inc_ref(v_c_64_);
v_bc_x3f_65_ = lean_ctor_get(v_self_54_, 6);
lean_inc(v_bc_x3f_65_);
v_hash_104_ = lean_ctor_get_uint64(v_ilean_62_, sizeof(void*)*1);
v_ext_105_ = lean_ctor_get(v_ilean_62_, 0);
lean_inc_ref(v_ext_105_);
v_obj_106_ = lean_box(1);
v___x_107_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_108_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_54_);
v___x_109_ = l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_108_);
v_obj_110_ = l_Lake_JsonObject_insertJson(v_obj_106_, v___x_107_, v___x_109_);
v___x_111_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_128_ = lean_string_utf8_byte_size(v_ext_105_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_nat_dec_eq(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_131_ = l_Lake_Hash_hex(v_hash_104_);
v___x_132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_133_ = lean_string_append(v___x_131_, v___x_132_);
v___x_134_ = lean_string_append(v___x_133_, v_ext_105_);
lean_dec_ref(v_ext_105_);
v___y_113_ = v___x_134_;
goto v___jp_112_;
}
else
{
lean_object* v___x_135_; 
lean_dec_ref(v_ext_105_);
v___x_135_ = l_Lake_Hash_hex(v_hash_104_);
v___y_113_ = v___x_135_;
goto v___jp_112_;
}
v___jp_55_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_59_, 0, v___y_58_);
v___x_60_ = l_Lake_JsonObject_insertJson(v___y_57_, v___y_56_, v___x_59_);
v___x_61_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
v___jp_66_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_70_, 0, v___y_69_);
v___x_71_ = l_Lake_JsonObject_insertJson(v___y_68_, v___y_67_, v___x_70_);
if (lean_obj_tag(v_bc_x3f_65_) == 1)
{
lean_object* v_val_72_; uint64_t v_hash_73_; lean_object* v_ext_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_val_72_ = lean_ctor_get(v_bc_x3f_65_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v_bc_x3f_65_);
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
v___y_56_ = v___x_75_;
v___y_57_ = v___x_71_;
v___y_58_ = v___x_82_;
goto v___jp_55_;
}
else
{
lean_object* v___x_83_; 
lean_dec_ref(v_ext_74_);
v___x_83_ = l_Lake_Hash_hex(v_hash_73_);
v___y_56_ = v___x_75_;
v___y_57_ = v___x_71_;
v___y_58_ = v___x_83_;
goto v___jp_55_;
}
}
else
{
lean_object* v___x_84_; 
lean_dec(v_bc_x3f_65_);
v___x_84_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_71_);
return v___x_84_;
}
}
v___jp_85_:
{
uint64_t v_hash_87_; lean_object* v_ext_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_hash_87_ = lean_ctor_get_uint64(v_c_64_, sizeof(void*)*1);
v_ext_88_ = lean_ctor_get(v_c_64_, 0);
lean_inc_ref(v_ext_88_);
lean_dec_ref(v_c_64_);
v___x_89_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_90_ = lean_string_utf8_byte_size(v_ext_88_);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_nat_dec_eq(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = l_Lake_Hash_hex(v_hash_87_);
v___x_94_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_95_ = lean_string_append(v___x_93_, v___x_94_);
v___x_96_ = lean_string_append(v___x_95_, v_ext_88_);
lean_dec_ref(v_ext_88_);
v___y_67_ = v___x_89_;
v___y_68_ = v_obj_86_;
v___y_69_ = v___x_96_;
goto v___jp_66_;
}
else
{
lean_object* v___x_97_; 
lean_dec_ref(v_ext_88_);
v___x_97_ = l_Lake_Hash_hex(v_hash_87_);
v___y_67_ = v___x_89_;
v___y_68_ = v_obj_86_;
v___y_69_ = v___x_97_;
goto v___jp_66_;
}
}
v___jp_98_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_102_, 0, v___y_101_);
v___x_103_ = l_Lake_JsonObject_insertJson(v___y_99_, v___y_100_, v___x_102_);
v_obj_86_ = v___x_103_;
goto v___jp_85_;
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_114_, 0, v___y_113_);
v___x_115_ = l_Lake_JsonObject_insertJson(v_obj_110_, v___x_111_, v___x_114_);
if (lean_obj_tag(v_ir_x3f_63_) == 1)
{
lean_object* v_val_116_; uint64_t v_hash_117_; lean_object* v_ext_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_val_116_ = lean_ctor_get(v_ir_x3f_63_, 0);
lean_inc(v_val_116_);
lean_dec_ref(v_ir_x3f_63_);
v_hash_117_ = lean_ctor_get_uint64(v_val_116_, sizeof(void*)*1);
v_ext_118_ = lean_ctor_get(v_val_116_, 0);
lean_inc_ref(v_ext_118_);
lean_dec(v_val_116_);
v___x_119_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_120_ = lean_string_utf8_byte_size(v_ext_118_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = l_Lake_Hash_hex(v_hash_117_);
v___x_124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0));
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
v___x_126_ = lean_string_append(v___x_125_, v_ext_118_);
lean_dec_ref(v_ext_118_);
v___y_99_ = v___x_115_;
v___y_100_ = v___x_119_;
v___y_101_ = v___x_126_;
goto v___jp_98_;
}
else
{
lean_object* v___x_127_; 
lean_dec_ref(v_ext_118_);
v___x_127_ = l_Lake_Hash_hex(v_hash_117_);
v___y_99_ = v___x_115_;
v___y_100_ = v___x_119_;
v___y_101_ = v___x_127_;
goto v___jp_98_;
}
}
else
{
lean_dec(v_ir_x3f_63_);
v_obj_86_ = v___x_115_;
goto v___jp_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0));
return v___x_141_;
}
else
{
lean_object* v___x_142_; 
v___x_142_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_140_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
v_a_151_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_159_ == 0)
{
v___x_153_ = v___x_142_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_a_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(size_t v_sz_160_, size_t v_i_161_, lean_object* v_bs_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lean_usize_dec_lt(v_i_161_, v_sz_160_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_bs_162_);
return v___x_164_;
}
else
{
lean_object* v_v_165_; lean_object* v___x_166_; 
v_v_165_ = lean_array_uget_borrowed(v_bs_162_, v_i_161_);
lean_inc(v_v_165_);
v___x_166_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_165_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_bs_162_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v_bs_x27_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v_a_175_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_175_);
lean_dec_ref(v___x_166_);
v___x_176_ = lean_unsigned_to_nat(0u);
v_bs_x27_177_ = lean_array_uset(v_bs_162_, v_i_161_, v___x_176_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_161_, v___x_178_);
v___x_180_ = lean_array_uset(v_bs_x27_177_, v_i_161_, v_a_175_);
v_i_161_ = v___x_179_;
v_bs_162_ = v___x_180_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(lean_object* v_sz_182_, lean_object* v_i_183_, lean_object* v_bs_184_){
_start:
{
size_t v_sz_boxed_185_; size_t v_i_boxed_186_; lean_object* v_res_187_; 
v_sz_boxed_185_ = lean_unbox_usize(v_sz_182_);
lean_dec(v_sz_182_);
v_i_boxed_186_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_res_187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_185_, v_i_boxed_186_, v_bs_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(lean_object* v_x_190_){
_start:
{
if (lean_obj_tag(v_x_190_) == 4)
{
lean_object* v_elems_191_; size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; 
v_elems_191_ = lean_ctor_get(v_x_190_, 0);
lean_inc_ref(v_elems_191_);
lean_dec_ref(v_x_190_);
v_sz_192_ = lean_array_size(v_elems_191_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_192_, v___x_193_, v_elems_191_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_195_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0));
v___x_196_ = lean_unsigned_to_nat(80u);
v___x_197_ = l_Lean_Json_pretty(v_x_190_, v___x_196_);
v___x_198_ = lean_string_append(v___x_195_, v___x_197_);
lean_dec_ref(v___x_197_);
v___x_199_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1));
v___x_200_ = lean_string_append(v___x_198_, v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputDescrs_fromJson_x3f(lean_object* v_val_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Json_getObj_x3f(v_val_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_a_229_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_220_);
v___x_230_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__2));
v___x_231_ = l_Lake_JsonObject_getJson_x3f(v_a_229_, v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
lean_dec(v_a_229_);
v___x_232_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1));
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_401_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_401_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_401_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_401_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; 
v___x_237_ = l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(v_val_233_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_247_; 
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_247_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2));
v___x_243_ = lean_string_append(v___x_242_, v_a_238_);
lean_dec(v_a_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v_a_248_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_237_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_237_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 0);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_a_256_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_237_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_array_get_size(v_a_256_);
v___x_259_ = lean_nat_dec_lt(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v___x_260_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4));
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__3));
v___x_262_ = l_Lake_JsonObject_getJson_x3f(v_a_229_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; 
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v___x_263_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6));
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_400_; 
v_val_264_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_400_ == 0)
{
v___x_266_ = v___x_262_;
v_isShared_267_ = v_isSharedCheck_400_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_val_264_);
lean_dec(v___x_262_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_400_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_264_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_278_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7));
v___x_274_ = lean_string_append(v___x_273_, v_a_269_);
lean_dec(v_a_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v_a_279_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_268_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_268_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 0);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_399_; 
v_a_287_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_399_ == 0)
{
v___x_289_ = v___x_268_;
v_isShared_290_ = v_isSharedCheck_399_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_268_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_399_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v_a_317_; lean_object* v_a_326_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_291_ = lean_array_fget(v_a_256_, v___x_257_);
v___x_375_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__4));
v___x_376_ = l_Lake_JsonObject_getJson_x3f(v_a_229_, v___x_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
v_a_326_ = v___x_377_;
goto v___jp_325_;
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
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
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
v___x_384_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12));
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
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
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
v_a_326_ = v_a_398_;
goto v___jp_325_;
}
}
}
v___jp_292_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_298_, 0, v___x_291_);
lean_ctor_set(v___x_298_, 1, v___y_293_);
lean_ctor_set(v___x_298_, 2, v___y_297_);
lean_ctor_set(v___x_298_, 3, v_a_287_);
lean_ctor_set(v___x_298_, 4, v___y_294_);
lean_ctor_set(v___x_298_, 5, v___y_296_);
lean_ctor_set(v___x_298_, 6, v___y_295_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_298_);
v___x_300_ = v___x_289_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
v___jp_302_:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(2u);
v___x_308_ = lean_nat_dec_lt(v___x_307_, v___x_258_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
v___x_309_ = lean_box(0);
v___y_293_ = v___y_306_;
v___y_294_ = v___y_303_;
v___y_295_ = v___y_305_;
v___y_296_ = v___y_304_;
v___y_297_ = v___x_309_;
goto v___jp_292_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_array_fget(v_a_256_, v___x_307_);
lean_dec(v_a_256_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_310_);
v___x_312_ = v___x_266_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
v___y_293_ = v___y_306_;
v___y_294_ = v___y_303_;
v___y_295_ = v___y_305_;
v___y_296_ = v___y_304_;
v___y_297_ = v___x_312_;
goto v___jp_292_;
}
}
}
v___jp_314_:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_dec_lt(v___x_318_, v___x_258_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_del_object(v___x_235_);
v___x_320_ = lean_box(0);
v___y_303_ = v___y_315_;
v___y_304_ = v___y_316_;
v___y_305_ = v_a_317_;
v___y_306_ = v___x_320_;
goto v___jp_302_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_array_fget_borrowed(v_a_256_, v___x_318_);
lean_inc(v___x_321_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_321_);
v___x_323_ = v___x_235_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v___y_303_ = v___y_315_;
v___y_304_ = v___y_316_;
v___y_305_ = v_a_317_;
v___y_306_ = v___x_323_;
goto v___jp_302_;
}
}
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__1));
v___x_328_ = l_Lake_JsonObject_getJson_x3f(v_a_229_, v___x_327_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
lean_dec(v_a_326_);
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v___x_329_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9));
return v___x_329_;
}
else
{
lean_object* v_val_330_; lean_object* v___x_331_; 
v_val_330_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_330_);
lean_dec_ref(v___x_328_);
v___x_331_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_a_326_);
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10));
v___x_337_ = lean_string_append(v___x_336_, v_a_332_);
lean_dec(v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_326_);
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
lean_dec(v_a_229_);
v_a_342_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_331_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_331_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 0);
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_331_);
v___x_351_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_toJson___closed__0));
v___x_352_ = l_Lake_JsonObject_getJson_x3f(v_a_229_, v___x_351_);
lean_dec(v_a_229_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_box(0);
v___y_315_ = v_a_326_;
v___y_316_ = v_a_350_;
v_a_317_ = v___x_353_;
goto v___jp_314_;
}
else
{
lean_object* v_val_354_; lean_object* v___x_355_; 
v_val_354_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_val_354_);
lean_dec_ref(v___x_352_);
v___x_355_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_350_);
lean_dec(v_a_326_);
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_365_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11));
v___x_361_ = lean_string_append(v___x_360_, v_a_356_);
lean_dec(v_a_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_a_350_);
lean_dec(v_a_326_);
lean_dec(v___x_291_);
lean_del_object(v___x_289_);
lean_dec(v_a_287_);
lean_del_object(v___x_266_);
lean_dec(v_a_256_);
lean_del_object(v___x_235_);
v_a_366_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_355_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_355_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_355_);
v___y_315_ = v_a_326_;
v___y_316_ = v_a_350_;
v_a_317_ = v_a_374_;
goto v___jp_314_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleOutputArtifacts_descrs(lean_object* v_arts_404_){
_start:
{
lean_object* v_olean_405_; lean_object* v_oleanServer_x3f_406_; lean_object* v_oleanPrivate_x3f_407_; lean_object* v_ilean_408_; lean_object* v_ir_x3f_409_; lean_object* v_c_410_; lean_object* v_bc_x3f_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_476_; 
v_olean_405_ = lean_ctor_get(v_arts_404_, 0);
v_oleanServer_x3f_406_ = lean_ctor_get(v_arts_404_, 1);
v_oleanPrivate_x3f_407_ = lean_ctor_get(v_arts_404_, 2);
v_ilean_408_ = lean_ctor_get(v_arts_404_, 3);
v_ir_x3f_409_ = lean_ctor_get(v_arts_404_, 4);
v_c_410_ = lean_ctor_get(v_arts_404_, 5);
v_bc_x3f_411_ = lean_ctor_get(v_arts_404_, 6);
v_isSharedCheck_476_ = !lean_is_exclusive(v_arts_404_);
if (v_isSharedCheck_476_ == 0)
{
v___x_413_ = v_arts_404_;
v_isShared_414_ = v_isSharedCheck_476_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_bc_x3f_411_);
lean_inc(v_c_410_);
lean_inc(v_ir_x3f_409_);
lean_inc(v_ilean_408_);
lean_inc(v_oleanPrivate_x3f_407_);
lean_inc(v_oleanServer_x3f_406_);
lean_inc(v_olean_405_);
lean_dec(v_arts_404_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_476_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_descr_415_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_455_; 
v_descr_415_ = lean_ctor_get(v_olean_405_, 0);
lean_inc_ref(v_descr_415_);
lean_dec_ref(v_olean_405_);
if (lean_obj_tag(v_oleanServer_x3f_406_) == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
v___y_455_ = v___x_466_;
goto v___jp_454_;
}
else
{
lean_object* v_val_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_val_467_ = lean_ctor_get(v_oleanServer_x3f_406_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_oleanServer_x3f_406_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v_oleanServer_x3f_406_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_val_467_);
lean_dec(v_oleanServer_x3f_406_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_descr_471_; lean_object* v___x_473_; 
v_descr_471_ = lean_ctor_get(v_val_467_, 0);
lean_inc_ref(v_descr_471_);
lean_dec(v_val_467_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_descr_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_descr_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
v___y_455_ = v___x_473_;
goto v___jp_454_;
}
}
}
v___jp_416_:
{
if (lean_obj_tag(v_bc_x3f_411_) == 0)
{
lean_object* v_descr_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v_descr_421_ = lean_ctor_get(v_c_410_, 0);
lean_inc_ref(v_descr_421_);
lean_dec_ref(v_c_410_);
v___x_422_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 6, v___x_422_);
lean_ctor_set(v___x_413_, 5, v_descr_421_);
lean_ctor_set(v___x_413_, 4, v___y_420_);
lean_ctor_set(v___x_413_, 3, v___y_418_);
lean_ctor_set(v___x_413_, 2, v___y_419_);
lean_ctor_set(v___x_413_, 1, v___y_417_);
lean_ctor_set(v___x_413_, 0, v_descr_415_);
v___x_424_ = v___x_413_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_descr_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___y_417_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v___y_419_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v___y_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v___y_420_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_descr_421_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_438_; 
v_val_426_ = lean_ctor_get(v_bc_x3f_411_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_bc_x3f_411_);
if (v_isSharedCheck_438_ == 0)
{
v___x_428_ = v_bc_x3f_411_;
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v_bc_x3f_411_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_descr_430_; lean_object* v_descr_431_; lean_object* v___x_433_; 
v_descr_430_ = lean_ctor_get(v_c_410_, 0);
lean_inc_ref(v_descr_430_);
lean_dec_ref(v_c_410_);
v_descr_431_ = lean_ctor_get(v_val_426_, 0);
lean_inc_ref(v_descr_431_);
lean_dec(v_val_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_descr_431_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_descr_431_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 6, v___x_433_);
lean_ctor_set(v___x_413_, 5, v_descr_430_);
lean_ctor_set(v___x_413_, 4, v___y_420_);
lean_ctor_set(v___x_413_, 3, v___y_418_);
lean_ctor_set(v___x_413_, 2, v___y_419_);
lean_ctor_set(v___x_413_, 1, v___y_417_);
lean_ctor_set(v___x_413_, 0, v_descr_415_);
v___x_435_ = v___x_413_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_descr_415_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___y_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v___y_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v___y_418_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v___y_420_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v_descr_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 6, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
v___jp_439_:
{
if (lean_obj_tag(v_ir_x3f_409_) == 0)
{
lean_object* v_descr_442_; lean_object* v___x_443_; 
v_descr_442_ = lean_ctor_get(v_ilean_408_, 0);
lean_inc_ref(v_descr_442_);
lean_dec_ref(v_ilean_408_);
v___x_443_ = lean_box(0);
v___y_417_ = v___y_440_;
v___y_418_ = v_descr_442_;
v___y_419_ = v___y_441_;
v___y_420_ = v___x_443_;
goto v___jp_416_;
}
else
{
lean_object* v_val_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_453_; 
v_val_444_ = lean_ctor_get(v_ir_x3f_409_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_ir_x3f_409_);
if (v_isSharedCheck_453_ == 0)
{
v___x_446_ = v_ir_x3f_409_;
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_val_444_);
lean_dec(v_ir_x3f_409_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_descr_448_; lean_object* v_descr_449_; lean_object* v___x_451_; 
v_descr_448_ = lean_ctor_get(v_ilean_408_, 0);
lean_inc_ref(v_descr_448_);
lean_dec_ref(v_ilean_408_);
v_descr_449_ = lean_ctor_get(v_val_444_, 0);
lean_inc_ref(v_descr_449_);
lean_dec(v_val_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_descr_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_descr_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
v___y_417_ = v___y_440_;
v___y_418_ = v_descr_448_;
v___y_419_ = v___y_441_;
v___y_420_ = v___x_451_;
goto v___jp_416_;
}
}
}
}
v___jp_454_:
{
if (lean_obj_tag(v_oleanPrivate_x3f_407_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
v___y_440_ = v___y_455_;
v___y_441_ = v___x_456_;
goto v___jp_439_;
}
else
{
lean_object* v_val_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_val_457_ = lean_ctor_get(v_oleanPrivate_x3f_407_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_oleanPrivate_x3f_407_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v_oleanPrivate_x3f_407_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_val_457_);
lean_dec(v_oleanPrivate_x3f_407_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_descr_461_; lean_object* v___x_463_; 
v_descr_461_ = lean_ctor_get(v_val_457_, 0);
lean_inc_ref(v_descr_461_);
lean_dec(v_val_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v_descr_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_descr_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v___y_440_ = v___y_455_;
v___y_441_ = v___x_463_;
goto v___jp_439_;
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
