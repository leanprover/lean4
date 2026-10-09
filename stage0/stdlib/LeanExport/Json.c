// Lean compiler output
// Module: LeanExport.Json
// Imports: public import Lean.Data.Json.Parser
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
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_num(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_LeanExport_Json_arrayCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unexpected character in array"};
static const lean_object* l_LeanExport_Json_arrayCore___closed__0 = (const lean_object*)&l_LeanExport_Json_arrayCore___closed__0_value;
static const lean_ctor_object l_LeanExport_Json_arrayCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_Json_arrayCore___closed__0_value)}};
static const lean_object* l_LeanExport_Json_arrayCore___closed__1 = (const lean_object*)&l_LeanExport_Json_arrayCore___closed__1_value;
static const lean_string_object l_LeanExport_Json_anyCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unexpected input"};
static const lean_object* l_LeanExport_Json_anyCore___closed__0 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__0_value;
static const lean_ctor_object l_LeanExport_Json_anyCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_Json_anyCore___closed__0_value)}};
static const lean_object* l_LeanExport_Json_anyCore___closed__1 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__1_value;
static const lean_string_object l_LeanExport_Json_anyCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_LeanExport_Json_anyCore___closed__2 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__2_value;
static const lean_string_object l_LeanExport_Json_anyCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_LeanExport_Json_anyCore___closed__3 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__3_value;
static const lean_string_object l_LeanExport_Json_anyCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_LeanExport_Json_anyCore___closed__4 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__4_value;
static const lean_string_object l_LeanExport_Json_objectCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_LeanExport_Json_objectCore___closed__2 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__2_value;
static const lean_string_object l_LeanExport_Json_objectCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected \""};
static const lean_object* l_LeanExport_Json_objectCore___closed__0 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__0_value;
static const lean_ctor_object l_LeanExport_Json_objectCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_Json_objectCore___closed__0_value)}};
static const lean_object* l_LeanExport_Json_objectCore___closed__1 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__1_value;
static const lean_string_object l_LeanExport_Json_objectCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected character in object"};
static const lean_object* l_LeanExport_Json_objectCore___closed__3 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__3_value;
static const lean_ctor_object l_LeanExport_Json_objectCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_Json_objectCore___closed__3_value)}};
static const lean_object* l_LeanExport_Json_objectCore___closed__4 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__4_value;
static const lean_string_object l_LeanExport_Json_objectCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected :"};
static const lean_object* l_LeanExport_Json_objectCore___closed__5 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__5_value;
static const lean_ctor_object l_LeanExport_Json_objectCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_Json_objectCore___closed__5_value)}};
static const lean_object* l_LeanExport_Json_objectCore___closed__6 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__6_value;
static const lean_string_object l_LeanExport_Json_objectCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "duplicate object key "};
static const lean_object* l_LeanExport_Json_objectCore___closed__7 = (const lean_object*)&l_LeanExport_Json_objectCore___closed__7_value;
LEAN_EXPORT lean_object* l_LeanExport_Json_objectCore(lean_object*, lean_object*);
static const lean_ctor_object l_LeanExport_Json_anyCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_LeanExport_Json_anyCore___closed__5 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__5_value;
static const lean_array_object l_LeanExport_Json_anyCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LeanExport_Json_anyCore___closed__6 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__6_value;
static const lean_ctor_object l_LeanExport_Json_anyCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_LeanExport_Json_anyCore___closed__6_value)}};
static const lean_object* l_LeanExport_Json_anyCore___closed__7 = (const lean_object*)&l_LeanExport_Json_anyCore___closed__7_value;
LEAN_EXPORT lean_object* l_LeanExport_Json_anyCore(lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_Json_arrayCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_LeanExport_Json_parse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_LeanExport_Json_parse___lam__0___closed__0 = (const lean_object*)&l_LeanExport_Json_parse___lam__0___closed__0_value;
static const lean_ctor_object l_LeanExport_Json_parse___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_Json_parse___lam__0___closed__0_value)}};
static const lean_object* l_LeanExport_Json_parse___lam__0___closed__1 = (const lean_object*)&l_LeanExport_Json_parse___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_LeanExport_Json_parse___lam__0(lean_object*);
static const lean_closure_object l_LeanExport_Json_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_LeanExport_Json_parse___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_LeanExport_Json_parse___closed__0 = (const lean_object*)&l_LeanExport_Json_parse___closed__0_value;
LEAN_EXPORT lean_object* l_LeanExport_Json_parse(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_l_4_; lean_object* v_r_5_; uint8_t v___x_6_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
v_l_4_ = lean_ctor_get(v_t_2_, 3);
v_r_5_ = lean_ctor_get(v_t_2_, 4);
v___x_6_ = lean_string_compare(v_k_1_, v_k_3_);
switch(v___x_6_)
{
case 0:
{
v_t_2_ = v_l_4_;
goto _start;
}
case 1:
{
uint8_t v___x_8_; 
v___x_8_ = 1;
return v___x_8_;
}
default: 
{
v_t_2_ = v_r_5_;
goto _start;
}
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg___boxed(lean_object* v_k_11_, lean_object* v_t_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_k_11_, v_t_12_);
lean_dec(v_t_12_);
lean_dec_ref(v_k_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(lean_object* v_msg_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_panic_fn_borrowed(v___x_16_, v_msg_15_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_21_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2));
v___x_22_ = lean_unsigned_to_nat(35u);
v___x_23_ = lean_unsigned_to_nat(182u);
v___x_24_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1));
v___x_25_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_26_ = l_mkPanicMessageWithDecl(v___x_25_, v___x_24_, v___x_23_, v___x_22_, v___x_21_);
return v___x_26_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_27_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2));
v___x_28_ = lean_unsigned_to_nat(21u);
v___x_29_ = lean_unsigned_to_nat(183u);
v___x_30_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1));
v___x_31_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_32_ = l_mkPanicMessageWithDecl(v___x_31_, v___x_30_, v___x_29_, v___x_28_, v___x_27_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6));
v___x_36_ = lean_unsigned_to_nat(35u);
v___x_37_ = lean_unsigned_to_nat(276u);
v___x_38_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5));
v___x_39_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_40_ = l_mkPanicMessageWithDecl(v___x_39_, v___x_38_, v___x_37_, v___x_36_, v___x_35_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_41_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6));
v___x_42_ = lean_unsigned_to_nat(21u);
v___x_43_ = lean_unsigned_to_nat(277u);
v___x_44_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5));
v___x_45_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_46_ = l_mkPanicMessageWithDecl(v___x_45_, v___x_44_, v___x_43_, v___x_42_, v___x_41_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(lean_object* v_k_47_, lean_object* v_v_48_, lean_object* v_t_49_){
_start:
{
if (lean_obj_tag(v_t_49_) == 0)
{
lean_object* v_size_50_; lean_object* v_k_51_; lean_object* v_v_52_; lean_object* v_l_53_; lean_object* v_r_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_410_; 
v_size_50_ = lean_ctor_get(v_t_49_, 0);
v_k_51_ = lean_ctor_get(v_t_49_, 1);
v_v_52_ = lean_ctor_get(v_t_49_, 2);
v_l_53_ = lean_ctor_get(v_t_49_, 3);
v_r_54_ = lean_ctor_get(v_t_49_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v_t_49_);
if (v_isSharedCheck_410_ == 0)
{
v___x_56_ = v_t_49_;
v_isShared_57_ = v_isSharedCheck_410_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_r_54_);
lean_inc(v_l_53_);
lean_inc(v_v_52_);
lean_inc(v_k_51_);
lean_inc(v_size_50_);
lean_dec(v_t_49_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_410_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
uint8_t v___x_58_; 
v___x_58_ = lean_string_compare(v_k_47_, v_k_51_);
switch(v___x_58_)
{
case 0:
{
lean_object* v___x_59_; 
lean_dec(v_size_50_);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_k_47_, v_v_48_, v_l_53_);
if (lean_obj_tag(v_r_54_) == 0)
{
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_size_60_; lean_object* v_size_61_; lean_object* v_k_62_; lean_object* v_v_63_; lean_object* v_l_64_; lean_object* v_r_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_size_60_ = lean_ctor_get(v_r_54_, 0);
v_size_61_ = lean_ctor_get(v___x_59_, 0);
v_k_62_ = lean_ctor_get(v___x_59_, 1);
v_v_63_ = lean_ctor_get(v___x_59_, 2);
v_l_64_ = lean_ctor_get(v___x_59_, 3);
v_r_65_ = lean_ctor_get(v___x_59_, 4);
lean_inc(v_r_65_);
v___x_66_ = lean_unsigned_to_nat(3u);
v___x_67_ = lean_nat_mul(v___x_66_, v_size_60_);
v___x_68_ = lean_nat_dec_lt(v___x_67_, v_size_61_);
lean_dec(v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
lean_dec(v_r_65_);
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lean_nat_add(v___x_69_, v_size_61_);
v___x_71_ = lean_nat_add(v___x_70_, v_size_60_);
lean_dec(v___x_70_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 3, v___x_59_);
lean_ctor_set(v___x_56_, 0, v___x_71_);
v___x_73_ = v___x_56_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v_r_54_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
else
{
lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_146_; 
lean_inc(v_l_64_);
lean_inc(v_v_63_);
lean_inc(v_k_62_);
lean_inc(v_size_61_);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; lean_object* v_unused_148_; lean_object* v_unused_149_; lean_object* v_unused_150_; lean_object* v_unused_151_; 
v_unused_147_ = lean_ctor_get(v___x_59_, 4);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v___x_59_, 3);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v___x_59_, 2);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v___x_59_, 1);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v___x_59_, 0);
lean_dec(v_unused_151_);
v___x_76_ = v___x_59_;
v_isShared_77_ = v_isSharedCheck_146_;
goto v_resetjp_75_;
}
else
{
lean_dec(v___x_59_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_146_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
if (lean_obj_tag(v_l_64_) == 0)
{
if (lean_obj_tag(v_r_65_) == 0)
{
lean_object* v_size_78_; lean_object* v_size_79_; lean_object* v_k_80_; lean_object* v_v_81_; lean_object* v_l_82_; lean_object* v_r_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_size_78_ = lean_ctor_get(v_l_64_, 0);
v_size_79_ = lean_ctor_get(v_r_65_, 0);
v_k_80_ = lean_ctor_get(v_r_65_, 1);
v_v_81_ = lean_ctor_get(v_r_65_, 2);
v_l_82_ = lean_ctor_get(v_r_65_, 3);
v_r_83_ = lean_ctor_get(v_r_65_, 4);
v___x_84_ = lean_unsigned_to_nat(2u);
v___x_85_ = lean_nat_mul(v___x_84_, v_size_78_);
v___x_86_ = lean_nat_dec_lt(v_size_79_, v___x_85_);
lean_dec(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_r_83_);
lean_inc(v_l_82_);
lean_inc(v_v_81_);
lean_inc(v_k_80_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_r_65_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; lean_object* v_unused_119_; lean_object* v_unused_120_; lean_object* v_unused_121_; 
v_unused_117_ = lean_ctor_get(v_r_65_, 4);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_r_65_, 3);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_r_65_, 2);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_r_65_, 1);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_r_65_, 0);
lean_dec(v_unused_121_);
v___x_88_ = v_r_65_;
v_isShared_89_ = v_isSharedCheck_116_;
goto v_resetjp_87_;
}
else
{
lean_dec(v_r_65_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_116_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___x_104_; lean_object* v___y_106_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v___x_90_, v_size_61_);
lean_dec(v_size_61_);
v___x_92_ = lean_nat_add(v___x_91_, v_size_60_);
lean_dec(v___x_91_);
v___x_104_ = lean_nat_add(v___x_90_, v_size_78_);
if (lean_obj_tag(v_l_82_) == 0)
{
lean_object* v_size_114_; 
v_size_114_ = lean_ctor_get(v_l_82_, 0);
lean_inc(v_size_114_);
v___y_106_ = v_size_114_;
goto v___jp_105_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___y_106_ = v___x_115_;
goto v___jp_105_;
}
v___jp_93_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_nat_add(v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec(v___y_95_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_r_54_);
lean_ctor_set(v___x_88_, 3, v_r_83_);
lean_ctor_set(v___x_88_, 2, v_v_52_);
lean_ctor_set(v___x_88_, 1, v_k_51_);
lean_ctor_set(v___x_88_, 0, v___x_97_);
v___x_99_ = v___x_88_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_r_83_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v_r_54_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 4, v___x_99_);
lean_ctor_set(v___x_76_, 3, v___y_94_);
lean_ctor_set(v___x_76_, 2, v_v_81_);
lean_ctor_set(v___x_76_, 1, v_k_80_);
lean_ctor_set(v___x_76_, 0, v___x_92_);
v___x_101_ = v___x_76_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_k_80_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_v_81_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v___y_94_);
lean_ctor_set(v_reuseFailAlloc_102_, 4, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_nat_add(v___x_104_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___x_104_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v_l_82_);
lean_ctor_set(v___x_56_, 3, v_l_64_);
lean_ctor_set(v___x_56_, 2, v_v_63_);
lean_ctor_set(v___x_56_, 1, v_k_62_);
lean_ctor_set(v___x_56_, 0, v___x_107_);
v___x_109_ = v___x_56_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_l_64_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_l_82_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_add(v___x_90_, v_size_60_);
if (lean_obj_tag(v_r_83_) == 0)
{
lean_object* v_size_111_; 
v_size_111_ = lean_ctor_get(v_r_83_, 0);
lean_inc(v_size_111_);
v___y_94_ = v___x_109_;
v___y_95_ = v___x_110_;
v___y_96_ = v_size_111_;
goto v___jp_93_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___y_94_ = v___x_109_;
v___y_95_ = v___x_110_;
v___y_96_ = v___x_112_;
goto v___jp_93_;
}
}
}
}
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_del_object(v___x_56_);
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v___x_122_, v_size_61_);
lean_dec(v_size_61_);
v___x_124_ = lean_nat_add(v___x_123_, v_size_60_);
lean_dec(v___x_123_);
v___x_125_ = lean_nat_add(v___x_122_, v_size_60_);
v___x_126_ = lean_nat_add(v___x_125_, v_size_79_);
lean_dec(v___x_125_);
lean_inc_ref(v_r_54_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 4, v_r_54_);
lean_ctor_set(v___x_76_, 3, v_r_65_);
lean_ctor_set(v___x_76_, 2, v_v_52_);
lean_ctor_set(v___x_76_, 1, v_k_51_);
lean_ctor_set(v___x_76_, 0, v___x_126_);
v___x_128_ = v___x_76_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_r_65_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_r_54_);
v___x_128_ = v_reuseFailAlloc_141_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
v_isSharedCheck_135_ = !lean_is_exclusive(v_r_54_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; lean_object* v_unused_137_; lean_object* v_unused_138_; lean_object* v_unused_139_; lean_object* v_unused_140_; 
v_unused_136_ = lean_ctor_get(v_r_54_, 4);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_r_54_, 3);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_r_54_, 2);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_r_54_, 1);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_r_54_, 0);
lean_dec(v_unused_140_);
v___x_130_ = v_r_54_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_r_54_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v___x_128_);
lean_ctor_set(v___x_130_, 3, v_l_64_);
lean_ctor_set(v___x_130_, 2, v_v_63_);
lean_ctor_set(v___x_130_, 1, v_k_62_);
lean_ctor_set(v___x_130_, 0, v___x_124_);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_62_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_63_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_l_64_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v___x_128_);
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
else
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec_ref_known(v_l_64_, 5);
lean_del_object(v___x_76_);
lean_dec(v_v_63_);
lean_dec(v_k_62_);
lean_dec(v_size_61_);
lean_dec_ref_known(v_r_54_, 5);
lean_del_object(v___x_56_);
lean_dec(v_v_52_);
lean_dec(v_k_51_);
v___x_142_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3);
v___x_143_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_142_);
return v___x_143_;
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_del_object(v___x_76_);
lean_dec(v_r_65_);
lean_dec(v_v_63_);
lean_dec(v_k_62_);
lean_dec(v_size_61_);
lean_dec_ref_known(v_r_54_, 5);
lean_del_object(v___x_56_);
lean_dec(v_v_52_);
lean_dec(v_k_51_);
v___x_144_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4);
v___x_145_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_144_);
return v___x_145_;
}
}
}
}
else
{
lean_object* v_size_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v_size_152_ = lean_ctor_get(v_r_54_, 0);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v___x_153_, v_size_152_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 3, v___x_59_);
lean_ctor_set(v___x_56_, 0, v___x_154_);
v___x_156_ = v___x_56_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_r_54_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_l_158_; 
v_l_158_ = lean_ctor_get(v___x_59_, 3);
if (lean_obj_tag(v_l_158_) == 0)
{
lean_object* v_r_159_; 
lean_inc_ref(v_l_158_);
v_r_159_ = lean_ctor_get(v___x_59_, 4);
lean_inc(v_r_159_);
if (lean_obj_tag(v_r_159_) == 0)
{
lean_object* v_size_160_; lean_object* v_k_161_; lean_object* v_v_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_176_; 
v_size_160_ = lean_ctor_get(v___x_59_, 0);
v_k_161_ = lean_ctor_get(v___x_59_, 1);
v_v_162_ = lean_ctor_get(v___x_59_, 2);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; lean_object* v_unused_178_; 
v_unused_177_ = lean_ctor_get(v___x_59_, 4);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v___x_59_, 3);
lean_dec(v_unused_178_);
v___x_164_ = v___x_59_;
v_isShared_165_ = v_isSharedCheck_176_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_v_162_);
lean_inc(v_k_161_);
lean_inc(v_size_160_);
lean_dec(v___x_59_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_176_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_size_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v_size_166_ = lean_ctor_get(v_r_159_, 0);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v___x_167_, v_size_160_);
lean_dec(v_size_160_);
v___x_169_ = lean_nat_add(v___x_167_, v_size_166_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v_r_54_);
lean_ctor_set(v___x_164_, 3, v_r_159_);
lean_ctor_set(v___x_164_, 2, v_v_52_);
lean_ctor_set(v___x_164_, 1, v_k_51_);
lean_ctor_set(v___x_164_, 0, v___x_169_);
v___x_171_ = v___x_164_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_159_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_54_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_171_);
lean_ctor_set(v___x_56_, 3, v_l_158_);
lean_ctor_set(v___x_56_, 2, v_v_162_);
lean_ctor_set(v___x_56_, 1, v_k_161_);
lean_ctor_set(v___x_56_, 0, v___x_168_);
v___x_173_ = v___x_56_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_k_161_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_v_162_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v_l_158_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_k_179_; lean_object* v_v_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_192_; 
v_k_179_ = lean_ctor_get(v___x_59_, 1);
v_v_180_ = lean_ctor_get(v___x_59_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_193_ = lean_ctor_get(v___x_59_, 4);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v___x_59_, 3);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v___x_59_, 0);
lean_dec(v_unused_195_);
v___x_182_ = v___x_59_;
v_isShared_183_ = v_isSharedCheck_192_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_v_180_);
lean_inc(v_k_179_);
lean_dec(v___x_59_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_192_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_unsigned_to_nat(3u);
v___x_185_ = lean_unsigned_to_nat(1u);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 3, v_r_159_);
lean_ctor_set(v___x_182_, 2, v_v_52_);
lean_ctor_set(v___x_182_, 1, v_k_51_);
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_r_159_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_r_159_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_187_);
lean_ctor_set(v___x_56_, 3, v_l_158_);
lean_ctor_set(v___x_56_, 2, v_v_180_);
lean_ctor_set(v___x_56_, 1, v_k_179_);
lean_ctor_set(v___x_56_, 0, v___x_184_);
v___x_189_ = v___x_56_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_k_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_v_180_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_l_158_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
else
{
lean_object* v_r_196_; 
v_r_196_ = lean_ctor_get(v___x_59_, 4);
lean_inc(v_r_196_);
if (lean_obj_tag(v_r_196_) == 0)
{
lean_object* v_k_197_; lean_object* v_v_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_222_; 
lean_inc(v_l_158_);
v_k_197_ = lean_ctor_get(v___x_59_, 1);
v_v_198_ = lean_ctor_get(v___x_59_, 2);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; 
v_unused_223_ = lean_ctor_get(v___x_59_, 4);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v___x_59_, 3);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v___x_59_, 0);
lean_dec(v_unused_225_);
v___x_200_ = v___x_59_;
v_isShared_201_ = v_isSharedCheck_222_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_v_198_);
lean_inc(v_k_197_);
lean_dec(v___x_59_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_222_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_k_202_; lean_object* v_v_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_218_; 
v_k_202_ = lean_ctor_get(v_r_196_, 1);
v_v_203_ = lean_ctor_get(v_r_196_, 2);
v_isSharedCheck_218_ = !lean_is_exclusive(v_r_196_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; lean_object* v_unused_220_; lean_object* v_unused_221_; 
v_unused_219_ = lean_ctor_get(v_r_196_, 4);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_r_196_, 3);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_r_196_, 0);
lean_dec(v_unused_221_);
v___x_205_ = v_r_196_;
v_isShared_206_ = v_isSharedCheck_218_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_v_203_);
lean_inc(v_k_202_);
lean_dec(v_r_196_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_218_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_207_ = lean_unsigned_to_nat(3u);
v___x_208_ = lean_unsigned_to_nat(1u);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 4, v_l_158_);
lean_ctor_set(v___x_205_, 3, v_l_158_);
lean_ctor_set(v___x_205_, 2, v_v_198_);
lean_ctor_set(v___x_205_, 1, v_k_197_);
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_k_197_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_v_198_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_l_158_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_l_158_);
v___x_210_ = v_reuseFailAlloc_217_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 4, v_l_158_);
lean_ctor_set(v___x_200_, 2, v_v_52_);
lean_ctor_set(v___x_200_, 1, v_k_51_);
lean_ctor_set(v___x_200_, 0, v___x_208_);
v___x_212_ = v___x_200_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_l_158_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_l_158_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_212_);
lean_ctor_set(v___x_56_, 3, v___x_210_);
lean_ctor_set(v___x_56_, 2, v_v_203_);
lean_ctor_set(v___x_56_, 1, v_k_202_);
lean_ctor_set(v___x_56_, 0, v___x_207_);
v___x_214_ = v___x_56_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
else
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(2u);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v_r_196_);
lean_ctor_set(v___x_56_, 3, v___x_59_);
lean_ctor_set(v___x_56_, 0, v___x_226_);
v___x_228_ = v___x_56_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v_r_196_);
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
else
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(1u);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_59_);
lean_ctor_set(v___x_56_, 3, v___x_59_);
lean_ctor_set(v___x_56_, 0, v___x_230_);
v___x_232_ = v___x_56_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v___x_59_);
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
case 1:
{
lean_object* v___x_235_; 
lean_dec(v_v_52_);
lean_dec(v_k_51_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 2, v_v_48_);
lean_ctor_set(v___x_56_, 1, v_k_47_);
v___x_235_ = v___x_56_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_size_50_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_k_47_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_v_48_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_l_53_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_r_54_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
default: 
{
lean_object* v___x_237_; 
lean_dec(v_size_50_);
v___x_237_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_k_47_, v_v_48_, v_r_54_);
if (lean_obj_tag(v_l_53_) == 0)
{
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_size_238_; lean_object* v_size_239_; lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v_l_242_; lean_object* v_r_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_size_238_ = lean_ctor_get(v_l_53_, 0);
v_size_239_ = lean_ctor_get(v___x_237_, 0);
v_k_240_ = lean_ctor_get(v___x_237_, 1);
v_v_241_ = lean_ctor_get(v___x_237_, 2);
v_l_242_ = lean_ctor_get(v___x_237_, 3);
lean_inc(v_l_242_);
v_r_243_ = lean_ctor_get(v___x_237_, 4);
v___x_244_ = lean_unsigned_to_nat(3u);
v___x_245_ = lean_nat_mul(v___x_244_, v_size_238_);
v___x_246_ = lean_nat_dec_lt(v___x_245_, v_size_239_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec(v_l_242_);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_add(v___x_247_, v_size_238_);
v___x_249_ = lean_nat_add(v___x_248_, v_size_239_);
lean_dec(v___x_248_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_237_);
lean_ctor_set(v___x_56_, 0, v___x_249_);
v___x_251_ = v___x_56_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_l_53_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v___x_237_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_322_; 
lean_inc(v_r_243_);
lean_inc(v_v_241_);
lean_inc(v_k_240_);
lean_inc(v_size_239_);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; 
v_unused_323_ = lean_ctor_get(v___x_237_, 4);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v___x_237_, 3);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v___x_237_, 2);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v___x_237_, 1);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_327_);
v___x_254_ = v___x_237_;
v_isShared_255_ = v_isSharedCheck_322_;
goto v_resetjp_253_;
}
else
{
lean_dec(v___x_237_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_322_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
if (lean_obj_tag(v_l_242_) == 0)
{
if (lean_obj_tag(v_r_243_) == 0)
{
lean_object* v_size_256_; lean_object* v_k_257_; lean_object* v_v_258_; lean_object* v_l_259_; lean_object* v_r_260_; lean_object* v_size_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_size_256_ = lean_ctor_get(v_l_242_, 0);
v_k_257_ = lean_ctor_get(v_l_242_, 1);
v_v_258_ = lean_ctor_get(v_l_242_, 2);
v_l_259_ = lean_ctor_get(v_l_242_, 3);
v_r_260_ = lean_ctor_get(v_l_242_, 4);
v_size_261_ = lean_ctor_get(v_r_243_, 0);
v___x_262_ = lean_unsigned_to_nat(2u);
v___x_263_ = lean_nat_mul(v___x_262_, v_size_261_);
v___x_264_ = lean_nat_dec_lt(v_size_256_, v___x_263_);
lean_dec(v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_293_; 
lean_inc(v_r_260_);
lean_inc(v_l_259_);
lean_inc(v_v_258_);
lean_inc(v_k_257_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_l_242_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_294_ = lean_ctor_get(v_l_242_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_242_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_242_, 2);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_242_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_242_, 0);
lean_dec(v_unused_298_);
v___x_266_ = v_l_242_;
v_isShared_267_ = v_isSharedCheck_293_;
goto v_resetjp_265_;
}
else
{
lean_dec(v_l_242_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_293_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_283_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v___x_268_, v_size_238_);
v___x_270_ = lean_nat_add(v___x_269_, v_size_239_);
lean_dec(v_size_239_);
if (lean_obj_tag(v_l_259_) == 0)
{
lean_object* v_size_291_; 
v_size_291_ = lean_ctor_get(v_l_259_, 0);
lean_inc(v_size_291_);
v___y_283_ = v_size_291_;
goto v___jp_282_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___y_283_ = v___x_292_;
goto v___jp_282_;
}
v___jp_271_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_nat_add(v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec(v___y_273_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 4, v_r_243_);
lean_ctor_set(v___x_266_, 3, v_r_260_);
lean_ctor_set(v___x_266_, 2, v_v_241_);
lean_ctor_set(v___x_266_, 1, v_k_240_);
lean_ctor_set(v___x_266_, 0, v___x_275_);
v___x_277_ = v___x_266_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_r_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_r_243_);
v___x_277_ = v_reuseFailAlloc_281_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_279_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v___x_277_);
lean_ctor_set(v___x_254_, 3, v___y_272_);
lean_ctor_set(v___x_254_, 2, v_v_258_);
lean_ctor_set(v___x_254_, 1, v_k_257_);
lean_ctor_set(v___x_254_, 0, v___x_270_);
v___x_279_ = v___x_254_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_k_257_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_v_258_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v___y_272_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
v___jp_282_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_nat_add(v___x_269_, v___y_283_);
lean_dec(v___y_283_);
lean_dec(v___x_269_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v_l_259_);
lean_ctor_set(v___x_56_, 0, v___x_284_);
v___x_286_ = v___x_56_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_l_53_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_l_259_);
v___x_286_ = v_reuseFailAlloc_290_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; 
v___x_287_ = lean_nat_add(v___x_268_, v_size_261_);
if (lean_obj_tag(v_r_260_) == 0)
{
lean_object* v_size_288_; 
v_size_288_ = lean_ctor_get(v_r_260_, 0);
lean_inc(v_size_288_);
v___y_272_ = v___x_286_;
v___y_273_ = v___x_287_;
v___y_274_ = v_size_288_;
goto v___jp_271_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___y_272_ = v___x_286_;
v___y_273_ = v___x_287_;
v___y_274_ = v___x_289_;
goto v___jp_271_;
}
}
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_del_object(v___x_56_);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v___x_299_, v_size_238_);
v___x_301_ = lean_nat_add(v___x_300_, v_size_239_);
lean_dec(v_size_239_);
v___x_302_ = lean_nat_add(v___x_300_, v_size_256_);
lean_dec(v___x_300_);
lean_inc_ref(v_l_53_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v_l_242_);
lean_ctor_set(v___x_254_, 3, v_l_53_);
lean_ctor_set(v___x_254_, 2, v_v_52_);
lean_ctor_set(v___x_254_, 1, v_k_51_);
lean_ctor_set(v___x_254_, 0, v___x_302_);
v___x_304_ = v___x_254_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_l_53_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_l_242_);
v___x_304_ = v_reuseFailAlloc_317_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v_l_53_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_312_ = lean_ctor_get(v_l_53_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_53_, 3);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_53_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_53_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_53_, 0);
lean_dec(v_unused_316_);
v___x_306_ = v_l_53_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_l_53_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 4, v_r_243_);
lean_ctor_set(v___x_306_, 3, v___x_304_);
lean_ctor_set(v___x_306_, 2, v_v_241_);
lean_ctor_set(v___x_306_, 1, v_k_240_);
lean_ctor_set(v___x_306_, 0, v___x_301_);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_r_243_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref_known(v_l_242_, 5);
lean_del_object(v___x_254_);
lean_dec(v_v_241_);
lean_dec(v_k_240_);
lean_dec(v_size_239_);
lean_dec_ref_known(v_l_53_, 5);
lean_del_object(v___x_56_);
lean_dec(v_v_52_);
lean_dec(v_k_51_);
v___x_318_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7);
v___x_319_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_318_);
return v___x_319_;
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_del_object(v___x_254_);
lean_dec(v_r_243_);
lean_dec(v_v_241_);
lean_dec(v_k_240_);
lean_dec(v_size_239_);
lean_dec_ref_known(v_l_53_, 5);
lean_del_object(v___x_56_);
lean_dec(v_v_52_);
lean_dec(v_k_51_);
v___x_320_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8);
v___x_321_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_320_);
return v___x_321_;
}
}
}
}
else
{
lean_object* v_size_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v_size_328_ = lean_ctor_get(v_l_53_, 0);
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_add(v___x_329_, v_size_328_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_237_);
lean_ctor_set(v___x_56_, 0, v___x_330_);
v___x_332_ = v___x_56_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_l_53_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v___x_237_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_l_334_; 
v_l_334_ = lean_ctor_get(v___x_237_, 3);
lean_inc(v_l_334_);
if (lean_obj_tag(v_l_334_) == 0)
{
lean_object* v_r_335_; 
v_r_335_ = lean_ctor_get(v___x_237_, 4);
lean_inc(v_r_335_);
if (lean_obj_tag(v_r_335_) == 0)
{
lean_object* v_size_336_; lean_object* v_k_337_; lean_object* v_v_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_352_; 
v_size_336_ = lean_ctor_get(v___x_237_, 0);
v_k_337_ = lean_ctor_get(v___x_237_, 1);
v_v_338_ = lean_ctor_get(v___x_237_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_353_ = lean_ctor_get(v___x_237_, 4);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v___x_237_, 3);
lean_dec(v_unused_354_);
v___x_340_ = v___x_237_;
v_isShared_341_ = v_isSharedCheck_352_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_v_338_);
lean_inc(v_k_337_);
lean_inc(v_size_336_);
lean_dec(v___x_237_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_352_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_size_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v_size_342_ = lean_ctor_get(v_l_334_, 0);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v___x_343_, v_size_336_);
lean_dec(v_size_336_);
v___x_345_ = lean_nat_add(v___x_343_, v_size_342_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 4, v_l_334_);
lean_ctor_set(v___x_340_, 3, v_l_53_);
lean_ctor_set(v___x_340_, 2, v_v_52_);
lean_ctor_set(v___x_340_, 1, v_k_51_);
lean_ctor_set(v___x_340_, 0, v___x_345_);
v___x_347_ = v___x_340_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_l_53_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_l_334_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_349_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v_r_335_);
lean_ctor_set(v___x_56_, 3, v___x_347_);
lean_ctor_set(v___x_56_, 2, v_v_338_);
lean_ctor_set(v___x_56_, 1, v_k_337_);
lean_ctor_set(v___x_56_, 0, v___x_344_);
v___x_349_ = v___x_56_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_r_335_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_k_355_; lean_object* v_v_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_380_; 
v_k_355_ = lean_ctor_get(v___x_237_, 1);
v_v_356_ = lean_ctor_get(v___x_237_, 2);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_381_ = lean_ctor_get(v___x_237_, 4);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v___x_237_, 3);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_383_);
v___x_358_ = v___x_237_;
v_isShared_359_ = v_isSharedCheck_380_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_v_356_);
lean_inc(v_k_355_);
lean_dec(v___x_237_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_380_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_376_; 
v_k_360_ = lean_ctor_get(v_l_334_, 1);
v_v_361_ = lean_ctor_get(v_l_334_, 2);
v_isSharedCheck_376_ = !lean_is_exclusive(v_l_334_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_377_ = lean_ctor_get(v_l_334_, 4);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_l_334_, 3);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_l_334_, 0);
lean_dec(v_unused_379_);
v___x_363_ = v_l_334_;
v_isShared_364_ = v_isSharedCheck_376_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_v_361_);
lean_inc(v_k_360_);
lean_dec(v_l_334_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_376_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_unsigned_to_nat(3u);
v___x_366_ = lean_unsigned_to_nat(1u);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 4, v_r_335_);
lean_ctor_set(v___x_363_, 3, v_r_335_);
lean_ctor_set(v___x_363_, 2, v_v_52_);
lean_ctor_set(v___x_363_, 1, v_k_51_);
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_r_335_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_r_335_);
v___x_368_ = v_reuseFailAlloc_375_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 3, v_r_335_);
lean_ctor_set(v___x_358_, 0, v___x_366_);
v___x_370_ = v___x_358_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_355_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_356_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_r_335_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_r_335_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_370_);
lean_ctor_set(v___x_56_, 3, v___x_368_);
lean_ctor_set(v___x_56_, 2, v_v_361_);
lean_ctor_set(v___x_56_, 1, v_k_360_);
lean_ctor_set(v___x_56_, 0, v___x_365_);
v___x_372_ = v___x_56_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_384_; 
v_r_384_ = lean_ctor_get(v___x_237_, 4);
lean_inc(v_r_384_);
if (lean_obj_tag(v_r_384_) == 0)
{
lean_object* v_k_385_; lean_object* v_v_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_398_; 
v_k_385_ = lean_ctor_get(v___x_237_, 1);
v_v_386_ = lean_ctor_get(v___x_237_, 2);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_399_ = lean_ctor_get(v___x_237_, 4);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v___x_237_, 3);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v___x_237_, 0);
lean_dec(v_unused_401_);
v___x_388_ = v___x_237_;
v_isShared_389_ = v_isSharedCheck_398_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_v_386_);
lean_inc(v_k_385_);
lean_dec(v___x_237_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_398_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(3u);
v___x_391_ = lean_unsigned_to_nat(1u);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v_l_334_);
lean_ctor_set(v___x_388_, 2, v_v_52_);
lean_ctor_set(v___x_388_, 1, v_k_51_);
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_l_334_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_l_334_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v_r_384_);
lean_ctor_set(v___x_56_, 3, v___x_393_);
lean_ctor_set(v___x_56_, 2, v_v_386_);
lean_ctor_set(v___x_56_, 1, v_k_385_);
lean_ctor_set(v___x_56_, 0, v___x_390_);
v___x_395_ = v___x_56_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_385_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_v_386_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_r_384_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(2u);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_237_);
lean_ctor_set(v___x_56_, 3, v_r_384_);
lean_ctor_set(v___x_56_, 0, v___x_402_);
v___x_404_ = v___x_56_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_r_384_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v___x_237_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(1u);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 4, v___x_237_);
lean_ctor_set(v___x_56_, 3, v___x_237_);
lean_ctor_set(v___x_56_, 0, v___x_406_);
v___x_408_ = v___x_56_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_51_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_52_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v___x_237_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_k_47_);
lean_ctor_set(v___x_412_, 2, v_v_48_);
lean_ctor_set(v___x_412_, 3, v_t_49_);
lean_ctor_set(v___x_412_, 4, v_t_49_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_objectCore(lean_object* v_kvs_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_437_; uint8_t v_decide_438_; 
v_fst_435_ = lean_ctor_get(v_a_434_, 0);
v_snd_436_ = lean_ctor_get(v_a_434_, 1);
v___x_437_ = lean_string_utf8_byte_size(v_fst_435_);
v_decide_438_ = lean_nat_dec_eq(v_snd_436_, v___x_437_);
if (v_decide_438_ == 0)
{
uint32_t v___x_439_; uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_string_utf8_get_fast(v_fst_435_, v_snd_436_);
v___x_440_ = 34;
v___x_441_ = lean_uint32_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_kvs_433_);
v___x_442_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__1));
v___x_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_443_, 0, v_a_434_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
return v___x_443_;
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_545_; 
lean_inc(v_snd_436_);
lean_inc(v_fst_435_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_a_434_, 1);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_a_434_, 0);
lean_dec(v_unused_547_);
v___x_445_ = v_a_434_;
v_isShared_446_ = v_isSharedCheck_545_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_a_434_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_545_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_string_utf8_next_fast(v_fst_435_, v_snd_436_);
lean_dec(v_snd_436_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_fst_435_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_544_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__2));
v___x_451_ = l_Lean_Json_Parser_strCore(v___x_450_, v___x_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_pos_452_; lean_object* v_res_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_534_; 
v_pos_452_ = lean_ctor_get(v___x_451_, 0);
v_res_453_ = lean_ctor_get(v___x_451_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_534_ == 0)
{
v___x_455_ = v___x_451_;
v_isShared_456_ = v_isSharedCheck_534_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_res_453_);
lean_inc(v_pos_452_);
lean_dec(v___x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_534_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_533_; 
v_fst_488_ = lean_ctor_get(v_pos_452_, 0);
v_snd_489_ = lean_ctor_get(v_pos_452_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_pos_452_);
if (v_isSharedCheck_533_ == 0)
{
v___x_491_ = v_pos_452_;
v_isShared_492_ = v_isSharedCheck_533_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snd_489_);
lean_inc(v_fst_488_);
lean_dec(v_pos_452_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_533_;
goto v_resetjp_490_;
}
v___jp_457_:
{
if (v___y_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec(v___y_461_);
lean_dec(v___y_460_);
lean_dec(v___y_458_);
lean_dec(v_res_453_);
lean_dec(v_kvs_433_);
v___x_463_ = lean_box(0);
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 1);
lean_ctor_set(v___x_455_, 1, v___x_463_);
lean_ctor_set(v___x_455_, 0, v___y_459_);
v___x_465_ = v___x_455_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___y_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
uint32_t v___x_467_; lean_object* v___x_468_; uint32_t v___x_469_; uint8_t v___x_470_; 
lean_dec_ref(v___y_459_);
v___x_467_ = lean_string_utf8_get_fast(v___y_460_, v___y_461_);
v___x_468_ = lean_string_utf8_next_fast(v___y_460_, v___y_461_);
lean_dec(v___y_461_);
v___x_469_ = 125;
v___x_470_ = lean_uint32_dec_eq(v___x_467_, v___x_469_);
if (v___x_470_ == 0)
{
uint32_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 44;
v___x_472_ = lean_uint32_dec_eq(v___x_467_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
lean_dec(v___y_458_);
lean_dec(v_res_453_);
lean_dec(v_kvs_433_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___y_460_);
lean_ctor_set(v___x_473_, 1, v___x_468_);
v___x_474_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__4));
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 1);
lean_ctor_set(v___x_455_, 1, v___x_474_);
lean_ctor_set(v___x_455_, 0, v___x_473_);
v___x_476_ = v___x_455_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_del_object(v___x_455_);
v___x_478_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v___y_460_, v___x_468_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___y_460_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_res_453_, v___y_458_, v_kvs_433_);
v_kvs_433_ = v___x_480_;
v_a_434_ = v___x_479_;
goto _start;
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_482_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v___y_460_, v___x_468_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___y_460_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_res_453_, v___y_458_, v_kvs_433_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_484_);
lean_ctor_set(v___x_455_, 0, v___x_483_);
v___x_486_ = v___x_455_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_488_, v_snd_489_);
lean_inc(v___x_493_);
lean_inc(v_fst_488_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_fst_488_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_532_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
uint8_t v___x_496_; uint8_t v___y_498_; 
v___x_496_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_res_453_, v_kvs_433_);
if (v___x_496_ == 0)
{
lean_object* v___x_525_; uint8_t v_decide_526_; 
v___x_525_ = lean_string_utf8_byte_size(v_fst_488_);
v_decide_526_ = lean_nat_dec_eq(v___x_493_, v___x_525_);
if (v_decide_526_ == 0)
{
v___y_498_ = v___x_441_;
goto v___jp_497_;
}
else
{
v___y_498_ = v___x_496_;
goto v___jp_497_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v___x_493_);
lean_dec(v_fst_488_);
lean_del_object(v___x_455_);
lean_dec(v_kvs_433_);
v___x_527_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__7));
v___x_528_ = l_String_quote(v_res_453_);
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
lean_dec_ref(v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_495_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
v___jp_497_:
{
if (v___y_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v___x_493_);
lean_dec(v_fst_488_);
lean_del_object(v___x_455_);
lean_dec(v_res_453_);
lean_dec(v_kvs_433_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_495_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
else
{
uint32_t v___x_501_; uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_string_utf8_get_fast(v_fst_488_, v___x_493_);
v___x_502_ = 58;
v___x_503_ = lean_uint32_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v___x_493_);
lean_dec(v_fst_488_);
lean_del_object(v___x_455_);
lean_dec(v_res_453_);
lean_dec(v_kvs_433_);
v___x_504_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__6));
v___x_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_495_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref(v___x_495_);
v___x_506_ = lean_string_utf8_next_fast(v_fst_488_, v___x_493_);
lean_dec(v___x_493_);
v___x_507_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_488_, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_fst_488_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_LeanExport_Json_anyCore(v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_pos_510_; lean_object* v_res_511_; lean_object* v_fst_512_; lean_object* v_snd_513_; lean_object* v___x_514_; uint8_t v_decide_515_; 
v_pos_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_pos_510_);
v_res_511_ = lean_ctor_get(v___x_509_, 1);
lean_inc(v_res_511_);
lean_dec_ref_known(v___x_509_, 2);
v_fst_512_ = lean_ctor_get(v_pos_510_, 0);
lean_inc(v_fst_512_);
v_snd_513_ = lean_ctor_get(v_pos_510_, 1);
lean_inc(v_snd_513_);
v___x_514_ = lean_string_utf8_byte_size(v_fst_512_);
v_decide_515_ = lean_nat_dec_eq(v_snd_513_, v___x_514_);
if (v_decide_515_ == 0)
{
v___y_458_ = v_res_511_;
v___y_459_ = v_pos_510_;
v___y_460_ = v_fst_512_;
v___y_461_ = v_snd_513_;
v___y_462_ = v___x_503_;
goto v___jp_457_;
}
else
{
v___y_458_ = v_res_511_;
v___y_459_ = v_pos_510_;
v___y_460_ = v_fst_512_;
v___y_461_ = v_snd_513_;
v___y_462_ = v___x_496_;
goto v___jp_457_;
}
}
else
{
lean_object* v_pos_516_; lean_object* v_err_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_del_object(v___x_455_);
lean_dec(v_res_453_);
lean_dec(v_kvs_433_);
v_pos_516_ = lean_ctor_get(v___x_509_, 0);
v_err_517_ = lean_ctor_get(v___x_509_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_509_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_err_517_);
lean_inc(v_pos_516_);
lean_dec(v___x_509_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_pos_516_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_err_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
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
else
{
lean_object* v_pos_535_; lean_object* v_err_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_kvs_433_);
v_pos_535_ = lean_ctor_get(v___x_451_, 0);
v_err_536_ = lean_ctor_get(v___x_451_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_451_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_err_536_);
lean_inc(v_pos_535_);
lean_dec(v___x_451_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_pos_535_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_err_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_kvs_433_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_434_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_anyCore(lean_object* v_a_556_){
_start:
{
lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_593_; uint8_t v_decide_594_; 
v_fst_591_ = lean_ctor_get(v_a_556_, 0);
v_snd_592_ = lean_ctor_get(v_a_556_, 1);
v___x_593_ = lean_string_utf8_byte_size(v_fst_591_);
v_decide_594_ = lean_nat_dec_eq(v_snd_592_, v___x_593_);
if (v_decide_594_ == 0)
{
uint32_t v___x_595_; uint32_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_string_utf8_get_fast(v_fst_591_, v_snd_592_);
v___x_596_ = 91;
v___x_597_ = lean_uint32_dec_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
uint32_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 123;
v___x_599_ = lean_uint32_dec_eq(v___x_595_, v___x_598_);
if (v___x_599_ == 0)
{
uint32_t v___x_600_; uint8_t v___x_601_; 
v___x_600_ = 34;
v___x_601_ = lean_uint32_dec_eq(v___x_595_, v___x_600_);
if (v___x_601_ == 0)
{
uint32_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = 102;
v___x_603_ = lean_uint32_dec_eq(v___x_595_, v___x_602_);
if (v___x_603_ == 0)
{
uint32_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 116;
v___x_605_ = lean_uint32_dec_eq(v___x_595_, v___x_604_);
if (v___x_605_ == 0)
{
uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 110;
v___x_607_ = lean_uint32_dec_eq(v___x_595_, v___x_606_);
if (v___x_607_ == 0)
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 45;
v___x_609_ = lean_uint32_dec_eq(v___x_595_, v___x_608_);
if (v___x_609_ == 0)
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 48;
v___x_611_ = lean_uint32_dec_le(v___x_610_, v___x_595_);
if (v___x_611_ == 0)
{
goto v___jp_588_;
}
else
{
uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 57;
v___x_613_ = lean_uint32_dec_le(v___x_595_, v___x_612_);
if (v___x_613_ == 0)
{
goto v___jp_588_;
}
else
{
goto v___jp_557_;
}
}
}
else
{
goto v___jp_557_;
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__2));
v___x_615_ = l_Std_Internal_Parsec_String_pstring(v___x_614_, v_a_556_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_pos_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_634_; 
v_pos_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v___x_615_, 1);
lean_dec(v_unused_635_);
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_pos_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_fst_620_; lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
v_fst_620_ = lean_ctor_get(v_pos_616_, 0);
v_snd_621_ = lean_ctor_get(v_pos_616_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_pos_616_);
if (v_isSharedCheck_633_ == 0)
{
v___x_623_ = v_pos_616_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec(v_pos_616_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_620_, v_snd_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_632_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_box(0);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_628_);
lean_ctor_set(v___x_618_, 0, v___x_627_);
v___x_630_ = v___x_618_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_object* v_pos_636_; lean_object* v_err_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_pos_636_ = lean_ctor_get(v___x_615_, 0);
v_err_637_ = lean_ctor_get(v___x_615_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_615_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_err_637_);
lean_inc(v_pos_636_);
lean_dec(v___x_615_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_pos_636_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_err_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__3));
v___x_646_ = l_Std_Internal_Parsec_String_pstring(v___x_645_, v_a_556_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_pos_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_665_; 
v_pos_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v___x_646_, 1);
lean_dec(v_unused_666_);
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_pos_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_664_; 
v_fst_651_ = lean_ctor_get(v_pos_647_, 0);
v_snd_652_ = lean_ctor_get(v_pos_647_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_pos_647_);
if (v_isSharedCheck_664_ == 0)
{
v___x_654_ = v_pos_647_;
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
lean_dec(v_pos_647_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_664_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_651_, v_snd_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fst_651_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_663_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_659_, 0, v___x_605_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_659_);
lean_ctor_set(v___x_649_, 0, v___x_658_);
v___x_661_ = v___x_649_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
else
{
lean_object* v_pos_667_; lean_object* v_err_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_pos_667_ = lean_ctor_get(v___x_646_, 0);
v_err_668_ = lean_ctor_get(v___x_646_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_646_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_err_668_);
lean_inc(v_pos_667_);
lean_dec(v___x_646_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_pos_667_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_err_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__4));
v___x_677_ = l_Std_Internal_Parsec_String_pstring(v___x_676_, v_a_556_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_pos_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_696_; 
v_pos_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v___x_677_, 1);
lean_dec(v_unused_697_);
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_696_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_pos_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_696_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_695_; 
v_fst_682_ = lean_ctor_get(v_pos_678_, 0);
v_snd_683_ = lean_ctor_get(v_pos_678_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_pos_678_);
if (v_isSharedCheck_695_ == 0)
{
v___x_685_ = v_pos_678_;
v_isShared_686_ = v_isSharedCheck_695_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_inc(v_fst_682_);
lean_dec(v_pos_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_695_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_682_, v_snd_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_694_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_690_, 0, v___x_601_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_690_);
lean_ctor_set(v___x_680_, 0, v___x_689_);
v___x_692_ = v___x_680_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
else
{
lean_object* v_pos_698_; lean_object* v_err_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_pos_698_ = lean_ctor_get(v___x_677_, 0);
v_err_699_ = lean_ctor_get(v___x_677_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_677_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_err_699_);
lean_inc(v_pos_698_);
lean_dec(v___x_677_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_pos_698_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_err_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_745_; 
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
v_isSharedCheck_745_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_746_ = lean_ctor_get(v_a_556_, 1);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_a_556_, 0);
lean_dec(v_unused_747_);
v___x_708_ = v_a_556_;
v_isShared_709_ = v_isSharedCheck_745_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_a_556_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_745_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_string_utf8_next_fast(v_fst_591_, v_snd_592_);
lean_dec(v_snd_592_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_744_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__2));
v___x_714_ = l_Lean_Json_Parser_strCore(v___x_713_, v___x_712_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_pos_715_; lean_object* v_res_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_734_; 
v_pos_715_ = lean_ctor_get(v___x_714_, 0);
v_res_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_734_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_734_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_res_716_);
lean_inc(v_pos_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_734_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_733_; 
v_fst_720_ = lean_ctor_get(v_pos_715_, 0);
v_snd_721_ = lean_ctor_get(v_pos_715_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_pos_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_723_ = v_pos_715_;
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_inc(v_fst_720_);
lean_dec(v_pos_715_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_720_, v_snd_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_732_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v_res_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_728_);
lean_ctor_set(v___x_718_, 0, v___x_727_);
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
else
{
lean_object* v_pos_735_; lean_object* v_err_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_pos_735_ = lean_ctor_get(v___x_714_, 0);
v_err_736_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_714_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_err_736_);
lean_inc(v_pos_735_);
lean_dec(v___x_714_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_pos_735_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_err_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_790_; 
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_791_ = lean_ctor_get(v_a_556_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_a_556_, 0);
lean_dec(v_unused_792_);
v___x_749_ = v_a_556_;
v_isShared_750_ = v_isSharedCheck_790_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_a_556_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_790_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = lean_string_utf8_next_fast(v_fst_591_, v_snd_592_);
lean_dec(v_snd_592_);
v___x_752_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_591_, v___x_751_);
lean_inc(v___x_752_);
lean_inc(v_fst_591_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_752_);
v___x_754_ = v___x_749_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_789_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
uint8_t v___y_756_; uint8_t v_decide_788_; 
v_decide_788_ = lean_nat_dec_eq(v___x_752_, v___x_593_);
if (v_decide_788_ == 0)
{
v___y_756_ = v___x_599_;
goto v___jp_755_;
}
else
{
v___y_756_ = v___x_597_;
goto v___jp_755_;
}
v___jp_755_:
{
if (v___y_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v___x_752_);
lean_dec(v_fst_591_);
v___x_757_ = lean_box(0);
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_754_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
return v___x_758_;
}
else
{
uint32_t v___x_759_; uint32_t v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_string_utf8_get_fast(v_fst_591_, v___x_752_);
v___x_760_ = 125;
v___x_761_ = lean_uint32_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec(v___x_752_);
lean_dec(v_fst_591_);
v___x_762_ = lean_box(1);
v___x_763_ = l_LeanExport_Json_objectCore(v___x_762_, v___x_754_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_pos_764_; lean_object* v_res_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_pos_764_ = lean_ctor_get(v___x_763_, 0);
v_res_765_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_773_ == 0)
{
v___x_767_ = v___x_763_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_res_765_);
lean_inc(v_pos_764_);
lean_dec(v___x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_769_, 0, v_res_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_pos_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_pos_774_; lean_object* v_err_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_pos_774_ = lean_ctor_get(v___x_763_, 0);
v_err_775_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_763_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_err_775_);
lean_inc(v_pos_774_);
lean_dec(v___x_763_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_pos_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_err_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec_ref(v___x_754_);
v___x_783_ = lean_string_utf8_next_fast(v_fst_591_, v___x_752_);
lean_dec(v___x_752_);
v___x_784_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_591_, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_fst_591_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__5));
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
return v___x_787_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_835_; 
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
v_isSharedCheck_835_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; 
v_unused_836_ = lean_ctor_get(v_a_556_, 1);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_a_556_, 0);
lean_dec(v_unused_837_);
v___x_794_ = v_a_556_;
v_isShared_795_ = v_isSharedCheck_835_;
goto v_resetjp_793_;
}
else
{
lean_dec(v_a_556_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_835_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_string_utf8_next_fast(v_fst_591_, v_snd_592_);
lean_dec(v_snd_592_);
v___x_797_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_591_, v___x_796_);
lean_inc(v___x_797_);
lean_inc(v_fst_591_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_797_);
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_834_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
uint8_t v_decide_803_; 
v_decide_803_ = lean_nat_dec_eq(v___x_797_, v___x_593_);
if (v_decide_803_ == 0)
{
if (v___x_597_ == 0)
{
lean_dec(v___x_797_);
lean_dec(v_fst_591_);
goto v___jp_800_;
}
else
{
uint32_t v___x_804_; uint32_t v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_string_utf8_get_fast(v_fst_591_, v___x_797_);
v___x_805_ = 93;
v___x_806_ = lean_uint32_dec_eq(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v___x_797_);
lean_dec(v_fst_591_);
v___x_807_ = lean_unsigned_to_nat(4u);
v___x_808_ = lean_mk_empty_array_with_capacity(v___x_807_);
v___x_809_ = l_LeanExport_Json_arrayCore(v___x_808_, v___x_799_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_pos_810_; lean_object* v_res_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_pos_810_ = lean_ctor_get(v___x_809_, 0);
v_res_811_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v___x_809_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_res_811_);
lean_inc(v_pos_810_);
lean_dec(v___x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_815_, 0, v_res_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_pos_810_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_pos_820_; lean_object* v_err_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_pos_820_ = lean_ctor_get(v___x_809_, 0);
v_err_821_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_809_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_err_821_);
lean_inc(v_pos_820_);
lean_dec(v___x_809_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_pos_820_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_err_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___x_799_);
v___x_829_ = lean_string_utf8_next_fast(v_fst_591_, v___x_797_);
lean_dec(v___x_797_);
v___x_830_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_591_, v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_fst_591_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__7));
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
return v___x_833_;
}
}
}
else
{
lean_dec(v___x_797_);
lean_dec(v_fst_591_);
goto v___jp_800_;
}
v___jp_800_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_box(0);
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v_a_556_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
v___jp_557_:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Json_Parser_num(v_a_556_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_pos_559_; lean_object* v_res_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_578_; 
v_pos_559_ = lean_ctor_get(v___x_558_, 0);
v_res_560_ = lean_ctor_get(v___x_558_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_578_ == 0)
{
v___x_562_ = v___x_558_;
v_isShared_563_ = v_isSharedCheck_578_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_res_560_);
lean_inc(v_pos_559_);
lean_dec(v___x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_578_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v_fst_564_ = lean_ctor_get(v_pos_559_, 0);
v_snd_565_ = lean_ctor_get(v_pos_559_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_pos_559_);
if (v_isSharedCheck_577_ == 0)
{
v___x_567_ = v_pos_559_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_inc(v_fst_564_);
lean_dec(v_pos_559_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_564_, v_snd_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_fst_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_576_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_572_, 0, v_res_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_572_);
lean_ctor_set(v___x_562_, 0, v___x_571_);
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v_pos_579_; lean_object* v_err_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_pos_579_ = lean_ctor_get(v___x_558_, 0);
v_err_580_ = lean_ctor_get(v___x_558_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_558_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_err_580_);
lean_inc(v_pos_579_);
lean_dec(v___x_558_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_pos_579_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_err_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
v___jp_588_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__1));
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v_a_556_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_arrayCore(lean_object* v_acc_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_LeanExport_Json_anyCore(v_a_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_pos_843_; lean_object* v_res_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_888_; 
v_pos_843_ = lean_ctor_get(v___x_842_, 0);
v_res_844_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_888_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_888_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_res_844_);
lean_inc(v_pos_843_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_888_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_850_; uint8_t v_decide_851_; 
v_fst_848_ = lean_ctor_get(v_pos_843_, 0);
v_snd_849_ = lean_ctor_get(v_pos_843_, 1);
v___x_850_ = lean_string_utf8_byte_size(v_fst_848_);
v_decide_851_ = lean_nat_dec_eq(v_snd_849_, v___x_850_);
if (v_decide_851_ == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_881_; 
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
v_isSharedCheck_881_ = !lean_is_exclusive(v_pos_843_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_882_ = lean_ctor_get(v_pos_843_, 1);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_pos_843_, 0);
lean_dec(v_unused_883_);
v___x_853_ = v_pos_843_;
v_isShared_854_ = v_isSharedCheck_881_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_pos_843_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_881_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; uint32_t v___x_856_; lean_object* v___x_857_; uint32_t v___x_858_; uint8_t v___x_859_; 
v___x_855_ = lean_array_push(v_acc_840_, v_res_844_);
v___x_856_ = lean_string_utf8_get_fast(v_fst_848_, v_snd_849_);
v___x_857_ = lean_string_utf8_next_fast(v_fst_848_, v_snd_849_);
lean_dec(v_snd_849_);
v___x_858_ = 93;
v___x_859_ = lean_uint32_dec_eq(v___x_856_, v___x_858_);
if (v___x_859_ == 0)
{
uint32_t v___x_860_; uint8_t v___x_861_; 
v___x_860_ = 44;
v___x_861_ = lean_uint32_dec_eq(v___x_856_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v___x_855_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_857_);
v___x_863_ = v___x_853_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_857_);
v___x_863_ = v_reuseFailAlloc_868_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = ((lean_object*)(l_LeanExport_Json_arrayCore___closed__1));
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 1, v___x_864_);
lean_ctor_set(v___x_846_, 0, v___x_863_);
v___x_866_ = v___x_846_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_871_; 
lean_del_object(v___x_846_);
v___x_869_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_848_, v___x_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_869_);
v___x_871_ = v___x_853_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_873_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_acc_840_ = v___x_855_;
v_a_841_ = v___x_871_;
goto _start;
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_848_, v___x_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_874_);
v___x_876_ = v___x_853_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_855_);
lean_ctor_set(v___x_846_, 0, v___x_876_);
v___x_878_ = v___x_846_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_855_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec(v_res_844_);
lean_dec_ref(v_acc_840_);
v___x_884_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 1, v___x_884_);
v___x_886_ = v___x_846_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_pos_843_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_pos_889_; lean_object* v_err_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_acc_840_);
v_pos_889_ = lean_ctor_get(v___x_842_, 0);
v_err_890_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_842_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_err_890_);
lean_inc(v_pos_889_);
lean_dec(v___x_842_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_pos_889_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_err_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2(lean_object* v_00_u03b2_898_, lean_object* v_k_899_, lean_object* v_t_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_k_899_, v_t_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___boxed(lean_object* v_00_u03b2_902_, lean_object* v_k_903_, lean_object* v_t_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2(v_00_u03b2_902_, v_k_903_, v_t_904_);
lean_dec(v_t_904_);
lean_dec_ref(v_k_903_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3(lean_object* v_00_u03b2_907_, lean_object* v_msg_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v_msg_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3(lean_object* v_00_u03b2_910_, lean_object* v_k_911_, lean_object* v_v_912_, lean_object* v_t_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_k_911_, v_v_912_, v_t_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_parse___lam__0(lean_object* v___y_918_){
_start:
{
lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_944_; 
v_fst_919_ = lean_ctor_get(v___y_918_, 0);
v_snd_920_ = lean_ctor_get(v___y_918_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___y_918_);
if (v_isSharedCheck_944_ == 0)
{
v___x_922_ = v___y_918_;
v_isShared_923_ = v_isSharedCheck_944_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_920_);
lean_inc(v_fst_919_);
lean_dec(v___y_918_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_944_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_919_, v_snd_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_fst_919_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_943_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; 
v___x_927_ = l_LeanExport_Json_anyCore(v___x_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_pos_928_; lean_object* v_fst_929_; lean_object* v_snd_930_; lean_object* v___x_931_; uint8_t v_decide_932_; 
v_pos_928_ = lean_ctor_get(v___x_927_, 0);
v_fst_929_ = lean_ctor_get(v_pos_928_, 0);
v_snd_930_ = lean_ctor_get(v_pos_928_, 1);
v___x_931_ = lean_string_utf8_byte_size(v_fst_929_);
v_decide_932_ = lean_nat_dec_eq(v_snd_930_, v___x_931_);
if (v_decide_932_ == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
lean_inc(v_pos_928_);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; lean_object* v_unused_942_; 
v_unused_941_ = lean_ctor_get(v___x_927_, 1);
lean_dec(v_unused_941_);
v_unused_942_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_942_);
v___x_934_ = v___x_927_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l_LeanExport_Json_parse___lam__0___closed__1));
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 1);
lean_ctor_set(v___x_934_, 1, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_pos_928_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
return v___x_927_;
}
}
else
{
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_parse(lean_object* v_s_946_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; 
v___f_947_ = ((lean_object*)(l_LeanExport_Json_parse___closed__0));
v___x_948_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_947_, v_s_946_);
return v___x_948_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanExport_Json(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanExport_Json(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanExport_Json(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanExport_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanExport_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanExport_Json(builtin);
}
#ifdef __cplusplus
}
#endif
