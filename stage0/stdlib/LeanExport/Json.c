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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_t_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_k_1_, v_t_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg___boxed(lean_object* v_k_12_, lean_object* v_t_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_k_12_, v_t_13_);
lean_dec(v_t_13_);
lean_dec_ref(v_k_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(lean_object* v_msg_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_box(1);
v___x_18_ = lean_panic_fn_borrowed(v___x_17_, v_msg_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_22_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2));
v___x_23_ = lean_unsigned_to_nat(35u);
v___x_24_ = lean_unsigned_to_nat(182u);
v___x_25_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1));
v___x_26_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_27_ = l_mkPanicMessageWithDecl(v___x_26_, v___x_25_, v___x_24_, v___x_23_, v___x_22_);
return v___x_27_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_28_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__2));
v___x_29_ = lean_unsigned_to_nat(21u);
v___x_30_ = lean_unsigned_to_nat(183u);
v___x_31_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__1));
v___x_32_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_33_ = l_mkPanicMessageWithDecl(v___x_32_, v___x_31_, v___x_30_, v___x_29_, v___x_28_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_36_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6));
v___x_37_ = lean_unsigned_to_nat(35u);
v___x_38_ = lean_unsigned_to_nat(276u);
v___x_39_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5));
v___x_40_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_41_ = l_mkPanicMessageWithDecl(v___x_40_, v___x_39_, v___x_38_, v___x_37_, v___x_36_);
return v___x_41_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_42_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__6));
v___x_43_ = lean_unsigned_to_nat(21u);
v___x_44_ = lean_unsigned_to_nat(277u);
v___x_45_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__5));
v___x_46_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__0));
v___x_47_ = l_mkPanicMessageWithDecl(v___x_46_, v___x_45_, v___x_44_, v___x_43_, v___x_42_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(lean_object* v_k_48_, lean_object* v_v_49_, lean_object* v_t_50_){
_start:
{
if (lean_obj_tag(v_t_50_) == 0)
{
lean_object* v_size_51_; lean_object* v_k_52_; lean_object* v_v_53_; lean_object* v_l_54_; lean_object* v_r_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_411_; 
v_size_51_ = lean_ctor_get(v_t_50_, 0);
v_k_52_ = lean_ctor_get(v_t_50_, 1);
v_v_53_ = lean_ctor_get(v_t_50_, 2);
v_l_54_ = lean_ctor_get(v_t_50_, 3);
v_r_55_ = lean_ctor_get(v_t_50_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v_t_50_);
if (v_isSharedCheck_411_ == 0)
{
v___x_57_ = v_t_50_;
v_isShared_58_ = v_isSharedCheck_411_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_r_55_);
lean_inc(v_l_54_);
lean_inc(v_v_53_);
lean_inc(v_k_52_);
lean_inc(v_size_51_);
lean_dec(v_t_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_411_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; 
v___x_59_ = lean_string_compare(v_k_48_, v_k_52_);
switch(v___x_59_)
{
case 0:
{
lean_object* v___x_60_; 
lean_dec(v_size_51_);
v___x_60_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_k_48_, v_v_49_, v_l_54_);
if (lean_obj_tag(v_r_55_) == 0)
{
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_size_61_; lean_object* v_size_62_; lean_object* v_k_63_; lean_object* v_v_64_; lean_object* v_l_65_; lean_object* v_r_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_size_61_ = lean_ctor_get(v_r_55_, 0);
v_size_62_ = lean_ctor_get(v___x_60_, 0);
v_k_63_ = lean_ctor_get(v___x_60_, 1);
v_v_64_ = lean_ctor_get(v___x_60_, 2);
v_l_65_ = lean_ctor_get(v___x_60_, 3);
v_r_66_ = lean_ctor_get(v___x_60_, 4);
lean_inc(v_r_66_);
v___x_67_ = lean_unsigned_to_nat(3u);
v___x_68_ = lean_nat_mul(v___x_67_, v_size_61_);
v___x_69_ = lean_nat_dec_lt(v___x_68_, v_size_62_);
lean_dec(v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
lean_dec(v_r_66_);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v___x_70_, v_size_62_);
v___x_72_ = lean_nat_add(v___x_71_, v_size_61_);
lean_dec(v___x_71_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 3, v___x_60_);
lean_ctor_set(v___x_57_, 0, v___x_72_);
v___x_74_ = v___x_57_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_75_, 3, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_75_, 4, v_r_55_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_147_; 
lean_inc(v_l_65_);
lean_inc(v_v_64_);
lean_inc(v_k_63_);
lean_inc(v_size_62_);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; lean_object* v_unused_149_; lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; 
v_unused_148_ = lean_ctor_get(v___x_60_, 4);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v___x_60_, 3);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v___x_60_, 2);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v___x_60_, 1);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_152_);
v___x_77_ = v___x_60_;
v_isShared_78_ = v_isSharedCheck_147_;
goto v_resetjp_76_;
}
else
{
lean_dec(v___x_60_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_147_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
if (lean_obj_tag(v_l_65_) == 0)
{
if (lean_obj_tag(v_r_66_) == 0)
{
lean_object* v_size_79_; lean_object* v_size_80_; lean_object* v_k_81_; lean_object* v_v_82_; lean_object* v_l_83_; lean_object* v_r_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_size_79_ = lean_ctor_get(v_l_65_, 0);
v_size_80_ = lean_ctor_get(v_r_66_, 0);
v_k_81_ = lean_ctor_get(v_r_66_, 1);
v_v_82_ = lean_ctor_get(v_r_66_, 2);
v_l_83_ = lean_ctor_get(v_r_66_, 3);
v_r_84_ = lean_ctor_get(v_r_66_, 4);
v___x_85_ = lean_unsigned_to_nat(2u);
v___x_86_ = lean_nat_mul(v___x_85_, v_size_79_);
v___x_87_ = lean_nat_dec_lt(v_size_80_, v___x_86_);
lean_dec(v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_117_; 
lean_inc(v_r_84_);
lean_inc(v_l_83_);
lean_inc(v_v_82_);
lean_inc(v_k_81_);
v_isSharedCheck_117_ = !lean_is_exclusive(v_r_66_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; lean_object* v_unused_119_; lean_object* v_unused_120_; lean_object* v_unused_121_; lean_object* v_unused_122_; 
v_unused_118_ = lean_ctor_get(v_r_66_, 4);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_r_66_, 3);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_r_66_, 2);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_r_66_, 1);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_r_66_, 0);
lean_dec(v_unused_122_);
v___x_89_ = v_r_66_;
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_r_66_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___x_105_; lean_object* v___y_107_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v___x_91_, v_size_62_);
lean_dec(v_size_62_);
v___x_93_ = lean_nat_add(v___x_92_, v_size_61_);
lean_dec(v___x_92_);
v___x_105_ = lean_nat_add(v___x_91_, v_size_79_);
if (lean_obj_tag(v_l_83_) == 0)
{
lean_object* v_size_115_; 
v_size_115_ = lean_ctor_get(v_l_83_, 0);
lean_inc(v_size_115_);
v___y_107_ = v_size_115_;
goto v___jp_106_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___y_107_ = v___x_116_;
goto v___jp_106_;
}
v___jp_94_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_nat_add(v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec(v___y_96_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 4, v_r_55_);
lean_ctor_set(v___x_89_, 3, v_r_84_);
lean_ctor_set(v___x_89_, 2, v_v_53_);
lean_ctor_set(v___x_89_, 1, v_k_52_);
lean_ctor_set(v___x_89_, 0, v___x_98_);
v___x_100_ = v___x_89_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_104_, 3, v_r_84_);
lean_ctor_set(v_reuseFailAlloc_104_, 4, v_r_55_);
v___x_100_ = v_reuseFailAlloc_104_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_100_);
lean_ctor_set(v___x_77_, 3, v___y_95_);
lean_ctor_set(v___x_77_, 2, v_v_82_);
lean_ctor_set(v___x_77_, 1, v_k_81_);
lean_ctor_set(v___x_77_, 0, v___x_93_);
v___x_102_ = v___x_77_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_k_81_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_v_82_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v___y_95_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = lean_nat_add(v___x_105_, v___y_107_);
lean_dec(v___y_107_);
lean_dec(v___x_105_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_l_83_);
lean_ctor_set(v___x_57_, 3, v_l_65_);
lean_ctor_set(v___x_57_, 2, v_v_64_);
lean_ctor_set(v___x_57_, 1, v_k_63_);
lean_ctor_set(v___x_57_, 0, v___x_108_);
v___x_110_ = v___x_57_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_k_63_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_v_64_);
lean_ctor_set(v_reuseFailAlloc_114_, 3, v_l_65_);
lean_ctor_set(v_reuseFailAlloc_114_, 4, v_l_83_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; 
v___x_111_ = lean_nat_add(v___x_91_, v_size_61_);
if (lean_obj_tag(v_r_84_) == 0)
{
lean_object* v_size_112_; 
v_size_112_ = lean_ctor_get(v_r_84_, 0);
lean_inc(v_size_112_);
v___y_95_ = v___x_110_;
v___y_96_ = v___x_111_;
v___y_97_ = v_size_112_;
goto v___jp_94_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___y_95_ = v___x_110_;
v___y_96_ = v___x_111_;
v___y_97_ = v___x_113_;
goto v___jp_94_;
}
}
}
}
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
lean_del_object(v___x_57_);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v___x_123_, v_size_62_);
lean_dec(v_size_62_);
v___x_125_ = lean_nat_add(v___x_124_, v_size_61_);
lean_dec(v___x_124_);
v___x_126_ = lean_nat_add(v___x_123_, v_size_61_);
v___x_127_ = lean_nat_add(v___x_126_, v_size_80_);
lean_dec(v___x_126_);
lean_inc_ref(v_r_55_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_55_);
lean_ctor_set(v___x_77_, 3, v_r_66_);
lean_ctor_set(v___x_77_, 2, v_v_53_);
lean_ctor_set(v___x_77_, 1, v_k_52_);
lean_ctor_set(v___x_77_, 0, v___x_127_);
v___x_129_ = v___x_77_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_r_66_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_r_55_);
v___x_129_ = v_reuseFailAlloc_142_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_isSharedCheck_136_ = !lean_is_exclusive(v_r_55_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; lean_object* v_unused_138_; lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_137_ = lean_ctor_get(v_r_55_, 4);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_r_55_, 3);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_r_55_, 2);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_r_55_, 1);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_r_55_, 0);
lean_dec(v_unused_141_);
v___x_131_ = v_r_55_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_dec(v_r_55_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_129_);
lean_ctor_set(v___x_131_, 3, v_l_65_);
lean_ctor_set(v___x_131_, 2, v_v_64_);
lean_ctor_set(v___x_131_, 1, v_k_63_);
lean_ctor_set(v___x_131_, 0, v___x_125_);
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_k_63_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_v_64_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_l_65_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v___x_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec_ref_known(v_l_65_, 5);
lean_del_object(v___x_77_);
lean_dec(v_v_64_);
lean_dec(v_k_63_);
lean_dec(v_size_62_);
lean_dec_ref_known(v_r_55_, 5);
lean_del_object(v___x_57_);
lean_dec(v_v_53_);
lean_dec(v_k_52_);
v___x_143_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__3);
v___x_144_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_143_);
return v___x_144_;
}
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_del_object(v___x_77_);
lean_dec(v_r_66_);
lean_dec(v_v_64_);
lean_dec(v_k_63_);
lean_dec(v_size_62_);
lean_dec_ref_known(v_r_55_, 5);
lean_del_object(v___x_57_);
lean_dec(v_v_53_);
lean_dec(v_k_52_);
v___x_145_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__4);
v___x_146_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_145_);
return v___x_146_;
}
}
}
}
else
{
lean_object* v_size_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v_size_153_ = lean_ctor_get(v_r_55_, 0);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v___x_154_, v_size_153_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 3, v___x_60_);
lean_ctor_set(v___x_57_, 0, v___x_155_);
v___x_157_ = v___x_57_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v_r_55_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_l_159_; 
v_l_159_ = lean_ctor_get(v___x_60_, 3);
if (lean_obj_tag(v_l_159_) == 0)
{
lean_object* v_r_160_; 
lean_inc_ref(v_l_159_);
v_r_160_ = lean_ctor_get(v___x_60_, 4);
lean_inc(v_r_160_);
if (lean_obj_tag(v_r_160_) == 0)
{
lean_object* v_size_161_; lean_object* v_k_162_; lean_object* v_v_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_177_; 
v_size_161_ = lean_ctor_get(v___x_60_, 0);
v_k_162_ = lean_ctor_get(v___x_60_, 1);
v_v_163_ = lean_ctor_get(v___x_60_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; 
v_unused_178_ = lean_ctor_get(v___x_60_, 4);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v___x_60_, 3);
lean_dec(v_unused_179_);
v___x_165_ = v___x_60_;
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_v_163_);
lean_inc(v_k_162_);
lean_inc(v_size_161_);
lean_dec(v___x_60_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_size_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v_size_167_ = lean_ctor_get(v_r_160_, 0);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v___x_168_, v_size_161_);
lean_dec(v_size_161_);
v___x_170_ = lean_nat_add(v___x_168_, v_size_167_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 4, v_r_55_);
lean_ctor_set(v___x_165_, 3, v_r_160_);
lean_ctor_set(v___x_165_, 2, v_v_53_);
lean_ctor_set(v___x_165_, 1, v_k_52_);
lean_ctor_set(v___x_165_, 0, v___x_170_);
v___x_172_ = v___x_165_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_r_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_r_55_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_172_);
lean_ctor_set(v___x_57_, 3, v_l_159_);
lean_ctor_set(v___x_57_, 2, v_v_163_);
lean_ctor_set(v___x_57_, 1, v_k_162_);
lean_ctor_set(v___x_57_, 0, v___x_169_);
v___x_174_ = v___x_57_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_162_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_163_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_l_159_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_k_180_; lean_object* v_v_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_193_; 
v_k_180_ = lean_ctor_get(v___x_60_, 1);
v_v_181_ = lean_ctor_get(v___x_60_, 2);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; lean_object* v_unused_195_; lean_object* v_unused_196_; 
v_unused_194_ = lean_ctor_get(v___x_60_, 4);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v___x_60_, 3);
lean_dec(v_unused_195_);
v_unused_196_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_196_);
v___x_183_ = v___x_60_;
v_isShared_184_ = v_isSharedCheck_193_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_v_181_);
lean_inc(v_k_180_);
lean_dec(v___x_60_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_193_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_unsigned_to_nat(3u);
v___x_186_ = lean_unsigned_to_nat(1u);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 3, v_r_160_);
lean_ctor_set(v___x_183_, 2, v_v_53_);
lean_ctor_set(v___x_183_, 1, v_k_52_);
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_r_160_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_r_160_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_188_);
lean_ctor_set(v___x_57_, 3, v_l_159_);
lean_ctor_set(v___x_57_, 2, v_v_181_);
lean_ctor_set(v___x_57_, 1, v_k_180_);
lean_ctor_set(v___x_57_, 0, v___x_185_);
v___x_190_ = v___x_57_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_180_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_181_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_l_159_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_object* v_r_197_; 
v_r_197_ = lean_ctor_get(v___x_60_, 4);
lean_inc(v_r_197_);
if (lean_obj_tag(v_r_197_) == 0)
{
lean_object* v_k_198_; lean_object* v_v_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_223_; 
lean_inc(v_l_159_);
v_k_198_ = lean_ctor_get(v___x_60_, 1);
v_v_199_ = lean_ctor_get(v___x_60_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; 
v_unused_224_ = lean_ctor_get(v___x_60_, 4);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v___x_60_, 3);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_226_);
v___x_201_ = v___x_60_;
v_isShared_202_ = v_isSharedCheck_223_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_v_199_);
lean_inc(v_k_198_);
lean_dec(v___x_60_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_223_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_k_203_; lean_object* v_v_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_219_; 
v_k_203_ = lean_ctor_get(v_r_197_, 1);
v_v_204_ = lean_ctor_get(v_r_197_, 2);
v_isSharedCheck_219_ = !lean_is_exclusive(v_r_197_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; lean_object* v_unused_221_; lean_object* v_unused_222_; 
v_unused_220_ = lean_ctor_get(v_r_197_, 4);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_r_197_, 3);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_r_197_, 0);
lean_dec(v_unused_222_);
v___x_206_ = v_r_197_;
v_isShared_207_ = v_isSharedCheck_219_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_v_204_);
lean_inc(v_k_203_);
lean_dec(v_r_197_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_219_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = lean_unsigned_to_nat(3u);
v___x_209_ = lean_unsigned_to_nat(1u);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 4, v_l_159_);
lean_ctor_set(v___x_206_, 3, v_l_159_);
lean_ctor_set(v___x_206_, 2, v_v_199_);
lean_ctor_set(v___x_206_, 1, v_k_198_);
lean_ctor_set(v___x_206_, 0, v___x_209_);
v___x_211_ = v___x_206_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_198_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_199_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_l_159_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_l_159_);
v___x_211_ = v_reuseFailAlloc_218_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 4, v_l_159_);
lean_ctor_set(v___x_201_, 2, v_v_53_);
lean_ctor_set(v___x_201_, 1, v_k_52_);
lean_ctor_set(v___x_201_, 0, v___x_209_);
v___x_213_ = v___x_201_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_l_159_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_l_159_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_213_);
lean_ctor_set(v___x_57_, 3, v___x_211_);
lean_ctor_set(v___x_57_, 2, v_v_204_);
lean_ctor_set(v___x_57_, 1, v_k_203_);
lean_ctor_set(v___x_57_, 0, v___x_208_);
v___x_215_ = v___x_57_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_203_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_204_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(2u);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_r_197_);
lean_ctor_set(v___x_57_, 3, v___x_60_);
lean_ctor_set(v___x_57_, 0, v___x_227_);
v___x_229_ = v___x_57_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_r_197_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(1u);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_60_);
lean_ctor_set(v___x_57_, 3, v___x_60_);
lean_ctor_set(v___x_57_, 0, v___x_231_);
v___x_233_ = v___x_57_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v___x_60_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
case 1:
{
lean_object* v___x_236_; 
lean_dec(v_v_53_);
lean_dec(v_k_52_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 2, v_v_49_);
lean_ctor_set(v___x_57_, 1, v_k_48_);
v___x_236_ = v___x_57_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_size_51_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_48_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_49_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_r_55_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
default: 
{
lean_object* v___x_238_; 
lean_dec(v_size_51_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_k_48_, v_v_49_, v_r_55_);
if (lean_obj_tag(v_l_54_) == 0)
{
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_size_239_; lean_object* v_size_240_; lean_object* v_k_241_; lean_object* v_v_242_; lean_object* v_l_243_; lean_object* v_r_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_size_239_ = lean_ctor_get(v_l_54_, 0);
v_size_240_ = lean_ctor_get(v___x_238_, 0);
v_k_241_ = lean_ctor_get(v___x_238_, 1);
v_v_242_ = lean_ctor_get(v___x_238_, 2);
v_l_243_ = lean_ctor_get(v___x_238_, 3);
lean_inc(v_l_243_);
v_r_244_ = lean_ctor_get(v___x_238_, 4);
v___x_245_ = lean_unsigned_to_nat(3u);
v___x_246_ = lean_nat_mul(v___x_245_, v_size_239_);
v___x_247_ = lean_nat_dec_lt(v___x_246_, v_size_240_);
lean_dec(v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec(v_l_243_);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_add(v___x_248_, v_size_239_);
v___x_250_ = lean_nat_add(v___x_249_, v_size_240_);
lean_dec(v___x_249_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_238_);
lean_ctor_set(v___x_57_, 0, v___x_250_);
v___x_252_ = v___x_57_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v___x_238_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_323_; 
lean_inc(v_r_244_);
lean_inc(v_v_242_);
lean_inc(v_k_241_);
lean_inc(v_size_240_);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; 
v_unused_324_ = lean_ctor_get(v___x_238_, 4);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v___x_238_, 3);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v___x_238_, 2);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v___x_238_, 1);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v___x_238_, 0);
lean_dec(v_unused_328_);
v___x_255_ = v___x_238_;
v_isShared_256_ = v_isSharedCheck_323_;
goto v_resetjp_254_;
}
else
{
lean_dec(v___x_238_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_323_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
if (lean_obj_tag(v_l_243_) == 0)
{
if (lean_obj_tag(v_r_244_) == 0)
{
lean_object* v_size_257_; lean_object* v_k_258_; lean_object* v_v_259_; lean_object* v_l_260_; lean_object* v_r_261_; lean_object* v_size_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_size_257_ = lean_ctor_get(v_l_243_, 0);
v_k_258_ = lean_ctor_get(v_l_243_, 1);
v_v_259_ = lean_ctor_get(v_l_243_, 2);
v_l_260_ = lean_ctor_get(v_l_243_, 3);
v_r_261_ = lean_ctor_get(v_l_243_, 4);
v_size_262_ = lean_ctor_get(v_r_244_, 0);
v___x_263_ = lean_unsigned_to_nat(2u);
v___x_264_ = lean_nat_mul(v___x_263_, v_size_262_);
v___x_265_ = lean_nat_dec_lt(v_size_257_, v___x_264_);
lean_dec(v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_294_; 
lean_inc(v_r_261_);
lean_inc(v_l_260_);
lean_inc(v_v_259_);
lean_inc(v_k_258_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_l_243_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_295_ = lean_ctor_get(v_l_243_, 4);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_243_, 3);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_243_, 2);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_243_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_l_243_, 0);
lean_dec(v_unused_299_);
v___x_267_ = v_l_243_;
v_isShared_268_ = v_isSharedCheck_294_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_l_243_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_294_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_284_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v___x_269_, v_size_239_);
v___x_271_ = lean_nat_add(v___x_270_, v_size_240_);
lean_dec(v_size_240_);
if (lean_obj_tag(v_l_260_) == 0)
{
lean_object* v_size_292_; 
v_size_292_ = lean_ctor_get(v_l_260_, 0);
lean_inc(v_size_292_);
v___y_284_ = v_size_292_;
goto v___jp_283_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___y_284_ = v___x_293_;
goto v___jp_283_;
}
v___jp_272_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_nat_add(v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec(v___y_274_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 4, v_r_244_);
lean_ctor_set(v___x_267_, 3, v_r_261_);
lean_ctor_set(v___x_267_, 2, v_v_242_);
lean_ctor_set(v___x_267_, 1, v_k_241_);
lean_ctor_set(v___x_267_, 0, v___x_276_);
v___x_278_ = v___x_267_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_r_261_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_r_244_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 4, v___x_278_);
lean_ctor_set(v___x_255_, 3, v___y_273_);
lean_ctor_set(v___x_255_, 2, v_v_259_);
lean_ctor_set(v___x_255_, 1, v_k_258_);
lean_ctor_set(v___x_255_, 0, v___x_271_);
v___x_280_ = v___x_255_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_258_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_v_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v___y_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_nat_add(v___x_270_, v___y_284_);
lean_dec(v___y_284_);
lean_dec(v___x_270_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_l_260_);
lean_ctor_set(v___x_57_, 0, v___x_285_);
v___x_287_ = v___x_57_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_l_260_);
v___x_287_ = v_reuseFailAlloc_291_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_nat_add(v___x_269_, v_size_262_);
if (lean_obj_tag(v_r_261_) == 0)
{
lean_object* v_size_289_; 
v_size_289_ = lean_ctor_get(v_r_261_, 0);
lean_inc(v_size_289_);
v___y_273_ = v___x_287_;
v___y_274_ = v___x_288_;
v___y_275_ = v_size_289_;
goto v___jp_272_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___y_273_ = v___x_287_;
v___y_274_ = v___x_288_;
v___y_275_ = v___x_290_;
goto v___jp_272_;
}
}
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
lean_del_object(v___x_57_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v___x_300_, v_size_239_);
v___x_302_ = lean_nat_add(v___x_301_, v_size_240_);
lean_dec(v_size_240_);
v___x_303_ = lean_nat_add(v___x_301_, v_size_257_);
lean_dec(v___x_301_);
lean_inc_ref(v_l_54_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 4, v_l_243_);
lean_ctor_set(v___x_255_, 3, v_l_54_);
lean_ctor_set(v___x_255_, 2, v_v_53_);
lean_ctor_set(v___x_255_, 1, v_k_52_);
lean_ctor_set(v___x_255_, 0, v___x_303_);
v___x_305_ = v___x_255_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v_l_243_);
v___x_305_ = v_reuseFailAlloc_318_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_isSharedCheck_312_ = !lean_is_exclusive(v_l_54_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_313_ = lean_ctor_get(v_l_54_, 4);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_54_, 3);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_54_, 2);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_54_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_l_54_, 0);
lean_dec(v_unused_317_);
v___x_307_ = v_l_54_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_dec(v_l_54_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 4, v_r_244_);
lean_ctor_set(v___x_307_, 3, v___x_305_);
lean_ctor_set(v___x_307_, 2, v_v_242_);
lean_ctor_set(v___x_307_, 1, v_k_241_);
lean_ctor_set(v___x_307_, 0, v___x_302_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_r_244_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref_known(v_l_243_, 5);
lean_del_object(v___x_255_);
lean_dec(v_v_242_);
lean_dec(v_k_241_);
lean_dec(v_size_240_);
lean_dec_ref_known(v_l_54_, 5);
lean_del_object(v___x_57_);
lean_dec(v_v_53_);
lean_dec(v_k_52_);
v___x_319_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__7);
v___x_320_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_319_);
return v___x_320_;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_255_);
lean_dec(v_r_244_);
lean_dec(v_v_242_);
lean_dec(v_k_241_);
lean_dec(v_size_240_);
lean_dec_ref_known(v_l_54_, 5);
lean_del_object(v___x_57_);
lean_dec(v_v_53_);
lean_dec(v_k_52_);
v___x_321_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg___closed__8);
v___x_322_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v___x_321_);
return v___x_322_;
}
}
}
}
else
{
lean_object* v_size_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v_size_329_ = lean_ctor_get(v_l_54_, 0);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v___x_330_, v_size_329_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_238_);
lean_ctor_set(v___x_57_, 0, v___x_331_);
v___x_333_ = v___x_57_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v___x_238_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_l_335_; 
v_l_335_ = lean_ctor_get(v___x_238_, 3);
lean_inc(v_l_335_);
if (lean_obj_tag(v_l_335_) == 0)
{
lean_object* v_r_336_; 
v_r_336_ = lean_ctor_get(v___x_238_, 4);
lean_inc(v_r_336_);
if (lean_obj_tag(v_r_336_) == 0)
{
lean_object* v_size_337_; lean_object* v_k_338_; lean_object* v_v_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_353_; 
v_size_337_ = lean_ctor_get(v___x_238_, 0);
v_k_338_ = lean_ctor_get(v___x_238_, 1);
v_v_339_ = lean_ctor_get(v___x_238_, 2);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; 
v_unused_354_ = lean_ctor_get(v___x_238_, 4);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v___x_238_, 3);
lean_dec(v_unused_355_);
v___x_341_ = v___x_238_;
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_v_339_);
lean_inc(v_k_338_);
lean_inc(v_size_337_);
lean_dec(v___x_238_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_size_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v_size_343_ = lean_ctor_get(v_l_335_, 0);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v___x_344_, v_size_337_);
lean_dec(v_size_337_);
v___x_346_ = lean_nat_add(v___x_344_, v_size_343_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_l_335_);
lean_ctor_set(v___x_341_, 3, v_l_54_);
lean_ctor_set(v___x_341_, 2, v_v_53_);
lean_ctor_set(v___x_341_, 1, v_k_52_);
lean_ctor_set(v___x_341_, 0, v___x_346_);
v___x_348_ = v___x_341_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_l_335_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_r_336_);
lean_ctor_set(v___x_57_, 3, v___x_348_);
lean_ctor_set(v___x_57_, 2, v_v_339_);
lean_ctor_set(v___x_57_, 1, v_k_338_);
lean_ctor_set(v___x_57_, 0, v___x_345_);
v___x_350_ = v___x_57_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_338_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_339_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_r_336_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_k_356_; lean_object* v_v_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_381_; 
v_k_356_ = lean_ctor_get(v___x_238_, 1);
v_v_357_ = lean_ctor_get(v___x_238_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; lean_object* v_unused_383_; lean_object* v_unused_384_; 
v_unused_382_ = lean_ctor_get(v___x_238_, 4);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v___x_238_, 3);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v___x_238_, 0);
lean_dec(v_unused_384_);
v___x_359_ = v___x_238_;
v_isShared_360_ = v_isSharedCheck_381_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_v_357_);
lean_inc(v_k_356_);
lean_dec(v___x_238_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_381_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_k_361_; lean_object* v_v_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_377_; 
v_k_361_ = lean_ctor_get(v_l_335_, 1);
v_v_362_ = lean_ctor_get(v_l_335_, 2);
v_isSharedCheck_377_ = !lean_is_exclusive(v_l_335_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_378_ = lean_ctor_get(v_l_335_, 4);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_l_335_, 3);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_l_335_, 0);
lean_dec(v_unused_380_);
v___x_364_ = v_l_335_;
v_isShared_365_ = v_isSharedCheck_377_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_v_362_);
lean_inc(v_k_361_);
lean_dec(v_l_335_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_377_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_unsigned_to_nat(3u);
v___x_367_ = lean_unsigned_to_nat(1u);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_r_336_);
lean_ctor_set(v___x_364_, 3, v_r_336_);
lean_ctor_set(v___x_364_, 2, v_v_53_);
lean_ctor_set(v___x_364_, 1, v_k_52_);
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_r_336_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_r_336_);
v___x_369_ = v_reuseFailAlloc_376_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 3, v_r_336_);
lean_ctor_set(v___x_359_, 0, v___x_367_);
v___x_371_ = v___x_359_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_356_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_357_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_r_336_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_r_336_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_371_);
lean_ctor_set(v___x_57_, 3, v___x_369_);
lean_ctor_set(v___x_57_, 2, v_v_362_);
lean_ctor_set(v___x_57_, 1, v_k_361_);
lean_ctor_set(v___x_57_, 0, v___x_366_);
v___x_373_ = v___x_57_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_361_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_362_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_385_; 
v_r_385_ = lean_ctor_get(v___x_238_, 4);
lean_inc(v_r_385_);
if (lean_obj_tag(v_r_385_) == 0)
{
lean_object* v_k_386_; lean_object* v_v_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v_k_386_ = lean_ctor_get(v___x_238_, 1);
v_v_387_ = lean_ctor_get(v___x_238_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_400_ = lean_ctor_get(v___x_238_, 4);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v___x_238_, 3);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v___x_238_, 0);
lean_dec(v_unused_402_);
v___x_389_ = v___x_238_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_v_387_);
lean_inc(v_k_386_);
lean_dec(v___x_238_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_unsigned_to_nat(1u);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 4, v_l_335_);
lean_ctor_set(v___x_389_, 2, v_v_53_);
lean_ctor_set(v___x_389_, 1, v_k_52_);
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_335_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_l_335_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_r_385_);
lean_ctor_set(v___x_57_, 3, v___x_394_);
lean_ctor_set(v___x_57_, 2, v_v_387_);
lean_ctor_set(v___x_57_, 1, v_k_386_);
lean_ctor_set(v___x_57_, 0, v___x_391_);
v___x_396_ = v___x_57_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_386_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_387_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_r_385_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(2u);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_238_);
lean_ctor_set(v___x_57_, 3, v_r_385_);
lean_ctor_set(v___x_57_, 0, v___x_403_);
v___x_405_ = v___x_57_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_r_385_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v___x_238_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(1u);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_238_);
lean_ctor_set(v___x_57_, 3, v___x_238_);
lean_ctor_set(v___x_57_, 0, v___x_407_);
v___x_409_ = v___x_57_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_238_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_k_48_);
lean_ctor_set(v___x_413_, 2, v_v_49_);
lean_ctor_set(v___x_413_, 3, v_t_50_);
lean_ctor_set(v___x_413_, 4, v_t_50_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_objectCore(lean_object* v_kvs_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_438_; uint8_t v_decide_439_; 
v_fst_436_ = lean_ctor_get(v_a_435_, 0);
v_snd_437_ = lean_ctor_get(v_a_435_, 1);
v___x_438_ = lean_string_utf8_byte_size(v_fst_436_);
v_decide_439_ = lean_nat_dec_eq(v_snd_437_, v___x_438_);
if (v_decide_439_ == 0)
{
uint32_t v___x_440_; uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_string_utf8_get_fast(v_fst_436_, v_snd_437_);
v___x_441_ = 34;
v___x_442_ = lean_uint32_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_kvs_434_);
v___x_443_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__1));
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v_a_435_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_546_; 
lean_inc(v_snd_437_);
lean_inc(v_fst_436_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_a_435_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_547_ = lean_ctor_get(v_a_435_, 1);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_a_435_, 0);
lean_dec(v_unused_548_);
v___x_446_ = v_a_435_;
v_isShared_447_ = v_isSharedCheck_546_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_a_435_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_546_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_string_utf8_next_fast(v_fst_436_, v_snd_437_);
lean_dec(v_snd_437_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_fst_436_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_545_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__2));
v___x_452_ = l_Lean_Json_Parser_strCore(v___x_451_, v___x_450_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_pos_453_; lean_object* v_res_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_535_; 
v_pos_453_ = lean_ctor_get(v___x_452_, 0);
v_res_454_ = lean_ctor_get(v___x_452_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_535_ == 0)
{
v___x_456_ = v___x_452_;
v_isShared_457_ = v_isSharedCheck_535_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_res_454_);
lean_inc(v_pos_453_);
lean_dec(v___x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_535_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; uint8_t v___y_463_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_534_; 
v_fst_489_ = lean_ctor_get(v_pos_453_, 0);
v_snd_490_ = lean_ctor_get(v_pos_453_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_pos_453_);
if (v_isSharedCheck_534_ == 0)
{
v___x_492_ = v_pos_453_;
v_isShared_493_ = v_isSharedCheck_534_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_inc(v_fst_489_);
lean_dec(v_pos_453_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_534_;
goto v_resetjp_491_;
}
v___jp_458_:
{
if (v___y_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec(v___y_462_);
lean_dec(v___y_461_);
lean_dec(v___y_459_);
lean_dec(v_res_454_);
lean_dec(v_kvs_434_);
v___x_464_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 1);
lean_ctor_set(v___x_456_, 1, v___x_464_);
lean_ctor_set(v___x_456_, 0, v___y_460_);
v___x_466_ = v___x_456_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___y_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
uint32_t v___x_468_; lean_object* v___x_469_; uint32_t v___x_470_; uint8_t v___x_471_; 
lean_dec_ref(v___y_460_);
v___x_468_ = lean_string_utf8_get_fast(v___y_461_, v___y_462_);
v___x_469_ = lean_string_utf8_next_fast(v___y_461_, v___y_462_);
lean_dec(v___y_462_);
v___x_470_ = 125;
v___x_471_ = lean_uint32_dec_eq(v___x_468_, v___x_470_);
if (v___x_471_ == 0)
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = 44;
v___x_473_ = lean_uint32_dec_eq(v___x_468_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v___y_459_);
lean_dec(v_res_454_);
lean_dec(v_kvs_434_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___y_461_);
lean_ctor_set(v___x_474_, 1, v___x_469_);
v___x_475_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__4));
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 1);
lean_ctor_set(v___x_456_, 1, v___x_475_);
lean_ctor_set(v___x_456_, 0, v___x_474_);
v___x_477_ = v___x_456_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_del_object(v___x_456_);
v___x_479_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v___y_461_, v___x_469_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___y_461_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_res_454_, v___y_459_, v_kvs_434_);
v_kvs_434_ = v___x_481_;
v_a_435_ = v___x_480_;
goto _start;
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_483_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v___y_461_, v___x_469_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_461_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_res_454_, v___y_459_, v_kvs_434_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_485_);
lean_ctor_set(v___x_456_, 0, v___x_484_);
v___x_487_ = v___x_456_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_489_, v_snd_490_);
lean_inc(v___x_494_);
lean_inc(v_fst_489_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fst_489_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_533_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
uint8_t v___x_497_; uint8_t v___y_499_; 
v___x_497_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_res_454_, v_kvs_434_);
if (v___x_497_ == 0)
{
lean_object* v___x_526_; uint8_t v_decide_527_; 
v___x_526_ = lean_string_utf8_byte_size(v_fst_489_);
v_decide_527_ = lean_nat_dec_eq(v___x_494_, v___x_526_);
if (v_decide_527_ == 0)
{
v___y_499_ = v___x_442_;
goto v___jp_498_;
}
else
{
v___y_499_ = v___x_497_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_494_);
lean_dec(v_fst_489_);
lean_del_object(v___x_456_);
lean_dec(v_kvs_434_);
v___x_528_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__7));
v___x_529_ = l_String_quote(v_res_454_);
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
lean_dec_ref(v___x_529_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_496_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v___x_494_);
lean_dec(v_fst_489_);
lean_del_object(v___x_456_);
lean_dec(v_res_454_);
lean_dec(v_kvs_434_);
v___x_500_ = lean_box(0);
v___x_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_496_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
else
{
uint32_t v___x_502_; uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_string_utf8_get_fast(v_fst_489_, v___x_494_);
v___x_503_ = 58;
v___x_504_ = lean_uint32_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v___x_494_);
lean_dec(v_fst_489_);
lean_del_object(v___x_456_);
lean_dec(v_res_454_);
lean_dec(v_kvs_434_);
v___x_505_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__6));
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_496_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec_ref(v___x_496_);
v___x_507_ = lean_string_utf8_next_fast(v_fst_489_, v___x_494_);
lean_dec(v___x_494_);
v___x_508_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_489_, v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_fst_489_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_LeanExport_Json_anyCore(v___x_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_pos_511_; lean_object* v_res_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_515_; uint8_t v_decide_516_; 
v_pos_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_pos_511_);
v_res_512_ = lean_ctor_get(v___x_510_, 1);
lean_inc(v_res_512_);
lean_dec_ref_known(v___x_510_, 2);
v_fst_513_ = lean_ctor_get(v_pos_511_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_pos_511_, 1);
lean_inc(v_snd_514_);
v___x_515_ = lean_string_utf8_byte_size(v_fst_513_);
v_decide_516_ = lean_nat_dec_eq(v_snd_514_, v___x_515_);
if (v_decide_516_ == 0)
{
v___y_459_ = v_res_512_;
v___y_460_ = v_pos_511_;
v___y_461_ = v_fst_513_;
v___y_462_ = v_snd_514_;
v___y_463_ = v___x_504_;
goto v___jp_458_;
}
else
{
v___y_459_ = v_res_512_;
v___y_460_ = v_pos_511_;
v___y_461_ = v_fst_513_;
v___y_462_ = v_snd_514_;
v___y_463_ = v___x_497_;
goto v___jp_458_;
}
}
else
{
lean_object* v_pos_517_; lean_object* v_err_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_456_);
lean_dec(v_res_454_);
lean_dec(v_kvs_434_);
v_pos_517_ = lean_ctor_get(v___x_510_, 0);
v_err_518_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_510_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_err_518_);
lean_inc(v_pos_517_);
lean_dec(v___x_510_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_pos_517_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_err_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
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
lean_object* v_pos_536_; lean_object* v_err_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_kvs_434_);
v_pos_536_ = lean_ctor_get(v___x_452_, 0);
v_err_537_ = lean_ctor_get(v___x_452_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_452_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_err_537_);
lean_inc(v_pos_536_);
lean_dec(v___x_452_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_pos_536_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_err_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_kvs_434_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_435_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_anyCore(lean_object* v_a_557_){
_start:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_594_; uint8_t v_decide_595_; 
v_fst_592_ = lean_ctor_get(v_a_557_, 0);
v_snd_593_ = lean_ctor_get(v_a_557_, 1);
v___x_594_ = lean_string_utf8_byte_size(v_fst_592_);
v_decide_595_ = lean_nat_dec_eq(v_snd_593_, v___x_594_);
if (v_decide_595_ == 0)
{
uint32_t v___x_596_; uint32_t v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_string_utf8_get_fast(v_fst_592_, v_snd_593_);
v___x_597_ = 91;
v___x_598_ = lean_uint32_dec_eq(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
uint32_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 123;
v___x_600_ = lean_uint32_dec_eq(v___x_596_, v___x_599_);
if (v___x_600_ == 0)
{
uint32_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 34;
v___x_602_ = lean_uint32_dec_eq(v___x_596_, v___x_601_);
if (v___x_602_ == 0)
{
uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 102;
v___x_604_ = lean_uint32_dec_eq(v___x_596_, v___x_603_);
if (v___x_604_ == 0)
{
uint32_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 116;
v___x_606_ = lean_uint32_dec_eq(v___x_596_, v___x_605_);
if (v___x_606_ == 0)
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 110;
v___x_608_ = lean_uint32_dec_eq(v___x_596_, v___x_607_);
if (v___x_608_ == 0)
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 45;
v___x_610_ = lean_uint32_dec_eq(v___x_596_, v___x_609_);
if (v___x_610_ == 0)
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 48;
v___x_612_ = lean_uint32_dec_le(v___x_611_, v___x_596_);
if (v___x_612_ == 0)
{
goto v___jp_589_;
}
else
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 57;
v___x_614_ = lean_uint32_dec_le(v___x_596_, v___x_613_);
if (v___x_614_ == 0)
{
goto v___jp_589_;
}
else
{
goto v___jp_558_;
}
}
}
else
{
goto v___jp_558_;
}
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__2));
v___x_616_ = l_Std_Internal_Parsec_String_pstring(v___x_615_, v_a_557_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_pos_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_635_; 
v_pos_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v___x_616_, 1);
lean_dec(v_unused_636_);
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_pos_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_635_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_634_; 
v_fst_621_ = lean_ctor_get(v_pos_617_, 0);
v_snd_622_ = lean_ctor_get(v_pos_617_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_pos_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_624_ = v_pos_617_;
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_snd_622_);
lean_inc(v_fst_621_);
lean_dec(v_pos_617_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_621_, v_snd_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_fst_621_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_633_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_box(0);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_629_);
lean_ctor_set(v___x_619_, 0, v___x_628_);
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
else
{
lean_object* v_pos_637_; lean_object* v_err_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_pos_637_ = lean_ctor_get(v___x_616_, 0);
v_err_638_ = lean_ctor_get(v___x_616_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_616_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_err_638_);
lean_inc(v_pos_637_);
lean_dec(v___x_616_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_pos_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_err_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__3));
v___x_647_ = l_Std_Internal_Parsec_String_pstring(v___x_646_, v_a_557_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_pos_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_666_; 
v_pos_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_647_, 1);
lean_dec(v_unused_667_);
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_pos_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_665_; 
v_fst_652_ = lean_ctor_get(v_pos_648_, 0);
v_snd_653_ = lean_ctor_get(v_pos_648_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_pos_648_);
if (v_isSharedCheck_665_ == 0)
{
v___x_655_ = v_pos_648_;
v_isShared_656_ = v_isSharedCheck_665_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec(v_pos_648_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_665_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_652_, v_snd_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_664_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_660_, 0, v___x_606_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_660_);
lean_ctor_set(v___x_650_, 0, v___x_659_);
v___x_662_ = v___x_650_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
else
{
lean_object* v_pos_668_; lean_object* v_err_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_pos_668_ = lean_ctor_get(v___x_647_, 0);
v_err_669_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_647_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_err_669_);
lean_inc(v_pos_668_);
lean_dec(v___x_647_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_pos_668_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_err_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__4));
v___x_678_ = l_Std_Internal_Parsec_String_pstring(v___x_677_, v_a_557_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_pos_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_697_; 
v_pos_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_678_, 1);
lean_dec(v_unused_698_);
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_pos_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_fst_683_ = lean_ctor_get(v_pos_679_, 0);
v_snd_684_ = lean_ctor_get(v_pos_679_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_pos_679_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v_pos_679_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v_pos_679_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_683_, v_snd_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_fst_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_695_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_691_, 0, v___x_602_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_691_);
lean_ctor_set(v___x_681_, 0, v___x_690_);
v___x_693_ = v___x_681_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
else
{
lean_object* v_pos_699_; lean_object* v_err_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_pos_699_ = lean_ctor_get(v___x_678_, 0);
v_err_700_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_678_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_err_700_);
lean_inc(v_pos_699_);
lean_dec(v___x_678_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_pos_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_err_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_746_; 
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_747_ = lean_ctor_get(v_a_557_, 1);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_a_557_, 0);
lean_dec(v_unused_748_);
v___x_709_ = v_a_557_;
v_isShared_710_ = v_isSharedCheck_746_;
goto v_resetjp_708_;
}
else
{
lean_dec(v_a_557_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_746_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_string_utf8_next_fast(v_fst_592_, v_snd_593_);
lean_dec(v_snd_593_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_745_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_LeanExport_Json_objectCore___closed__2));
v___x_715_ = l_Lean_Json_Parser_strCore(v___x_714_, v___x_713_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_pos_716_; lean_object* v_res_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_735_; 
v_pos_716_ = lean_ctor_get(v___x_715_, 0);
v_res_717_ = lean_ctor_get(v___x_715_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_735_ == 0)
{
v___x_719_ = v___x_715_;
v_isShared_720_ = v_isSharedCheck_735_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_res_717_);
lean_inc(v_pos_716_);
lean_dec(v___x_715_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_735_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_734_; 
v_fst_721_ = lean_ctor_get(v_pos_716_, 0);
v_snd_722_ = lean_ctor_get(v_pos_716_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_pos_716_);
if (v_isSharedCheck_734_ == 0)
{
v___x_724_ = v_pos_716_;
v_isShared_725_ = v_isSharedCheck_734_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_722_);
lean_inc(v_fst_721_);
lean_dec(v_pos_716_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_734_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_721_, v_snd_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_fst_721_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_733_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_729_, 0, v_res_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v___x_729_);
lean_ctor_set(v___x_719_, 0, v___x_728_);
v___x_731_ = v___x_719_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_object* v_pos_736_; lean_object* v_err_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_pos_736_ = lean_ctor_get(v___x_715_, 0);
v_err_737_ = lean_ctor_get(v___x_715_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_715_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_err_737_);
lean_inc(v_pos_736_);
lean_dec(v___x_715_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_pos_736_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_err_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_792_ = lean_ctor_get(v_a_557_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_a_557_, 0);
lean_dec(v_unused_793_);
v___x_750_ = v_a_557_;
v_isShared_751_ = v_isSharedCheck_791_;
goto v_resetjp_749_;
}
else
{
lean_dec(v_a_557_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_791_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_752_ = lean_string_utf8_next_fast(v_fst_592_, v_snd_593_);
lean_dec(v_snd_593_);
v___x_753_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_592_, v___x_752_);
lean_inc(v___x_753_);
lean_inc(v_fst_592_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_753_);
v___x_755_ = v___x_750_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_790_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
uint8_t v___y_757_; uint8_t v_decide_789_; 
v_decide_789_ = lean_nat_dec_eq(v___x_753_, v___x_594_);
if (v_decide_789_ == 0)
{
v___y_757_ = v___x_600_;
goto v___jp_756_;
}
else
{
v___y_757_ = v___x_598_;
goto v___jp_756_;
}
v___jp_756_:
{
if (v___y_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v___x_753_);
lean_dec(v_fst_592_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_755_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
return v___x_759_;
}
else
{
uint32_t v___x_760_; uint32_t v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_string_utf8_get_fast(v_fst_592_, v___x_753_);
v___x_761_ = 125;
v___x_762_ = lean_uint32_dec_eq(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v___x_753_);
lean_dec(v_fst_592_);
v___x_763_ = lean_box(1);
v___x_764_ = l_LeanExport_Json_objectCore(v___x_763_, v___x_755_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_pos_765_; lean_object* v_res_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_pos_765_ = lean_ctor_get(v___x_764_, 0);
v_res_766_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_774_ == 0)
{
v___x_768_ = v___x_764_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_res_766_);
lean_inc(v_pos_765_);
lean_dec(v___x_764_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_770_, 0, v_res_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_pos_765_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
else
{
lean_object* v_pos_775_; lean_object* v_err_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_pos_775_ = lean_ctor_get(v___x_764_, 0);
v_err_776_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_764_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_err_776_);
lean_inc(v_pos_775_);
lean_dec(v___x_764_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_pos_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_err_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v___x_755_);
v___x_784_ = lean_string_utf8_next_fast(v_fst_592_, v___x_753_);
lean_dec(v___x_753_);
v___x_785_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_592_, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_fst_592_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__5));
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
return v___x_788_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_837_ = lean_ctor_get(v_a_557_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_a_557_, 0);
lean_dec(v_unused_838_);
v___x_795_ = v_a_557_;
v_isShared_796_ = v_isSharedCheck_836_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_a_557_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_836_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = lean_string_utf8_next_fast(v_fst_592_, v_snd_593_);
lean_dec(v_snd_593_);
v___x_798_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_592_, v___x_797_);
lean_inc(v___x_798_);
lean_inc(v_fst_592_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_835_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
uint8_t v_decide_804_; 
v_decide_804_ = lean_nat_dec_eq(v___x_798_, v___x_594_);
if (v_decide_804_ == 0)
{
if (v___x_598_ == 0)
{
lean_dec(v___x_798_);
lean_dec(v_fst_592_);
goto v___jp_801_;
}
else
{
uint32_t v___x_805_; uint32_t v___x_806_; uint8_t v___x_807_; 
v___x_805_ = lean_string_utf8_get_fast(v_fst_592_, v___x_798_);
v___x_806_ = 93;
v___x_807_ = lean_uint32_dec_eq(v___x_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v___x_798_);
lean_dec(v_fst_592_);
v___x_808_ = lean_unsigned_to_nat(4u);
v___x_809_ = lean_mk_empty_array_with_capacity(v___x_808_);
v___x_810_ = l_LeanExport_Json_arrayCore(v___x_809_, v___x_800_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_pos_811_; lean_object* v_res_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_820_; 
v_pos_811_ = lean_ctor_get(v___x_810_, 0);
v_res_812_ = lean_ctor_get(v___x_810_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_820_ == 0)
{
v___x_814_ = v___x_810_;
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_res_812_);
lean_inc(v_pos_811_);
lean_dec(v___x_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_816_, 0, v_res_812_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_pos_811_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_pos_821_; lean_object* v_err_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_pos_821_ = lean_ctor_get(v___x_810_, 0);
v_err_822_ = lean_ctor_get(v___x_810_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_810_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_err_822_);
lean_inc(v_pos_821_);
lean_dec(v___x_810_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_pos_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_err_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v___x_800_);
v___x_830_ = lean_string_utf8_next_fast(v_fst_592_, v___x_798_);
lean_dec(v___x_798_);
v___x_831_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_592_, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_fst_592_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__7));
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
}
else
{
lean_dec(v___x_798_);
lean_dec(v_fst_592_);
goto v___jp_801_;
}
v___jp_801_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
return v___x_803_;
}
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_box(0);
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v_a_557_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
return v___x_840_;
}
v___jp_558_:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Json_Parser_num(v_a_557_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_pos_560_; lean_object* v_res_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_579_; 
v_pos_560_ = lean_ctor_get(v___x_559_, 0);
v_res_561_ = lean_ctor_get(v___x_559_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_579_ == 0)
{
v___x_563_ = v___x_559_;
v_isShared_564_ = v_isSharedCheck_579_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_res_561_);
lean_inc(v_pos_560_);
lean_dec(v___x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_579_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_578_; 
v_fst_565_ = lean_ctor_get(v_pos_560_, 0);
v_snd_566_ = lean_ctor_get(v_pos_560_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_pos_560_);
if (v_isSharedCheck_578_ == 0)
{
v___x_568_ = v_pos_560_;
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v_pos_560_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_578_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_565_, v_snd_566_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v___x_570_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_fst_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_577_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_573_, 0, v_res_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_573_);
lean_ctor_set(v___x_563_, 0, v___x_572_);
v___x_575_ = v___x_563_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
else
{
lean_object* v_pos_580_; lean_object* v_err_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_pos_580_ = lean_ctor_get(v___x_559_, 0);
v_err_581_ = lean_ctor_get(v___x_559_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_559_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_err_581_);
lean_inc(v_pos_580_);
lean_dec(v___x_559_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_pos_580_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_err_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
v___jp_589_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_LeanExport_Json_anyCore___closed__1));
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_557_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_arrayCore(lean_object* v_acc_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_LeanExport_Json_anyCore(v_a_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_pos_844_; lean_object* v_res_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_889_; 
v_pos_844_ = lean_ctor_get(v___x_843_, 0);
v_res_845_ = lean_ctor_get(v___x_843_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_889_ == 0)
{
v___x_847_ = v___x_843_;
v_isShared_848_ = v_isSharedCheck_889_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_res_845_);
lean_inc(v_pos_844_);
lean_dec(v___x_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_889_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_851_; uint8_t v_decide_852_; 
v_fst_849_ = lean_ctor_get(v_pos_844_, 0);
v_snd_850_ = lean_ctor_get(v_pos_844_, 1);
v___x_851_ = lean_string_utf8_byte_size(v_fst_849_);
v_decide_852_ = lean_nat_dec_eq(v_snd_850_, v___x_851_);
if (v_decide_852_ == 0)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_882_; 
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
v_isSharedCheck_882_ = !lean_is_exclusive(v_pos_844_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_883_ = lean_ctor_get(v_pos_844_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_pos_844_, 0);
lean_dec(v_unused_884_);
v___x_854_ = v_pos_844_;
v_isShared_855_ = v_isSharedCheck_882_;
goto v_resetjp_853_;
}
else
{
lean_dec(v_pos_844_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_882_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; uint32_t v___x_857_; lean_object* v___x_858_; uint32_t v___x_859_; uint8_t v___x_860_; 
v___x_856_ = lean_array_push(v_acc_841_, v_res_845_);
v___x_857_ = lean_string_utf8_get_fast(v_fst_849_, v_snd_850_);
v___x_858_ = lean_string_utf8_next_fast(v_fst_849_, v_snd_850_);
lean_dec(v_snd_850_);
v___x_859_ = 93;
v___x_860_ = lean_uint32_dec_eq(v___x_857_, v___x_859_);
if (v___x_860_ == 0)
{
uint32_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = 44;
v___x_862_ = lean_uint32_dec_eq(v___x_857_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_864_; 
lean_dec_ref(v___x_856_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_858_);
v___x_864_ = v___x_854_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_858_);
v___x_864_ = v_reuseFailAlloc_869_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = ((lean_object*)(l_LeanExport_Json_arrayCore___closed__1));
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 1, v___x_865_);
lean_ctor_set(v___x_847_, 0, v___x_864_);
v___x_867_ = v___x_847_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_del_object(v___x_847_);
v___x_870_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_849_, v___x_858_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_870_);
v___x_872_ = v___x_854_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_874_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
v_acc_841_ = v___x_856_;
v_a_842_ = v___x_872_;
goto _start;
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_849_, v___x_858_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_875_);
v___x_877_ = v___x_854_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_856_);
lean_ctor_set(v___x_847_, 0, v___x_877_);
v___x_879_ = v___x_847_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_856_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec(v_res_845_);
lean_dec_ref(v_acc_841_);
v___x_885_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 1, v___x_885_);
v___x_887_ = v___x_847_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_pos_844_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_pos_890_; lean_object* v_err_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_acc_841_);
v_pos_890_ = lean_ctor_get(v___x_843_, 0);
v_err_891_ = lean_ctor_get(v___x_843_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_843_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_err_891_);
lean_inc(v_pos_890_);
lean_dec(v___x_843_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_pos_890_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_err_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2(lean_object* v_00_u03b2_899_, lean_object* v_k_900_, lean_object* v_t_901_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___redArg(v_k_900_, v_t_901_);
return v___x_902_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_900_ = stack[1].m_obj;
lean_object* v_t_901_ = stack[2].m_obj;
uint8_t v_res_903_;
v_res_903_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2(lean_box(0), v_k_900_, v_t_901_);
stack->m_num = v_res_903_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2___boxed(lean_object* v_00_u03b2_904_, lean_object* v_k_905_, lean_object* v_t_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l_Std_DTreeMap_Internal_Impl_contains___at___00LeanExport_Json_objectCore_spec__2(v_00_u03b2_904_, v_k_905_, v_t_906_);
lean_dec(v_t_906_);
lean_dec_ref(v_k_905_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3(lean_object* v_00_u03b2_909_, lean_object* v_msg_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3_spec__3___redArg(v_msg_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3(lean_object* v_00_u03b2_912_, lean_object* v_k_913_, lean_object* v_v_914_, lean_object* v_t_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00LeanExport_Json_objectCore_spec__3___redArg(v_k_913_, v_v_914_, v_t_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_parse___lam__0(lean_object* v___y_920_){
_start:
{
lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_946_; 
v_fst_921_ = lean_ctor_get(v___y_920_, 0);
v_snd_922_ = lean_ctor_get(v___y_920_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v___y_920_);
if (v_isSharedCheck_946_ == 0)
{
v___x_924_ = v___y_920_;
v_isShared_925_ = v_isSharedCheck_946_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snd_922_);
lean_inc(v_fst_921_);
lean_dec(v___y_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_946_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_921_, v_snd_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_fst_921_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_926_);
v___x_928_ = v_reuseFailAlloc_945_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = l_LeanExport_Json_anyCore(v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_pos_930_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v___x_933_; uint8_t v_decide_934_; 
v_pos_930_ = lean_ctor_get(v___x_929_, 0);
v_fst_931_ = lean_ctor_get(v_pos_930_, 0);
v_snd_932_ = lean_ctor_get(v_pos_930_, 1);
v___x_933_ = lean_string_utf8_byte_size(v_fst_931_);
v_decide_934_ = lean_nat_dec_eq(v_snd_932_, v___x_933_);
if (v_decide_934_ == 0)
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
lean_inc(v_pos_930_);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_943_ = lean_ctor_get(v___x_929_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_944_);
v___x_936_ = v___x_929_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_dec(v___x_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = ((lean_object*)(l_LeanExport_Json_parse___lam__0___closed__1));
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 1);
lean_ctor_set(v___x_936_, 1, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_pos_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
return v___x_929_;
}
}
else
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_Json_parse(lean_object* v_s_948_){
_start:
{
lean_object* v___f_949_; lean_object* v___x_950_; 
v___f_949_ = ((lean_object*)(l_LeanExport_Json_parse___closed__0));
v___x_950_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_949_, v_s_948_);
return v___x_950_;
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
