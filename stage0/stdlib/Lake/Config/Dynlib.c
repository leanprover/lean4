// Lean compiler output
// Module: Lake.Config.Dynlib
// Imports: public import Lake.Config.OutFormat
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
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_string_object l_Lake_instInhabitedDynlib_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedDynlib_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__0_value;
static const lean_array_object l_Lake_instInhabitedDynlib_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedDynlib_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__1_value;
static const lean_ctor_object l_Lake_instInhabitedDynlib_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedDynlib_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedDynlib_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedDynlib_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedDynlib_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDynlib_default = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDynlib = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__2_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDynlib_repr_spec__1(lean_object*);
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__5_value;
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprDynlib_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDynlib_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__9_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value;
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__11_value;
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "plugin"};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lake_instReprDynlib_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDynlib_repr___redArg___closed__14;
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "deps"};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__15 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__15_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__16 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__16_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__0_value;
static lean_once_cell_t l_Lake_instReprDynlib_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDynlib_repr___redArg___closed__18;
static lean_once_cell_t l_Lake_instReprDynlib_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDynlib_repr___redArg___closed__19;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__20 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__20_value;
static const lean_string_object l_Lake_instReprDynlib_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprDynlib_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__17_value)}};
static const lean_object* l_Lake_instReprDynlib_repr___redArg___closed__21 = (const lean_object*)&l_Lake_instReprDynlib_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprDynlib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprDynlib_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprDynlib___closed__0 = (const lean_object*)&l_Lake_instReprDynlib___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprDynlib = (const lean_object*)&l_Lake_instReprDynlib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Dynlib_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Dynlib_instToJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Dynlib_instToJson___closed__0 = (const lean_object*)&l_Lake_Dynlib_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Dynlib_instToJson = (const lean_object*)&l_Lake_Dynlib_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Dynlib_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Dynlib_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Dynlib_instToString___closed__0 = (const lean_object*)&l_Lake_Dynlib_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Dynlib_instToString = (const lean_object*)&l_Lake_Dynlib_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Dynlib_instCoeFilePath = (const lean_object*)&l_Lake_Dynlib_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDynlib_repr_spec__1(lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_nat_to_int(v_a_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(8u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(10u);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_dec(v_x_46_);
return v_x_47_;
}
else
{
lean_object* v_head_49_; lean_object* v_tail_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_60_; 
v_head_49_ = lean_ctor_get(v_x_48_, 0);
v_tail_50_ = lean_ctor_get(v_x_48_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_48_);
if (v_isSharedCheck_60_ == 0)
{
v___x_52_ = v_x_48_;
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_tail_50_);
lean_inc(v_head_49_);
lean_dec(v_x_48_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
lean_inc(v_x_46_);
if (v_isShared_53_ == 0)
{
lean_ctor_set_tag(v___x_52_, 5);
lean_ctor_set(v___x_52_, 1, v_x_46_);
lean_ctor_set(v___x_52_, 0, v_x_47_);
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_x_47_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_x_46_);
v___x_55_ = v_reuseFailAlloc_59_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Lake_instReprDynlib_repr___redArg(v_head_49_);
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(v_x_46_, v___x_57_, v_tail_50_);
return v___x_58_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_63_; 
lean_dec(v_x_62_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v_tail_64_; 
v_tail_64_ = lean_ctor_get(v_x_61_, 1);
if (lean_obj_tag(v_tail_64_) == 0)
{
lean_object* v_head_65_; lean_object* v___x_66_; 
lean_dec(v_x_62_);
v_head_65_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_head_65_);
lean_dec_ref(v_x_61_);
v___x_66_ = l_Lake_instReprDynlib_repr___redArg(v_head_65_);
return v___x_66_;
}
else
{
lean_object* v_head_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc(v_tail_64_);
v_head_67_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_head_67_);
lean_dec_ref(v_x_61_);
v___x_68_ = l_Lake_instReprDynlib_repr___redArg(v_head_67_);
v___x_69_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(v_x_62_, v___x_68_, v_tail_64_);
return v___x_69_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0));
v___x_72_ = lean_string_length(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(lean_object* v_xs_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_array_get_size(v_xs_83_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_nat_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_87_ = lean_array_to_list(v_xs_83_);
v___x_88_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3));
v___x_89_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(v___x_87_, v___x_88_);
v___x_90_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6);
v___x_91_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7));
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_89_);
v___x_93_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8));
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_90_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_Std_Format_fill(v___x_95_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; 
lean_dec_ref(v_xs_83_);
v___x_97_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10));
return v___x_97_;
}
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__0));
v___x_100_ = lean_string_length(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__18, &l_Lake_instReprDynlib_repr___redArg___closed__18_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__18);
v___x_102_ = lean_nat_to_int(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr___redArg(lean_object* v_x_108_){
_start:
{
lean_object* v_path_109_; lean_object* v_name_110_; uint8_t v_plugin_111_; lean_object* v_deps_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_path_109_ = lean_ctor_get(v_x_108_, 0);
lean_inc_ref(v_path_109_);
v_name_110_ = lean_ctor_get(v_x_108_, 1);
lean_inc_ref(v_name_110_);
v_plugin_111_ = lean_ctor_get_uint8(v_x_108_, sizeof(void*)*3);
v_deps_112_ = lean_ctor_get(v_x_108_, 2);
lean_inc_ref(v_deps_112_);
lean_dec_ref(v_x_108_);
v___x_113_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__5));
v___x_114_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__6));
v___x_115_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__7, &l_Lake_instReprDynlib_repr___redArg___closed__7_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__7);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__9));
v___x_118_ = l_String_quote(v_path_109_);
v___x_119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v___x_116_);
v___x_122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_115_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = 0;
v___x_124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set_uint8(v___x_124_, sizeof(void*)*1, v___x_123_);
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_114_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2));
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_box(1);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__11));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_113_);
v___x_133_ = l_String_quote(v_name_110_);
v___x_134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___x_135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_115_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_123_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_126_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_128_);
v___x_140_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__13));
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_113_);
v___x_143_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__14, &l_Lake_instReprDynlib_repr___redArg___closed__14_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__14);
v___x_144_ = l_Bool_repr___redArg(v_plugin_111_);
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_123_);
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_142_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_126_);
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_128_);
v___x_150_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__16));
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_113_);
v___x_153_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(v_deps_112_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_115_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_123_);
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_152_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__19, &l_Lake_instReprDynlib_repr___redArg___closed__19_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__19);
v___x_158_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__20));
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_156_);
v___x_160_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__21));
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_157_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_123_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_dec(v_x_164_);
return v_x_165_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_178_; 
v_head_167_ = lean_ctor_get(v_x_166_, 0);
v_tail_168_ = lean_ctor_get(v_x_166_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_178_ == 0)
{
v___x_170_ = v_x_166_;
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_tail_168_);
lean_inc(v_head_167_);
lean_dec(v_x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
lean_inc(v_x_164_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 5);
lean_ctor_set(v___x_170_, 1, v_x_164_);
lean_ctor_set(v___x_170_, 0, v_x_165_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_x_165_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_x_164_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Lake_instReprDynlib_repr___redArg(v_head_167_);
v___x_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v_x_165_ = v___x_175_;
v_x_166_ = v_tail_168_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr(lean_object* v_x_179_, lean_object* v_prec_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lake_instReprDynlib_repr___redArg(v_x_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr___boxed(lean_object* v_x_182_, lean_object* v_prec_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lake_instReprDynlib_repr(v_x_182_, v_prec_183_);
lean_dec(v_prec_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object* v_self_187_){
_start:
{
lean_object* v_path_188_; lean_object* v___x_189_; 
v_path_188_ = lean_ctor_get(v_self_187_, 0);
lean_inc_ref(v_path_188_);
lean_dec_ref(v_self_187_);
v___x_189_ = l_System_FilePath_parent(v_path_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToJson___lam__0(lean_object* v_x_190_){
_start:
{
lean_object* v_path_191_; lean_object* v___x_192_; 
v_path_191_ = lean_ctor_get(v_x_190_, 0);
lean_inc_ref(v_path_191_);
v___x_192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_192_, 0, v_path_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToJson___lam__0___boxed(lean_object* v_x_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lake_Dynlib_instToJson___lam__0(v_x_193_);
lean_dec_ref(v_x_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToString___lam__0(lean_object* v_x_197_){
_start:
{
lean_object* v_path_198_; 
v_path_198_ = lean_ctor_get(v_x_197_, 0);
lean_inc_ref(v_path_198_);
return v_path_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToString___lam__0___boxed(lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_Dynlib_instToString___lam__0(v_x_199_);
lean_dec_ref(v_x_199_);
return v_res_200_;
}
}
lean_object* runtime_initialize_Lake_Config_OutFormat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_OutFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Dynlib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_OutFormat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_OutFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Dynlib(builtin);
}
#ifdef __cplusplus
}
#endif
