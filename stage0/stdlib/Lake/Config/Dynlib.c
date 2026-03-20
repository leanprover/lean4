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
extern lean_object* l_System_instInhabitedFilePath_default;
static const lean_string_object l_Lake_instInhabitedDynlib_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedDynlib_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__0_value;
static const lean_array_object l_Lake_instInhabitedDynlib_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedDynlib_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedDynlib_default___closed__1_value;
static lean_once_cell_t l_Lake_instInhabitedDynlib_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedDynlib_default___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedDynlib_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedDynlib;
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
static lean_object* _init_l_Lake_instInhabitedDynlib_default___closed__2(void){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = ((lean_object*)(l_Lake_instInhabitedDynlib_default___closed__1));
v___x_5_ = 0;
v___x_6_ = ((lean_object*)(l_Lake_instInhabitedDynlib_default___closed__0));
v___x_7_ = l_System_instInhabitedFilePath_default;
v___x_8_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_4_);
lean_ctor_set_uint8(v___x_8_, sizeof(void*)*3, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lake_instInhabitedDynlib_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lake_instInhabitedDynlib_default___closed__2, &l_Lake_instInhabitedDynlib_default___closed__2_once, _init_l_Lake_instInhabitedDynlib_default___closed__2);
return v___x_9_;
}
}
static lean_object* _init_l_Lake_instInhabitedDynlib(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lake_instInhabitedDynlib_default;
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDynlib_repr_spec__1(lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_nat_to_int(v_a_11_);
return v___x_12_;
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(8u);
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(10u);
v___x_40_ = lean_nat_to_int(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_dec(v_x_47_);
return v_x_48_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_61_; 
v_head_50_ = lean_ctor_get(v_x_49_, 0);
v_tail_51_ = lean_ctor_get(v_x_49_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_61_ == 0)
{
v___x_53_ = v_x_49_;
v_isShared_54_ = v_isSharedCheck_61_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_tail_51_);
lean_inc(v_head_50_);
lean_dec(v_x_49_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_61_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
lean_inc(v_x_47_);
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 5);
lean_ctor_set(v___x_53_, 1, v_x_47_);
lean_ctor_set(v___x_53_, 0, v_x_48_);
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_x_48_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_x_47_);
v___x_56_ = v_reuseFailAlloc_60_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = l_Lake_instReprDynlib_repr___redArg(v_head_50_);
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(v_x_47_, v___x_58_, v_tail_51_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v___x_64_; 
lean_dec(v_x_63_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
else
{
lean_object* v_tail_65_; 
v_tail_65_ = lean_ctor_get(v_x_62_, 1);
if (lean_obj_tag(v_tail_65_) == 0)
{
lean_object* v_head_66_; lean_object* v___x_67_; 
lean_dec(v_x_63_);
v_head_66_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_head_66_);
lean_dec_ref(v_x_62_);
v___x_67_ = l_Lake_instReprDynlib_repr___redArg(v_head_66_);
return v___x_67_;
}
else
{
lean_object* v_head_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_inc(v_tail_65_);
v_head_68_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_head_68_);
lean_dec_ref(v_x_62_);
v___x_69_ = l_Lake_instReprDynlib_repr___redArg(v_head_68_);
v___x_70_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(v_x_63_, v___x_69_, v_tail_65_);
return v___x_70_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0));
v___x_73_ = lean_string_length(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5);
v___x_75_ = lean_nat_to_int(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(lean_object* v_xs_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_array_get_size(v_xs_84_);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_nat_dec_eq(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_88_ = lean_array_to_list(v_xs_84_);
v___x_89_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3));
v___x_90_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(v___x_88_, v___x_89_);
v___x_91_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6);
v___x_92_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_90_);
v___x_94_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8));
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = l_Std_Format_fill(v___x_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
lean_dec_ref(v_xs_84_);
v___x_98_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10));
return v___x_98_;
}
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__0));
v___x_101_ = lean_string_length(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lake_instReprDynlib_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__18, &l_Lake_instReprDynlib_repr___redArg___closed__18_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__18);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr___redArg(lean_object* v_x_109_){
_start:
{
lean_object* v_path_110_; lean_object* v_name_111_; uint8_t v_plugin_112_; lean_object* v_deps_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_path_110_ = lean_ctor_get(v_x_109_, 0);
lean_inc_ref(v_path_110_);
v_name_111_ = lean_ctor_get(v_x_109_, 1);
lean_inc_ref(v_name_111_);
v_plugin_112_ = lean_ctor_get_uint8(v_x_109_, sizeof(void*)*3);
v_deps_113_ = lean_ctor_get(v_x_109_, 2);
lean_inc_ref(v_deps_113_);
lean_dec_ref(v_x_109_);
v___x_114_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__5));
v___x_115_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__6));
v___x_116_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__7, &l_Lake_instReprDynlib_repr___redArg___closed__7_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__7);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__9));
v___x_119_ = l_String_quote(v_path_110_);
v___x_120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_118_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v___x_117_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_116_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_115_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_box(1);
v___x_130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__11));
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_114_);
v___x_134_ = l_String_quote(v_name_111_);
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_116_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*1, v___x_124_);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_133_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_127_);
v___x_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_129_);
v___x_141_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__13));
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_114_);
v___x_144_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__14, &l_Lake_instReprDynlib_repr___redArg___closed__14_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__14);
v___x_145_ = l_Bool_repr___redArg(v_plugin_112_);
v___x_146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_124_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_143_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_127_);
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_129_);
v___x_151_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__16));
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_114_);
v___x_154_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(v_deps_113_);
v___x_155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_116_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_124_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_153_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_obj_once(&l_Lake_instReprDynlib_repr___redArg___closed__19, &l_Lake_instReprDynlib_repr___redArg___closed__19_once, _init_l_Lake_instReprDynlib_repr___redArg___closed__19);
v___x_159_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__20));
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_157_);
v___x_161_ = ((lean_object*)(l_Lake_instReprDynlib_repr___redArg___closed__21));
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_158_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*1, v___x_124_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_dec(v_x_165_);
return v_x_166_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_head_168_ = lean_ctor_get(v_x_167_, 0);
v_tail_169_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_x_167_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_tail_169_);
lean_inc(v_head_168_);
lean_dec(v_x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
lean_inc(v_x_165_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 5);
lean_ctor_set(v___x_171_, 1, v_x_165_);
lean_ctor_set(v___x_171_, 0, v_x_166_);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_x_166_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_x_165_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lake_instReprDynlib_repr___redArg(v_head_168_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v_x_166_ = v___x_176_;
v_x_167_ = v_tail_169_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr(lean_object* v_x_180_, lean_object* v_prec_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lake_instReprDynlib_repr___redArg(v_x_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDynlib_repr___boxed(lean_object* v_x_183_, lean_object* v_prec_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lake_instReprDynlib_repr(v_x_183_, v_prec_184_);
lean_dec(v_prec_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object* v_self_188_){
_start:
{
lean_object* v_path_189_; lean_object* v___x_190_; 
v_path_189_ = lean_ctor_get(v_self_188_, 0);
lean_inc_ref(v_path_189_);
lean_dec_ref(v_self_188_);
v___x_190_ = l_System_FilePath_parent(v_path_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToJson___lam__0(lean_object* v_x_191_){
_start:
{
lean_object* v_path_192_; lean_object* v___x_193_; 
v_path_192_ = lean_ctor_get(v_x_191_, 0);
lean_inc_ref(v_path_192_);
v___x_193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_193_, 0, v_path_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToJson___lam__0___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_Dynlib_instToJson___lam__0(v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToString___lam__0(lean_object* v_x_198_){
_start:
{
lean_object* v_path_199_; 
v_path_199_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_path_199_);
return v_path_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_instToString___lam__0___boxed(lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_Dynlib_instToString___lam__0(v_x_200_);
lean_dec_ref(v_x_200_);
return v_res_201_;
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
l_Lake_instInhabitedDynlib_default = _init_l_Lake_instInhabitedDynlib_default();
lean_mark_persistent(l_Lake_instInhabitedDynlib_default);
l_Lake_instInhabitedDynlib = _init_l_Lake_instInhabitedDynlib();
lean_mark_persistent(l_Lake_instInhabitedDynlib);
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
