// Lean compiler output
// Module: Lake.Config.OutFormat
// Imports: public import Lean.Setup public import Init.Data.String.TakeDrop
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_listToLines___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_listToLines___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_listToLines___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_listToLines___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_listToLines___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_listToLines___redArg___closed__0 = (const lean_object*)&l_Lake_listToLines___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_listToLines___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_listToLines(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__0 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__0_value;
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__1 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__1_value;
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__2 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__2_value;
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__3 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__3_value;
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__4 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__4_value;
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__5 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__5_value;
static const lean_closure_object l_Lake_arrayToLines___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_arrayToLines___redArg___closed__6 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__6_value;
static const lean_ctor_object l_Lake_arrayToLines___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_arrayToLines___redArg___closed__0_value),((lean_object*)&l_Lake_arrayToLines___redArg___closed__1_value)}};
static const lean_object* l_Lake_arrayToLines___redArg___closed__7 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__7_value;
static const lean_ctor_object l_Lake_arrayToLines___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_arrayToLines___redArg___closed__7_value),((lean_object*)&l_Lake_arrayToLines___redArg___closed__2_value),((lean_object*)&l_Lake_arrayToLines___redArg___closed__3_value),((lean_object*)&l_Lake_arrayToLines___redArg___closed__4_value),((lean_object*)&l_Lake_arrayToLines___redArg___closed__5_value)}};
static const lean_object* l_Lake_arrayToLines___redArg___closed__8 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__8_value;
static const lean_ctor_object l_Lake_arrayToLines___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_arrayToLines___redArg___closed__8_value),((lean_object*)&l_Lake_arrayToLines___redArg___closed__6_value)}};
static const lean_object* l_Lake_arrayToLines___redArg___closed__9 = (const lean_object*)&l_Lake_arrayToLines___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_arrayToLines___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_arrayToLines(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instToTextJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_compress, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToTextJson___closed__0 = (const lean_object*)&l_Lake_instToTextJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToTextJson = (const lean_object*)&l_Lake_instToTextJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextArray___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryText___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryText___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instQueryText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryText___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instQueryText___closed__0 = (const lean_object*)&l_Lake_instQueryText___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instQueryText(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object*);
static const lean_closure_object l_Lake_instQueryTextUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryTextUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instQueryTextUnit___closed__0 = (const lean_object*)&l_Lake_instQueryTextUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instQueryTextUnit = (const lean_object*)&l_Lake_instQueryTextUnit___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instQueryJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instQueryJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instQueryJson___closed__0 = (const lean_object*)&l_Lake_instQueryJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instQueryJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object*);
static const lean_closure_object l_Lake_instQueryJsonUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instQueryJsonUnit___closed__0 = (const lean_object*)&l_Lake_instQueryJsonUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instQueryJsonUnit = (const lean_object*)&l_Lake_instQueryJsonUnit___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_nullFormat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_nullFormat___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_nullFormat(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_nullFormat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ppImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l_Lake_ppImport___closed__0 = (const lean_object*)&l_Lake_ppImport___closed__0_value;
static const lean_string_object l_Lake_ppImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "all "};
static const lean_object* l_Lake_ppImport___closed__1 = (const lean_object*)&l_Lake_ppImport___closed__1_value;
static const lean_string_object l_Lake_ppImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l_Lake_ppImport___closed__2 = (const lean_object*)&l_Lake_ppImport___closed__2_value;
static const lean_string_object l_Lake_ppImport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "public "};
static const lean_object* l_Lake_ppImport___closed__3 = (const lean_object*)&l_Lake_ppImport___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_ppImport(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ppImport___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ppModuleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lake_ppModuleHeader___closed__0 = (const lean_object*)&l_Lake_ppModuleHeader___closed__0_value;
static const lean_string_object l_Lake_ppModuleHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "module prelude"};
static const lean_object* l_Lake_ppModuleHeader___closed__1 = (const lean_object*)&l_Lake_ppModuleHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ppModuleHeader___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0 = (const lean_object*)&l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader = (const lean_object*)&l___private_Lake_Config_OutFormat_0__Lake_instQueryTextModuleHeader___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lake_OutFormat_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_OutFormat_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lake_OutFormat_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___redArg(lean_object* v_text_22_){
_start:
{
lean_inc(v_text_22_);
return v_text_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___redArg___boxed(lean_object* v_text_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_OutFormat_text_elim___redArg(v_text_23_);
lean_dec(v_text_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_text_28_){
_start:
{
lean_inc(v_text_28_);
return v_text_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_text_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lake_OutFormat_text_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_text_32_);
lean_dec(v_text_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___redArg(lean_object* v_json_35_){
_start:
{
lean_inc(v_json_35_);
return v_json_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___redArg___boxed(lean_object* v_json_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_OutFormat_json_elim___redArg(v_json_36_);
lean_dec(v_json_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_json_41_){
_start:
{
lean_inc(v_json_41_);
return v_json_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_json_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lake_OutFormat_json_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_json_45_);
lean_dec(v_json_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___redArg(lean_object* v_inst_48_){
_start:
{
lean_inc_ref(v_inst_48_);
return v_inst_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___redArg___boxed(lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_instToTextOfToString___redArg(v_inst_49_);
lean_dec_ref(v_inst_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_){
_start:
{
lean_inc_ref(v_inst_52_);
return v_inst_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___boxed(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lake_instToTextOfToString(v_00_u03b1_53_, v_inst_54_);
lean_dec_ref(v_inst_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_listToLines___redArg___lam__0(lean_object* v_f_57_, lean_object* v_x1_58_, lean_object* v_x2_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_apply_1(v_f_57_, v_x2_59_);
v___x_61_ = lean_string_append(v_x1_58_, v___x_60_);
lean_dec_ref(v___x_60_);
v___x_62_ = ((lean_object*)(l_Lake_listToLines___redArg___lam__0___closed__0));
v___x_63_ = lean_string_append(v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_listToLines___redArg(lean_object* v_as_65_, lean_object* v_f_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___f_67_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_67_, 0, v_f_66_);
v___x_68_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_69_ = l_List_foldl___redArg(v___f_67_, v___x_68_, v_as_65_);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_string_utf8_byte_size(v___x_69_);
lean_inc(v___x_69_);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_69_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_72_);
v___x_74_ = l_String_Slice_Pos_prevn(v___x_73_, v___x_72_, v___x_70_);
lean_dec_ref_known(v___x_73_, 3);
v___x_75_ = lean_string_utf8_extract_fast(v___x_69_, v___x_71_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v___x_69_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_listToLines(lean_object* v_00_u03b1_76_, lean_object* v_as_77_, lean_object* v_f_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___f_79_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_79_, 0, v_f_78_);
v___x_80_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_81_ = l_List_foldl___redArg(v___f_79_, v___x_80_, v_as_77_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_string_utf8_byte_size(v___x_81_);
lean_inc(v___x_81_);
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_81_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_84_);
v___x_86_ = l_String_Slice_Pos_prevn(v___x_85_, v___x_84_, v___x_82_);
lean_dec_ref_known(v___x_85_, 3);
v___x_87_ = lean_string_utf8_extract_fast(v___x_81_, v___x_83_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v___x_81_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_arrayToLines___redArg(lean_object* v_as_107_, lean_object* v_f_108_){
_start:
{
lean_object* v___y_110_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_117_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_array_get_size(v_as_107_);
v___x_120_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v___x_121_ = lean_nat_dec_lt(v___x_118_, v___x_119_);
if (v___x_121_ == 0)
{
lean_dec_ref(v_f_108_);
lean_dec_ref(v_as_107_);
v___y_110_ = v___x_117_;
goto v___jp_109_;
}
else
{
lean_object* v___f_122_; uint8_t v___x_123_; 
v___f_122_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_122_, 0, v_f_108_);
v___x_123_ = lean_nat_dec_le(v___x_119_, v___x_119_);
if (v___x_123_ == 0)
{
if (v___x_121_ == 0)
{
lean_dec_ref(v___f_122_);
lean_dec_ref(v_as_107_);
v___y_110_ = v___x_117_;
goto v___jp_109_;
}
else
{
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_119_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_120_, v___f_122_, v_as_107_, v___x_124_, v___x_125_, v___x_117_);
v___y_110_ = v___x_126_;
goto v___jp_109_;
}
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_119_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_120_, v___f_122_, v_as_107_, v___x_127_, v___x_128_, v___x_117_);
v___y_110_ = v___x_129_;
goto v___jp_109_;
}
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_string_utf8_byte_size(v___y_110_);
lean_inc_ref(v___y_110_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v___y_110_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
v___x_115_ = l_String_Slice_Pos_prevn(v___x_114_, v___x_113_, v___x_111_);
lean_dec_ref_known(v___x_114_, 3);
v___x_116_ = lean_string_utf8_extract_fast(v___y_110_, v___x_112_, v___x_115_);
lean_dec(v___x_115_);
lean_dec_ref(v___y_110_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_arrayToLines(lean_object* v_00_u03b1_130_, lean_object* v_as_131_, lean_object* v_f_132_){
_start:
{
lean_object* v___y_134_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v_as_131_);
v___x_144_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v___x_145_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_145_ == 0)
{
lean_dec_ref(v_f_132_);
lean_dec_ref(v_as_131_);
v___y_134_ = v___x_141_;
goto v___jp_133_;
}
else
{
lean_object* v___f_146_; uint8_t v___x_147_; 
v___f_146_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_146_, 0, v_f_132_);
v___x_147_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_147_ == 0)
{
if (v___x_145_ == 0)
{
lean_dec_ref(v___f_146_);
lean_dec_ref(v_as_131_);
v___y_134_ = v___x_141_;
goto v___jp_133_;
}
else
{
size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; 
v___x_148_ = ((size_t)0ULL);
v___x_149_ = lean_usize_of_nat(v___x_143_);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_144_, v___f_146_, v_as_131_, v___x_148_, v___x_149_, v___x_141_);
v___y_134_ = v___x_150_;
goto v___jp_133_;
}
}
else
{
size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((size_t)0ULL);
v___x_152_ = lean_usize_of_nat(v___x_143_);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_144_, v___f_146_, v_as_131_, v___x_151_, v___x_152_, v___x_141_);
v___y_134_ = v___x_153_;
goto v___jp_133_;
}
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_string_utf8_byte_size(v___y_134_);
lean_inc_ref(v___y_134_);
v___x_138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_138_, 0, v___y_134_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_137_);
v___x_139_ = l_String_Slice_Pos_prevn(v___x_138_, v___x_137_, v___x_135_);
lean_dec_ref_known(v___x_138_, 3);
v___x_140_ = lean_string_utf8_extract_fast(v___y_134_, v___x_136_, v___x_139_);
lean_dec(v___x_139_);
lean_dec_ref(v___y_134_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg___lam__0(lean_object* v_inst_156_, lean_object* v_x1_157_, lean_object* v_x2_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = lean_apply_1(v_inst_156_, v_x2_158_);
v___x_160_ = lean_string_append(v_x1_157_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = ((lean_object*)(l_Lake_listToLines___redArg___lam__0___closed__0));
v___x_162_ = lean_string_append(v___x_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg___lam__1(lean_object* v___f_163_, lean_object* v_x_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_165_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_166_ = l_List_foldl___redArg(v___f_163_, v___x_165_, v_x_164_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_string_utf8_byte_size(v___x_166_);
lean_inc(v___x_166_);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_166_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
v___x_171_ = l_String_Slice_Pos_prevn(v___x_170_, v___x_169_, v___x_167_);
lean_dec_ref_known(v___x_170_, 3);
v___x_172_ = lean_string_utf8_extract_fast(v___x_166_, v___x_168_, v___x_171_);
lean_dec(v___x_171_);
lean_dec(v___x_166_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg(lean_object* v_inst_173_){
_start:
{
lean_object* v___f_174_; lean_object* v___f_175_; 
v___f_174_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_174_, 0, v_inst_173_);
v___f_175_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_175_, 0, v___f_174_);
return v___f_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lake_instToTextList___redArg(v_inst_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray___redArg___lam__1(lean_object* v___f_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___y_182_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_189_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_array_get_size(v_x_180_);
v___x_192_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v___x_193_ = lean_nat_dec_lt(v___x_190_, v___x_191_);
if (v___x_193_ == 0)
{
lean_dec_ref(v_x_180_);
lean_dec_ref(v___f_179_);
v___y_182_ = v___x_189_;
goto v___jp_181_;
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_191_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_192_, v___f_179_, v_x_180_, v___x_194_, v___x_195_, v___x_189_);
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_string_utf8_byte_size(v___y_182_);
lean_inc_ref(v___y_182_);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___y_182_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_185_);
v___x_187_ = l_String_Slice_Pos_prevn(v___x_186_, v___x_185_, v___x_183_);
lean_dec_ref_known(v___x_186_, 3);
v___x_188_ = lean_string_utf8_extract_fast(v___y_182_, v___x_184_, v___x_187_);
lean_dec(v___x_187_);
lean_dec_ref(v___y_182_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray___redArg(lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___f_199_; 
v___f_198_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_198_, 0, v_inst_197_);
v___f_199_ = lean_alloc_closure((void*)(l_Lake_instToTextArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_199_, 0, v___f_198_);
return v___f_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray(lean_object* v_00_u03b1_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lake_instToTextArray___redArg(v_inst_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText___lam__0(lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText___lam__0___boxed(lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_instQueryText___lam__0(v_x_205_);
lean_dec(v_x_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText(lean_object* v_00_u03b1_208_){
_start:
{
lean_object* v___f_209_; 
v___f_209_ = ((lean_object*)(l_Lake_instQueryText___closed__0));
return v___f_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg(lean_object* v_inst_210_){
_start:
{
lean_inc_ref(v_inst_210_);
return v_inst_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg___boxed(lean_object* v_inst_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lake_instQueryTextOfToText___redArg(v_inst_211_);
lean_dec_ref(v_inst_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText(lean_object* v_00_u03b1_213_, lean_object* v_inst_214_){
_start:
{
lean_inc_ref(v_inst_214_);
return v_inst_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___boxed(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_instQueryTextOfToText(v_00_u03b1_215_, v_inst_216_);
lean_dec_ref(v_inst_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextList___redArg(lean_object* v_inst_218_){
_start:
{
lean_object* v___f_219_; lean_object* v___f_220_; 
v___f_219_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_219_, 0, v_inst_218_);
v___f_220_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_220_, 0, v___f_219_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextList(lean_object* v_00_u03b1_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lake_instQueryTextList___redArg(v_inst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray___redArg(lean_object* v_inst_224_){
_start:
{
lean_object* v___f_225_; lean_object* v___f_226_; 
v___f_225_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_225_, 0, v_inst_224_);
v___f_226_ = lean_alloc_closure((void*)(l_Lake_instToTextArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_226_, 0, v___f_225_);
return v___f_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lake_instQueryTextArray___redArg(v_inst_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___lam__0(lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___lam__0___boxed(lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lake_instQueryJson___lam__0(v_x_236_);
lean_dec(v_x_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson(lean_object* v_00_u03b1_239_){
_start:
{
lean_object* v___f_240_; 
v___f_240_ = ((lean_object*)(l_Lake_instQueryJson___closed__0));
return v___f_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg(lean_object* v_inst_241_){
_start:
{
lean_inc_ref(v_inst_241_);
return v_inst_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg___boxed(lean_object* v_inst_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lake_instQueryJsonOfToJson___redArg(v_inst_242_);
lean_dec_ref(v_inst_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson(lean_object* v_00_u03b1_244_, lean_object* v_inst_245_){
_start:
{
lean_inc_ref(v_inst_245_);
return v_inst_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___boxed(lean_object* v_00_u03b1_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lake_instQueryJsonOfToJson(v_00_u03b1_246_, v_inst_247_);
lean_dec_ref(v_inst_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__0(lean_object* v_inst_249_, lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_apply_1(v_inst_249_, v_x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__1(lean_object* v___f_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; size_t v_sz_256_; size_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_254_ = lean_array_mk(v_x_253_);
v___x_255_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v_sz_256_ = lean_array_size(v___x_254_);
v___x_257_ = ((size_t)0ULL);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_255_, v___f_252_, v_sz_256_, v___x_257_, v___x_254_);
v___x_259_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg(lean_object* v_inst_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___f_262_; 
v___f_261_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_261_, 0, v_inst_260_);
v___f_262_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_262_, 0, v___f_261_);
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lake_instQueryJsonList___redArg(v_inst_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg___lam__1(lean_object* v___f_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; size_t v_sz_269_; size_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v_sz_269_ = lean_array_size(v_x_267_);
v___x_270_ = ((size_t)0ULL);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_268_, v___f_266_, v_sz_269_, v___x_270_, v_x_267_);
v___x_272_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg(lean_object* v_inst_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___f_275_; 
v___f_274_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_274_, 0, v_inst_273_);
v___f_275_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_275_, 0, v___f_274_);
return v___f_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray(lean_object* v_00_u03b1_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lake_instQueryJsonArray___redArg(v_inst_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object* v_x_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson___redArg(lean_object* v_inst_283_, lean_object* v_inst_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_inst_283_);
lean_ctor_set(v___x_285_, 1, v_inst_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson(lean_object* v_00_u03b1_286_, lean_object* v_inst_287_, lean_object* v_inst_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_inst_287_);
lean_ctor_set(v___x_289_, 1, v_inst_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lake_nullFormat___redArg___closed__0(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(0);
v___x_291_ = l_Lean_Json_compress(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg(uint8_t v_fmt_292_){
_start:
{
if (v_fmt_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lake_nullFormat___redArg___closed__0, &l_Lake_nullFormat___redArg___closed__0_once, _init_l_Lake_nullFormat___redArg___closed__0);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg___boxed(lean_object* v_fmt_295_){
_start:
{
uint8_t v_fmt_boxed_296_; lean_object* v_res_297_; 
v_fmt_boxed_296_ = lean_unbox(v_fmt_295_);
v_res_297_ = l_Lake_nullFormat___redArg(v_fmt_boxed_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat(lean_object* v_00_u03b1_298_, uint8_t v_fmt_299_, lean_object* v_x_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lake_nullFormat___redArg(v_fmt_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___boxed(lean_object* v_00_u03b1_302_, lean_object* v_fmt_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_fmt_boxed_305_; lean_object* v_res_306_; 
v_fmt_boxed_305_ = lean_unbox(v_fmt_303_);
v_res_306_ = l_Lake_nullFormat(v_00_u03b1_302_, v_fmt_boxed_305_, v_x_304_);
lean_dec(v_x_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg(lean_object* v_inst_307_, uint8_t v_fmt_308_, lean_object* v_a_309_){
_start:
{
if (v_fmt_308_ == 0)
{
lean_object* v_toQueryText_310_; lean_object* v___x_311_; 
v_toQueryText_310_ = lean_ctor_get(v_inst_307_, 0);
lean_inc_ref(v_toQueryText_310_);
lean_dec_ref(v_inst_307_);
v___x_311_ = lean_apply_1(v_toQueryText_310_, v_a_309_);
return v___x_311_;
}
else
{
lean_object* v_toQueryJson_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_toQueryJson_312_ = lean_ctor_get(v_inst_307_, 1);
lean_inc_ref(v_toQueryJson_312_);
lean_dec_ref(v_inst_307_);
v___x_313_ = lean_apply_1(v_toQueryJson_312_, v_a_309_);
v___x_314_ = l_Lean_Json_compress(v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg___boxed(lean_object* v_inst_315_, lean_object* v_fmt_316_, lean_object* v_a_317_){
_start:
{
uint8_t v_fmt_boxed_318_; lean_object* v_res_319_; 
v_fmt_boxed_318_ = lean_unbox(v_fmt_316_);
v_res_319_ = l_Lake_formatQuery___redArg(v_inst_315_, v_fmt_boxed_318_, v_a_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery(lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, uint8_t v_fmt_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lake_formatQuery___redArg(v_inst_321_, v_fmt_322_, v_a_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___boxed(lean_object* v_00_u03b1_325_, lean_object* v_inst_326_, lean_object* v_fmt_327_, lean_object* v_a_328_){
_start:
{
uint8_t v_fmt_boxed_329_; lean_object* v_res_330_; 
v_fmt_boxed_329_ = lean_unbox(v_fmt_327_);
v_res_330_ = l_Lake_formatQuery(v_00_u03b1_325_, v_inst_326_, v_fmt_boxed_329_, v_a_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lake_ppImport(lean_object* v_imp_335_, uint8_t v_isModule_336_, lean_object* v_init_337_){
_start:
{
lean_object* v_s_339_; lean_object* v_s_345_; lean_object* v_s_352_; 
if (v_isModule_336_ == 0)
{
v_s_352_ = v_init_337_;
goto v___jp_351_;
}
else
{
uint8_t v_isExported_356_; 
v_isExported_356_ = lean_ctor_get_uint8(v_imp_335_, sizeof(void*)*1 + 1);
if (v_isExported_356_ == 0)
{
v_s_352_ = v_init_337_;
goto v___jp_351_;
}
else
{
lean_object* v___x_357_; lean_object* v_s_358_; 
v___x_357_ = ((lean_object*)(l_Lake_ppImport___closed__3));
v_s_358_ = lean_string_append(v_init_337_, v___x_357_);
v_s_352_ = v_s_358_;
goto v___jp_351_;
}
}
v___jp_338_:
{
lean_object* v_module_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v_s_343_; 
v_module_340_ = lean_ctor_get(v_imp_335_, 0);
lean_inc(v_module_340_);
lean_dec_ref(v_imp_335_);
v___x_341_ = 1;
v___x_342_ = l_Lean_Name_toString(v_module_340_, v___x_341_);
v_s_343_ = lean_string_append(v_s_339_, v___x_342_);
lean_dec_ref(v___x_342_);
return v_s_343_;
}
v___jp_344_:
{
uint8_t v_importAll_346_; lean_object* v___x_347_; lean_object* v_s_348_; 
v_importAll_346_ = lean_ctor_get_uint8(v_imp_335_, sizeof(void*)*1);
v___x_347_ = ((lean_object*)(l_Lake_ppImport___closed__0));
v_s_348_ = lean_string_append(v_s_345_, v___x_347_);
if (v_importAll_346_ == 0)
{
v_s_339_ = v_s_348_;
goto v___jp_338_;
}
else
{
lean_object* v___x_349_; lean_object* v_s_350_; 
v___x_349_ = ((lean_object*)(l_Lake_ppImport___closed__1));
v_s_350_ = lean_string_append(v_s_348_, v___x_349_);
v_s_339_ = v_s_350_;
goto v___jp_338_;
}
}
v___jp_351_:
{
uint8_t v_isMeta_353_; 
v_isMeta_353_ = lean_ctor_get_uint8(v_imp_335_, sizeof(void*)*1 + 2);
if (v_isMeta_353_ == 0)
{
v_s_345_ = v_s_352_;
goto v___jp_344_;
}
else
{
lean_object* v___x_354_; lean_object* v_s_355_; 
v___x_354_ = ((lean_object*)(l_Lake_ppImport___closed__2));
v_s_355_ = lean_string_append(v_s_352_, v___x_354_);
v_s_345_ = v_s_355_;
goto v___jp_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ppImport___boxed(lean_object* v_imp_359_, lean_object* v_isModule_360_, lean_object* v_init_361_){
_start:
{
uint8_t v_isModule_boxed_362_; lean_object* v_res_363_; 
v_isModule_boxed_362_ = lean_unbox(v_isModule_360_);
v_res_363_ = l_Lake_ppImport(v_imp_359_, v_isModule_boxed_362_, v_init_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(uint8_t v_isModule_364_, lean_object* v_as_365_, size_t v_i_366_, size_t v_stop_367_, lean_object* v_b_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_eq(v_i_366_, v_stop_367_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; uint32_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; size_t v___x_374_; size_t v___x_375_; 
v___x_370_ = lean_array_uget_borrowed(v_as_365_, v_i_366_);
v___x_371_ = 10;
v___x_372_ = lean_string_push(v_b_368_, v___x_371_);
lean_inc(v___x_370_);
v___x_373_ = l_Lake_ppImport(v___x_370_, v_isModule_364_, v___x_372_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_add(v_i_366_, v___x_374_);
v_i_366_ = v___x_375_;
v_b_368_ = v___x_373_;
goto _start;
}
else
{
return v_b_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0___boxed(lean_object* v_isModule_377_, lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_, lean_object* v_b_381_){
_start:
{
uint8_t v_isModule_boxed_382_; size_t v_i_boxed_383_; size_t v_stop_boxed_384_; lean_object* v_res_385_; 
v_isModule_boxed_382_ = lean_unbox(v_isModule_377_);
v_i_boxed_383_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_384_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_boxed_382_, v_as_378_, v_i_boxed_383_, v_stop_boxed_384_, v_b_381_);
lean_dec_ref(v_as_378_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader(lean_object* v_header_388_){
_start:
{
lean_object* v_imports_389_; uint8_t v_isModule_390_; lean_object* v___y_392_; 
v_imports_389_ = lean_ctor_get(v_header_388_, 0);
v_isModule_390_ = lean_ctor_get_uint8(v_header_388_, sizeof(void*)*1);
if (v_isModule_390_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = ((lean_object*)(l_Lake_ppModuleHeader___closed__0));
v___y_392_ = v___x_403_;
goto v___jp_391_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_Lake_ppModuleHeader___closed__1));
v___y_392_ = v___x_404_;
goto v___jp_391_;
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_array_get_size(v_imports_389_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_inc_ref(v___y_392_);
return v___y_392_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = lean_nat_dec_le(v___x_394_, v___x_394_);
if (v___x_396_ == 0)
{
if (v___x_395_ == 0)
{
lean_inc_ref(v___y_392_);
return v___y_392_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_394_);
lean_inc_ref(v___y_392_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_390_, v_imports_389_, v___x_397_, v___x_398_, v___y_392_);
return v___x_399_;
}
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_394_);
lean_inc_ref(v___y_392_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_390_, v_imports_389_, v___x_400_, v___x_401_, v___y_392_);
return v___x_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader___boxed(lean_object* v_header_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lake_ppModuleHeader(v_header_405_);
lean_dec_ref(v_header_405_);
return v_res_406_;
}
}
lean_object* runtime_initialize_Lean_Setup(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_OutFormat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_OutFormat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Setup(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_OutFormat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_OutFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_OutFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_OutFormat(builtin);
}
#ifdef __cplusplus
}
#endif
