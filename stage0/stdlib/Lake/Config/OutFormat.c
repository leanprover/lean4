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
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_le(v___x_191_, v___x_191_);
if (v___x_194_ == 0)
{
if (v___x_193_ == 0)
{
lean_dec_ref(v_x_180_);
lean_dec_ref(v___f_179_);
v___y_182_ = v___x_189_;
goto v___jp_181_;
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((size_t)0ULL);
v___x_196_ = lean_usize_of_nat(v___x_191_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_192_, v___f_179_, v_x_180_, v___x_195_, v___x_196_, v___x_189_);
v___y_182_ = v___x_197_;
goto v___jp_181_;
}
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_191_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_192_, v___f_179_, v_x_180_, v___x_198_, v___x_199_, v___x_189_);
v___y_182_ = v___x_200_;
goto v___jp_181_;
}
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
LEAN_EXPORT lean_object* l_Lake_instToTextArray___redArg(lean_object* v_inst_201_){
_start:
{
lean_object* v___f_202_; lean_object* v___f_203_; 
v___f_202_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_202_, 0, v_inst_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Lake_instToTextArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_203_, 0, v___f_202_);
return v___f_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray(lean_object* v_00_u03b1_204_, lean_object* v_inst_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lake_instToTextArray___redArg(v_inst_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText___lam__0(lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText___lam__0___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_instQueryText___lam__0(v_x_209_);
lean_dec(v_x_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText(lean_object* v_00_u03b1_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = ((lean_object*)(l_Lake_instQueryText___closed__0));
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg(lean_object* v_inst_214_){
_start:
{
lean_inc_ref(v_inst_214_);
return v_inst_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg___boxed(lean_object* v_inst_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lake_instQueryTextOfToText___redArg(v_inst_215_);
lean_dec_ref(v_inst_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_){
_start:
{
lean_inc_ref(v_inst_218_);
return v_inst_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___boxed(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_instQueryTextOfToText(v_00_u03b1_219_, v_inst_220_);
lean_dec_ref(v_inst_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextList___redArg(lean_object* v_inst_222_){
_start:
{
lean_object* v___f_223_; lean_object* v___f_224_; 
v___f_223_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_223_, 0, v_inst_222_);
v___f_224_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_224_, 0, v___f_223_);
return v___f_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextList(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lake_instQueryTextList___redArg(v_inst_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray___redArg(lean_object* v_inst_228_){
_start:
{
lean_object* v___f_229_; lean_object* v___f_230_; 
v___f_229_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_229_, 0, v_inst_228_);
v___f_230_ = lean_alloc_closure((void*)(l_Lake_instToTextArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_230_, 0, v___f_229_);
return v___f_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lake_instQueryTextArray___redArg(v_inst_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___lam__0(lean_object* v_x_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___lam__0___boxed(lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_instQueryJson___lam__0(v_x_240_);
lean_dec(v_x_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson(lean_object* v_00_u03b1_243_){
_start:
{
lean_object* v___f_244_; 
v___f_244_ = ((lean_object*)(l_Lake_instQueryJson___closed__0));
return v___f_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg(lean_object* v_inst_245_){
_start:
{
lean_inc_ref(v_inst_245_);
return v_inst_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg___boxed(lean_object* v_inst_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_instQueryJsonOfToJson___redArg(v_inst_246_);
lean_dec_ref(v_inst_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_){
_start:
{
lean_inc_ref(v_inst_249_);
return v_inst_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___boxed(lean_object* v_00_u03b1_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_instQueryJsonOfToJson(v_00_u03b1_250_, v_inst_251_);
lean_dec_ref(v_inst_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__0(lean_object* v_inst_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_apply_1(v_inst_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__1(lean_object* v___f_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; size_t v_sz_260_; size_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_258_ = lean_array_mk(v_x_257_);
v___x_259_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v_sz_260_ = lean_array_size(v___x_258_);
v___x_261_ = ((size_t)0ULL);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_259_, v___f_256_, v_sz_260_, v___x_261_, v___x_258_);
v___x_263_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg(lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; lean_object* v___f_266_; 
v___f_265_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_265_, 0, v_inst_264_);
v___f_266_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_266_, 0, v___f_265_);
return v___f_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lake_instQueryJsonList___redArg(v_inst_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg___lam__1(lean_object* v___f_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; size_t v_sz_273_; size_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v_sz_273_ = lean_array_size(v_x_271_);
v___x_274_ = ((size_t)0ULL);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_272_, v___f_270_, v_sz_273_, v___x_274_, v_x_271_);
v___x_276_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg(lean_object* v_inst_277_){
_start:
{
lean_object* v___f_278_; lean_object* v___f_279_; 
v___f_278_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_278_, 0, v_inst_277_);
v___f_279_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_279_, 0, v___f_278_);
return v___f_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray(lean_object* v_00_u03b1_280_, lean_object* v_inst_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lake_instQueryJsonArray___redArg(v_inst_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_box(0);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson___redArg(lean_object* v_inst_287_, lean_object* v_inst_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_inst_287_);
lean_ctor_set(v___x_289_, 1, v_inst_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_inst_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_inst_291_);
lean_ctor_set(v___x_293_, 1, v_inst_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lake_nullFormat___redArg___closed__0(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
v___x_295_ = l_Lean_Json_compress(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg(uint8_t v_fmt_296_){
_start:
{
if (v_fmt_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lake_nullFormat___redArg___closed__0, &l_Lake_nullFormat___redArg___closed__0_once, _init_l_Lake_nullFormat___redArg___closed__0);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg___boxed(lean_object* v_fmt_299_){
_start:
{
uint8_t v_fmt_boxed_300_; lean_object* v_res_301_; 
v_fmt_boxed_300_ = lean_unbox(v_fmt_299_);
v_res_301_ = l_Lake_nullFormat___redArg(v_fmt_boxed_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat(lean_object* v_00_u03b1_302_, uint8_t v_fmt_303_, lean_object* v_x_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lake_nullFormat___redArg(v_fmt_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___boxed(lean_object* v_00_u03b1_306_, lean_object* v_fmt_307_, lean_object* v_x_308_){
_start:
{
uint8_t v_fmt_boxed_309_; lean_object* v_res_310_; 
v_fmt_boxed_309_ = lean_unbox(v_fmt_307_);
v_res_310_ = l_Lake_nullFormat(v_00_u03b1_306_, v_fmt_boxed_309_, v_x_308_);
lean_dec(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg(lean_object* v_inst_311_, uint8_t v_fmt_312_, lean_object* v_a_313_){
_start:
{
if (v_fmt_312_ == 0)
{
lean_object* v_toQueryText_314_; lean_object* v___x_315_; 
v_toQueryText_314_ = lean_ctor_get(v_inst_311_, 0);
lean_inc_ref(v_toQueryText_314_);
lean_dec_ref(v_inst_311_);
v___x_315_ = lean_apply_1(v_toQueryText_314_, v_a_313_);
return v___x_315_;
}
else
{
lean_object* v_toQueryJson_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_toQueryJson_316_ = lean_ctor_get(v_inst_311_, 1);
lean_inc_ref(v_toQueryJson_316_);
lean_dec_ref(v_inst_311_);
v___x_317_ = lean_apply_1(v_toQueryJson_316_, v_a_313_);
v___x_318_ = l_Lean_Json_compress(v___x_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg___boxed(lean_object* v_inst_319_, lean_object* v_fmt_320_, lean_object* v_a_321_){
_start:
{
uint8_t v_fmt_boxed_322_; lean_object* v_res_323_; 
v_fmt_boxed_322_ = lean_unbox(v_fmt_320_);
v_res_323_ = l_Lake_formatQuery___redArg(v_inst_319_, v_fmt_boxed_322_, v_a_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, uint8_t v_fmt_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lake_formatQuery___redArg(v_inst_325_, v_fmt_326_, v_a_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___boxed(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_fmt_331_, lean_object* v_a_332_){
_start:
{
uint8_t v_fmt_boxed_333_; lean_object* v_res_334_; 
v_fmt_boxed_333_ = lean_unbox(v_fmt_331_);
v_res_334_ = l_Lake_formatQuery(v_00_u03b1_329_, v_inst_330_, v_fmt_boxed_333_, v_a_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lake_ppImport(lean_object* v_imp_339_, uint8_t v_isModule_340_, lean_object* v_init_341_){
_start:
{
lean_object* v_s_343_; lean_object* v_s_349_; lean_object* v_s_356_; 
if (v_isModule_340_ == 0)
{
v_s_356_ = v_init_341_;
goto v___jp_355_;
}
else
{
uint8_t v_isExported_360_; 
v_isExported_360_ = lean_ctor_get_uint8(v_imp_339_, sizeof(void*)*1 + 1);
if (v_isExported_360_ == 0)
{
v_s_356_ = v_init_341_;
goto v___jp_355_;
}
else
{
lean_object* v___x_361_; lean_object* v_s_362_; 
v___x_361_ = ((lean_object*)(l_Lake_ppImport___closed__3));
v_s_362_ = lean_string_append(v_init_341_, v___x_361_);
v_s_356_ = v_s_362_;
goto v___jp_355_;
}
}
v___jp_342_:
{
lean_object* v_module_344_; uint8_t v___x_345_; lean_object* v___x_346_; lean_object* v_s_347_; 
v_module_344_ = lean_ctor_get(v_imp_339_, 0);
lean_inc(v_module_344_);
lean_dec_ref(v_imp_339_);
v___x_345_ = 1;
v___x_346_ = l_Lean_Name_toString(v_module_344_, v___x_345_);
v_s_347_ = lean_string_append(v_s_343_, v___x_346_);
lean_dec_ref(v___x_346_);
return v_s_347_;
}
v___jp_348_:
{
uint8_t v_importAll_350_; lean_object* v___x_351_; lean_object* v_s_352_; 
v_importAll_350_ = lean_ctor_get_uint8(v_imp_339_, sizeof(void*)*1);
v___x_351_ = ((lean_object*)(l_Lake_ppImport___closed__0));
v_s_352_ = lean_string_append(v_s_349_, v___x_351_);
if (v_importAll_350_ == 0)
{
v_s_343_ = v_s_352_;
goto v___jp_342_;
}
else
{
lean_object* v___x_353_; lean_object* v_s_354_; 
v___x_353_ = ((lean_object*)(l_Lake_ppImport___closed__1));
v_s_354_ = lean_string_append(v_s_352_, v___x_353_);
v_s_343_ = v_s_354_;
goto v___jp_342_;
}
}
v___jp_355_:
{
uint8_t v_isMeta_357_; 
v_isMeta_357_ = lean_ctor_get_uint8(v_imp_339_, sizeof(void*)*1 + 2);
if (v_isMeta_357_ == 0)
{
v_s_349_ = v_s_356_;
goto v___jp_348_;
}
else
{
lean_object* v___x_358_; lean_object* v_s_359_; 
v___x_358_ = ((lean_object*)(l_Lake_ppImport___closed__2));
v_s_359_ = lean_string_append(v_s_356_, v___x_358_);
v_s_349_ = v_s_359_;
goto v___jp_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ppImport___boxed(lean_object* v_imp_363_, lean_object* v_isModule_364_, lean_object* v_init_365_){
_start:
{
uint8_t v_isModule_boxed_366_; lean_object* v_res_367_; 
v_isModule_boxed_366_ = lean_unbox(v_isModule_364_);
v_res_367_ = l_Lake_ppImport(v_imp_363_, v_isModule_boxed_366_, v_init_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(uint8_t v_isModule_368_, lean_object* v_as_369_, size_t v_i_370_, size_t v_stop_371_, lean_object* v_b_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_eq(v_i_370_, v_stop_371_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint32_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; size_t v___x_378_; size_t v___x_379_; 
v___x_374_ = lean_array_uget_borrowed(v_as_369_, v_i_370_);
v___x_375_ = 10;
v___x_376_ = lean_string_push(v_b_372_, v___x_375_);
lean_inc(v___x_374_);
v___x_377_ = l_Lake_ppImport(v___x_374_, v_isModule_368_, v___x_376_);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_370_, v___x_378_);
v_i_370_ = v___x_379_;
v_b_372_ = v___x_377_;
goto _start;
}
else
{
return v_b_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0___boxed(lean_object* v_isModule_381_, lean_object* v_as_382_, lean_object* v_i_383_, lean_object* v_stop_384_, lean_object* v_b_385_){
_start:
{
uint8_t v_isModule_boxed_386_; size_t v_i_boxed_387_; size_t v_stop_boxed_388_; lean_object* v_res_389_; 
v_isModule_boxed_386_ = lean_unbox(v_isModule_381_);
v_i_boxed_387_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_stop_boxed_388_ = lean_unbox_usize(v_stop_384_);
lean_dec(v_stop_384_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_boxed_386_, v_as_382_, v_i_boxed_387_, v_stop_boxed_388_, v_b_385_);
lean_dec_ref(v_as_382_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader(lean_object* v_header_392_){
_start:
{
lean_object* v_imports_393_; uint8_t v_isModule_394_; lean_object* v___y_396_; 
v_imports_393_ = lean_ctor_get(v_header_392_, 0);
v_isModule_394_ = lean_ctor_get_uint8(v_header_392_, sizeof(void*)*1);
if (v_isModule_394_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = ((lean_object*)(l_Lake_ppModuleHeader___closed__0));
v___y_396_ = v___x_407_;
goto v___jp_395_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l_Lake_ppModuleHeader___closed__1));
v___y_396_ = v___x_408_;
goto v___jp_395_;
}
v___jp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_array_get_size(v_imports_393_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_inc_ref(v___y_396_);
return v___y_396_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_le(v___x_398_, v___x_398_);
if (v___x_400_ == 0)
{
if (v___x_399_ == 0)
{
lean_inc_ref(v___y_396_);
return v___y_396_;
}
else
{
size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; 
v___x_401_ = ((size_t)0ULL);
v___x_402_ = lean_usize_of_nat(v___x_398_);
lean_inc_ref(v___y_396_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_394_, v_imports_393_, v___x_401_, v___x_402_, v___y_396_);
return v___x_403_;
}
}
else
{
size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v___x_404_ = ((size_t)0ULL);
v___x_405_ = lean_usize_of_nat(v___x_398_);
lean_inc_ref(v___y_396_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_394_, v_imports_393_, v___x_404_, v___x_405_, v___y_396_);
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader___boxed(lean_object* v_header_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_ppModuleHeader(v_header_409_);
lean_dec_ref(v_header_409_);
return v_res_410_;
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
