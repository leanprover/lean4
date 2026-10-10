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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instQueryText___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryText___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instQueryText___redArg___closed__0 = (const lean_object*)&l_Lake_instQueryText___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg();
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instQueryJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryJson___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instQueryJson___redArg___closed__0 = (const lean_object*)&l_Lake_instQueryJson___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg();
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg___boxed(lean_object*);
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
lean_object* l_Lake_OutFormat_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_OutFormat_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_OutFormat_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_OutFormat_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_OutFormat_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lake_OutFormat_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_OutFormat_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_OutFormat_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_OutFormat_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___redArg(lean_object* v_text_24_){
_start:
{
lean_inc(v_text_24_);
return v_text_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___redArg___boxed(lean_object* v_text_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_OutFormat_text_elim___redArg(v_text_25_);
lean_dec(v_text_25_);
return v_res_26_;
}
}
lean_object* l_Lake_OutFormat_text_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_text_30_){
_start:
{
lean_inc(v_text_30_);
return v_text_30_;
}
}
LEAN_EXPORT void l_Lake_OutFormat_text_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_text_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_OutFormat_text_elim(lean_box(0), v_t_28_, lean_box(0), v_text_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_text_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_text_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_OutFormat_text_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_text_35_);
lean_dec(v_text_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___redArg(lean_object* v_json_38_){
_start:
{
lean_inc(v_json_38_);
return v_json_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___redArg___boxed(lean_object* v_json_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_OutFormat_json_elim___redArg(v_json_39_);
lean_dec(v_json_39_);
return v_res_40_;
}
}
lean_object* l_Lake_OutFormat_json_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_json_44_){
_start:
{
lean_inc(v_json_44_);
return v_json_44_;
}
}
LEAN_EXPORT void l_Lake_OutFormat_json_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_json_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_OutFormat_json_elim(lean_box(0), v_t_42_, lean_box(0), v_json_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lake_OutFormat_json_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_json_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_OutFormat_json_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_json_49_);
lean_dec(v_json_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___redArg(lean_object* v_inst_52_){
_start:
{
lean_inc_ref(v_inst_52_);
return v_inst_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___redArg___boxed(lean_object* v_inst_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_instToTextOfToString___redArg(v_inst_53_);
lean_dec_ref(v_inst_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_){
_start:
{
lean_inc_ref(v_inst_56_);
return v_inst_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextOfToString___boxed(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_instToTextOfToString(v_00_u03b1_57_, v_inst_58_);
lean_dec_ref(v_inst_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_listToLines___redArg___lam__0(lean_object* v_f_61_, lean_object* v_x1_62_, lean_object* v_x2_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_apply_1(v_f_61_, v_x2_63_);
v___x_65_ = lean_string_append(v_x1_62_, v___x_64_);
lean_dec_ref(v___x_64_);
v___x_66_ = ((lean_object*)(l_Lake_listToLines___redArg___lam__0___closed__0));
v___x_67_ = lean_string_append(v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_listToLines___redArg(lean_object* v_as_69_, lean_object* v_f_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___f_71_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_71_, 0, v_f_70_);
v___x_72_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_73_ = l_List_foldl___redArg(v___f_71_, v___x_72_, v_as_69_);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_string_utf8_byte_size(v___x_73_);
lean_inc(v___x_73_);
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v___x_73_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
v___x_78_ = l_String_Slice_Pos_prevn(v___x_77_, v___x_76_, v___x_74_);
lean_dec_ref_known(v___x_77_, 3);
v___x_79_ = lean_string_utf8_extract_fast(v___x_73_, v___x_75_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_73_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_listToLines(lean_object* v_00_u03b1_80_, lean_object* v_as_81_, lean_object* v_f_82_){
_start:
{
lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___f_83_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_83_, 0, v_f_82_);
v___x_84_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_85_ = l_List_foldl___redArg(v___f_83_, v___x_84_, v_as_81_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_string_utf8_byte_size(v___x_85_);
lean_inc(v___x_85_);
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_85_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
v___x_90_ = l_String_Slice_Pos_prevn(v___x_89_, v___x_88_, v___x_86_);
lean_dec_ref_known(v___x_89_, 3);
v___x_91_ = lean_string_utf8_extract_fast(v___x_85_, v___x_87_, v___x_90_);
lean_dec(v___x_90_);
lean_dec(v___x_85_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_arrayToLines___redArg(lean_object* v_as_111_, lean_object* v_f_112_){
_start:
{
lean_object* v___y_114_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_121_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_array_get_size(v_as_111_);
v___x_124_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v___x_125_ = lean_nat_dec_lt(v___x_122_, v___x_123_);
if (v___x_125_ == 0)
{
lean_dec_ref(v_f_112_);
lean_dec_ref(v_as_111_);
v___y_114_ = v___x_121_;
goto v___jp_113_;
}
else
{
lean_object* v___f_126_; uint8_t v___x_127_; 
v___f_126_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_126_, 0, v_f_112_);
v___x_127_ = lean_nat_dec_le(v___x_123_, v___x_123_);
if (v___x_127_ == 0)
{
if (v___x_125_ == 0)
{
lean_dec_ref(v___f_126_);
lean_dec_ref(v_as_111_);
v___y_114_ = v___x_121_;
goto v___jp_113_;
}
else
{
size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v___x_128_ = ((size_t)0ULL);
v___x_129_ = lean_usize_of_nat(v___x_123_);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_124_, v___f_126_, v_as_111_, v___x_128_, v___x_129_, v___x_121_);
v___y_114_ = v___x_130_;
goto v___jp_113_;
}
}
else
{
size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_123_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_124_, v___f_126_, v_as_111_, v___x_131_, v___x_132_, v___x_121_);
v___y_114_ = v___x_133_;
goto v___jp_113_;
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_string_utf8_byte_size(v___y_114_);
lean_inc_ref(v___y_114_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v___y_114_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
v___x_119_ = l_String_Slice_Pos_prevn(v___x_118_, v___x_117_, v___x_115_);
lean_dec_ref_known(v___x_118_, 3);
v___x_120_ = lean_string_utf8_extract_fast(v___y_114_, v___x_116_, v___x_119_);
lean_dec(v___x_119_);
lean_dec_ref(v___y_114_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_arrayToLines(lean_object* v_00_u03b1_134_, lean_object* v_as_135_, lean_object* v_f_136_){
_start:
{
lean_object* v___y_138_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_145_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_array_get_size(v_as_135_);
v___x_148_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v___x_149_ = lean_nat_dec_lt(v___x_146_, v___x_147_);
if (v___x_149_ == 0)
{
lean_dec_ref(v_f_136_);
lean_dec_ref(v_as_135_);
v___y_138_ = v___x_145_;
goto v___jp_137_;
}
else
{
lean_object* v___f_150_; uint8_t v___x_151_; 
v___f_150_ = lean_alloc_closure((void*)(l_Lake_listToLines___redArg___lam__0), 3, 1);
lean_closure_set(v___f_150_, 0, v_f_136_);
v___x_151_ = lean_nat_dec_le(v___x_147_, v___x_147_);
if (v___x_151_ == 0)
{
if (v___x_149_ == 0)
{
lean_dec_ref(v___f_150_);
lean_dec_ref(v_as_135_);
v___y_138_ = v___x_145_;
goto v___jp_137_;
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_147_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_148_, v___f_150_, v_as_135_, v___x_152_, v___x_153_, v___x_145_);
v___y_138_ = v___x_154_;
goto v___jp_137_;
}
}
else
{
size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((size_t)0ULL);
v___x_156_ = lean_usize_of_nat(v___x_147_);
v___x_157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_148_, v___f_150_, v_as_135_, v___x_155_, v___x_156_, v___x_145_);
v___y_138_ = v___x_157_;
goto v___jp_137_;
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_string_utf8_byte_size(v___y_138_);
lean_inc_ref(v___y_138_);
v___x_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_142_, 0, v___y_138_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
lean_ctor_set(v___x_142_, 2, v___x_141_);
v___x_143_ = l_String_Slice_Pos_prevn(v___x_142_, v___x_141_, v___x_139_);
lean_dec_ref_known(v___x_142_, 3);
v___x_144_ = lean_string_utf8_extract_fast(v___y_138_, v___x_140_, v___x_143_);
lean_dec(v___x_143_);
lean_dec_ref(v___y_138_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg___lam__0(lean_object* v_inst_160_, lean_object* v_x1_161_, lean_object* v_x2_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_apply_1(v_inst_160_, v_x2_162_);
v___x_164_ = lean_string_append(v_x1_161_, v___x_163_);
lean_dec_ref(v___x_163_);
v___x_165_ = ((lean_object*)(l_Lake_listToLines___redArg___lam__0___closed__0));
v___x_166_ = lean_string_append(v___x_164_, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg___lam__1(lean_object* v___f_167_, lean_object* v_x_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_169_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_170_ = l_List_foldl___redArg(v___f_167_, v___x_169_, v_x_168_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_string_utf8_byte_size(v___x_170_);
lean_inc(v___x_170_);
v___x_174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_170_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
v___x_175_ = l_String_Slice_Pos_prevn(v___x_174_, v___x_173_, v___x_171_);
lean_dec_ref_known(v___x_174_, 3);
v___x_176_ = lean_string_utf8_extract_fast(v___x_170_, v___x_172_, v___x_175_);
lean_dec(v___x_175_);
lean_dec(v___x_170_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList___redArg(lean_object* v_inst_177_){
_start:
{
lean_object* v___f_178_; lean_object* v___f_179_; 
v___f_178_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_178_, 0, v_inst_177_);
v___f_179_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_179_, 0, v___f_178_);
return v___f_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextList(lean_object* v_00_u03b1_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lake_instToTextList___redArg(v_inst_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextArray___redArg___lam__1(lean_object* v___f_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___y_186_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_193_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_array_get_size(v_x_184_);
v___x_196_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v___x_197_ = lean_nat_dec_lt(v___x_194_, v___x_195_);
if (v___x_197_ == 0)
{
lean_dec_ref(v_x_184_);
lean_dec_ref(v___f_183_);
v___y_186_ = v___x_193_;
goto v___jp_185_;
}
else
{
size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_of_nat(v___x_195_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_196_, v___f_183_, v_x_184_, v___x_198_, v___x_199_, v___x_193_);
v___y_186_ = v___x_200_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_string_utf8_byte_size(v___y_186_);
lean_inc_ref(v___y_186_);
v___x_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_190_, 0, v___y_186_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_189_);
v___x_191_ = l_String_Slice_Pos_prevn(v___x_190_, v___x_189_, v___x_187_);
lean_dec_ref_known(v___x_190_, 3);
v___x_192_ = lean_string_utf8_extract_fast(v___y_186_, v___x_188_, v___x_191_);
lean_dec(v___x_191_);
lean_dec_ref(v___y_186_);
return v___x_192_;
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
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg___lam__0(lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg___lam__0___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_instQueryText___redArg___lam__0(v_x_209_);
lean_dec(v_x_209_);
return v_res_210_;
}
}
lean_object* l_Lake_instQueryText___redArg(){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = ((lean_object*)(l_Lake_instQueryText___redArg___closed__0));
return v___f_213_;
}
}
LEAN_EXPORT void l_Lake_instQueryText___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_214_;
v_res_214_ = l_Lake_instQueryText___redArg();
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lake_instQueryText___redArg___boxed(lean_object* v___dummy_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lake_instQueryText___redArg();
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryText(lean_object* v_00_u03b1_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = ((lean_object*)(l_Lake_instQueryText___redArg___closed__0));
return v___f_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg(lean_object* v_inst_219_){
_start:
{
lean_inc_ref(v_inst_219_);
return v_inst_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___redArg___boxed(lean_object* v_inst_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_instQueryTextOfToText___redArg(v_inst_220_);
lean_dec_ref(v_inst_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_){
_start:
{
lean_inc_ref(v_inst_223_);
return v_inst_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextOfToText___boxed(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lake_instQueryTextOfToText(v_00_u03b1_224_, v_inst_225_);
lean_dec_ref(v_inst_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextList___redArg(lean_object* v_inst_227_){
_start:
{
lean_object* v___f_228_; lean_object* v___f_229_; 
v___f_228_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_228_, 0, v_inst_227_);
v___f_229_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_229_, 0, v___f_228_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextList(lean_object* v_00_u03b1_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lake_instQueryTextList___redArg(v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray___redArg(lean_object* v_inst_233_){
_start:
{
lean_object* v___f_234_; lean_object* v___f_235_; 
v___f_234_ = lean_alloc_closure((void*)(l_Lake_instToTextList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_234_, 0, v_inst_233_);
v___f_235_ = lean_alloc_closure((void*)(l_Lake_instToTextArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_235_, 0, v___f_234_);
return v___f_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextArray(lean_object* v_00_u03b1_236_, lean_object* v_inst_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lake_instQueryTextArray___redArg(v_inst_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg___lam__0(lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg___lam__0___boxed(lean_object* v_x_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_instQueryJson___redArg___lam__0(v_x_245_);
lean_dec(v_x_245_);
return v_res_246_;
}
}
lean_object* l_Lake_instQueryJson___redArg(){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = ((lean_object*)(l_Lake_instQueryJson___redArg___closed__0));
return v___f_249_;
}
}
LEAN_EXPORT void l_Lake_instQueryJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_250_;
v_res_250_ = l_Lake_instQueryJson___redArg();
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson___redArg___boxed(lean_object* v___dummy_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_instQueryJson___redArg();
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJson(lean_object* v_00_u03b1_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = ((lean_object*)(l_Lake_instQueryJson___redArg___closed__0));
return v___f_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg(lean_object* v_inst_255_){
_start:
{
lean_inc_ref(v_inst_255_);
return v_inst_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___redArg___boxed(lean_object* v_inst_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lake_instQueryJsonOfToJson___redArg(v_inst_256_);
lean_dec_ref(v_inst_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_){
_start:
{
lean_inc_ref(v_inst_259_);
return v_inst_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonOfToJson___boxed(lean_object* v_00_u03b1_260_, lean_object* v_inst_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lake_instQueryJsonOfToJson(v_00_u03b1_260_, v_inst_261_);
lean_dec_ref(v_inst_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__0(lean_object* v_inst_263_, lean_object* v_x_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_apply_1(v_inst_263_, v_x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg___lam__1(lean_object* v___f_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; size_t v_sz_270_; size_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_268_ = lean_array_mk(v_x_267_);
v___x_269_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v_sz_270_ = lean_array_size(v___x_268_);
v___x_271_ = ((size_t)0ULL);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_269_, v___f_266_, v_sz_270_, v___x_271_, v___x_268_);
v___x_273_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList___redArg(lean_object* v_inst_274_){
_start:
{
lean_object* v___f_275_; lean_object* v___f_276_; 
v___f_275_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_275_, 0, v_inst_274_);
v___f_276_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_276_, 0, v___f_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonList(lean_object* v_00_u03b1_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lake_instQueryJsonList___redArg(v_inst_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg___lam__1(lean_object* v___f_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___x_282_; size_t v_sz_283_; size_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_282_ = ((lean_object*)(l_Lake_arrayToLines___redArg___closed__9));
v_sz_283_ = lean_array_size(v_x_281_);
v___x_284_ = ((size_t)0ULL);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_282_, v___f_280_, v_sz_283_, v___x_284_, v_x_281_);
v___x_286_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray___redArg(lean_object* v_inst_287_){
_start:
{
lean_object* v___f_288_; lean_object* v___f_289_; 
v___f_288_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_288_, 0, v_inst_287_);
v___f_289_ = lean_alloc_closure((void*)(l_Lake_instQueryJsonArray___redArg___lam__1), 2, 1);
lean_closure_set(v___f_289_, 0, v___f_288_);
return v___f_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonArray(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lake_instQueryJsonArray___redArg(v_inst_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object* v_x_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson___redArg(lean_object* v_inst_297_, lean_object* v_inst_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_inst_297_);
lean_ctor_set(v___x_299_, 1, v_inst_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_instFormatQueryOfQueryTextOfQueryJson(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_inst_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_inst_301_);
lean_ctor_set(v___x_303_, 1, v_inst_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lake_nullFormat___redArg___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(0);
v___x_305_ = l_Lean_Json_compress(v___x_304_);
return v___x_305_;
}
}
lean_object* l_Lake_nullFormat___redArg(uint8_t v_fmt_306_){
_start:
{
if (v_fmt_306_ == 0)
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Lake_listToLines___redArg___closed__0));
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = lean_obj_once(&l_Lake_nullFormat___redArg___closed__0, &l_Lake_nullFormat___redArg___closed__0_once, _init_l_Lake_nullFormat___redArg___closed__0);
return v___x_308_;
}
}
}
LEAN_EXPORT void l_Lake_nullFormat___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_306_ = stack[0].m_num;
lean_object* v_res_309_;
v_res_309_ = l_Lake_nullFormat___redArg(v_fmt_306_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___redArg___boxed(lean_object* v_fmt_310_){
_start:
{
uint8_t v_fmt_boxed_311_; lean_object* v_res_312_; 
v_fmt_boxed_311_ = lean_unbox(v_fmt_310_);
v_res_312_ = l_Lake_nullFormat___redArg(v_fmt_boxed_311_);
return v_res_312_;
}
}
lean_object* l_Lake_nullFormat(lean_object* v_00_u03b1_313_, uint8_t v_fmt_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lake_nullFormat___redArg(v_fmt_314_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Lake_nullFormat_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_314_ = stack[1].m_num;
lean_object* v_x_315_ = stack[2].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Lake_nullFormat(lean_box(0), v_fmt_314_, v_x_315_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lake_nullFormat___boxed(lean_object* v_00_u03b1_318_, lean_object* v_fmt_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_fmt_boxed_321_; lean_object* v_res_322_; 
v_fmt_boxed_321_ = lean_unbox(v_fmt_319_);
v_res_322_ = l_Lake_nullFormat(v_00_u03b1_318_, v_fmt_boxed_321_, v_x_320_);
lean_dec(v_x_320_);
return v_res_322_;
}
}
lean_object* l_Lake_formatQuery___redArg(lean_object* v_inst_323_, uint8_t v_fmt_324_, lean_object* v_a_325_){
_start:
{
if (v_fmt_324_ == 0)
{
lean_object* v_toQueryText_326_; lean_object* v___x_327_; 
v_toQueryText_326_ = lean_ctor_get(v_inst_323_, 0);
lean_inc_ref(v_toQueryText_326_);
lean_dec_ref(v_inst_323_);
v___x_327_ = lean_apply_1(v_toQueryText_326_, v_a_325_);
return v___x_327_;
}
else
{
lean_object* v_toQueryJson_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_toQueryJson_328_ = lean_ctor_get(v_inst_323_, 1);
lean_inc_ref(v_toQueryJson_328_);
lean_dec_ref(v_inst_323_);
v___x_329_ = lean_apply_1(v_toQueryJson_328_, v_a_325_);
v___x_330_ = l_Lean_Json_compress(v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_323_ = stack[0].m_obj;
uint8_t v_fmt_324_ = stack[1].m_num;
lean_object* v_a_325_ = stack[2].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_Lake_formatQuery___redArg(v_inst_323_, v_fmt_324_, v_a_325_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___redArg___boxed(lean_object* v_inst_332_, lean_object* v_fmt_333_, lean_object* v_a_334_){
_start:
{
uint8_t v_fmt_boxed_335_; lean_object* v_res_336_; 
v_fmt_boxed_335_ = lean_unbox(v_fmt_333_);
v_res_336_ = l_Lake_formatQuery___redArg(v_inst_332_, v_fmt_boxed_335_, v_a_334_);
return v_res_336_;
}
}
lean_object* l_Lake_formatQuery(lean_object* v_00_u03b1_337_, lean_object* v_inst_338_, uint8_t v_fmt_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lake_formatQuery___redArg(v_inst_338_, v_fmt_339_, v_a_340_);
return v___x_341_;
}
}
LEAN_EXPORT void l_Lake_formatQuery_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_338_ = stack[1].m_obj;
uint8_t v_fmt_339_ = stack[2].m_num;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lake_formatQuery(lean_box(0), v_inst_338_, v_fmt_339_, v_a_340_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___boxed(lean_object* v_00_u03b1_343_, lean_object* v_inst_344_, lean_object* v_fmt_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_fmt_boxed_347_; lean_object* v_res_348_; 
v_fmt_boxed_347_ = lean_unbox(v_fmt_345_);
v_res_348_ = l_Lake_formatQuery(v_00_u03b1_343_, v_inst_344_, v_fmt_boxed_347_, v_a_346_);
return v_res_348_;
}
}
lean_object* l_Lake_ppImport(lean_object* v_imp_353_, uint8_t v_isModule_354_, lean_object* v_init_355_){
_start:
{
lean_object* v_s_357_; lean_object* v_s_363_; lean_object* v_s_370_; 
if (v_isModule_354_ == 0)
{
v_s_370_ = v_init_355_;
goto v___jp_369_;
}
else
{
uint8_t v_isExported_374_; 
v_isExported_374_ = lean_ctor_get_uint8(v_imp_353_, sizeof(void*)*1 + 1);
if (v_isExported_374_ == 0)
{
v_s_370_ = v_init_355_;
goto v___jp_369_;
}
else
{
lean_object* v___x_375_; lean_object* v_s_376_; 
v___x_375_ = ((lean_object*)(l_Lake_ppImport___closed__3));
v_s_376_ = lean_string_append(v_init_355_, v___x_375_);
v_s_370_ = v_s_376_;
goto v___jp_369_;
}
}
v___jp_356_:
{
lean_object* v_module_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v_s_361_; 
v_module_358_ = lean_ctor_get(v_imp_353_, 0);
lean_inc(v_module_358_);
lean_dec_ref(v_imp_353_);
v___x_359_ = 1;
v___x_360_ = l_Lean_Name_toString(v_module_358_, v___x_359_);
v_s_361_ = lean_string_append(v_s_357_, v___x_360_);
lean_dec_ref(v___x_360_);
return v_s_361_;
}
v___jp_362_:
{
uint8_t v_importAll_364_; lean_object* v___x_365_; lean_object* v_s_366_; 
v_importAll_364_ = lean_ctor_get_uint8(v_imp_353_, sizeof(void*)*1);
v___x_365_ = ((lean_object*)(l_Lake_ppImport___closed__0));
v_s_366_ = lean_string_append(v_s_363_, v___x_365_);
if (v_importAll_364_ == 0)
{
v_s_357_ = v_s_366_;
goto v___jp_356_;
}
else
{
lean_object* v___x_367_; lean_object* v_s_368_; 
v___x_367_ = ((lean_object*)(l_Lake_ppImport___closed__1));
v_s_368_ = lean_string_append(v_s_366_, v___x_367_);
v_s_357_ = v_s_368_;
goto v___jp_356_;
}
}
v___jp_369_:
{
uint8_t v_isMeta_371_; 
v_isMeta_371_ = lean_ctor_get_uint8(v_imp_353_, sizeof(void*)*1 + 2);
if (v_isMeta_371_ == 0)
{
v_s_363_ = v_s_370_;
goto v___jp_362_;
}
else
{
lean_object* v___x_372_; lean_object* v_s_373_; 
v___x_372_ = ((lean_object*)(l_Lake_ppImport___closed__2));
v_s_373_ = lean_string_append(v_s_370_, v___x_372_);
v_s_363_ = v_s_373_;
goto v___jp_362_;
}
}
}
}
LEAN_EXPORT void l_Lake_ppImport_0interp(lean_interpreter_value* stack)
{
lean_object* v_imp_353_ = stack[0].m_obj;
uint8_t v_isModule_354_ = stack[1].m_num;
lean_object* v_init_355_ = stack[2].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lake_ppImport(v_imp_353_, v_isModule_354_, v_init_355_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lake_ppImport___boxed(lean_object* v_imp_378_, lean_object* v_isModule_379_, lean_object* v_init_380_){
_start:
{
uint8_t v_isModule_boxed_381_; lean_object* v_res_382_; 
v_isModule_boxed_381_ = lean_unbox(v_isModule_379_);
v_res_382_ = l_Lake_ppImport(v_imp_378_, v_isModule_boxed_381_, v_init_380_);
return v_res_382_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(uint8_t v_isModule_383_, lean_object* v_as_384_, size_t v_i_385_, size_t v_stop_386_, lean_object* v_b_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_eq(v_i_385_, v_stop_386_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint32_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; size_t v___x_393_; size_t v___x_394_; 
v___x_389_ = lean_array_uget_borrowed(v_as_384_, v_i_385_);
v___x_390_ = 10;
v___x_391_ = lean_string_push(v_b_387_, v___x_390_);
lean_inc(v___x_389_);
v___x_392_ = l_Lake_ppImport(v___x_389_, v_isModule_383_, v___x_391_);
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_add(v_i_385_, v___x_393_);
v_i_385_ = v___x_394_;
v_b_387_ = v___x_392_;
goto _start;
}
else
{
return v_b_387_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_isModule_383_ = stack[0].m_num;
lean_object* v_as_384_ = stack[1].m_obj;
size_t v_i_385_ = stack[2].m_num;
size_t v_stop_386_ = stack[3].m_num;
lean_object* v_b_387_ = stack[4].m_obj;
lean_object* v_res_396_;
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_383_, v_as_384_, v_i_385_, v_stop_386_, v_b_387_);
stack->m_obj
 = v_res_396_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0___boxed(lean_object* v_isModule_397_, lean_object* v_as_398_, lean_object* v_i_399_, lean_object* v_stop_400_, lean_object* v_b_401_){
_start:
{
uint8_t v_isModule_boxed_402_; size_t v_i_boxed_403_; size_t v_stop_boxed_404_; lean_object* v_res_405_; 
v_isModule_boxed_402_ = lean_unbox(v_isModule_397_);
v_i_boxed_403_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_stop_boxed_404_ = lean_unbox_usize(v_stop_400_);
lean_dec(v_stop_400_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_boxed_402_, v_as_398_, v_i_boxed_403_, v_stop_boxed_404_, v_b_401_);
lean_dec_ref(v_as_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader(lean_object* v_header_408_){
_start:
{
lean_object* v_imports_409_; uint8_t v_isModule_410_; lean_object* v___y_412_; 
v_imports_409_ = lean_ctor_get(v_header_408_, 0);
v_isModule_410_ = lean_ctor_get_uint8(v_header_408_, sizeof(void*)*1);
if (v_isModule_410_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Lake_ppModuleHeader___closed__0));
v___y_412_ = v___x_423_;
goto v___jp_411_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Lake_ppModuleHeader___closed__1));
v___y_412_ = v___x_424_;
goto v___jp_411_;
}
v___jp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_array_get_size(v_imports_409_);
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_inc_ref(v___y_412_);
return v___y_412_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_le(v___x_414_, v___x_414_);
if (v___x_416_ == 0)
{
if (v___x_415_ == 0)
{
lean_inc_ref(v___y_412_);
return v___y_412_;
}
else
{
size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v___x_417_ = ((size_t)0ULL);
v___x_418_ = lean_usize_of_nat(v___x_414_);
lean_inc_ref(v___y_412_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_410_, v_imports_409_, v___x_417_, v___x_418_, v___y_412_);
return v___x_419_;
}
}
else
{
size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
v___x_420_ = ((size_t)0ULL);
v___x_421_ = lean_usize_of_nat(v___x_414_);
lean_inc_ref(v___y_412_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_ppModuleHeader_spec__0(v_isModule_410_, v_imports_409_, v___x_420_, v___x_421_, v___y_412_);
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ppModuleHeader___boxed(lean_object* v_header_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lake_ppModuleHeader(v_header_425_);
lean_dec_ref(v_header_425_);
return v_res_426_;
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
