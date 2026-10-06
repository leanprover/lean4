// Lean compiler output
// Module: Lean.Data.Lsp.Diagnostics
// Imports: public import Lean.Data.Lsp.Basic public import Lean.Data.Lsp.Utf16
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson(lean_object*);
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqLocation_beq(lean_object*, lean_object*);
lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedRange_default;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLocation_toJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
uint8_t l_Lean_Lsp_instOrdLocation_ord(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedLocation_default;
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonString___lam__0(lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticSeverity_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticSeverity;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticSeverity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticSeverity_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown DiagnosticSeverity '"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticCode_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticCode_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "expected string or integer diagnostic code, got '"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticCode___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticTag_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticTag;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticTag_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticTag_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown DiagnosticTag"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanDiagnosticTag;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown LeanDiagnosticTag"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value;
static const lean_string_object l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value;
static const lean_array_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "DiagnosticRelatedInformation"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 67, 100, 141, 182, 93, 157, 48)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 206, 14, 113, 158, 249, 116, 159)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 62, 76, 216, 222, 7, 163, 13)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instBEq___private__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRange_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fullRange"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isSilent"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tags"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "leanTags"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "relatedInformation"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRange_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "DiagnosticWith"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 36, 183, 1, 15, 160, 190, 39)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(113, 10, 234, 83, 106, 95, 218, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fullRange\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(204, 14, 121, 252, 204, 139, 33, 252)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "severity\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(136, 53, 226, 217, 90, 118, 120, 32)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isSilent\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(192, 110, 237, 190, 164, 148, 251, 95)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "code\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(96, 225, 246, 128, 47, 4, 255, 46)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "source\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value),LEAN_SCALAR_PTR_LITERAL(6, 190, 134, 180, 155, 172, 192, 107)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tags\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value),LEAN_SCALAR_PTR_LITERAL(96, 97, 143, 141, 248, 70, 73, 149)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "leanTags\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value),LEAN_SCALAR_PTR_LITERAL(202, 184, 187, 33, 211, 98, 60, 106)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "relatedInformation\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value),LEAN_SCALAR_PTR_LITERAL(21, 251, 114, 194, 100, 169, 63, 219)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "data\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value),LEAN_SCALAR_PTR_LITERAL(14, 29, 170, 31, 135, 79, 138, 199)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1 = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isIncremental"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "diagnostics"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "PublishDiagnosticsParams"};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 161, 220, 51, 147, 166, 27, 251)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 169, 49, 149, 57, 117, 3, 84)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7;
static const lean_string_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12;
static const lean_string_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "isIncremental\?"};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 146, 63, 25, 119, 245, 185, 30)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(236, 43, 109, 94, 169, 251, 160, 225)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(lean_object* v_error_22_){
_start:
{
lean_inc(v_error_22_);
return v_error_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(lean_object* v_error_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(v_error_23_);
lean_dec(v_error_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_error_28_){
_start:
{
lean_inc(v_error_28_);
return v_error_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_error_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Lsp_DiagnosticSeverity_error_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_error_32_);
lean_dec(v_error_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(lean_object* v_warning_35_){
_start:
{
lean_inc(v_warning_35_);
return v_warning_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(lean_object* v_warning_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(v_warning_36_);
lean_dec(v_warning_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_warning_41_){
_start:
{
lean_inc(v_warning_41_);
return v_warning_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_warning_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_warning_45_);
lean_dec(v_warning_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(lean_object* v_information_48_){
_start:
{
lean_inc(v_information_48_);
return v_information_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(lean_object* v_information_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(v_information_49_);
lean_dec(v_information_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_information_54_){
_start:
{
lean_inc(v_information_54_);
return v_information_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_information_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Lsp_DiagnosticSeverity_information_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_information_58_);
lean_dec(v_information_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(lean_object* v_hint_61_){
_start:
{
lean_inc(v_hint_61_);
return v_hint_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(lean_object* v_hint_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(v_hint_62_);
lean_dec(v_hint_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_hint_67_){
_start:
{
lean_inc(v_hint_67_);
return v_hint_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_hint_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_hint_71_);
lean_dec(v_hint_71_);
return v_res_73_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default(void){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity(void){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticSeverity_beq(uint8_t v_x_76_, uint8_t v_y_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_78_ = lean_box(v_x_76_);
v___x_79_ = lean_obj_tag_nat(v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_box(v_y_77_);
v___x_81_ = lean_obj_tag_nat(v___x_80_);
lean_dec(v___x_80_);
v___x_82_ = lean_nat_dec_eq(v___x_79_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(lean_object* v_x_83_, lean_object* v_y_84_){
_start:
{
uint8_t v_x_24__boxed_85_; uint8_t v_y_25__boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_x_24__boxed_85_ = lean_unbox(v_x_83_);
v_y_25__boxed_86_ = lean_unbox(v_y_84_);
v_res_87_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v_x_24__boxed_85_, v_y_25__boxed_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticSeverity_ord(uint8_t v_x_91_, uint8_t v_y_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_93_ = lean_box(v_x_91_);
v___x_94_ = lean_obj_tag_nat(v___x_93_);
lean_dec(v___x_93_);
v___x_95_ = lean_box(v_y_92_);
v___x_96_ = lean_obj_tag_nat(v___x_95_);
lean_dec(v___x_95_);
v___x_97_ = lean_nat_dec_lt(v___x_94_, v___x_96_);
if (v___x_97_ == 0)
{
uint8_t v___x_98_; 
v___x_98_ = lean_nat_dec_eq(v___x_94_, v___x_96_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
v___x_99_ = 2;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 1;
return v___x_100_;
}
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(lean_object* v_x_102_, lean_object* v_y_103_){
_start:
{
uint8_t v_x_33__boxed_104_; uint8_t v_y_34__boxed_105_; uint8_t v_res_106_; lean_object* v_r_107_; 
v_x_33__boxed_104_ = lean_unbox(v_x_102_);
v_y_34__boxed_105_ = lean_unbox(v_y_103_);
v_res_106_ = l_Lean_Lsp_instOrdDiagnosticSeverity_ord(v_x_33__boxed_104_, v_y_34__boxed_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(lean_object* v_j_124_){
_start:
{
lean_object* v___x_133_; 
lean_inc(v_j_124_);
v___x_133_ = l_Lean_Json_getNat_x3f(v_j_124_);
if (lean_obj_tag(v___x_133_) == 1)
{
lean_object* v_a_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_dec_eq(v_a_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_nat_dec_eq(v_a_134_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(3u);
v___x_140_ = lean_nat_dec_eq(v_a_134_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_dec_eq(v_a_134_, v___x_141_);
lean_dec(v_a_134_);
if (v___x_142_ == 0)
{
goto v___jp_125_;
}
else
{
lean_object* v___x_143_; 
lean_dec(v_j_124_);
v___x_143_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2));
return v___x_143_;
}
}
else
{
lean_object* v___x_144_; 
lean_dec(v_a_134_);
lean_dec(v_j_124_);
v___x_144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3));
return v___x_144_;
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v_a_134_);
lean_dec(v_j_124_);
v___x_145_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4));
return v___x_145_;
}
}
else
{
lean_object* v___x_146_; 
lean_dec(v_a_134_);
lean_dec(v_j_124_);
v___x_146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5));
return v___x_146_;
}
}
else
{
lean_dec_ref(v___x_133_);
goto v___jp_125_;
}
v___jp_125_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_126_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
v___x_127_ = lean_unsigned_to_nat(80u);
v___x_128_ = l_Lean_Json_pretty(v_j_124_, v___x_127_);
v___x_129_ = lean_string_append(v___x_126_, v___x_128_);
lean_dec_ref(v___x_128_);
v___x_130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_131_ = lean_string_append(v___x_129_, v___x_130_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = l_Lean_JsonNumber_fromNat(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0);
v___x_152_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(2u);
v___x_154_ = l_Lean_JsonNumber_fromNat(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2);
v___x_156_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(3u);
v___x_158_ = l_Lean_JsonNumber_fromNat(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4);
v___x_160_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = l_Lean_JsonNumber_fromNat(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6);
v___x_164_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(uint8_t v_x_165_){
_start:
{
switch(v_x_165_)
{
case 0:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_166_;
}
case 1:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_167_;
}
case 2:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
return v___x_168_;
}
default: 
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed(lean_object* v_x_170_){
_start:
{
uint8_t v_x_106__boxed_171_; lean_object* v_res_172_; 
v_x_106__boxed_171_ = lean_unbox(v_x_170_);
v_res_172_ = l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(v_x_106__boxed_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___impl(lean_object* v_x_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_tag_nat(v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___impl___boxed(lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Lsp_DiagnosticCode_ctorIdx___impl(v_x_177_);
lean_dec_ref(v_x_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(lean_object* v_t_179_, lean_object* v_k_180_){
_start:
{
if (lean_obj_tag(v_t_179_) == 0)
{
lean_object* v_i_181_; lean_object* v___x_182_; 
v_i_181_ = lean_ctor_get(v_t_179_, 0);
lean_inc(v_i_181_);
lean_dec_ref_known(v_t_179_, 1);
v___x_182_ = lean_apply_1(v_k_180_, v_i_181_);
return v___x_182_;
}
else
{
lean_object* v_s_183_; lean_object* v___x_184_; 
v_s_183_ = lean_ctor_get(v_t_179_, 0);
lean_inc_ref(v_s_183_);
lean_dec_ref_known(v_t_179_, 1);
v___x_184_ = lean_apply_1(v_k_180_, v_s_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim(lean_object* v_motive_185_, lean_object* v_ctorIdx_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_k_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_187_, v_k_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(lean_object* v_motive_191_, lean_object* v_ctorIdx_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_k_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Lsp_DiagnosticCode_ctorElim(v_motive_191_, v_ctorIdx_192_, v_t_193_, v_h_194_, v_k_195_);
lean_dec(v_ctorIdx_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim___redArg(lean_object* v_t_197_, lean_object* v_int_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_197_, v_int_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim(lean_object* v_motive_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_int_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_201_, v_int_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim___redArg(lean_object* v_t_205_, lean_object* v_string_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_205_, v_string_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim(lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_string_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_209_, v_string_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_nat_to_int(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Lsp_instInhabitedDiagnosticCode_default;
return v___x_218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticCode_beq(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v_i_221_; lean_object* v_i_222_; uint8_t v___x_223_; 
v_i_221_ = lean_ctor_get(v_x_219_, 0);
v_i_222_ = lean_ctor_get(v_x_220_, 0);
v___x_223_ = lean_int_dec_eq(v_i_221_, v_i_222_);
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
else
{
if (lean_obj_tag(v_x_220_) == 1)
{
lean_object* v_s_225_; lean_object* v_s_226_; uint8_t v___x_227_; 
v_s_225_ = lean_ctor_get(v_x_219_, 0);
v_s_226_ = lean_ctor_get(v_x_220_, 0);
v___x_227_ = lean_string_dec_eq(v_s_225_, v_s_226_);
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_x_229_, v_x_230_);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_x_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticCode_ord(lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
if (lean_obj_tag(v_x_236_) == 0)
{
lean_object* v_i_237_; lean_object* v_i_238_; uint8_t v___x_239_; 
v_i_237_ = lean_ctor_get(v_x_235_, 0);
v_i_238_ = lean_ctor_get(v_x_236_, 0);
v___x_239_ = lean_int_dec_lt(v_i_237_, v_i_238_);
if (v___x_239_ == 0)
{
uint8_t v___x_240_; 
v___x_240_ = lean_int_dec_eq(v_i_237_, v_i_238_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
v___x_241_ = 2;
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 1;
return v___x_242_;
}
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 0;
return v___x_243_;
}
}
else
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
}
else
{
if (lean_obj_tag(v_x_236_) == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 2;
return v___x_245_;
}
else
{
lean_object* v_s_246_; lean_object* v_s_247_; uint8_t v___x_248_; 
v_s_246_ = lean_ctor_get(v_x_235_, 0);
v_s_247_ = lean_ctor_get(v_x_236_, 0);
v___x_248_ = lean_string_compare(v_s_246_, v_s_247_);
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Lean_Lsp_instOrdDiagnosticCode_ord(v_x_249_, v_x_250_);
lean_dec_ref(v_x_250_);
lean_dec_ref(v_x_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(lean_object* v_x_256_){
_start:
{
switch(lean_obj_tag(v_x_256_))
{
case 2:
{
lean_object* v_n_265_; lean_object* v_mantissa_266_; lean_object* v_exponent_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_n_265_ = lean_ctor_get(v_x_256_, 0);
v_mantissa_266_ = lean_ctor_get(v_n_265_, 0);
v_exponent_267_ = lean_ctor_get(v_n_265_, 1);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_dec_eq(v_exponent_267_, v___x_268_);
if (v___x_269_ == 0)
{
goto v___jp_257_;
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
lean_inc(v_mantissa_266_);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_x_256_, 0);
lean_dec(v_unused_278_);
v___x_271_ = v_x_256_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_x_256_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 0);
lean_ctor_set(v___x_271_, 0, v_mantissa_266_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_mantissa_266_);
v___x_274_ = v_reuseFailAlloc_276_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
}
}
case 3:
{
lean_object* v_s_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_s_279_ = lean_ctor_get(v_x_256_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v_x_256_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_s_279_);
lean_dec(v_x_256_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_s_279_);
v___x_284_ = v_reuseFailAlloc_286_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
default: 
{
goto v___jp_257_;
}
}
v___jp_257_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_258_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_259_ = lean_unsigned_to_nat(80u);
v___x_260_ = l_Lean_Json_pretty(v_x_256_, v___x_259_);
v___x_261_ = lean_string_append(v___x_258_, v___x_260_);
lean_dec_ref(v___x_260_);
v___x_262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_263_ = lean_string_append(v___x_261_, v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_i_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v_i_291_ = lean_ctor_get(v_x_290_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v_x_290_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_i_291_);
lean_dec(v_x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_JsonNumber_fromInt(v_i_291_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 2);
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_s_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_s_300_ = lean_ctor_get(v_x_290_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v_x_290_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_s_300_);
lean_dec(v_x_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 3);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_s_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___impl(uint8_t v_x_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_box(v_x_310_);
v___x_312_ = lean_obj_tag_nat(v___x_311_);
lean_dec(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___impl___boxed(lean_object* v_x_313_){
_start:
{
uint8_t v_x_4__boxed_314_; lean_object* v_res_315_; 
v_x_4__boxed_314_ = lean_unbox(v_x_313_);
v_res_315_ = l_Lean_Lsp_DiagnosticTag_ctorIdx___impl(v_x_4__boxed_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(lean_object* v_k_316_){
_start:
{
lean_inc(v_k_316_);
return v_k_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(v_k_317_);
lean_dec(v_k_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim(lean_object* v_motive_319_, lean_object* v_ctorIdx_320_, uint8_t v_t_321_, lean_object* v_h_322_, lean_object* v_k_323_){
_start:
{
lean_inc(v_k_323_);
return v_k_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(lean_object* v_motive_324_, lean_object* v_ctorIdx_325_, lean_object* v_t_326_, lean_object* v_h_327_, lean_object* v_k_328_){
_start:
{
uint8_t v_t_boxed_329_; lean_object* v_res_330_; 
v_t_boxed_329_ = lean_unbox(v_t_326_);
v_res_330_ = l_Lean_Lsp_DiagnosticTag_ctorElim(v_motive_324_, v_ctorIdx_325_, v_t_boxed_329_, v_h_327_, v_k_328_);
lean_dec(v_k_328_);
lean_dec(v_ctorIdx_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(lean_object* v_unnecessary_331_){
_start:
{
lean_inc(v_unnecessary_331_);
return v_unnecessary_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(lean_object* v_unnecessary_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(v_unnecessary_332_);
lean_dec(v_unnecessary_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim(lean_object* v_motive_334_, uint8_t v_t_335_, lean_object* v_h_336_, lean_object* v_unnecessary_337_){
_start:
{
lean_inc(v_unnecessary_337_);
return v_unnecessary_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_unnecessary_341_){
_start:
{
uint8_t v_t_boxed_342_; lean_object* v_res_343_; 
v_t_boxed_342_ = lean_unbox(v_t_339_);
v_res_343_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim(v_motive_338_, v_t_boxed_342_, v_h_340_, v_unnecessary_341_);
lean_dec(v_unnecessary_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(lean_object* v_deprecated_344_){
_start:
{
lean_inc(v_deprecated_344_);
return v_deprecated_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(lean_object* v_deprecated_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(v_deprecated_345_);
lean_dec(v_deprecated_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim(lean_object* v_motive_347_, uint8_t v_t_348_, lean_object* v_h_349_, lean_object* v_deprecated_350_){
_start:
{
lean_inc(v_deprecated_350_);
return v_deprecated_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(lean_object* v_motive_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_deprecated_354_){
_start:
{
uint8_t v_t_boxed_355_; lean_object* v_res_356_; 
v_t_boxed_355_ = lean_unbox(v_t_352_);
v_res_356_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim(v_motive_351_, v_t_boxed_355_, v_h_353_, v_deprecated_354_);
lean_dec(v_deprecated_354_);
return v_res_356_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default(void){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag(void){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticTag_beq(uint8_t v_x_359_, uint8_t v_y_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_361_ = lean_box(v_x_359_);
v___x_362_ = lean_obj_tag_nat(v___x_361_);
lean_dec(v___x_361_);
v___x_363_ = lean_box(v_y_360_);
v___x_364_ = lean_obj_tag_nat(v___x_363_);
lean_dec(v___x_363_);
v___x_365_ = lean_nat_dec_eq(v___x_362_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(lean_object* v_x_366_, lean_object* v_y_367_){
_start:
{
uint8_t v_x_24__boxed_368_; uint8_t v_y_25__boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_x_24__boxed_368_ = lean_unbox(v_x_366_);
v_y_25__boxed_369_ = lean_unbox(v_y_367_);
v_res_370_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v_x_24__boxed_368_, v_y_25__boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticTag_ord(uint8_t v_x_374_, uint8_t v_y_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_376_ = lean_box(v_x_374_);
v___x_377_ = lean_obj_tag_nat(v___x_376_);
lean_dec(v___x_376_);
v___x_378_ = lean_box(v_y_375_);
v___x_379_ = lean_obj_tag_nat(v___x_378_);
lean_dec(v___x_378_);
v___x_380_ = lean_nat_dec_lt(v___x_377_, v___x_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_eq(v___x_377_, v___x_379_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = 2;
return v___x_382_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 1;
return v___x_383_;
}
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 0;
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(lean_object* v_x_385_, lean_object* v_y_386_){
_start:
{
uint8_t v_x_33__boxed_387_; uint8_t v_y_34__boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_x_33__boxed_387_ = lean_unbox(v_x_385_);
v_y_34__boxed_388_ = lean_unbox(v_y_386_);
v_res_389_ = l_Lean_Lsp_instOrdDiagnosticTag_ord(v_x_33__boxed_387_, v_y_34__boxed_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object* v_j_402_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Json_getNat_x3f(v_j_402_);
if (lean_obj_tag(v___x_405_) == 1)
{
lean_object* v_a_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_dec_eq(v_a_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(2u);
v___x_410_ = lean_nat_dec_eq(v_a_406_, v___x_409_);
lean_dec(v_a_406_);
if (v___x_410_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2));
return v___x_411_;
}
}
else
{
lean_object* v___x_412_; 
lean_dec(v_a_406_);
v___x_412_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3));
return v___x_412_;
}
}
else
{
lean_dec_ref(v___x_405_);
goto v___jp_403_;
}
v___jp_403_:
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1));
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t v_x_415_){
_start:
{
if (v_x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_416_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object* v_x_418_){
_start:
{
uint8_t v_x_48__boxed_419_; lean_object* v_res_420_; 
v_x_48__boxed_419_ = lean_unbox(v_x_418_);
v_res_420_ = l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(v_x_48__boxed_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___impl(uint8_t v_x_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_box(v_x_423_);
v___x_425_ = lean_obj_tag_nat(v___x_424_);
lean_dec(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___impl___boxed(lean_object* v_x_426_){
_start:
{
uint8_t v_x_4__boxed_427_; lean_object* v_res_428_; 
v_x_4__boxed_427_ = lean_unbox(v_x_426_);
v_res_428_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___impl(v_x_4__boxed_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(lean_object* v_k_429_){
_start:
{
lean_inc(v_k_429_);
return v_k_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(lean_object* v_k_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(v_k_430_);
lean_dec(v_k_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim(lean_object* v_motive_432_, lean_object* v_ctorIdx_433_, uint8_t v_t_434_, lean_object* v_h_435_, lean_object* v_k_436_){
_start:
{
lean_inc(v_k_436_);
return v_k_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(lean_object* v_motive_437_, lean_object* v_ctorIdx_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_k_441_){
_start:
{
uint8_t v_t_boxed_442_; lean_object* v_res_443_; 
v_t_boxed_442_ = lean_unbox(v_t_439_);
v_res_443_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim(v_motive_437_, v_ctorIdx_438_, v_t_boxed_442_, v_h_440_, v_k_441_);
lean_dec(v_k_441_);
lean_dec(v_ctorIdx_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(lean_object* v_unsolvedGoals_444_){
_start:
{
lean_inc(v_unsolvedGoals_444_);
return v_unsolvedGoals_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(lean_object* v_unsolvedGoals_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(v_unsolvedGoals_445_);
lean_dec(v_unsolvedGoals_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(lean_object* v_motive_447_, uint8_t v_t_448_, lean_object* v_h_449_, lean_object* v_unsolvedGoals_450_){
_start:
{
lean_inc(v_unsolvedGoals_450_);
return v_unsolvedGoals_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(lean_object* v_motive_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_unsolvedGoals_454_){
_start:
{
uint8_t v_t_boxed_455_; lean_object* v_res_456_; 
v_t_boxed_455_ = lean_unbox(v_t_452_);
v_res_456_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(v_motive_451_, v_t_boxed_455_, v_h_453_, v_unsolvedGoals_454_);
lean_dec(v_unsolvedGoals_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(lean_object* v_goalsAccomplished_457_){
_start:
{
lean_inc(v_goalsAccomplished_457_);
return v_goalsAccomplished_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(lean_object* v_goalsAccomplished_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(v_goalsAccomplished_458_);
lean_dec(v_goalsAccomplished_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(lean_object* v_motive_460_, uint8_t v_t_461_, lean_object* v_h_462_, lean_object* v_goalsAccomplished_463_){
_start:
{
lean_inc(v_goalsAccomplished_463_);
return v_goalsAccomplished_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(lean_object* v_motive_464_, lean_object* v_t_465_, lean_object* v_h_466_, lean_object* v_goalsAccomplished_467_){
_start:
{
uint8_t v_t_boxed_468_; lean_object* v_res_469_; 
v_t_boxed_468_ = lean_unbox(v_t_465_);
v_res_469_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(v_motive_464_, v_t_boxed_468_, v_h_466_, v_goalsAccomplished_467_);
lean_dec(v_goalsAccomplished_467_);
return v_res_469_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default(void){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag(void){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(uint8_t v_x_472_, uint8_t v_y_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_474_ = lean_box(v_x_472_);
v___x_475_ = lean_obj_tag_nat(v___x_474_);
lean_dec(v___x_474_);
v___x_476_ = lean_box(v_y_473_);
v___x_477_ = lean_obj_tag_nat(v___x_476_);
lean_dec(v___x_476_);
v___x_478_ = lean_nat_dec_eq(v___x_475_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
uint8_t v_x_24__boxed_481_; uint8_t v_y_25__boxed_482_; uint8_t v_res_483_; lean_object* v_r_484_; 
v_x_24__boxed_481_ = lean_unbox(v_x_479_);
v_y_25__boxed_482_ = lean_unbox(v_y_480_);
v_res_483_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v_x_24__boxed_481_, v_y_25__boxed_482_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(uint8_t v_x_487_, uint8_t v_y_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_489_ = lean_box(v_x_487_);
v___x_490_ = lean_obj_tag_nat(v___x_489_);
lean_dec(v___x_489_);
v___x_491_ = lean_box(v_y_488_);
v___x_492_ = lean_obj_tag_nat(v___x_491_);
lean_dec(v___x_491_);
v___x_493_ = lean_nat_dec_lt(v___x_490_, v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_eq(v___x_490_, v___x_492_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = 2;
return v___x_495_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = 1;
return v___x_496_;
}
}
else
{
uint8_t v___x_497_; 
v___x_497_ = 0;
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(lean_object* v_x_498_, lean_object* v_y_499_){
_start:
{
uint8_t v_x_33__boxed_500_; uint8_t v_y_34__boxed_501_; uint8_t v_res_502_; lean_object* v_r_503_; 
v_x_33__boxed_500_ = lean_unbox(v_x_498_);
v_y_34__boxed_501_ = lean_unbox(v_y_499_);
v_res_502_ = l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(v_x_33__boxed_500_, v_y_34__boxed_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(lean_object* v_j_515_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Json_getNat_x3f(v_j_515_);
if (lean_obj_tag(v___x_518_) == 1)
{
lean_object* v_a_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_dec_eq(v_a_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(2u);
v___x_523_ = lean_nat_dec_eq(v_a_519_, v___x_522_);
lean_dec(v_a_519_);
if (v___x_523_ == 0)
{
goto v___jp_516_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2));
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v_a_519_);
v___x_525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3));
return v___x_525_;
}
}
else
{
lean_dec_ref(v___x_518_);
goto v___jp_516_;
}
v___jp_516_:
{
lean_object* v___x_517_; 
v___x_517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1));
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(uint8_t v_x_528_){
_start:
{
if (v_x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(lean_object* v_x_531_){
_start:
{
uint8_t v_x_48__boxed_532_; lean_object* v_res_533_; 
v_x_48__boxed_532_ = lean_unbox(v_x_531_);
v_res_533_ = l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(v_x_48__boxed_532_);
return v_res_533_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0));
v___x_538_ = l_Lean_Lsp_instInhabitedLocation_default;
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
return v___x_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_location_544_; lean_object* v_message_545_; lean_object* v_location_546_; lean_object* v_message_547_; uint8_t v___x_548_; 
v_location_544_ = lean_ctor_get(v_x_542_, 0);
v_message_545_ = lean_ctor_get(v_x_542_, 1);
v_location_546_ = lean_ctor_get(v_x_543_, 0);
v_message_547_ = lean_ctor_get(v_x_543_, 1);
v___x_548_ = l_Lean_Lsp_instBEqLocation_beq(v_location_544_, v_location_546_);
if (v___x_548_ == 0)
{
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = lean_string_dec_eq(v_message_545_, v_message_547_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v_x_550_, v_x_551_);
lean_dec_ref(v_x_551_);
lean_dec_ref(v_x_550_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
if (lean_obj_tag(v_a_556_) == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_array_to_list(v_a_557_);
return v___x_558_;
}
else
{
lean_object* v_head_559_; lean_object* v_tail_560_; lean_object* v___x_561_; 
v_head_559_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_head_559_);
v_tail_560_ = lean_ctor_get(v_a_556_, 1);
lean_inc(v_tail_560_);
lean_dec_ref_known(v_a_556_, 2);
v___x_561_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_557_, v_head_559_);
v_a_556_ = v_tail_560_;
v_a_557_ = v___x_561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object* v_x_567_){
_start:
{
lean_object* v_location_568_; lean_object* v_message_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_589_; 
v_location_568_ = lean_ctor_get(v_x_567_, 0);
v_message_569_ = lean_ctor_get(v_x_567_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_589_ == 0)
{
v___x_571_ = v_x_567_;
v_isShared_572_ = v_isSharedCheck_589_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_message_569_);
lean_inc(v_location_568_);
lean_dec(v_x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_589_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
v___x_574_ = l_Lean_Lsp_instToJsonLocation_toJson(v_location_568_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_574_);
lean_ctor_set(v___x_571_, 0, v___x_573_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_588_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_580_, 0, v_message_569_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_577_);
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_577_);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_578_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_586_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_584_, v___x_585_);
v___x_587_ = l_Lean_Json_mkObj(v___x_586_);
lean_dec(v___x_586_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object* v_j_592_, lean_object* v_k_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_Json_getObjValD(v_j_592_, v_k_593_);
v___x_595_ = l_Lean_Lsp_instFromJsonLocation_fromJson(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object* v_j_596_, lean_object* v_k_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_j_596_, v_k_597_);
lean_dec_ref(v_k_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object* v_j_599_, lean_object* v_k_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = l_Lean_Json_getObjValD(v_j_599_, v_k_600_);
v___x_602_ = l_Lean_Json_getStr_x3f(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object* v_j_603_, lean_object* v_k_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_j_603_, v_k_604_);
lean_dec_ref(v_k_604_);
return v_res_605_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4(void){
_start:
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = 1;
v___x_614_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3));
v___x_615_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_618_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4);
v___x_619_ = lean_string_append(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8(void){
_start:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 1;
v___x_623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7));
v___x_624_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8);
v___x_626_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
v___x_627_ = lean_string_append(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_630_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9);
v___x_631_ = lean_string_append(v___x_630_, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13(void){
_start:
{
uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = 1;
v___x_635_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12));
v___x_636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_638_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
v___x_639_ = lean_string_append(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_641_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14);
v___x_642_ = lean_string_append(v___x_641_, v___x_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object* v_json_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
lean_inc(v_json_643_);
v___x_645_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_json_643_, v___x_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_json_643_);
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_655_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_650_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
v___x_651_ = lean_string_append(v___x_650_, v_a_646_);
lean_dec(v_a_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_651_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_json_643_);
v_a_656_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_645_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_645_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 0);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_664_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_645_, 1);
v___x_665_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_666_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_643_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_a_664_);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_676_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
v___x_672_ = lean_string_append(v___x_671_, v_a_667_);
lean_dec(v_a_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_672_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_a_664_);
v_a_677_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_666_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_666_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 0);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_a_685_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v___x_666_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_666_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_a_664_);
lean_ctor_set(v___x_689_, 1, v_a_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_location_698_; lean_object* v_message_699_; lean_object* v_location_700_; lean_object* v_message_701_; uint8_t v___x_702_; 
v_location_698_ = lean_ctor_get(v_x_696_, 0);
v_message_699_ = lean_ctor_get(v_x_696_, 1);
v_location_700_ = lean_ctor_get(v_x_697_, 0);
v_message_701_ = lean_ctor_get(v_x_697_, 1);
v___x_702_ = l_Lean_Lsp_instOrdLocation_ord(v_location_698_, v_location_700_);
if (v___x_702_ == 1)
{
uint8_t v___x_703_; 
v___x_703_ = lean_string_compare(v_message_699_, v_message_701_);
return v___x_703_;
}
else
{
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(v_x_704_, v_x_705_);
lean_dec_ref(v_x_705_);
lean_dec_ref(v_x_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object* v_inst_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_714_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0);
v___x_715_ = lean_box(0);
v___x_716_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_716_, 0, v___x_713_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_ctor_set(v___x_716_, 3, v___x_715_);
lean_ctor_set(v___x_716_, 4, v___x_715_);
lean_ctor_set(v___x_716_, 5, v___x_715_);
lean_ctor_set(v___x_716_, 6, v_inst_712_);
lean_ctor_set(v___x_716_, 7, v___x_715_);
lean_ctor_set(v___x_716_, 8, v___x_715_);
lean_ctor_set(v___x_716_, 9, v___x_715_);
lean_ctor_set(v___x_716_, 10, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object* v_00_u03b1_717_, lean_object* v_inst_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object* v_inst_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object* v_a_722_, lean_object* v_inst_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3(void){
_start:
{
lean_object* v___x_729_; lean_object* v___f_730_; 
v___x_729_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_730_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_730_, 0, v___x_729_);
return v___f_730_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object* v_inst_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_range_741_; lean_object* v_fullRange_x3f_742_; lean_object* v_severity_x3f_743_; lean_object* v_isSilent_x3f_744_; lean_object* v_code_x3f_745_; lean_object* v_source_x3f_746_; lean_object* v_message_747_; lean_object* v_tags_x3f_748_; lean_object* v_leanTags_x3f_749_; lean_object* v_relatedInformation_x3f_750_; lean_object* v_data_x3f_751_; lean_object* v_range_752_; lean_object* v_fullRange_x3f_753_; lean_object* v_severity_x3f_754_; lean_object* v_isSilent_x3f_755_; lean_object* v_code_x3f_756_; lean_object* v_source_x3f_757_; lean_object* v_message_758_; lean_object* v_tags_x3f_759_; lean_object* v_leanTags_x3f_760_; lean_object* v_relatedInformation_x3f_761_; lean_object* v_data_x3f_762_; uint8_t v___x_763_; 
v_range_741_ = lean_ctor_get(v_x_739_, 0);
lean_inc_ref(v_range_741_);
v_fullRange_x3f_742_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_fullRange_x3f_742_);
v_severity_x3f_743_ = lean_ctor_get(v_x_739_, 2);
lean_inc(v_severity_x3f_743_);
v_isSilent_x3f_744_ = lean_ctor_get(v_x_739_, 3);
lean_inc(v_isSilent_x3f_744_);
v_code_x3f_745_ = lean_ctor_get(v_x_739_, 4);
lean_inc(v_code_x3f_745_);
v_source_x3f_746_ = lean_ctor_get(v_x_739_, 5);
lean_inc(v_source_x3f_746_);
v_message_747_ = lean_ctor_get(v_x_739_, 6);
lean_inc(v_message_747_);
v_tags_x3f_748_ = lean_ctor_get(v_x_739_, 7);
lean_inc(v_tags_x3f_748_);
v_leanTags_x3f_749_ = lean_ctor_get(v_x_739_, 8);
lean_inc(v_leanTags_x3f_749_);
v_relatedInformation_x3f_750_ = lean_ctor_get(v_x_739_, 9);
lean_inc(v_relatedInformation_x3f_750_);
v_data_x3f_751_ = lean_ctor_get(v_x_739_, 10);
lean_inc(v_data_x3f_751_);
lean_dec_ref(v_x_739_);
v_range_752_ = lean_ctor_get(v_x_740_, 0);
lean_inc_ref(v_range_752_);
v_fullRange_x3f_753_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_fullRange_x3f_753_);
v_severity_x3f_754_ = lean_ctor_get(v_x_740_, 2);
lean_inc(v_severity_x3f_754_);
v_isSilent_x3f_755_ = lean_ctor_get(v_x_740_, 3);
lean_inc(v_isSilent_x3f_755_);
v_code_x3f_756_ = lean_ctor_get(v_x_740_, 4);
lean_inc(v_code_x3f_756_);
v_source_x3f_757_ = lean_ctor_get(v_x_740_, 5);
lean_inc(v_source_x3f_757_);
v_message_758_ = lean_ctor_get(v_x_740_, 6);
lean_inc(v_message_758_);
v_tags_x3f_759_ = lean_ctor_get(v_x_740_, 7);
lean_inc(v_tags_x3f_759_);
v_leanTags_x3f_760_ = lean_ctor_get(v_x_740_, 8);
lean_inc(v_leanTags_x3f_760_);
v_relatedInformation_x3f_761_ = lean_ctor_get(v_x_740_, 9);
lean_inc(v_relatedInformation_x3f_761_);
v_data_x3f_762_ = lean_ctor_get(v_x_740_, 10);
lean_inc(v_data_x3f_762_);
lean_dec_ref(v_x_740_);
v___x_763_ = l_Lean_Lsp_instBEqRange_beq(v_range_741_, v_range_752_);
lean_dec_ref(v_range_752_);
lean_dec_ref(v_range_741_);
if (v___x_763_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_message_758_);
lean_dec(v_source_x3f_757_);
lean_dec(v_code_x3f_756_);
lean_dec(v_isSilent_x3f_755_);
lean_dec(v_severity_x3f_754_);
lean_dec(v_fullRange_x3f_753_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
lean_dec(v_message_747_);
lean_dec(v_source_x3f_746_);
lean_dec(v_code_x3f_745_);
lean_dec(v_isSilent_x3f_744_);
lean_dec(v_severity_x3f_743_);
lean_dec(v_fullRange_x3f_742_);
lean_dec_ref(v_inst_738_);
return v___x_763_;
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0));
v___x_765_ = l_instBEqOption_beq___redArg(v___x_764_, v_fullRange_x3f_742_, v_fullRange_x3f_753_);
if (v___x_765_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_message_758_);
lean_dec(v_source_x3f_757_);
lean_dec(v_code_x3f_756_);
lean_dec(v_isSilent_x3f_755_);
lean_dec(v_severity_x3f_754_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
lean_dec(v_message_747_);
lean_dec(v_source_x3f_746_);
lean_dec(v_code_x3f_745_);
lean_dec(v_isSilent_x3f_744_);
lean_dec(v_severity_x3f_743_);
lean_dec_ref(v_inst_738_);
return v___x_765_;
}
else
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0));
v___x_767_ = l_instBEqOption_beq___redArg(v___x_766_, v_severity_x3f_743_, v_severity_x3f_754_);
if (v___x_767_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_message_758_);
lean_dec(v_source_x3f_757_);
lean_dec(v_code_x3f_756_);
lean_dec(v_isSilent_x3f_755_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
lean_dec(v_message_747_);
lean_dec(v_source_x3f_746_);
lean_dec(v_code_x3f_745_);
lean_dec(v_isSilent_x3f_744_);
lean_dec_ref(v_inst_738_);
return v___x_767_;
}
else
{
lean_object* v___f_768_; uint8_t v___x_769_; 
v___f_768_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2));
v___x_769_ = l_instBEqOption_beq___redArg(v___f_768_, v_isSilent_x3f_744_, v_isSilent_x3f_755_);
if (v___x_769_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_message_758_);
lean_dec(v_source_x3f_757_);
lean_dec(v_code_x3f_756_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
lean_dec(v_message_747_);
lean_dec(v_source_x3f_746_);
lean_dec(v_code_x3f_745_);
lean_dec_ref(v_inst_738_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticCode___closed__0));
v___x_771_ = l_instBEqOption_beq___redArg(v___x_770_, v_code_x3f_745_, v_code_x3f_756_);
if (v___x_771_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_message_758_);
lean_dec(v_source_x3f_757_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
lean_dec(v_message_747_);
lean_dec(v_source_x3f_746_);
lean_dec_ref(v_inst_738_);
return v___x_771_;
}
else
{
lean_object* v___f_772_; uint8_t v___x_773_; 
v___f_772_ = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3);
v___x_773_ = l_instBEqOption_beq___redArg(v___f_772_, v_source_x3f_746_, v_source_x3f_757_);
if (v___x_773_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_message_758_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
lean_dec(v_message_747_);
lean_dec_ref(v_inst_738_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_apply_2(v_inst_738_, v_message_747_, v_message_758_);
v___x_775_ = lean_unbox(v___x_774_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; 
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_tags_x3f_759_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
lean_dec(v_tags_x3f_748_);
v___x_776_ = lean_unbox(v___x_774_);
return v___x_776_;
}
else
{
lean_object* v___f_777_; uint8_t v___x_778_; 
v___f_777_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4));
v___x_778_ = l_instBEqOption_beq___redArg(v___f_777_, v_tags_x3f_748_, v_tags_x3f_759_);
if (v___x_778_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_leanTags_x3f_760_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
lean_dec(v_leanTags_x3f_749_);
return v___x_778_;
}
else
{
lean_object* v___f_779_; uint8_t v___x_780_; 
v___f_779_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5));
v___x_780_ = l_instBEqOption_beq___redArg(v___f_779_, v_leanTags_x3f_749_, v_leanTags_x3f_760_);
if (v___x_780_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_relatedInformation_x3f_761_);
lean_dec(v_data_x3f_751_);
lean_dec(v_relatedInformation_x3f_750_);
return v___x_780_;
}
else
{
lean_object* v___f_781_; uint8_t v___x_782_; 
v___f_781_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6));
v___x_782_ = l_instBEqOption_beq___redArg(v___f_781_, v_relatedInformation_x3f_750_, v_relatedInformation_x3f_761_);
if (v___x_782_ == 0)
{
lean_dec(v_data_x3f_762_);
lean_dec(v_data_x3f_751_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__7));
v___x_784_ = l_instBEqOption_beq___redArg(v___x_783_, v_data_x3f_751_, v_data_x3f_762_);
return v___x_784_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object* v_inst_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_785_, v_x_786_, v_x_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object* v_00_u03b1_790_, lean_object* v_inst_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_791_, v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object* v_00_u03b1_795_, lean_object* v_inst_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_Lsp_instBEqDiagnosticWith_beq(v_00_u03b1_795_, v_inst_796_, v_x_797_, v_x_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object* v_inst_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_802_, 0, lean_box(0));
lean_closure_set(v___x_802_, 1, v_inst_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object* v_00_u03b1_803_, lean_object* v_inst_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_805_, 0, lean_box(0));
lean_closure_set(v___x_805_, 1, v_inst_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object* v_inst_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_range_828_; lean_object* v_fullRange_x3f_829_; lean_object* v_severity_x3f_830_; lean_object* v_isSilent_x3f_831_; lean_object* v_code_x3f_832_; lean_object* v_source_x3f_833_; lean_object* v_message_834_; lean_object* v_tags_x3f_835_; lean_object* v_leanTags_x3f_836_; lean_object* v_relatedInformation_x3f_837_; lean_object* v_data_x3f_838_; lean_object* v___x_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_range_828_ = lean_ctor_get(v_x_827_, 0);
lean_inc_ref(v_range_828_);
v_fullRange_x3f_829_ = lean_ctor_get(v_x_827_, 1);
lean_inc(v_fullRange_x3f_829_);
v_severity_x3f_830_ = lean_ctor_get(v_x_827_, 2);
lean_inc(v_severity_x3f_830_);
v_isSilent_x3f_831_ = lean_ctor_get(v_x_827_, 3);
lean_inc(v_isSilent_x3f_831_);
v_code_x3f_832_ = lean_ctor_get(v_x_827_, 4);
lean_inc(v_code_x3f_832_);
v_source_x3f_833_ = lean_ctor_get(v_x_827_, 5);
lean_inc(v_source_x3f_833_);
v_message_834_ = lean_ctor_get(v_x_827_, 6);
lean_inc(v_message_834_);
v_tags_x3f_835_ = lean_ctor_get(v_x_827_, 7);
lean_inc(v_tags_x3f_835_);
v_leanTags_x3f_836_ = lean_ctor_get(v_x_827_, 8);
lean_inc(v_leanTags_x3f_836_);
v_relatedInformation_x3f_837_ = lean_ctor_get(v_x_827_, 9);
lean_inc(v_relatedInformation_x3f_837_);
v_data_x3f_838_ = lean_ctor_get(v_x_827_, 10);
lean_inc(v_data_x3f_838_);
lean_dec_ref(v_x_827_);
v___x_839_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0));
v___f_840_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0));
v___f_841_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1));
v___f_842_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0));
v___f_843_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2));
v___x_844_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3));
v___x_845_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4));
v___x_846_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5));
v___x_847_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6));
v___x_848_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_849_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_828_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_854_ = l_Lean_Json_opt___redArg(v___x_839_, v___x_853_, v_fullRange_x3f_829_);
v___x_855_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_856_ = l_Lean_Json_opt___redArg(v___f_840_, v___x_855_, v_severity_x3f_830_);
v___x_857_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_858_ = l_Lean_Json_opt___redArg(v___f_841_, v___x_857_, v_isSilent_x3f_831_);
v___x_859_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_860_ = l_Lean_Json_opt___redArg(v___f_842_, v___x_859_, v_code_x3f_832_);
v___x_861_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_862_ = l_Lean_Json_opt___redArg(v___f_843_, v___x_861_, v_source_x3f_833_);
v___x_863_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_864_ = lean_apply_1(v_inst_826_, v_message_834_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_851_);
v___x_867_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_868_ = l_Lean_Json_opt___redArg(v___x_844_, v___x_867_, v_tags_x3f_835_);
v___x_869_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_870_ = l_Lean_Json_opt___redArg(v___x_845_, v___x_869_, v_leanTags_x3f_836_);
v___x_871_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_872_ = l_Lean_Json_opt___redArg(v___x_846_, v___x_871_, v_relatedInformation_x3f_837_);
v___x_873_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_874_ = l_Lean_Json_opt___redArg(v___x_847_, v___x_873_, v_data_x3f_838_);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_851_);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_872_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_870_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_868_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_866_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_862_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_860_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_858_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_856_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_854_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_852_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_887_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_847_, v___x_885_, v___x_886_);
v___x_888_ = l_Lean_Json_mkObj(v___x_887_);
lean_dec(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object* v_00_u03b1_889_, lean_object* v_inst_890_, lean_object* v_x_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(v_inst_890_, v_x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object* v_inst_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_894_, 0, lean_box(0));
lean_closure_set(v___x_894_, 1, v_inst_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object* v_00_u03b1_895_, lean_object* v_inst_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_897_, 0, lean_box(0));
lean_closure_set(v___x_897_, 1, v_inst_896_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4(void){
_start:
{
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = 1;
v___x_907_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3));
v___x_908_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_910_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4);
v___x_911_ = lean_string_append(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = 1;
v___x_915_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6));
v___x_916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7);
v___x_918_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_919_ = lean_string_append(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_921_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8);
v___x_922_ = lean_string_append(v___x_921_, v___x_920_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12(void){
_start:
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = 1;
v___x_927_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11));
v___x_928_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12);
v___x_930_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_931_ = lean_string_append(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_933_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13);
v___x_934_ = lean_string_append(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = 1;
v___x_941_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17));
v___x_942_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18);
v___x_944_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_945_ = lean_string_append(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_947_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19);
v___x_948_ = lean_string_append(v___x_947_, v___x_946_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25(void){
_start:
{
uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = 1;
v___x_956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24));
v___x_957_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_956_, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25);
v___x_959_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_960_ = lean_string_append(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_962_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26);
v___x_963_ = lean_string_append(v___x_962_, v___x_961_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = 1;
v___x_970_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30));
v___x_971_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_970_, v___x_969_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31);
v___x_973_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_974_ = lean_string_append(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32);
v___x_977_ = lean_string_append(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38(void){
_start:
{
uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = 1;
v___x_985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37));
v___x_986_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_985_, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38);
v___x_988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_989_ = lean_string_append(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39);
v___x_992_ = lean_string_append(v___x_991_, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_994_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_995_ = lean_string_append(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41);
v___x_998_ = lean_string_append(v___x_997_, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47(void){
_start:
{
uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = 1;
v___x_1007_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46));
v___x_1008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47);
v___x_1010_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1011_ = lean_string_append(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48);
v___x_1014_ = lean_string_append(v___x_1013_, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54(void){
_start:
{
uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = 1;
v___x_1023_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53));
v___x_1024_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54);
v___x_1026_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1027_ = lean_string_append(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1029_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55);
v___x_1030_ = lean_string_append(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61(void){
_start:
{
uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = 1;
v___x_1039_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60));
v___x_1040_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1039_, v___x_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61);
v___x_1042_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1043_ = lean_string_append(v___x_1042_, v___x_1041_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1045_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62);
v___x_1046_ = lean_string_append(v___x_1045_, v___x_1044_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68(void){
_start:
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = 1;
v___x_1054_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67));
v___x_1055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68);
v___x_1057_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1058_ = lean_string_append(v___x_1057_, v___x_1056_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1060_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69);
v___x_1061_ = lean_string_append(v___x_1060_, v___x_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object* v_inst_1062_, lean_object* v_json_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0));
v___x_1065_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1));
v___x_1066_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_1063_);
v___x_1067_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1064_, v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1077_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1077_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1072_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_1073_ = lean_string_append(v___x_1072_, v_a_1068_);
lean_dec(v_a_1068_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1073_);
v___x_1075_ = v___x_1070_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1078_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1067_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1067_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 0);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_a_1086_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1087_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_1063_);
v___x_1088_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1065_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1098_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1098_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_1094_ = lean_string_append(v___x_1093_, v_a_1089_);
lean_dec(v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1094_);
v___x_1096_ = v___x_1091_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1099_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1088_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1088_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_a_1107_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1108_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15));
v___x_1109_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_1063_);
v___x_1110_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1108_, v___x_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_1116_ = lean_string_append(v___x_1115_, v_a_1111_);
lean_dec(v_a_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1116_);
v___x_1118_ = v___x_1113_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1121_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1110_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1110_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 0);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_a_1129_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22));
v___x_1131_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_1063_);
v___x_1132_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1130_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_1138_ = lean_string_append(v___x_1137_, v_a_1133_);
lean_dec(v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1138_);
v___x_1140_ = v___x_1135_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1143_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1132_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1132_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_a_1151_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1152_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28));
v___x_1153_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_1063_);
v___x_1154_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1152_, v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_1160_ = lean_string_append(v___x_1159_, v_a_1155_);
lean_dec(v_a_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1165_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1154_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1154_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 0);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_a_1173_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1174_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35));
v___x_1175_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_1063_);
v___x_1176_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1174_, v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1181_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_1182_ = lean_string_append(v___x_1181_, v_a_1177_);
lean_dec(v_a_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
lean_dec_ref(v_inst_1062_);
v_a_1187_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1176_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1176_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 0);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1195_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1196_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_1063_);
v___x_1197_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v_inst_1062_, v___x_1196_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1207_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_1203_ = lean_string_append(v___x_1202_, v_a_1198_);
lean_dec(v_a_1198_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1208_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1197_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1197_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 0);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1217_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44));
v___x_1218_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_1063_);
v___x_1219_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1217_, v___x_1218_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1229_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1229_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1224_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_1225_ = lean_string_append(v___x_1224_, v_a_1220_);
lean_dec(v_a_1220_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1225_);
v___x_1227_ = v___x_1222_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1230_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1219_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1219_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 0);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1238_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1239_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51));
v___x_1240_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_1063_);
v___x_1241_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1239_, v___x_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_a_1238_);
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1251_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_1247_ = lean_string_append(v___x_1246_, v_a_1242_);
lean_dec(v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1247_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_a_1238_);
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1252_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1241_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1241_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 0);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_a_1260_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1261_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58));
v___x_1262_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_1063_);
v___x_1263_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1261_, v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1260_);
lean_dec(v_a_1238_);
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1273_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1273_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1268_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_1269_ = lean_string_append(v___x_1268_, v_a_1264_);
lean_dec(v_a_1264_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1269_);
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_a_1260_);
lean_dec(v_a_1238_);
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
lean_dec(v_json_1063_);
v_a_1274_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1263_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1263_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 0);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1282_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1283_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65));
v___x_1284_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1285_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1063_, v___x_1283_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1282_);
lean_dec(v_a_1260_);
lean_dec(v_a_1238_);
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1295_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1295_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70);
v___x_1291_ = lean_string_append(v___x_1290_, v_a_1286_);
lean_dec(v_a_1286_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_a_1282_);
lean_dec(v_a_1260_);
lean_dec(v_a_1238_);
lean_dec(v_a_1216_);
lean_dec(v_a_1195_);
lean_dec(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec(v_a_1129_);
lean_dec(v_a_1107_);
lean_dec(v_a_1086_);
v_a_1296_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1285_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1285_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 0);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
v_a_1304_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1306_ = v___x_1285_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1285_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1308_, 0, v_a_1086_);
lean_ctor_set(v___x_1308_, 1, v_a_1107_);
lean_ctor_set(v___x_1308_, 2, v_a_1129_);
lean_ctor_set(v___x_1308_, 3, v_a_1151_);
lean_ctor_set(v___x_1308_, 4, v_a_1173_);
lean_ctor_set(v___x_1308_, 5, v_a_1195_);
lean_ctor_set(v___x_1308_, 6, v_a_1216_);
lean_ctor_set(v___x_1308_, 7, v_a_1238_);
lean_ctor_set(v___x_1308_, 8, v_a_1260_);
lean_ctor_set(v___x_1308_, 9, v_a_1282_);
lean_ctor_set(v___x_1308_, 10, v_a_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object* v_00_u03b1_1313_, lean_object* v_inst_1314_, lean_object* v_json_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(v_inst_1314_, v_json_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object* v_inst_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1318_, 0, lean_box(0));
lean_closure_set(v___x_1318_, 1, v_inst_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object* v_00_u03b1_1319_, lean_object* v_inst_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, v_inst_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object* v_d_1322_){
_start:
{
lean_object* v_fullRange_x3f_1323_; 
v_fullRange_x3f_1323_ = lean_ctor_get(v_d_1322_, 1);
if (lean_obj_tag(v_fullRange_x3f_1323_) == 0)
{
lean_object* v_range_1324_; 
v_range_1324_ = lean_ctor_get(v_d_1322_, 0);
lean_inc_ref(v_range_1324_);
return v_range_1324_;
}
else
{
lean_object* v_val_1325_; 
v_val_1325_ = lean_ctor_get(v_fullRange_x3f_1323_, 0);
lean_inc(v_val_1325_);
return v_val_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object* v_d_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1326_);
lean_dec_ref(v_d_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object* v_00_u03b1_1328_, lean_object* v_d_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object* v_00_u03b1_1331_, lean_object* v_d_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Lsp_DiagnosticWith_fullRange(v_00_u03b1_1331_, v_d_1332_);
lean_dec_ref(v_d_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1342_) == 0)
{
if (lean_obj_tag(v_x_1343_) == 0)
{
uint8_t v___x_1344_; 
v___x_1344_ = 1;
return v___x_1344_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = 0;
return v___x_1345_;
}
}
else
{
if (lean_obj_tag(v_x_1343_) == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = 0;
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; lean_object* v_val_1348_; uint8_t v___x_1349_; 
v_val_1347_ = lean_ctor_get(v_x_1342_, 0);
v_val_1348_ = lean_ctor_get(v_x_1343_, 0);
v___x_1349_ = lean_int_dec_eq(v_val_1347_, v_val_1348_);
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_x_1350_, v_x_1351_);
lean_dec(v_x_1351_);
lean_dec(v_x_1350_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(uint8_t v___x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1355_) == 0)
{
if (lean_obj_tag(v_x_1356_) == 0)
{
uint8_t v___x_1357_; 
v___x_1357_ = 1;
return v___x_1357_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
}
else
{
if (lean_obj_tag(v_x_1356_) == 0)
{
uint8_t v___x_1359_; 
v___x_1359_ = 0;
return v___x_1359_;
}
else
{
lean_object* v_val_1360_; uint8_t v___x_1361_; 
v_val_1360_ = lean_ctor_get(v_x_1356_, 0);
v___x_1361_ = lean_unbox(v_val_1360_);
if (v___x_1361_ == 0)
{
lean_object* v_val_1362_; uint8_t v___x_1363_; 
v_val_1362_ = lean_ctor_get(v_x_1355_, 0);
v___x_1363_ = lean_unbox(v_val_1362_);
if (v___x_1363_ == 0)
{
return v___x_1354_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_unbox(v_val_1360_);
return v___x_1364_;
}
}
else
{
lean_object* v_val_1365_; uint8_t v___x_1366_; 
v_val_1365_ = lean_ctor_get(v_x_1355_, 0);
v___x_1366_ = lean_unbox(v_val_1365_);
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object* v___x_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
uint8_t v___x_796__boxed_1370_; uint8_t v_res_1371_; lean_object* v_r_1372_; 
v___x_796__boxed_1370_ = lean_unbox(v___x_1367_);
v_res_1371_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v___x_796__boxed_1370_, v_x_1368_, v_x_1369_);
lean_dec(v_x_1369_);
lean_dec(v_x_1368_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(lean_object* v_xs_1373_, lean_object* v_ys_1374_, lean_object* v_x_1375_){
_start:
{
lean_object* v_zero_1376_; uint8_t v_isZero_1377_; 
v_zero_1376_ = lean_unsigned_to_nat(0u);
v_isZero_1377_ = lean_nat_dec_eq(v_x_1375_, v_zero_1376_);
if (v_isZero_1377_ == 1)
{
lean_dec(v_x_1375_);
return v_isZero_1377_;
}
else
{
lean_object* v_one_1378_; lean_object* v_n_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; 
v_one_1378_ = lean_unsigned_to_nat(1u);
v_n_1379_ = lean_nat_sub(v_x_1375_, v_one_1378_);
lean_dec(v_x_1375_);
v___x_1380_ = lean_array_fget_borrowed(v_xs_1373_, v_n_1379_);
v___x_1381_ = lean_array_fget_borrowed(v_ys_1374_, v_n_1379_);
v___x_1382_ = lean_unbox(v___x_1380_);
v___x_1383_ = lean_unbox(v___x_1381_);
v___x_1384_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec(v_n_1379_);
return v___x_1384_;
}
else
{
v_x_1375_ = v_n_1379_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(lean_object* v_xs_1386_, lean_object* v_ys_1387_, lean_object* v_x_1388_){
_start:
{
uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_res_1389_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1386_, v_ys_1387_, v_x_1388_);
lean_dec_ref(v_ys_1387_);
lean_dec_ref(v_xs_1386_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
if (lean_obj_tag(v_x_1392_) == 0)
{
uint8_t v___x_1393_; 
v___x_1393_ = 1;
return v___x_1393_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = 0;
return v___x_1394_;
}
}
else
{
if (lean_obj_tag(v_x_1392_) == 0)
{
uint8_t v___x_1395_; 
v___x_1395_ = 0;
return v___x_1395_;
}
else
{
lean_object* v_val_1396_; lean_object* v_val_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_val_1396_ = lean_ctor_get(v_x_1391_, 0);
v_val_1397_ = lean_ctor_get(v_x_1392_, 0);
v___x_1398_ = lean_array_get_size(v_val_1396_);
v___x_1399_ = lean_array_get_size(v_val_1397_);
v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
return v___x_1400_;
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_val_1396_, v_val_1397_, v___x_1398_);
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
uint8_t v_res_1404_; lean_object* v_r_1405_; 
v_res_1404_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_x_1402_, v_x_1403_);
lean_dec(v_x_1403_);
lean_dec(v_x_1402_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
if (lean_obj_tag(v_x_1407_) == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = 1;
return v___x_1408_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = 0;
return v___x_1409_;
}
}
else
{
if (lean_obj_tag(v_x_1407_) == 0)
{
uint8_t v___x_1410_; 
v___x_1410_ = 0;
return v___x_1410_;
}
else
{
lean_object* v_val_1411_; lean_object* v_val_1412_; uint8_t v___x_1413_; 
v_val_1411_ = lean_ctor_get(v_x_1406_, 0);
v_val_1412_ = lean_ctor_get(v_x_1407_, 0);
v___x_1413_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_val_1411_, v_val_1412_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
uint8_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_x_1414_, v_x_1415_);
lean_dec(v_x_1415_);
lean_dec(v_x_1414_);
v_r_1417_ = lean_box(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
if (lean_obj_tag(v_x_1419_) == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = 1;
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
}
else
{
if (lean_obj_tag(v_x_1419_) == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = 0;
return v___x_1422_;
}
else
{
lean_object* v_val_1423_; lean_object* v_val_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; 
v_val_1423_ = lean_ctor_get(v_x_1418_, 0);
v_val_1424_ = lean_ctor_get(v_x_1419_, 0);
v___x_1425_ = lean_unbox(v_val_1423_);
v___x_1426_ = lean_unbox(v_val_1424_);
v___x_1427_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v___x_1425_, v___x_1426_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_x_1428_, v_x_1429_);
lean_dec(v_x_1429_);
lean_dec(v_x_1428_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(lean_object* v_xs_1432_, lean_object* v_ys_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v_zero_1435_; uint8_t v_isZero_1436_; 
v_zero_1435_ = lean_unsigned_to_nat(0u);
v_isZero_1436_ = lean_nat_dec_eq(v_x_1434_, v_zero_1435_);
if (v_isZero_1436_ == 1)
{
lean_dec(v_x_1434_);
return v_isZero_1436_;
}
else
{
lean_object* v_one_1437_; lean_object* v_n_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; uint8_t v___x_1442_; uint8_t v___x_1443_; 
v_one_1437_ = lean_unsigned_to_nat(1u);
v_n_1438_ = lean_nat_sub(v_x_1434_, v_one_1437_);
lean_dec(v_x_1434_);
v___x_1439_ = lean_array_fget_borrowed(v_xs_1432_, v_n_1438_);
v___x_1440_ = lean_array_fget_borrowed(v_ys_1433_, v_n_1438_);
v___x_1441_ = lean_unbox(v___x_1439_);
v___x_1442_ = lean_unbox(v___x_1440_);
v___x_1443_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_dec(v_n_1438_);
return v___x_1443_;
}
else
{
v_x_1434_ = v_n_1438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_xs_1445_, lean_object* v_ys_1446_, lean_object* v_x_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1445_, v_ys_1446_, v_x_1447_);
lean_dec_ref(v_ys_1446_);
lean_dec_ref(v_xs_1445_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
if (lean_obj_tag(v_x_1451_) == 0)
{
uint8_t v___x_1452_; 
v___x_1452_ = 1;
return v___x_1452_;
}
else
{
uint8_t v___x_1453_; 
v___x_1453_ = 0;
return v___x_1453_;
}
}
else
{
if (lean_obj_tag(v_x_1451_) == 0)
{
uint8_t v___x_1454_; 
v___x_1454_ = 0;
return v___x_1454_;
}
else
{
lean_object* v_val_1455_; lean_object* v_val_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_val_1455_ = lean_ctor_get(v_x_1450_, 0);
v_val_1456_ = lean_ctor_get(v_x_1451_, 0);
v___x_1457_ = lean_array_get_size(v_val_1455_);
v___x_1458_ = lean_array_get_size(v_val_1456_);
v___x_1459_ = lean_nat_dec_eq(v___x_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
return v___x_1459_;
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_val_1455_, v_val_1456_, v___x_1457_);
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
uint8_t v_res_1463_; lean_object* v_r_1464_; 
v_res_1463_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_x_1461_, v_x_1462_);
lean_dec(v_x_1462_);
lean_dec(v_x_1461_);
v_r_1464_ = lean_box(v_res_1463_);
return v_r_1464_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
if (lean_obj_tag(v_x_1466_) == 0)
{
uint8_t v___x_1467_; 
v___x_1467_ = 1;
return v___x_1467_;
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = 0;
return v___x_1468_;
}
}
else
{
if (lean_obj_tag(v_x_1466_) == 0)
{
uint8_t v___x_1469_; 
v___x_1469_ = 0;
return v___x_1469_;
}
else
{
lean_object* v_val_1470_; lean_object* v_val_1471_; uint8_t v___x_1472_; 
v_val_1470_ = lean_ctor_get(v_x_1465_, 0);
v_val_1471_ = lean_ctor_get(v_x_1466_, 0);
v___x_1472_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_val_1470_, v_val_1471_);
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v_res_1475_; lean_object* v_r_1476_; 
v_res_1475_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_x_1473_, v_x_1474_);
lean_dec(v_x_1474_);
lean_dec(v_x_1473_);
v_r_1476_ = lean_box(v_res_1475_);
return v_r_1476_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
if (lean_obj_tag(v_x_1478_) == 0)
{
uint8_t v___x_1479_; 
v___x_1479_ = 1;
return v___x_1479_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = 0;
return v___x_1480_;
}
}
else
{
if (lean_obj_tag(v_x_1478_) == 0)
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
return v___x_1481_;
}
else
{
lean_object* v_val_1482_; lean_object* v_val_1483_; uint8_t v___x_1484_; 
v_val_1482_ = lean_ctor_get(v_x_1477_, 0);
v_val_1483_ = lean_ctor_get(v_x_1478_, 0);
v___x_1484_ = lean_string_dec_eq(v_val_1482_, v_val_1483_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_x_1485_, v_x_1486_);
lean_dec(v_x_1486_);
lean_dec(v_x_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
if (lean_obj_tag(v_x_1489_) == 0)
{
if (lean_obj_tag(v_x_1490_) == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = 1;
return v___x_1491_;
}
else
{
uint8_t v___x_1492_; 
v___x_1492_ = 0;
return v___x_1492_;
}
}
else
{
if (lean_obj_tag(v_x_1490_) == 0)
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
else
{
lean_object* v_val_1494_; lean_object* v_val_1495_; uint8_t v___x_1496_; 
v_val_1494_ = lean_ctor_get(v_x_1489_, 0);
v_val_1495_ = lean_ctor_get(v_x_1490_, 0);
v___x_1496_ = l_Lean_Lsp_instBEqRange_beq(v_val_1494_, v_val_1495_);
return v___x_1496_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_x_1497_, v_x_1498_);
lean_dec(v_x_1498_);
lean_dec(v_x_1497_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(lean_object* v_xs_1501_, lean_object* v_ys_1502_, lean_object* v_x_1503_){
_start:
{
lean_object* v_zero_1504_; uint8_t v_isZero_1505_; 
v_zero_1504_ = lean_unsigned_to_nat(0u);
v_isZero_1505_ = lean_nat_dec_eq(v_x_1503_, v_zero_1504_);
if (v_isZero_1505_ == 1)
{
lean_dec(v_x_1503_);
return v_isZero_1505_;
}
else
{
lean_object* v_one_1506_; lean_object* v_n_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_one_1506_ = lean_unsigned_to_nat(1u);
v_n_1507_ = lean_nat_sub(v_x_1503_, v_one_1506_);
lean_dec(v_x_1503_);
v___x_1508_ = lean_array_fget_borrowed(v_xs_1501_, v_n_1507_);
v___x_1509_ = lean_array_fget_borrowed(v_ys_1502_, v_n_1507_);
v___x_1510_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_dec(v_n_1507_);
return v___x_1510_;
}
else
{
v_x_1503_ = v_n_1507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_xs_1512_, lean_object* v_ys_1513_, lean_object* v_x_1514_){
_start:
{
uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_res_1515_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1512_, v_ys_1513_, v_x_1514_);
lean_dec_ref(v_ys_1513_);
lean_dec_ref(v_xs_1512_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 0)
{
if (lean_obj_tag(v_x_1518_) == 0)
{
uint8_t v___x_1519_; 
v___x_1519_ = 1;
return v___x_1519_;
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = 0;
return v___x_1520_;
}
}
else
{
if (lean_obj_tag(v_x_1518_) == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = 0;
return v___x_1521_;
}
else
{
lean_object* v_val_1522_; lean_object* v_val_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v_val_1522_ = lean_ctor_get(v_x_1517_, 0);
v_val_1523_ = lean_ctor_get(v_x_1518_, 0);
v___x_1524_ = lean_array_get_size(v_val_1522_);
v___x_1525_ = lean_array_get_size(v_val_1523_);
v___x_1526_ = lean_nat_dec_eq(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
return v___x_1526_;
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_val_1522_, v_val_1523_, v___x_1524_);
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_res_1530_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_x_1528_, v_x_1529_);
lean_dec(v_x_1529_);
lean_dec(v_x_1528_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v_range_1534_; lean_object* v_fullRange_x3f_1535_; lean_object* v_severity_x3f_1536_; lean_object* v_isSilent_x3f_1537_; lean_object* v_code_x3f_1538_; lean_object* v_source_x3f_1539_; lean_object* v_message_1540_; lean_object* v_tags_x3f_1541_; lean_object* v_leanTags_x3f_1542_; lean_object* v_relatedInformation_x3f_1543_; lean_object* v_data_x3f_1544_; lean_object* v_range_1545_; lean_object* v_fullRange_x3f_1546_; lean_object* v_severity_x3f_1547_; lean_object* v_isSilent_x3f_1548_; lean_object* v_code_x3f_1549_; lean_object* v_source_x3f_1550_; lean_object* v_message_1551_; lean_object* v_tags_x3f_1552_; lean_object* v_leanTags_x3f_1553_; lean_object* v_relatedInformation_x3f_1554_; lean_object* v_data_x3f_1555_; uint8_t v___x_1556_; 
v_range_1534_ = lean_ctor_get(v_x_1532_, 0);
v_fullRange_x3f_1535_ = lean_ctor_get(v_x_1532_, 1);
v_severity_x3f_1536_ = lean_ctor_get(v_x_1532_, 2);
v_isSilent_x3f_1537_ = lean_ctor_get(v_x_1532_, 3);
v_code_x3f_1538_ = lean_ctor_get(v_x_1532_, 4);
v_source_x3f_1539_ = lean_ctor_get(v_x_1532_, 5);
v_message_1540_ = lean_ctor_get(v_x_1532_, 6);
v_tags_x3f_1541_ = lean_ctor_get(v_x_1532_, 7);
v_leanTags_x3f_1542_ = lean_ctor_get(v_x_1532_, 8);
v_relatedInformation_x3f_1543_ = lean_ctor_get(v_x_1532_, 9);
v_data_x3f_1544_ = lean_ctor_get(v_x_1532_, 10);
v_range_1545_ = lean_ctor_get(v_x_1533_, 0);
v_fullRange_x3f_1546_ = lean_ctor_get(v_x_1533_, 1);
v_severity_x3f_1547_ = lean_ctor_get(v_x_1533_, 2);
v_isSilent_x3f_1548_ = lean_ctor_get(v_x_1533_, 3);
v_code_x3f_1549_ = lean_ctor_get(v_x_1533_, 4);
v_source_x3f_1550_ = lean_ctor_get(v_x_1533_, 5);
v_message_1551_ = lean_ctor_get(v_x_1533_, 6);
v_tags_x3f_1552_ = lean_ctor_get(v_x_1533_, 7);
v_leanTags_x3f_1553_ = lean_ctor_get(v_x_1533_, 8);
v_relatedInformation_x3f_1554_ = lean_ctor_get(v_x_1533_, 9);
v_data_x3f_1555_ = lean_ctor_get(v_x_1533_, 10);
v___x_1556_ = l_Lean_Lsp_instBEqRange_beq(v_range_1534_, v_range_1545_);
if (v___x_1556_ == 0)
{
return v___x_1556_;
}
else
{
uint8_t v___x_1557_; 
v___x_1557_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_fullRange_x3f_1535_, v_fullRange_x3f_1546_);
if (v___x_1557_ == 0)
{
return v___x_1557_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_severity_x3f_1536_, v_severity_x3f_1547_);
if (v___x_1558_ == 0)
{
return v___x_1558_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v___x_1558_, v_isSilent_x3f_1537_, v_isSilent_x3f_1548_);
if (v___x_1559_ == 0)
{
return v___x_1559_;
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_code_x3f_1538_, v_code_x3f_1549_);
if (v___x_1560_ == 0)
{
return v___x_1560_;
}
else
{
uint8_t v___x_1561_; 
v___x_1561_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_source_x3f_1539_, v_source_x3f_1550_);
if (v___x_1561_ == 0)
{
return v___x_1561_;
}
else
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_string_dec_eq(v_message_1540_, v_message_1551_);
if (v___x_1562_ == 0)
{
return v___x_1562_;
}
else
{
uint8_t v___x_1563_; 
v___x_1563_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_tags_x3f_1541_, v_tags_x3f_1552_);
if (v___x_1563_ == 0)
{
return v___x_1563_;
}
else
{
uint8_t v___x_1564_; 
v___x_1564_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_leanTags_x3f_1542_, v_leanTags_x3f_1553_);
if (v___x_1564_ == 0)
{
return v___x_1564_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_relatedInformation_x3f_1543_, v_relatedInformation_x3f_1554_);
if (v___x_1565_ == 0)
{
return v___x_1565_;
}
else
{
uint8_t v___x_1566_; 
v___x_1566_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_data_x3f_1544_, v_data_x3f_1555_);
return v___x_1566_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v_x_1567_, v_x_1568_);
lean_dec_ref(v_x_1568_);
lean_dec_ref(v_x_1567_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(lean_object* v_xs_1571_, lean_object* v_ys_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v_zero_1574_; uint8_t v_isZero_1575_; 
v_zero_1574_ = lean_unsigned_to_nat(0u);
v_isZero_1575_ = lean_nat_dec_eq(v_x_1573_, v_zero_1574_);
if (v_isZero_1575_ == 1)
{
lean_dec(v_x_1573_);
return v_isZero_1575_;
}
else
{
lean_object* v_one_1576_; lean_object* v_n_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v_one_1576_ = lean_unsigned_to_nat(1u);
v_n_1577_ = lean_nat_sub(v_x_1573_, v_one_1576_);
lean_dec(v_x_1573_);
v___x_1578_ = lean_array_fget_borrowed(v_xs_1571_, v_n_1577_);
v___x_1579_ = lean_array_fget_borrowed(v_ys_1572_, v_n_1577_);
v___x_1580_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec(v_n_1577_);
return v___x_1580_;
}
else
{
v_x_1573_ = v_n_1577_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(lean_object* v_xs_1582_, lean_object* v_ys_1583_, lean_object* v_x_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1582_, v_ys_1583_, v_x_1584_);
lean_dec_ref(v_ys_1583_);
lean_dec_ref(v_xs_1582_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_uri_1589_; lean_object* v_version_x3f_1590_; lean_object* v_isIncremental_x3f_1591_; lean_object* v_diagnostics_1592_; lean_object* v_uri_1593_; lean_object* v_version_x3f_1594_; lean_object* v_isIncremental_x3f_1595_; lean_object* v_diagnostics_1596_; uint8_t v___x_1597_; 
v_uri_1589_ = lean_ctor_get(v_x_1587_, 0);
v_version_x3f_1590_ = lean_ctor_get(v_x_1587_, 1);
v_isIncremental_x3f_1591_ = lean_ctor_get(v_x_1587_, 2);
v_diagnostics_1592_ = lean_ctor_get(v_x_1587_, 3);
v_uri_1593_ = lean_ctor_get(v_x_1588_, 0);
v_version_x3f_1594_ = lean_ctor_get(v_x_1588_, 1);
v_isIncremental_x3f_1595_ = lean_ctor_get(v_x_1588_, 2);
v_diagnostics_1596_ = lean_ctor_get(v_x_1588_, 3);
v___x_1597_ = lean_string_dec_eq(v_uri_1589_, v_uri_1593_);
if (v___x_1597_ == 0)
{
return v___x_1597_;
}
else
{
uint8_t v___x_1598_; 
v___x_1598_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_version_x3f_1590_, v_version_x3f_1594_);
if (v___x_1598_ == 0)
{
return v___x_1598_;
}
else
{
uint8_t v___x_1599_; 
v___x_1599_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v___x_1598_, v_isIncremental_x3f_1591_, v_isIncremental_x3f_1595_);
if (v___x_1599_ == 0)
{
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = lean_array_get_size(v_diagnostics_1592_);
v___x_1601_ = lean_array_get_size(v_diagnostics_1596_);
v___x_1602_ = lean_nat_dec_eq(v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
return v___x_1602_;
}
else
{
uint8_t v___x_1603_; 
v___x_1603_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_diagnostics_1592_, v_diagnostics_1596_, v___x_1600_);
return v___x_1603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
uint8_t v_res_1606_; lean_object* v_r_1607_; 
v_res_1606_ = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(v_x_1604_, v_x_1605_);
lean_dec_ref(v_x_1605_);
lean_dec_ref(v_x_1604_);
v_r_1607_ = lean_box(v_res_1606_);
return v_r_1607_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(lean_object* v_xs_1608_, lean_object* v_ys_1609_, lean_object* v_hsz_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
uint8_t v___x_1613_; 
v___x_1613_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1608_, v_ys_1609_, v_x_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(lean_object* v_xs_1614_, lean_object* v_ys_1615_, lean_object* v_hsz_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(v_xs_1614_, v_ys_1615_, v_hsz_1616_, v_x_1617_, v_x_1618_);
lean_dec_ref(v_ys_1615_);
lean_dec_ref(v_xs_1614_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(lean_object* v_xs_1621_, lean_object* v_ys_1622_, lean_object* v_hsz_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1621_, v_ys_1622_, v_x_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(lean_object* v_xs_1627_, lean_object* v_ys_1628_, lean_object* v_hsz_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(v_xs_1627_, v_ys_1628_, v_hsz_1629_, v_x_1630_, v_x_1631_);
lean_dec_ref(v_ys_1628_);
lean_dec_ref(v_xs_1627_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(lean_object* v_xs_1634_, lean_object* v_ys_1635_, lean_object* v_hsz_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
uint8_t v___x_1639_; 
v___x_1639_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1634_, v_ys_1635_, v_x_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(lean_object* v_xs_1640_, lean_object* v_ys_1641_, lean_object* v_hsz_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
uint8_t v_res_1645_; lean_object* v_r_1646_; 
v_res_1645_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(v_xs_1640_, v_ys_1641_, v_hsz_1642_, v_x_1643_, v_x_1644_);
lean_dec_ref(v_ys_1641_);
lean_dec_ref(v_xs_1640_);
v_r_1646_ = lean_box(v_res_1645_);
return v_r_1646_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(lean_object* v_xs_1647_, lean_object* v_ys_1648_, lean_object* v_hsz_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1647_, v_ys_1648_, v_x_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(lean_object* v_xs_1653_, lean_object* v_ys_1654_, lean_object* v_hsz_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(v_xs_1653_, v_ys_1654_, v_hsz_1655_, v_x_1656_, v_x_1657_);
lean_dec_ref(v_ys_1654_);
lean_dec_ref(v_xs_1653_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object* v_k_1662_, lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v___x_1664_; 
lean_dec_ref(v_k_1662_);
v___x_1664_ = lean_box(0);
return v___x_1664_;
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1676_; 
v_val_1665_ = lean_ctor_get(v_x_1663_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1667_ = v_x_1663_;
v_isShared_1668_ = v_isSharedCheck_1676_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_val_1665_);
lean_dec(v_x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1676_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = l_Lean_JsonNumber_fromInt(v_val_1665_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 2);
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_k_1662_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
return v___x_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object* v_k_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref(v_k_1677_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_val_1680_ = lean_ctor_get(v_x_1678_, 0);
v___x_1681_ = lean_alloc_ctor(1, 0, 1);
v___x_1682_ = lean_unbox(v_val_1680_);
lean_ctor_set_uint8(v___x_1681_, 0, v___x_1682_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_k_1677_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(lean_object* v_k_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v_k_1686_, v_x_1687_);
lean_dec(v_x_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(size_t v_sz_1689_, size_t v_i_1690_, lean_object* v_bs_1691_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_lt(v_i_1690_, v_sz_1689_);
if (v___x_1692_ == 0)
{
return v_bs_1691_;
}
else
{
lean_object* v_v_1693_; lean_object* v___x_1694_; lean_object* v_bs_x27_1695_; lean_object* v___y_1697_; uint8_t v___x_1702_; 
v_v_1693_ = lean_array_uget(v_bs_1691_, v_i_1690_);
v___x_1694_ = lean_unsigned_to_nat(0u);
v_bs_x27_1695_ = lean_array_uset(v_bs_1691_, v_i_1690_, v___x_1694_);
v___x_1702_ = lean_unbox(v_v_1693_);
lean_dec(v_v_1693_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1697_ = v___x_1703_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1697_ = v___x_1704_;
goto v___jp_1696_;
}
v___jp_1696_:
{
size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1690_, v___x_1698_);
lean_inc(v___y_1697_);
v___x_1700_ = lean_array_uset(v_bs_x27_1695_, v_i_1690_, v___y_1697_);
v_i_1690_ = v___x_1699_;
v_bs_1691_ = v___x_1700_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(lean_object* v_sz_1705_, lean_object* v_i_1706_, lean_object* v_bs_1707_){
_start:
{
size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1705_);
lean_dec(v_sz_1705_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_boxed_1708_, v_i_boxed_1709_, v_bs_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(lean_object* v_a_1711_){
_start:
{
size_t v_sz_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_sz_1712_ = lean_array_size(v_a_1711_);
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_1712_, v___x_1713_, v_a_1711_);
v___x_1715_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(lean_object* v_k_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_object* v___x_1718_; 
lean_dec_ref(v_k_1716_);
v___x_1718_ = lean_box(0);
return v___x_1718_;
}
else
{
lean_object* v_val_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_val_1719_ = lean_ctor_get(v_x_1717_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v_x_1717_, 1);
v___x_1720_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(v_val_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_k_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(lean_object* v_k_1724_, lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1725_) == 0)
{
lean_object* v___x_1726_; 
lean_dec_ref(v_k_1724_);
v___x_1726_ = lean_box(0);
return v___x_1726_;
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_val_1727_ = lean_ctor_get(v_x_1725_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v_x_1725_, 1);
v___x_1728_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_1727_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_k_1724_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(size_t v_sz_1732_, size_t v_i_1733_, lean_object* v_bs_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_lt(v_i_1733_, v_sz_1732_);
if (v___x_1735_ == 0)
{
return v_bs_1734_;
}
else
{
lean_object* v_v_1736_; lean_object* v___x_1737_; lean_object* v_bs_x27_1738_; lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v_v_1736_ = lean_array_uget(v_bs_1734_, v_i_1733_);
v___x_1737_ = lean_unsigned_to_nat(0u);
v_bs_x27_1738_ = lean_array_uset(v_bs_1734_, v_i_1733_, v___x_1737_);
v___x_1739_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_v_1736_);
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1733_, v___x_1740_);
v___x_1742_ = lean_array_uset(v_bs_x27_1738_, v_i_1733_, v___x_1739_);
v_i_1733_ = v___x_1741_;
v_bs_1734_ = v___x_1742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_1744_, lean_object* v_i_1745_, lean_object* v_bs_1746_){
_start:
{
size_t v_sz_boxed_1747_; size_t v_i_boxed_1748_; lean_object* v_res_1749_; 
v_sz_boxed_1747_ = lean_unbox_usize(v_sz_1744_);
lean_dec(v_sz_1744_);
v_i_boxed_1748_ = lean_unbox_usize(v_i_1745_);
lean_dec(v_i_1745_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_boxed_1747_, v_i_boxed_1748_, v_bs_1746_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(lean_object* v_a_1750_){
_start:
{
size_t v_sz_1751_; size_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_sz_1751_ = lean_array_size(v_a_1750_);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_1751_, v___x_1752_, v_a_1750_);
v___x_1754_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(lean_object* v_k_1755_, lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_k_1755_);
v___x_1757_ = lean_box(0);
return v___x_1757_;
}
else
{
lean_object* v_val_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_val_1758_ = lean_ctor_get(v_x_1756_, 0);
lean_inc(v_val_1758_);
lean_dec_ref_known(v_x_1756_, 1);
v___x_1759_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(v_val_1758_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_k_1755_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(lean_object* v_k_1763_, lean_object* v_x_1764_){
_start:
{
if (lean_obj_tag(v_x_1764_) == 0)
{
lean_object* v___x_1765_; 
lean_dec_ref(v_k_1763_);
v___x_1765_ = lean_box(0);
return v___x_1765_;
}
else
{
lean_object* v_val_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_val_1766_ = lean_ctor_get(v_x_1764_, 0);
lean_inc(v_val_1766_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_k_1763_);
lean_ctor_set(v___x_1767_, 1, v_val_1766_);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(lean_object* v_k_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v_k_1770_, v_x_1771_);
lean_dec(v_x_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(lean_object* v_k_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v___y_1776_; 
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_object* v___x_1780_; 
lean_dec_ref(v_k_1773_);
v___x_1780_ = lean_box(0);
return v___x_1780_;
}
else
{
lean_object* v_val_1781_; 
v_val_1781_ = lean_ctor_get(v_x_1774_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v_x_1774_, 1);
if (lean_obj_tag(v_val_1781_) == 0)
{
lean_object* v_i_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1790_; 
v_i_1782_ = lean_ctor_get(v_val_1781_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_val_1781_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1784_ = v_val_1781_;
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_i_1782_);
lean_dec(v_val_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = l_Lean_JsonNumber_fromInt(v_i_1782_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 2);
lean_ctor_set(v___x_1784_, 0, v___x_1786_);
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
v___y_1776_ = v___x_1788_;
goto v___jp_1775_;
}
}
}
else
{
lean_object* v_s_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_s_1791_ = lean_ctor_get(v_val_1781_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_val_1781_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v_val_1781_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_s_1791_);
lean_dec(v_val_1781_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 3);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_s_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
v___y_1776_ = v___x_1796_;
goto v___jp_1775_;
}
}
}
}
v___jp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_k_1773_);
lean_ctor_set(v___x_1777_, 1, v___y_1776_);
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(lean_object* v_k_1799_, lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v_k_1799_);
v___x_1801_ = lean_box(0);
return v___x_1801_;
}
else
{
lean_object* v_val_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1812_; 
v_val_1802_ = lean_ctor_get(v_x_1800_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1800_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1804_ = v_x_1800_;
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_val_1802_);
lean_dec(v_x_1800_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 3);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_val_1802_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_k_1799_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(lean_object* v_k_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v___y_1816_; 
if (lean_obj_tag(v_x_1814_) == 0)
{
lean_object* v___x_1820_; 
lean_dec_ref(v_k_1813_);
v___x_1820_ = lean_box(0);
return v___x_1820_;
}
else
{
lean_object* v_val_1821_; uint8_t v___x_1822_; 
v_val_1821_ = lean_ctor_get(v_x_1814_, 0);
v___x_1822_ = lean_unbox(v_val_1821_);
switch(v___x_1822_)
{
case 0:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1816_ = v___x_1823_;
goto v___jp_1815_;
}
case 1:
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1816_ = v___x_1824_;
goto v___jp_1815_;
}
case 2:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
v___y_1816_ = v___x_1825_;
goto v___jp_1815_;
}
default: 
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
v___y_1816_ = v___x_1826_;
goto v___jp_1815_;
}
}
}
v___jp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_inc(v___y_1816_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_k_1813_);
lean_ctor_set(v___x_1817_, 1, v___y_1816_);
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(lean_object* v_k_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v_k_1827_, v_x_1828_);
lean_dec(v_x_1828_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(size_t v_sz_1830_, size_t v_i_1831_, lean_object* v_bs_1832_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_lt(v_i_1831_, v_sz_1830_);
if (v___x_1833_ == 0)
{
return v_bs_1832_;
}
else
{
lean_object* v_v_1834_; lean_object* v___x_1835_; lean_object* v_bs_x27_1836_; lean_object* v___y_1838_; uint8_t v___x_1843_; 
v_v_1834_ = lean_array_uget(v_bs_1832_, v_i_1831_);
v___x_1835_ = lean_unsigned_to_nat(0u);
v_bs_x27_1836_ = lean_array_uset(v_bs_1832_, v_i_1831_, v___x_1835_);
v___x_1843_ = lean_unbox(v_v_1834_);
lean_dec(v_v_1834_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1838_ = v___x_1844_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1838_ = v___x_1845_;
goto v___jp_1837_;
}
v___jp_1837_:
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1831_, v___x_1839_);
lean_inc(v___y_1838_);
v___x_1841_ = lean_array_uset(v_bs_x27_1836_, v_i_1831_, v___y_1838_);
v_i_1831_ = v___x_1840_;
v_bs_1832_ = v___x_1841_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(lean_object* v_sz_1846_, lean_object* v_i_1847_, lean_object* v_bs_1848_){
_start:
{
size_t v_sz_boxed_1849_; size_t v_i_boxed_1850_; lean_object* v_res_1851_; 
v_sz_boxed_1849_ = lean_unbox_usize(v_sz_1846_);
lean_dec(v_sz_1846_);
v_i_boxed_1850_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_boxed_1849_, v_i_boxed_1850_, v_bs_1848_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(lean_object* v_a_1852_){
_start:
{
size_t v_sz_1853_; size_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_sz_1853_ = lean_array_size(v_a_1852_);
v___x_1854_ = ((size_t)0ULL);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_1853_, v___x_1854_, v_a_1852_);
v___x_1856_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(lean_object* v_k_1857_, lean_object* v_x_1858_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
lean_object* v___x_1859_; 
lean_dec_ref(v_k_1857_);
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
else
{
lean_object* v_val_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_val_1860_ = lean_ctor_get(v_x_1858_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v_x_1858_, 1);
v___x_1861_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(v_val_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v_k_1857_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(lean_object* v_x_1865_){
_start:
{
lean_object* v_range_1866_; lean_object* v_fullRange_x3f_1867_; lean_object* v_severity_x3f_1868_; lean_object* v_isSilent_x3f_1869_; lean_object* v_code_x3f_1870_; lean_object* v_source_x3f_1871_; lean_object* v_message_1872_; lean_object* v_tags_x3f_1873_; lean_object* v_leanTags_x3f_1874_; lean_object* v_relatedInformation_x3f_1875_; lean_object* v_data_x3f_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_range_1866_ = lean_ctor_get(v_x_1865_, 0);
lean_inc_ref(v_range_1866_);
v_fullRange_x3f_1867_ = lean_ctor_get(v_x_1865_, 1);
lean_inc(v_fullRange_x3f_1867_);
v_severity_x3f_1868_ = lean_ctor_get(v_x_1865_, 2);
lean_inc(v_severity_x3f_1868_);
v_isSilent_x3f_1869_ = lean_ctor_get(v_x_1865_, 3);
lean_inc(v_isSilent_x3f_1869_);
v_code_x3f_1870_ = lean_ctor_get(v_x_1865_, 4);
lean_inc(v_code_x3f_1870_);
v_source_x3f_1871_ = lean_ctor_get(v_x_1865_, 5);
lean_inc(v_source_x3f_1871_);
v_message_1872_ = lean_ctor_get(v_x_1865_, 6);
lean_inc(v_message_1872_);
v_tags_x3f_1873_ = lean_ctor_get(v_x_1865_, 7);
lean_inc(v_tags_x3f_1873_);
v_leanTags_x3f_1874_ = lean_ctor_get(v_x_1865_, 8);
lean_inc(v_leanTags_x3f_1874_);
v_relatedInformation_x3f_1875_ = lean_ctor_get(v_x_1865_, 9);
lean_inc(v_relatedInformation_x3f_1875_);
v_data_x3f_1876_ = lean_ctor_get(v_x_1865_, 10);
lean_inc(v_data_x3f_1876_);
lean_dec_ref(v_x_1865_);
v___x_1877_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_1878_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1866_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_1883_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(v___x_1882_, v_fullRange_x3f_1867_);
v___x_1884_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_1885_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v___x_1884_, v_severity_x3f_1868_);
lean_dec(v_severity_x3f_1868_);
v___x_1886_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_1887_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1886_, v_isSilent_x3f_1869_);
lean_dec(v_isSilent_x3f_1869_);
v___x_1888_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_1889_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(v___x_1888_, v_code_x3f_1870_);
v___x_1890_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_1891_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(v___x_1890_, v_source_x3f_1871_);
v___x_1892_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_1893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_message_1872_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1880_);
v___x_1896_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_1897_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(v___x_1896_, v_tags_x3f_1873_);
v___x_1898_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_1899_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(v___x_1898_, v_leanTags_x3f_1874_);
v___x_1900_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_1901_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(v___x_1900_, v_relatedInformation_x3f_1875_);
v___x_1902_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1903_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v___x_1902_, v_data_x3f_1876_);
lean_dec(v_data_x3f_1876_);
v___x_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___x_1880_);
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1901_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1899_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1897_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1895_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1891_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1889_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1887_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1885_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1883_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1881_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1916_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1914_, v___x_1915_);
v___x_1917_ = l_Lean_Json_mkObj(v___x_1916_);
lean_dec(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(size_t v_sz_1918_, size_t v_i_1919_, lean_object* v_bs_1920_){
_start:
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_usize_dec_lt(v_i_1919_, v_sz_1918_);
if (v___x_1921_ == 0)
{
return v_bs_1920_;
}
else
{
lean_object* v_v_1922_; lean_object* v___x_1923_; lean_object* v_bs_x27_1924_; lean_object* v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; lean_object* v___x_1928_; 
v_v_1922_ = lean_array_uget(v_bs_1920_, v_i_1919_);
v___x_1923_ = lean_unsigned_to_nat(0u);
v_bs_x27_1924_ = lean_array_uset(v_bs_1920_, v_i_1919_, v___x_1923_);
v___x_1925_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(v_v_1922_);
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1919_, v___x_1926_);
v___x_1928_ = lean_array_uset(v_bs_x27_1924_, v_i_1919_, v___x_1925_);
v_i_1919_ = v___x_1927_;
v_bs_1920_ = v___x_1928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(lean_object* v_sz_1930_, lean_object* v_i_1931_, lean_object* v_bs_1932_){
_start:
{
size_t v_sz_boxed_1933_; size_t v_i_boxed_1934_; lean_object* v_res_1935_; 
v_sz_boxed_1933_ = lean_unbox_usize(v_sz_1930_);
lean_dec(v_sz_1930_);
v_i_boxed_1934_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_boxed_1933_, v_i_boxed_1934_, v_bs_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(lean_object* v_a_1936_){
_start:
{
size_t v_sz_1937_; size_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_sz_1937_ = lean_array_size(v_a_1936_);
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_1937_, v___x_1938_, v_a_1936_);
v___x_1940_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object* v_x_1945_){
_start:
{
lean_object* v_uri_1946_; lean_object* v_version_x3f_1947_; lean_object* v_isIncremental_x3f_1948_; lean_object* v_diagnostics_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_uri_1946_ = lean_ctor_get(v_x_1945_, 0);
lean_inc_ref(v_uri_1946_);
v_version_x3f_1947_ = lean_ctor_get(v_x_1945_, 1);
lean_inc(v_version_x3f_1947_);
v_isIncremental_x3f_1948_ = lean_ctor_get(v_x_1945_, 2);
lean_inc(v_isIncremental_x3f_1948_);
v_diagnostics_1949_ = lean_ctor_get(v_x_1945_, 3);
lean_inc_ref(v_diagnostics_1949_);
lean_dec_ref(v_x_1945_);
v___x_1950_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
v___x_1951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_uri_1946_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
v___x_1956_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(v___x_1955_, v_version_x3f_1947_);
v___x_1957_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
v___x_1958_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1957_, v_isIncremental_x3f_1948_);
lean_dec(v_isIncremental_x3f_1948_);
v___x_1959_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_1960_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(v_diagnostics_1949_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v___x_1953_);
v___x_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___x_1953_);
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1958_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1956_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1954_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1968_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1966_, v___x_1967_);
v___x_1969_ = l_Lean_Json_mkObj(v___x_1968_);
lean_dec(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1974_) == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0));
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Json_getBool_x3f(v_x_1974_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1993_; 
v_a_1985_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1987_ = v___x_1976_;
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1976_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1985_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1989_);
v___x_1991_ = v___x_1987_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(lean_object* v_x_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v_x_1994_);
lean_dec(v_x_1994_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object* v_j_1996_, lean_object* v_k_1997_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = l_Lean_Json_getObjValD(v_j_1996_, v_k_1997_);
v___x_1999_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v___x_1998_);
lean_dec(v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_2000_, lean_object* v_k_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_j_2000_, v_k_2001_);
lean_dec_ref(v_k_2001_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object* v_x_2005_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0));
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Json_getInt_x3f(v_x_2005_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_a_2016_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v___x_2007_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2007_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_a_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object* v_j_2025_, lean_object* v_k_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = l_Lean_Json_getObjValD(v_j_2025_, v_k_2026_);
v___x_2028_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(v___x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_2029_, lean_object* v_k_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_j_2029_, v_k_2030_);
lean_dec_ref(v_k_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(lean_object* v_x_2034_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0));
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_x_2034_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(lean_object* v_j_2038_, lean_object* v_k_2039_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = l_Lean_Json_getObjValD(v_j_2038_, v_k_2039_);
v___x_2041_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(lean_object* v_j_2042_, lean_object* v_k_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_j_2042_, v_k_2043_);
lean_dec_ref(v_k_2043_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(size_t v_sz_2047_, size_t v_i_2048_, lean_object* v_bs_2049_){
_start:
{
uint8_t v___x_2052_; 
v___x_2052_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_bs_2049_);
return v___x_2053_;
}
else
{
lean_object* v_v_2054_; lean_object* v___x_2055_; 
v_v_2054_ = lean_array_uget_borrowed(v_bs_2049_, v_i_2048_);
lean_inc(v_v_2054_);
v___x_2055_ = l_Lean_Json_getNat_x3f(v_v_2054_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; lean_object* v_bs_x27_2058_; uint8_t v_a_2060_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_unsigned_to_nat(0u);
v_bs_x27_2058_ = lean_array_uset(v_bs_2049_, v_i_2048_, v___x_2057_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_dec_eq(v_a_2056_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = lean_nat_dec_eq(v_a_2056_, v___x_2068_);
lean_dec(v_a_2056_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_bs_x27_2058_);
goto v___jp_2050_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = 1;
v_a_2060_ = v___x_2070_;
goto v___jp_2059_;
}
}
else
{
uint8_t v___x_2071_; 
lean_dec(v_a_2056_);
v___x_2071_ = 0;
v_a_2060_ = v___x_2071_;
goto v___jp_2059_;
}
v___jp_2059_:
{
size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2048_, v___x_2061_);
v___x_2063_ = lean_box(v_a_2060_);
v___x_2064_ = lean_array_uset(v_bs_x27_2058_, v_i_2048_, v___x_2063_);
v_i_2048_ = v___x_2062_;
v_bs_2049_ = v___x_2064_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2055_);
lean_dec_ref(v_bs_2049_);
goto v___jp_2050_;
}
}
v___jp_2050_:
{
lean_object* v___x_2051_; 
v___x_2051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0));
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(lean_object* v_sz_2072_, lean_object* v_i_2073_, lean_object* v_bs_2074_){
_start:
{
size_t v_sz_boxed_2075_; size_t v_i_boxed_2076_; lean_object* v_res_2077_; 
v_sz_boxed_2075_ = lean_unbox_usize(v_sz_2072_);
lean_dec(v_sz_2072_);
v_i_boxed_2076_ = lean_unbox_usize(v_i_2073_);
lean_dec(v_i_2073_);
v_res_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_boxed_2075_, v_i_boxed_2076_, v_bs_2074_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2079_) == 4)
{
lean_object* v_elems_2080_; size_t v_sz_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v_elems_2080_ = lean_ctor_get(v_x_2079_, 0);
lean_inc_ref(v_elems_2080_);
lean_dec_ref_known(v_x_2079_, 1);
v_sz_2081_ = lean_array_size(v_elems_2080_);
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_2081_, v___x_2082_, v_elems_2080_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2084_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2085_ = lean_unsigned_to_nat(80u);
v___x_2086_ = l_Lean_Json_pretty(v_x_2079_, v___x_2085_);
v___x_2087_ = lean_string_append(v___x_2084_, v___x_2086_);
lean_dec_ref(v___x_2086_);
v___x_2088_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2089_ = lean_string_append(v___x_2087_, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0));
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(v_x_2093_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2112_; 
v_a_2104_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2106_ = v___x_2095_;
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2095_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_a_2104_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(lean_object* v_j_2113_, lean_object* v_k_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = l_Lean_Json_getObjValD(v_j_2113_, v_k_2114_);
v___x_2116_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(lean_object* v_j_2117_, lean_object* v_k_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_j_2117_, v_k_2118_);
lean_dec_ref(v_k_2118_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(lean_object* v_j_2120_, lean_object* v_k_2121_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = l_Lean_Json_getObjValD(v_j_2120_, v_k_2121_);
v___x_2123_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_j_2124_, lean_object* v_k_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_j_2124_, v_k_2125_);
lean_dec_ref(v_k_2125_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_x_2129_){
_start:
{
if (lean_obj_tag(v_x_2129_) == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0));
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_2129_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2148_; 
v_a_2140_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2142_ = v___x_2131_;
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2131_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_a_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2144_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(lean_object* v_j_2149_, lean_object* v_k_2150_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = l_Lean_Json_getObjValD(v_j_2149_, v_k_2150_);
v___x_2152_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_j_2153_, lean_object* v_k_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_j_2153_, v_k_2154_);
lean_dec_ref(v_k_2154_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(lean_object* v_x_2158_){
_start:
{
uint8_t v_a_2168_; 
if (lean_obj_tag(v_x_2158_) == 0)
{
lean_object* v___x_2172_; 
v___x_2172_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0));
return v___x_2172_;
}
else
{
lean_object* v___x_2173_; 
lean_inc(v_x_2158_);
v___x_2173_ = l_Lean_Json_getNat_x3f(v_x_2158_);
if (lean_obj_tag(v___x_2173_) == 1)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_dec_eq(v_a_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = lean_unsigned_to_nat(2u);
v___x_2178_ = lean_nat_dec_eq(v_a_2174_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_unsigned_to_nat(3u);
v___x_2180_ = lean_nat_dec_eq(v_a_2174_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(4u);
v___x_2182_ = lean_nat_dec_eq(v_a_2174_, v___x_2181_);
lean_dec(v_a_2174_);
if (v___x_2182_ == 0)
{
goto v___jp_2159_;
}
else
{
uint8_t v___x_2183_; 
lean_dec(v_x_2158_);
v___x_2183_ = 3;
v_a_2168_ = v___x_2183_;
goto v___jp_2167_;
}
}
else
{
uint8_t v___x_2184_; 
lean_dec(v_a_2174_);
lean_dec(v_x_2158_);
v___x_2184_ = 2;
v_a_2168_ = v___x_2184_;
goto v___jp_2167_;
}
}
else
{
uint8_t v___x_2185_; 
lean_dec(v_a_2174_);
lean_dec(v_x_2158_);
v___x_2185_ = 1;
v_a_2168_ = v___x_2185_;
goto v___jp_2167_;
}
}
else
{
uint8_t v___x_2186_; 
lean_dec(v_a_2174_);
lean_dec(v_x_2158_);
v___x_2186_ = 0;
v_a_2168_ = v___x_2186_;
goto v___jp_2167_;
}
}
else
{
lean_dec_ref(v___x_2173_);
goto v___jp_2159_;
}
}
v___jp_2159_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2160_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
v___x_2161_ = lean_unsigned_to_nat(80u);
v___x_2162_ = l_Lean_Json_pretty(v_x_2158_, v___x_2161_);
v___x_2163_ = lean_string_append(v___x_2160_, v___x_2162_);
lean_dec_ref(v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2165_ = lean_string_append(v___x_2163_, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
v___jp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_box(v_a_2168_);
v___x_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(lean_object* v_j_2187_, lean_object* v_k_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l_Lean_Json_getObjValD(v_j_2187_, v_k_2188_);
v___x_2190_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_j_2191_, lean_object* v_k_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_j_2191_, v_k_2192_);
lean_dec_ref(v_k_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(size_t v_sz_2196_, size_t v_i_2197_, lean_object* v_bs_2198_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = lean_usize_dec_lt(v_i_2197_, v_sz_2196_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_bs_2198_);
return v___x_2202_;
}
else
{
lean_object* v_v_2203_; lean_object* v___x_2204_; 
v_v_2203_ = lean_array_uget_borrowed(v_bs_2198_, v_i_2197_);
lean_inc(v_v_2203_);
v___x_2204_ = l_Lean_Json_getNat_x3f(v_v_2203_);
if (lean_obj_tag(v___x_2204_) == 1)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v_bs_x27_2207_; uint8_t v_a_2209_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = lean_unsigned_to_nat(0u);
v_bs_x27_2207_ = lean_array_uset(v_bs_2198_, v_i_2197_, v___x_2206_);
v___x_2215_ = lean_unsigned_to_nat(1u);
v___x_2216_ = lean_nat_dec_eq(v_a_2205_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = lean_unsigned_to_nat(2u);
v___x_2218_ = lean_nat_dec_eq(v_a_2205_, v___x_2217_);
lean_dec(v_a_2205_);
if (v___x_2218_ == 0)
{
lean_dec_ref(v_bs_x27_2207_);
goto v___jp_2199_;
}
else
{
uint8_t v___x_2219_; 
v___x_2219_ = 1;
v_a_2209_ = v___x_2219_;
goto v___jp_2208_;
}
}
else
{
uint8_t v___x_2220_; 
lean_dec(v_a_2205_);
v___x_2220_ = 0;
v_a_2209_ = v___x_2220_;
goto v___jp_2208_;
}
v___jp_2208_:
{
size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = ((size_t)1ULL);
v___x_2211_ = lean_usize_add(v_i_2197_, v___x_2210_);
v___x_2212_ = lean_box(v_a_2209_);
v___x_2213_ = lean_array_uset(v_bs_x27_2207_, v_i_2197_, v___x_2212_);
v_i_2197_ = v___x_2211_;
v_bs_2198_ = v___x_2213_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_bs_2198_);
goto v___jp_2199_;
}
}
v___jp_2199_:
{
lean_object* v___x_2200_; 
v___x_2200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0));
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_bs_2223_){
_start:
{
size_t v_sz_boxed_2224_; size_t v_i_boxed_2225_; lean_object* v_res_2226_; 
v_sz_boxed_2224_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2225_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_boxed_2224_, v_i_boxed_2225_, v_bs_2223_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(lean_object* v_x_2227_){
_start:
{
if (lean_obj_tag(v_x_2227_) == 4)
{
lean_object* v_elems_2228_; size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v_elems_2228_ = lean_ctor_get(v_x_2227_, 0);
lean_inc_ref(v_elems_2228_);
lean_dec_ref_known(v_x_2227_, 1);
v_sz_2229_ = lean_array_size(v_elems_2228_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_2229_, v___x_2230_, v_elems_2228_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2232_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2233_ = lean_unsigned_to_nat(80u);
v___x_2234_ = l_Lean_Json_pretty(v_x_2227_, v___x_2233_);
v___x_2235_ = lean_string_append(v___x_2232_, v___x_2234_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2237_ = lean_string_append(v___x_2235_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(lean_object* v_x_2241_){
_start:
{
if (lean_obj_tag(v_x_2241_) == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0));
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(v_x_2241_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2260_; 
v_a_2252_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2254_ = v___x_2243_;
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2243_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_a_2252_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2256_);
v___x_2258_ = v___x_2254_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(lean_object* v_j_2261_, lean_object* v_k_2262_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = l_Lean_Json_getObjValD(v_j_2261_, v_k_2262_);
v___x_2264_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(lean_object* v_j_2265_, lean_object* v_k_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_j_2265_, v_k_2266_);
lean_dec_ref(v_k_2266_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2270_) == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0));
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Json_getStr_x3f(v_x_2270_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
v_a_2281_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2283_ = v___x_2272_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2272_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_a_2281_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(lean_object* v_j_2290_, lean_object* v_k_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = l_Lean_Json_getObjValD(v_j_2290_, v_k_2291_);
v___x_2293_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(lean_object* v_j_2294_, lean_object* v_k_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_j_2294_, v_k_2295_);
lean_dec_ref(v_k_2295_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(size_t v_sz_2297_, size_t v_i_2298_, lean_object* v_bs_2299_){
_start:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_usize_dec_lt(v_i_2298_, v_sz_2297_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_bs_2299_);
return v___x_2301_;
}
else
{
lean_object* v_v_2302_; lean_object* v___x_2303_; 
v_v_2302_ = lean_array_uget_borrowed(v_bs_2299_, v_i_2298_);
lean_inc(v_v_2302_);
v___x_2303_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_bs_2299_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v_bs_x27_2314_; size_t v___x_2315_; size_t v___x_2316_; lean_object* v___x_2317_; 
v_a_2312_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2313_ = lean_unsigned_to_nat(0u);
v_bs_x27_2314_ = lean_array_uset(v_bs_2299_, v_i_2298_, v___x_2313_);
v___x_2315_ = ((size_t)1ULL);
v___x_2316_ = lean_usize_add(v_i_2298_, v___x_2315_);
v___x_2317_ = lean_array_uset(v_bs_x27_2314_, v_i_2298_, v_a_2312_);
v_i_2298_ = v___x_2316_;
v_bs_2299_ = v___x_2317_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(lean_object* v_sz_2319_, lean_object* v_i_2320_, lean_object* v_bs_2321_){
_start:
{
size_t v_sz_boxed_2322_; size_t v_i_boxed_2323_; lean_object* v_res_2324_; 
v_sz_boxed_2322_ = lean_unbox_usize(v_sz_2319_);
lean_dec(v_sz_2319_);
v_i_boxed_2323_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_res_2324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_boxed_2322_, v_i_boxed_2323_, v_bs_2321_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(lean_object* v_x_2325_){
_start:
{
if (lean_obj_tag(v_x_2325_) == 4)
{
lean_object* v_elems_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
v_elems_2326_ = lean_ctor_get(v_x_2325_, 0);
lean_inc_ref(v_elems_2326_);
lean_dec_ref_known(v_x_2325_, 1);
v_sz_2327_ = lean_array_size(v_elems_2326_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_2327_, v___x_2328_, v_elems_2326_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2330_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2331_ = lean_unsigned_to_nat(80u);
v___x_2332_ = l_Lean_Json_pretty(v_x_2325_, v___x_2331_);
v___x_2333_ = lean_string_append(v___x_2330_, v___x_2332_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2335_ = lean_string_append(v___x_2333_, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(lean_object* v_x_2339_){
_start:
{
if (lean_obj_tag(v_x_2339_) == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0));
return v___x_2340_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(v_x_2339_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2358_; 
v_a_2350_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2352_ = v___x_2341_;
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2341_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2358_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_a_2350_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(lean_object* v_j_2359_, lean_object* v_k_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = l_Lean_Json_getObjValD(v_j_2359_, v_k_2360_);
v___x_2362_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(lean_object* v_j_2363_, lean_object* v_k_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_j_2363_, v_k_2364_);
lean_dec_ref(v_k_2364_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(lean_object* v_x_2368_){
_start:
{
lean_object* v_a_2370_; lean_object* v_j_2374_; 
if (lean_obj_tag(v_x_2368_) == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0));
return v___x_2382_;
}
else
{
switch(lean_obj_tag(v_x_2368_))
{
case 2:
{
lean_object* v_n_2383_; lean_object* v_mantissa_2384_; lean_object* v_exponent_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v_n_2383_ = lean_ctor_get(v_x_2368_, 0);
v_mantissa_2384_ = lean_ctor_get(v_n_2383_, 0);
v_exponent_2385_ = lean_ctor_get(v_n_2383_, 1);
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = lean_nat_dec_eq(v_exponent_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
v_j_2374_ = v_x_2368_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2388_; 
lean_inc(v_mantissa_2384_);
lean_dec_ref_known(v_x_2368_, 1);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_mantissa_2384_);
v_a_2370_ = v___x_2388_;
goto v___jp_2369_;
}
}
case 3:
{
lean_object* v_s_2389_; lean_object* v___x_2390_; 
v_s_2389_ = lean_ctor_get(v_x_2368_, 0);
lean_inc_ref(v_s_2389_);
lean_dec_ref_known(v_x_2368_, 1);
v___x_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2390_, 0, v_s_2389_);
v_a_2370_ = v___x_2390_;
goto v___jp_2369_;
}
default: 
{
v_j_2374_ = v_x_2368_;
goto v___jp_2373_;
}
}
}
v___jp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2370_);
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
v___jp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2375_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_2376_ = lean_unsigned_to_nat(80u);
v___x_2377_ = l_Lean_Json_pretty(v_j_2374_, v___x_2376_);
v___x_2378_ = lean_string_append(v___x_2375_, v___x_2377_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2380_ = lean_string_append(v___x_2378_, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(lean_object* v_j_2391_, lean_object* v_k_2392_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = l_Lean_Json_getObjValD(v_j_2391_, v_k_2392_);
v___x_2394_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(lean_object* v_j_2395_, lean_object* v_k_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_j_2395_, v_k_2396_);
lean_dec_ref(v_k_2396_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(lean_object* v_json_2398_){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_2398_);
v___x_2400_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_json_2398_, v___x_2399_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_json_2398_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2410_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2410_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_2406_ = lean_string_append(v___x_2405_, v_a_2401_);
lean_dec(v_a_2401_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2406_);
v___x_2408_ = v___x_2403_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
else
{
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_json_2398_);
v_a_2411_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2400_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2400_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 0);
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_a_2419_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2420_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_2398_);
v___x_2421_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_json_2398_, v___x_2420_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2431_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2431_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_2427_ = lean_string_append(v___x_2426_, v_a_2422_);
lean_dec(v_a_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2427_);
v___x_2429_ = v___x_2424_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2432_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2421_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2421_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 0);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_a_2440_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2441_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_2398_);
v___x_2442_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_json_2398_, v___x_2441_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2452_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2452_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2447_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_2448_ = lean_string_append(v___x_2447_, v_a_2443_);
lean_dec(v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2448_);
v___x_2450_ = v___x_2445_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
else
{
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2453_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2442_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2442_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 0);
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_a_2461_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2462_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_2398_);
v___x_2463_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2398_, v___x_2462_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2473_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2473_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2468_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_2469_ = lean_string_append(v___x_2468_, v_a_2464_);
lean_dec(v_a_2464_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2469_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
else
{
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2474_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2463_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2463_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set_tag(v___x_2476_, 0);
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_a_2482_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2483_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_2398_);
v___x_2484_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_json_2398_, v___x_2483_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_2490_ = lean_string_append(v___x_2489_, v_a_2485_);
lean_dec(v_a_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2495_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2484_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2484_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 0);
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_a_2503_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2504_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_2398_);
v___x_2505_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_json_2398_, v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2515_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2515_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_2511_ = lean_string_append(v___x_2510_, v_a_2506_);
lean_dec(v_a_2506_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2511_);
v___x_2513_ = v___x_2508_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
else
{
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2516_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2505_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2505_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 0);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_a_2524_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2525_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_2398_);
v___x_2526_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2398_, v___x_2525_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2536_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2536_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2531_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_2532_ = lean_string_append(v___x_2531_, v_a_2527_);
lean_dec(v_a_2527_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2532_);
v___x_2534_ = v___x_2529_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
else
{
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2537_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2526_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2526_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 0);
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_a_2545_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2546_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_2398_);
v___x_2547_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_json_2398_, v___x_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v_a_2545_);
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_2553_ = lean_string_append(v___x_2552_, v_a_2548_);
lean_dec(v_a_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2553_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_a_2545_);
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2558_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2547_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2547_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set_tag(v___x_2560_, 0);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2567_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_2398_);
v___x_2568_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_json_2398_, v___x_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_a_2566_);
lean_dec(v_a_2545_);
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2578_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2578_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_2574_ = lean_string_append(v___x_2573_, v_a_2569_);
lean_dec(v_a_2569_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2574_);
v___x_2576_ = v___x_2571_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_a_2566_);
lean_dec(v_a_2545_);
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2579_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2568_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2568_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 0);
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_a_2587_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2588_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_2398_);
v___x_2589_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_json_2398_, v___x_2588_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2587_);
lean_dec(v_a_2566_);
lean_dec(v_a_2545_);
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2599_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2599_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2594_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_2595_ = lean_string_append(v___x_2594_, v_a_2590_);
lean_dec(v_a_2590_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2595_);
v___x_2597_ = v___x_2592_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
else
{
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_a_2587_);
lean_dec(v_a_2566_);
lean_dec(v_a_2545_);
lean_dec(v_a_2524_);
lean_dec(v_a_2503_);
lean_dec(v_a_2482_);
lean_dec(v_a_2461_);
lean_dec(v_a_2440_);
lean_dec(v_a_2419_);
lean_dec(v_json_2398_);
v_a_2600_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2589_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2589_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 0);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2619_; 
v_a_2608_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2609_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_2610_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_json_2398_, v___x_2609_);
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2619_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2615_, 0, v_a_2419_);
lean_ctor_set(v___x_2615_, 1, v_a_2440_);
lean_ctor_set(v___x_2615_, 2, v_a_2461_);
lean_ctor_set(v___x_2615_, 3, v_a_2482_);
lean_ctor_set(v___x_2615_, 4, v_a_2503_);
lean_ctor_set(v___x_2615_, 5, v_a_2524_);
lean_ctor_set(v___x_2615_, 6, v_a_2545_);
lean_ctor_set(v___x_2615_, 7, v_a_2566_);
lean_ctor_set(v___x_2615_, 8, v_a_2587_);
lean_ctor_set(v___x_2615_, 9, v_a_2608_);
lean_ctor_set(v___x_2615_, 10, v_a_2611_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2615_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_bs_2622_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = lean_usize_dec_lt(v_i_2621_, v_sz_2620_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_bs_2622_);
return v___x_2624_;
}
else
{
lean_object* v_v_2625_; lean_object* v___x_2626_; 
v_v_2625_ = lean_array_uget_borrowed(v_bs_2622_, v_i_2621_);
lean_inc(v_v_2625_);
v___x_2626_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(v_v_2625_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_bs_2622_);
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2636_; lean_object* v_bs_x27_2637_; size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v_a_2635_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2636_ = lean_unsigned_to_nat(0u);
v_bs_x27_2637_ = lean_array_uset(v_bs_2622_, v_i_2621_, v___x_2636_);
v___x_2638_ = ((size_t)1ULL);
v___x_2639_ = lean_usize_add(v_i_2621_, v___x_2638_);
v___x_2640_ = lean_array_uset(v_bs_x27_2637_, v_i_2621_, v_a_2635_);
v_i_2621_ = v___x_2639_;
v_bs_2622_ = v___x_2640_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2642_, lean_object* v_i_2643_, lean_object* v_bs_2644_){
_start:
{
size_t v_sz_boxed_2645_; size_t v_i_boxed_2646_; lean_object* v_res_2647_; 
v_sz_boxed_2645_ = lean_unbox_usize(v_sz_2642_);
lean_dec(v_sz_2642_);
v_i_boxed_2646_ = lean_unbox_usize(v_i_2643_);
lean_dec(v_i_2643_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_2645_, v_i_boxed_2646_, v_bs_2644_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2648_) == 4)
{
lean_object* v_elems_2649_; size_t v_sz_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v_elems_2649_ = lean_ctor_get(v_x_2648_, 0);
lean_inc_ref(v_elems_2649_);
lean_dec_ref_known(v_x_2648_, 1);
v_sz_2650_ = lean_array_size(v_elems_2649_);
v___x_2651_ = ((size_t)0ULL);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_2650_, v___x_2651_, v_elems_2649_);
return v___x_2652_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2653_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2654_ = lean_unsigned_to_nat(80u);
v___x_2655_ = l_Lean_Json_pretty(v_x_2648_, v___x_2654_);
v___x_2656_ = lean_string_append(v___x_2653_, v___x_2655_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2658_ = lean_string_append(v___x_2656_, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(lean_object* v_j_2660_, lean_object* v_k_2661_){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = l_Lean_Json_getObjValD(v_j_2660_, v_k_2661_);
v___x_2663_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(lean_object* v_j_2664_, lean_object* v_k_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_j_2664_, v_k_2665_);
lean_dec_ref(v_k_2665_);
return v_res_2666_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = 1;
v___x_2673_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1));
v___x_2674_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2673_, v___x_2672_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_2676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2);
v___x_2677_ = lean_string_append(v___x_2676_, v___x_2675_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = 1;
v___x_2681_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4));
v___x_2682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5);
v___x_2684_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2685_ = lean_string_append(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6);
v___x_2688_ = lean_string_append(v___x_2687_, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = 1;
v___x_2693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9));
v___x_2694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2693_, v___x_2692_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10);
v___x_2696_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2697_ = lean_string_append(v___x_2696_, v___x_2695_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11);
v___x_2700_ = lean_string_append(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = 1;
v___x_2705_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14));
v___x_2706_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15);
v___x_2708_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2709_ = lean_string_append(v___x_2708_, v___x_2707_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2711_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16);
v___x_2712_ = lean_string_append(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = 1;
v___x_2716_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18));
v___x_2717_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2716_, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19);
v___x_2719_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2720_ = lean_string_append(v___x_2719_, v___x_2718_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2722_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20);
v___x_2723_ = lean_string_append(v___x_2722_, v___x_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object* v_json_2724_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
lean_inc(v_json_2724_);
v___x_2726_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2724_, v___x_2725_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v_json_2724_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2736_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2736_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2731_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7);
v___x_2732_ = lean_string_append(v___x_2731_, v_a_2727_);
lean_dec(v_a_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2732_);
v___x_2734_ = v___x_2729_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_json_2724_);
v_a_2737_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2726_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2726_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 0);
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_a_2745_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2746_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
lean_inc(v_json_2724_);
v___x_2747_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_json_2724_, v___x_2746_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2745_);
lean_dec(v_json_2724_);
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2757_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2757_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2752_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12);
v___x_2753_ = lean_string_append(v___x_2752_, v_a_2748_);
lean_dec(v_a_2748_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2753_);
v___x_2755_ = v___x_2750_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_a_2745_);
lean_dec(v_json_2724_);
v_a_2758_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2747_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2747_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set_tag(v___x_2760_, 0);
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_a_2766_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2767_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
lean_inc(v_json_2724_);
v___x_2768_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2724_, v___x_2767_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2766_);
lean_dec(v_a_2745_);
lean_dec(v_json_2724_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2778_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2778_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2773_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17);
v___x_2774_ = lean_string_append(v___x_2773_, v_a_2769_);
lean_dec(v_a_2769_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2774_);
v___x_2776_ = v___x_2771_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2766_);
lean_dec(v_a_2745_);
lean_dec(v_json_2724_);
v_a_2779_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2768_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2768_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 0);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_a_2787_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2788_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_2789_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_json_2724_, v___x_2788_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_a_2787_);
lean_dec(v_a_2766_);
lean_dec(v_a_2745_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2794_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21);
v___x_2795_ = lean_string_append(v___x_2794_, v_a_2790_);
lean_dec(v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2795_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2787_);
lean_dec(v_a_2766_);
lean_dec(v_a_2745_);
v_a_2800_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2789_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2789_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set_tag(v___x_2802_, 0);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2816_; 
v_a_2808_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2810_ = v___x_2789_;
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2789_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2745_);
lean_ctor_set(v___x_2812_, 1, v_a_2766_);
lean_ctor_set(v___x_2812_, 2, v_a_2787_);
lean_ctor_set(v___x_2812_, 3, v_a_2808_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2812_);
v___x_2814_ = v___x_2810_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
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
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedDiagnosticSeverity_default = _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default();
l_Lean_Lsp_instInhabitedDiagnosticSeverity = _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity();
l_Lean_Lsp_instInhabitedDiagnosticCode_default = _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode_default);
l_Lean_Lsp_instInhabitedDiagnosticCode = _init_l_Lean_Lsp_instInhabitedDiagnosticCode();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode);
l_Lean_Lsp_instInhabitedDiagnosticTag_default = _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default();
l_Lean_Lsp_instInhabitedDiagnosticTag = _init_l_Lean_Lsp_instInhabitedDiagnosticTag();
l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default = _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default();
l_Lean_Lsp_instInhabitedLeanDiagnosticTag = _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag();
l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default = _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default);
l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation = _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Diagnostics(builtin);
}
#ifdef __cplusplus
}
#endif
