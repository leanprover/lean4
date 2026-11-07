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
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_656_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_645_, 1);
v___x_657_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_643_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_a_656_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_668_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
v___x_664_ = lean_string_append(v___x_663_, v_a_659_);
lean_dec(v_a_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_664_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_a_669_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_658_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_658_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_a_656_);
lean_ctor_set(v___x_673_, 1, v_a_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
lean_object* v_location_682_; lean_object* v_message_683_; lean_object* v_location_684_; lean_object* v_message_685_; uint8_t v___x_686_; 
v_location_682_ = lean_ctor_get(v_x_680_, 0);
v_message_683_ = lean_ctor_get(v_x_680_, 1);
v_location_684_ = lean_ctor_get(v_x_681_, 0);
v_message_685_ = lean_ctor_get(v_x_681_, 1);
v___x_686_ = l_Lean_Lsp_instOrdLocation_ord(v_location_682_, v_location_684_);
if (v___x_686_ == 1)
{
uint8_t v___x_687_; 
v___x_687_ = lean_string_compare(v_message_683_, v_message_685_);
return v___x_687_;
}
else
{
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(v_x_688_, v_x_689_);
lean_dec_ref(v_x_689_);
lean_dec_ref(v_x_688_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object* v_inst_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_698_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0);
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_700_, 0, v___x_697_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
lean_ctor_set(v___x_700_, 2, v___x_699_);
lean_ctor_set(v___x_700_, 3, v___x_699_);
lean_ctor_set(v___x_700_, 4, v___x_699_);
lean_ctor_set(v___x_700_, 5, v___x_699_);
lean_ctor_set(v___x_700_, 6, v_inst_696_);
lean_ctor_set(v___x_700_, 7, v___x_699_);
lean_ctor_set(v___x_700_, 8, v___x_699_);
lean_ctor_set(v___x_700_, 9, v___x_699_);
lean_ctor_set(v___x_700_, 10, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object* v_00_u03b1_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object* v_inst_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object* v_a_706_, lean_object* v_inst_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3(void){
_start:
{
lean_object* v___x_713_; lean_object* v___f_714_; 
v___x_713_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_714_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_714_, 0, v___x_713_);
return v___f_714_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object* v_inst_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_range_725_; lean_object* v_fullRange_x3f_726_; lean_object* v_severity_x3f_727_; lean_object* v_isSilent_x3f_728_; lean_object* v_code_x3f_729_; lean_object* v_source_x3f_730_; lean_object* v_message_731_; lean_object* v_tags_x3f_732_; lean_object* v_leanTags_x3f_733_; lean_object* v_relatedInformation_x3f_734_; lean_object* v_data_x3f_735_; lean_object* v_range_736_; lean_object* v_fullRange_x3f_737_; lean_object* v_severity_x3f_738_; lean_object* v_isSilent_x3f_739_; lean_object* v_code_x3f_740_; lean_object* v_source_x3f_741_; lean_object* v_message_742_; lean_object* v_tags_x3f_743_; lean_object* v_leanTags_x3f_744_; lean_object* v_relatedInformation_x3f_745_; lean_object* v_data_x3f_746_; uint8_t v___x_747_; 
v_range_725_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_range_725_);
v_fullRange_x3f_726_ = lean_ctor_get(v_x_723_, 1);
lean_inc(v_fullRange_x3f_726_);
v_severity_x3f_727_ = lean_ctor_get(v_x_723_, 2);
lean_inc(v_severity_x3f_727_);
v_isSilent_x3f_728_ = lean_ctor_get(v_x_723_, 3);
lean_inc(v_isSilent_x3f_728_);
v_code_x3f_729_ = lean_ctor_get(v_x_723_, 4);
lean_inc(v_code_x3f_729_);
v_source_x3f_730_ = lean_ctor_get(v_x_723_, 5);
lean_inc(v_source_x3f_730_);
v_message_731_ = lean_ctor_get(v_x_723_, 6);
lean_inc(v_message_731_);
v_tags_x3f_732_ = lean_ctor_get(v_x_723_, 7);
lean_inc(v_tags_x3f_732_);
v_leanTags_x3f_733_ = lean_ctor_get(v_x_723_, 8);
lean_inc(v_leanTags_x3f_733_);
v_relatedInformation_x3f_734_ = lean_ctor_get(v_x_723_, 9);
lean_inc(v_relatedInformation_x3f_734_);
v_data_x3f_735_ = lean_ctor_get(v_x_723_, 10);
lean_inc(v_data_x3f_735_);
lean_dec_ref(v_x_723_);
v_range_736_ = lean_ctor_get(v_x_724_, 0);
lean_inc_ref(v_range_736_);
v_fullRange_x3f_737_ = lean_ctor_get(v_x_724_, 1);
lean_inc(v_fullRange_x3f_737_);
v_severity_x3f_738_ = lean_ctor_get(v_x_724_, 2);
lean_inc(v_severity_x3f_738_);
v_isSilent_x3f_739_ = lean_ctor_get(v_x_724_, 3);
lean_inc(v_isSilent_x3f_739_);
v_code_x3f_740_ = lean_ctor_get(v_x_724_, 4);
lean_inc(v_code_x3f_740_);
v_source_x3f_741_ = lean_ctor_get(v_x_724_, 5);
lean_inc(v_source_x3f_741_);
v_message_742_ = lean_ctor_get(v_x_724_, 6);
lean_inc(v_message_742_);
v_tags_x3f_743_ = lean_ctor_get(v_x_724_, 7);
lean_inc(v_tags_x3f_743_);
v_leanTags_x3f_744_ = lean_ctor_get(v_x_724_, 8);
lean_inc(v_leanTags_x3f_744_);
v_relatedInformation_x3f_745_ = lean_ctor_get(v_x_724_, 9);
lean_inc(v_relatedInformation_x3f_745_);
v_data_x3f_746_ = lean_ctor_get(v_x_724_, 10);
lean_inc(v_data_x3f_746_);
lean_dec_ref(v_x_724_);
v___x_747_ = l_Lean_Lsp_instBEqRange_beq(v_range_725_, v_range_736_);
lean_dec_ref(v_range_736_);
lean_dec_ref(v_range_725_);
if (v___x_747_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_message_742_);
lean_dec(v_source_x3f_741_);
lean_dec(v_code_x3f_740_);
lean_dec(v_isSilent_x3f_739_);
lean_dec(v_severity_x3f_738_);
lean_dec(v_fullRange_x3f_737_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
lean_dec(v_message_731_);
lean_dec(v_source_x3f_730_);
lean_dec(v_code_x3f_729_);
lean_dec(v_isSilent_x3f_728_);
lean_dec(v_severity_x3f_727_);
lean_dec(v_fullRange_x3f_726_);
lean_dec_ref(v_inst_722_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0));
v___x_749_ = l_instBEqOption_beq___redArg(v___x_748_, v_fullRange_x3f_726_, v_fullRange_x3f_737_);
if (v___x_749_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_message_742_);
lean_dec(v_source_x3f_741_);
lean_dec(v_code_x3f_740_);
lean_dec(v_isSilent_x3f_739_);
lean_dec(v_severity_x3f_738_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
lean_dec(v_message_731_);
lean_dec(v_source_x3f_730_);
lean_dec(v_code_x3f_729_);
lean_dec(v_isSilent_x3f_728_);
lean_dec(v_severity_x3f_727_);
lean_dec_ref(v_inst_722_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0));
v___x_751_ = l_instBEqOption_beq___redArg(v___x_750_, v_severity_x3f_727_, v_severity_x3f_738_);
if (v___x_751_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_message_742_);
lean_dec(v_source_x3f_741_);
lean_dec(v_code_x3f_740_);
lean_dec(v_isSilent_x3f_739_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
lean_dec(v_message_731_);
lean_dec(v_source_x3f_730_);
lean_dec(v_code_x3f_729_);
lean_dec(v_isSilent_x3f_728_);
lean_dec_ref(v_inst_722_);
return v___x_751_;
}
else
{
lean_object* v___f_752_; uint8_t v___x_753_; 
v___f_752_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2));
v___x_753_ = l_instBEqOption_beq___redArg(v___f_752_, v_isSilent_x3f_728_, v_isSilent_x3f_739_);
if (v___x_753_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_message_742_);
lean_dec(v_source_x3f_741_);
lean_dec(v_code_x3f_740_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
lean_dec(v_message_731_);
lean_dec(v_source_x3f_730_);
lean_dec(v_code_x3f_729_);
lean_dec_ref(v_inst_722_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticCode___closed__0));
v___x_755_ = l_instBEqOption_beq___redArg(v___x_754_, v_code_x3f_729_, v_code_x3f_740_);
if (v___x_755_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_message_742_);
lean_dec(v_source_x3f_741_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
lean_dec(v_message_731_);
lean_dec(v_source_x3f_730_);
lean_dec_ref(v_inst_722_);
return v___x_755_;
}
else
{
lean_object* v___f_756_; uint8_t v___x_757_; 
v___f_756_ = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3);
v___x_757_ = l_instBEqOption_beq___redArg(v___f_756_, v_source_x3f_730_, v_source_x3f_741_);
if (v___x_757_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_message_742_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
lean_dec(v_message_731_);
lean_dec_ref(v_inst_722_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = lean_apply_2(v_inst_722_, v_message_731_, v_message_742_);
v___x_759_ = lean_unbox(v___x_758_);
if (v___x_759_ == 0)
{
uint8_t v___x_760_; 
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_tags_x3f_743_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
lean_dec(v_tags_x3f_732_);
v___x_760_ = lean_unbox(v___x_758_);
return v___x_760_;
}
else
{
lean_object* v___f_761_; uint8_t v___x_762_; 
v___f_761_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4));
v___x_762_ = l_instBEqOption_beq___redArg(v___f_761_, v_tags_x3f_732_, v_tags_x3f_743_);
if (v___x_762_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_leanTags_x3f_744_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
lean_dec(v_leanTags_x3f_733_);
return v___x_762_;
}
else
{
lean_object* v___f_763_; uint8_t v___x_764_; 
v___f_763_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5));
v___x_764_ = l_instBEqOption_beq___redArg(v___f_763_, v_leanTags_x3f_733_, v_leanTags_x3f_744_);
if (v___x_764_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_relatedInformation_x3f_745_);
lean_dec(v_data_x3f_735_);
lean_dec(v_relatedInformation_x3f_734_);
return v___x_764_;
}
else
{
lean_object* v___f_765_; uint8_t v___x_766_; 
v___f_765_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6));
v___x_766_ = l_instBEqOption_beq___redArg(v___f_765_, v_relatedInformation_x3f_734_, v_relatedInformation_x3f_745_);
if (v___x_766_ == 0)
{
lean_dec(v_data_x3f_746_);
lean_dec(v_data_x3f_735_);
return v___x_766_;
}
else
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__7));
v___x_768_ = l_instBEqOption_beq___redArg(v___x_767_, v_data_x3f_735_, v_data_x3f_746_);
return v___x_768_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object* v_inst_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_769_, v_x_770_, v_x_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object* v_00_u03b1_774_, lean_object* v_inst_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_775_, v_x_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object* v_00_u03b1_779_, lean_object* v_inst_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_Lsp_instBEqDiagnosticWith_beq(v_00_u03b1_779_, v_inst_780_, v_x_781_, v_x_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object* v_inst_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_786_, 0, lean_box(0));
lean_closure_set(v___x_786_, 1, v_inst_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object* v_00_u03b1_787_, lean_object* v_inst_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_789_, 0, lean_box(0));
lean_closure_set(v___x_789_, 1, v_inst_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object* v_inst_810_, lean_object* v_x_811_){
_start:
{
lean_object* v_range_812_; lean_object* v_fullRange_x3f_813_; lean_object* v_severity_x3f_814_; lean_object* v_isSilent_x3f_815_; lean_object* v_code_x3f_816_; lean_object* v_source_x3f_817_; lean_object* v_message_818_; lean_object* v_tags_x3f_819_; lean_object* v_leanTags_x3f_820_; lean_object* v_relatedInformation_x3f_821_; lean_object* v_data_x3f_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_range_812_ = lean_ctor_get(v_x_811_, 0);
lean_inc_ref(v_range_812_);
v_fullRange_x3f_813_ = lean_ctor_get(v_x_811_, 1);
lean_inc(v_fullRange_x3f_813_);
v_severity_x3f_814_ = lean_ctor_get(v_x_811_, 2);
lean_inc(v_severity_x3f_814_);
v_isSilent_x3f_815_ = lean_ctor_get(v_x_811_, 3);
lean_inc(v_isSilent_x3f_815_);
v_code_x3f_816_ = lean_ctor_get(v_x_811_, 4);
lean_inc(v_code_x3f_816_);
v_source_x3f_817_ = lean_ctor_get(v_x_811_, 5);
lean_inc(v_source_x3f_817_);
v_message_818_ = lean_ctor_get(v_x_811_, 6);
lean_inc(v_message_818_);
v_tags_x3f_819_ = lean_ctor_get(v_x_811_, 7);
lean_inc(v_tags_x3f_819_);
v_leanTags_x3f_820_ = lean_ctor_get(v_x_811_, 8);
lean_inc(v_leanTags_x3f_820_);
v_relatedInformation_x3f_821_ = lean_ctor_get(v_x_811_, 9);
lean_inc(v_relatedInformation_x3f_821_);
v_data_x3f_822_ = lean_ctor_get(v_x_811_, 10);
lean_inc(v_data_x3f_822_);
lean_dec_ref(v_x_811_);
v___x_823_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0));
v___f_824_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0));
v___f_825_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1));
v___f_826_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0));
v___f_827_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2));
v___x_828_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3));
v___x_829_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4));
v___x_830_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5));
v___x_831_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6));
v___x_832_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_833_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_812_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_838_ = l_Lean_Json_opt___redArg(v___x_823_, v___x_837_, v_fullRange_x3f_813_);
v___x_839_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_840_ = l_Lean_Json_opt___redArg(v___f_824_, v___x_839_, v_severity_x3f_814_);
v___x_841_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_842_ = l_Lean_Json_opt___redArg(v___f_825_, v___x_841_, v_isSilent_x3f_815_);
v___x_843_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_844_ = l_Lean_Json_opt___redArg(v___f_826_, v___x_843_, v_code_x3f_816_);
v___x_845_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_846_ = l_Lean_Json_opt___redArg(v___f_827_, v___x_845_, v_source_x3f_817_);
v___x_847_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_848_ = lean_apply_1(v_inst_810_, v_message_818_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_835_);
v___x_851_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_852_ = l_Lean_Json_opt___redArg(v___x_828_, v___x_851_, v_tags_x3f_819_);
v___x_853_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_854_ = l_Lean_Json_opt___redArg(v___x_829_, v___x_853_, v_leanTags_x3f_820_);
v___x_855_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_856_ = l_Lean_Json_opt___redArg(v___x_830_, v___x_855_, v_relatedInformation_x3f_821_);
v___x_857_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_858_ = l_Lean_Json_opt___redArg(v___x_831_, v___x_857_, v_data_x3f_822_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_835_);
v___x_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_856_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_854_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_852_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_850_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_846_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_844_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_842_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_840_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_838_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_836_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_871_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_831_, v___x_869_, v___x_870_);
v___x_872_ = l_Lean_Json_mkObj(v___x_871_);
lean_dec(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object* v_00_u03b1_873_, lean_object* v_inst_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(v_inst_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object* v_inst_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_878_, 0, lean_box(0));
lean_closure_set(v___x_878_, 1, v_inst_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object* v_00_u03b1_879_, lean_object* v_inst_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_881_, 0, lean_box(0));
lean_closure_set(v___x_881_, 1, v_inst_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4(void){
_start:
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = 1;
v___x_891_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3));
v___x_892_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_894_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4);
v___x_895_ = lean_string_append(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = 1;
v___x_899_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6));
v___x_900_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7);
v___x_902_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_903_ = lean_string_append(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_905_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8);
v___x_906_ = lean_string_append(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12(void){
_start:
{
uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = 1;
v___x_911_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11));
v___x_912_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12);
v___x_914_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_915_ = lean_string_append(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_917_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13);
v___x_918_ = lean_string_append(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = 1;
v___x_925_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17));
v___x_926_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18);
v___x_928_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_929_ = lean_string_append(v___x_928_, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_931_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19);
v___x_932_ = lean_string_append(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25(void){
_start:
{
uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = 1;
v___x_940_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24));
v___x_941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_940_, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25);
v___x_943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_944_ = lean_string_append(v___x_943_, v___x_942_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_946_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26);
v___x_947_ = lean_string_append(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = 1;
v___x_954_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30));
v___x_955_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_954_, v___x_953_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31);
v___x_957_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_958_ = lean_string_append(v___x_957_, v___x_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_960_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32);
v___x_961_ = lean_string_append(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38(void){
_start:
{
uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = 1;
v___x_969_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37));
v___x_970_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_969_, v___x_968_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38);
v___x_972_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_973_ = lean_string_append(v___x_972_, v___x_971_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39);
v___x_976_ = lean_string_append(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_979_ = lean_string_append(v___x_978_, v___x_977_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41);
v___x_982_ = lean_string_append(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47(void){
_start:
{
uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = 1;
v___x_991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46));
v___x_992_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_991_, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47);
v___x_994_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_995_ = lean_string_append(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48);
v___x_998_ = lean_string_append(v___x_997_, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54(void){
_start:
{
uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = 1;
v___x_1007_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53));
v___x_1008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54);
v___x_1010_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1011_ = lean_string_append(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55);
v___x_1014_ = lean_string_append(v___x_1013_, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61(void){
_start:
{
uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = 1;
v___x_1023_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60));
v___x_1024_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61);
v___x_1026_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1027_ = lean_string_append(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1029_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62);
v___x_1030_ = lean_string_append(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68(void){
_start:
{
uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = 1;
v___x_1038_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67));
v___x_1039_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1038_, v___x_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68);
v___x_1041_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1042_ = lean_string_append(v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1044_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69);
v___x_1045_ = lean_string_append(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object* v_inst_1046_, lean_object* v_json_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1048_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0));
v___x_1049_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1));
v___x_1050_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_1047_);
v___x_1051_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1048_, v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_json_1047_);
lean_dec_ref(v_inst_1046_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_1057_ = lean_string_append(v___x_1056_, v_a_1052_);
lean_dec(v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1062_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1063_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_1047_);
v___x_1064_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1049_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
lean_dec_ref(v_inst_1046_);
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1069_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_1070_ = lean_string_append(v___x_1069_, v_a_1065_);
lean_dec(v_a_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1070_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1075_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1076_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15));
v___x_1077_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_1047_);
v___x_1078_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1076_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
lean_dec_ref(v_inst_1046_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_1084_ = lean_string_append(v___x_1083_, v_a_1079_);
lean_dec(v_a_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_a_1089_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1090_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22));
v___x_1091_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_1047_);
v___x_1092_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1090_, v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
lean_dec_ref(v_inst_1046_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1097_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_1098_ = lean_string_append(v___x_1097_, v_a_1093_);
lean_dec(v_a_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_a_1103_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28));
v___x_1105_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_1047_);
v___x_1106_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1104_, v___x_1105_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
lean_dec_ref(v_inst_1046_);
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1116_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1116_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1111_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_1112_ = lean_string_append(v___x_1111_, v_a_1107_);
lean_dec(v_a_1107_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_a_1117_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35));
v___x_1119_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_1047_);
v___x_1120_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1118_, v___x_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_a_1117_);
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
lean_dec_ref(v_inst_1046_);
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_1126_ = lean_string_append(v___x_1125_, v_a_1121_);
lean_dec(v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1126_);
v___x_1128_ = v___x_1123_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_a_1131_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1132_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_1047_);
v___x_1133_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v_inst_1046_, v___x_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_a_1131_);
lean_dec(v_a_1117_);
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1143_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1143_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_1139_ = lean_string_append(v___x_1138_, v_a_1134_);
lean_dec(v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1139_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1144_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1145_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44));
v___x_1146_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_1047_);
v___x_1147_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1145_, v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1144_);
lean_dec(v_a_1131_);
lean_dec(v_a_1117_);
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_1153_ = lean_string_append(v___x_1152_, v_a_1148_);
lean_dec(v_a_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_a_1158_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1159_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51));
v___x_1160_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_1047_);
v___x_1161_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1159_, v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_a_1158_);
lean_dec(v_a_1144_);
lean_dec(v_a_1131_);
lean_dec(v_a_1117_);
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_1167_ = lean_string_append(v___x_1166_, v_a_1162_);
lean_dec(v_a_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1172_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58));
v___x_1174_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_1047_);
v___x_1175_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1173_, v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_a_1172_);
lean_dec(v_a_1158_);
lean_dec(v_a_1144_);
lean_dec(v_a_1131_);
lean_dec(v_a_1117_);
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
lean_dec(v_json_1047_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_1181_ = lean_string_append(v___x_1180_, v_a_1176_);
lean_dec(v_a_1176_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_a_1186_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1187_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65));
v___x_1188_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1189_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1047_, v___x_1187_, v___x_1188_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_a_1186_);
lean_dec(v_a_1172_);
lean_dec(v_a_1158_);
lean_dec(v_a_1144_);
lean_dec(v_a_1131_);
lean_dec(v_a_1117_);
lean_dec(v_a_1103_);
lean_dec(v_a_1089_);
lean_dec(v_a_1075_);
lean_dec(v_a_1062_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70);
v___x_1195_ = lean_string_append(v___x_1194_, v_a_1190_);
lean_dec(v_a_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_a_1200_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1202_ = v___x_1189_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1189_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1062_);
lean_ctor_set(v___x_1204_, 1, v_a_1075_);
lean_ctor_set(v___x_1204_, 2, v_a_1089_);
lean_ctor_set(v___x_1204_, 3, v_a_1103_);
lean_ctor_set(v___x_1204_, 4, v_a_1117_);
lean_ctor_set(v___x_1204_, 5, v_a_1131_);
lean_ctor_set(v___x_1204_, 6, v_a_1144_);
lean_ctor_set(v___x_1204_, 7, v_a_1158_);
lean_ctor_set(v___x_1204_, 8, v_a_1172_);
lean_ctor_set(v___x_1204_, 9, v_a_1186_);
lean_ctor_set(v___x_1204_, 10, v_a_1200_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object* v_00_u03b1_1209_, lean_object* v_inst_1210_, lean_object* v_json_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(v_inst_1210_, v_json_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object* v_inst_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1214_, 0, lean_box(0));
lean_closure_set(v___x_1214_, 1, v_inst_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object* v_00_u03b1_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1217_, 0, lean_box(0));
lean_closure_set(v___x_1217_, 1, v_inst_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object* v_d_1218_){
_start:
{
lean_object* v_fullRange_x3f_1219_; 
v_fullRange_x3f_1219_ = lean_ctor_get(v_d_1218_, 1);
if (lean_obj_tag(v_fullRange_x3f_1219_) == 0)
{
lean_object* v_range_1220_; 
v_range_1220_ = lean_ctor_get(v_d_1218_, 0);
lean_inc_ref(v_range_1220_);
return v_range_1220_;
}
else
{
lean_object* v_val_1221_; 
v_val_1221_ = lean_ctor_get(v_fullRange_x3f_1219_, 0);
lean_inc(v_val_1221_);
return v_val_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object* v_d_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1222_);
lean_dec_ref(v_d_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object* v_00_u03b1_1224_, lean_object* v_d_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_d_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Lsp_DiagnosticWith_fullRange(v_00_u03b1_1227_, v_d_1228_);
lean_dec_ref(v_d_1228_);
return v_res_1229_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
if (lean_obj_tag(v_x_1239_) == 0)
{
uint8_t v___x_1240_; 
v___x_1240_ = 1;
return v___x_1240_;
}
else
{
uint8_t v___x_1241_; 
v___x_1241_ = 0;
return v___x_1241_;
}
}
else
{
if (lean_obj_tag(v_x_1239_) == 0)
{
uint8_t v___x_1242_; 
v___x_1242_ = 0;
return v___x_1242_;
}
else
{
lean_object* v_val_1243_; lean_object* v_val_1244_; uint8_t v___x_1245_; 
v_val_1243_ = lean_ctor_get(v_x_1238_, 0);
v_val_1244_ = lean_ctor_get(v_x_1239_, 0);
v___x_1245_ = lean_int_dec_eq(v_val_1243_, v_val_1244_);
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_x_1246_, v_x_1247_);
lean_dec(v_x_1247_);
lean_dec(v_x_1246_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(uint8_t v___x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
if (lean_obj_tag(v_x_1252_) == 0)
{
uint8_t v___x_1253_; 
v___x_1253_ = 1;
return v___x_1253_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = 0;
return v___x_1254_;
}
}
else
{
if (lean_obj_tag(v_x_1252_) == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; uint8_t v___x_1257_; 
v_val_1256_ = lean_ctor_get(v_x_1252_, 0);
v___x_1257_ = lean_unbox(v_val_1256_);
if (v___x_1257_ == 0)
{
lean_object* v_val_1258_; uint8_t v___x_1259_; 
v_val_1258_ = lean_ctor_get(v_x_1251_, 0);
v___x_1259_ = lean_unbox(v_val_1258_);
if (v___x_1259_ == 0)
{
return v___x_1250_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_unbox(v_val_1256_);
return v___x_1260_;
}
}
else
{
lean_object* v_val_1261_; uint8_t v___x_1262_; 
v_val_1261_ = lean_ctor_get(v_x_1251_, 0);
v___x_1262_ = lean_unbox(v_val_1261_);
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object* v___x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
uint8_t v___x_854__boxed_1266_; uint8_t v_res_1267_; lean_object* v_r_1268_; 
v___x_854__boxed_1266_ = lean_unbox(v___x_1263_);
v_res_1267_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v___x_854__boxed_1266_, v_x_1264_, v_x_1265_);
lean_dec(v_x_1265_);
lean_dec(v_x_1264_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(lean_object* v_xs_1269_, lean_object* v_ys_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v_zero_1272_; uint8_t v_isZero_1273_; 
v_zero_1272_ = lean_unsigned_to_nat(0u);
v_isZero_1273_ = lean_nat_dec_eq(v_x_1271_, v_zero_1272_);
if (v_isZero_1273_ == 1)
{
lean_dec(v_x_1271_);
return v_isZero_1273_;
}
else
{
lean_object* v_one_1274_; lean_object* v_n_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; uint8_t v___x_1279_; uint8_t v___x_1280_; 
v_one_1274_ = lean_unsigned_to_nat(1u);
v_n_1275_ = lean_nat_sub(v_x_1271_, v_one_1274_);
lean_dec(v_x_1271_);
v___x_1276_ = lean_array_fget_borrowed(v_xs_1269_, v_n_1275_);
v___x_1277_ = lean_array_fget_borrowed(v_ys_1270_, v_n_1275_);
v___x_1278_ = lean_unbox(v___x_1276_);
v___x_1279_ = lean_unbox(v___x_1277_);
v___x_1280_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec(v_n_1275_);
return v___x_1280_;
}
else
{
v_x_1271_ = v_n_1275_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(lean_object* v_xs_1282_, lean_object* v_ys_1283_, lean_object* v_x_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1282_, v_ys_1283_, v_x_1284_);
lean_dec_ref(v_ys_1283_);
lean_dec_ref(v_xs_1282_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
if (lean_obj_tag(v_x_1288_) == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = 1;
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
}
else
{
if (lean_obj_tag(v_x_1288_) == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
return v___x_1291_;
}
else
{
lean_object* v_val_1292_; lean_object* v_val_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_val_1292_ = lean_ctor_get(v_x_1287_, 0);
v_val_1293_ = lean_ctor_get(v_x_1288_, 0);
v___x_1294_ = lean_array_get_size(v_val_1292_);
v___x_1295_ = lean_array_get_size(v_val_1293_);
v___x_1296_ = lean_nat_dec_eq(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
return v___x_1296_;
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_val_1292_, v_val_1293_, v___x_1294_);
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_x_1298_, v_x_1299_);
lean_dec(v_x_1299_);
lean_dec(v_x_1298_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
if (lean_obj_tag(v_x_1303_) == 0)
{
uint8_t v___x_1304_; 
v___x_1304_ = 1;
return v___x_1304_;
}
else
{
uint8_t v___x_1305_; 
v___x_1305_ = 0;
return v___x_1305_;
}
}
else
{
if (lean_obj_tag(v_x_1303_) == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = 0;
return v___x_1306_;
}
else
{
lean_object* v_val_1307_; lean_object* v_val_1308_; uint8_t v___x_1309_; 
v_val_1307_ = lean_ctor_get(v_x_1302_, 0);
v_val_1308_ = lean_ctor_get(v_x_1303_, 0);
v___x_1309_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_val_1307_, v_val_1308_);
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
uint8_t v_res_1312_; lean_object* v_r_1313_; 
v_res_1312_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_x_1310_, v_x_1311_);
lean_dec(v_x_1311_);
lean_dec(v_x_1310_);
v_r_1313_ = lean_box(v_res_1312_);
return v_r_1313_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
if (lean_obj_tag(v_x_1315_) == 0)
{
uint8_t v___x_1316_; 
v___x_1316_ = 1;
return v___x_1316_;
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = 0;
return v___x_1317_;
}
}
else
{
if (lean_obj_tag(v_x_1315_) == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = 0;
return v___x_1318_;
}
else
{
lean_object* v_val_1319_; lean_object* v_val_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; uint8_t v___x_1323_; 
v_val_1319_ = lean_ctor_get(v_x_1314_, 0);
v_val_1320_ = lean_ctor_get(v_x_1315_, 0);
v___x_1321_ = lean_unbox(v_val_1319_);
v___x_1322_ = lean_unbox(v_val_1320_);
v___x_1323_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v___x_1321_, v___x_1322_);
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(lean_object* v_x_1324_, lean_object* v_x_1325_){
_start:
{
uint8_t v_res_1326_; lean_object* v_r_1327_; 
v_res_1326_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_x_1324_, v_x_1325_);
lean_dec(v_x_1325_);
lean_dec(v_x_1324_);
v_r_1327_ = lean_box(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(lean_object* v_xs_1328_, lean_object* v_ys_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v_zero_1331_; uint8_t v_isZero_1332_; 
v_zero_1331_ = lean_unsigned_to_nat(0u);
v_isZero_1332_ = lean_nat_dec_eq(v_x_1330_, v_zero_1331_);
if (v_isZero_1332_ == 1)
{
lean_dec(v_x_1330_);
return v_isZero_1332_;
}
else
{
lean_object* v_one_1333_; lean_object* v_n_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; uint8_t v___x_1338_; uint8_t v___x_1339_; 
v_one_1333_ = lean_unsigned_to_nat(1u);
v_n_1334_ = lean_nat_sub(v_x_1330_, v_one_1333_);
lean_dec(v_x_1330_);
v___x_1335_ = lean_array_fget_borrowed(v_xs_1328_, v_n_1334_);
v___x_1336_ = lean_array_fget_borrowed(v_ys_1329_, v_n_1334_);
v___x_1337_ = lean_unbox(v___x_1335_);
v___x_1338_ = lean_unbox(v___x_1336_);
v___x_1339_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v_n_1334_);
return v___x_1339_;
}
else
{
v_x_1330_ = v_n_1334_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_xs_1341_, lean_object* v_ys_1342_, lean_object* v_x_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1341_, v_ys_1342_, v_x_1343_);
lean_dec_ref(v_ys_1342_);
lean_dec_ref(v_xs_1341_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
if (lean_obj_tag(v_x_1347_) == 0)
{
uint8_t v___x_1348_; 
v___x_1348_ = 1;
return v___x_1348_;
}
else
{
uint8_t v___x_1349_; 
v___x_1349_ = 0;
return v___x_1349_;
}
}
else
{
if (lean_obj_tag(v_x_1347_) == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = 0;
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; lean_object* v_val_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_val_1351_ = lean_ctor_get(v_x_1346_, 0);
v_val_1352_ = lean_ctor_get(v_x_1347_, 0);
v___x_1353_ = lean_array_get_size(v_val_1351_);
v___x_1354_ = lean_array_get_size(v_val_1352_);
v___x_1355_ = lean_nat_dec_eq(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
return v___x_1355_;
}
else
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_val_1351_, v_val_1352_, v___x_1353_);
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
uint8_t v_res_1359_; lean_object* v_r_1360_; 
v_res_1359_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_x_1357_, v_x_1358_);
lean_dec(v_x_1358_);
lean_dec(v_x_1357_);
v_r_1360_ = lean_box(v_res_1359_);
return v_r_1360_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 0)
{
if (lean_obj_tag(v_x_1362_) == 0)
{
uint8_t v___x_1363_; 
v___x_1363_ = 1;
return v___x_1363_;
}
else
{
uint8_t v___x_1364_; 
v___x_1364_ = 0;
return v___x_1364_;
}
}
else
{
if (lean_obj_tag(v_x_1362_) == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = 0;
return v___x_1365_;
}
else
{
lean_object* v_val_1366_; lean_object* v_val_1367_; uint8_t v___x_1368_; 
v_val_1366_ = lean_ctor_get(v_x_1361_, 0);
v_val_1367_ = lean_ctor_get(v_x_1362_, 0);
v___x_1368_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_val_1366_, v_val_1367_);
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_x_1369_, v_x_1370_);
lean_dec(v_x_1370_);
lean_dec(v_x_1369_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
if (lean_obj_tag(v_x_1374_) == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = 1;
return v___x_1375_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = 0;
return v___x_1376_;
}
}
else
{
if (lean_obj_tag(v_x_1374_) == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = 0;
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; lean_object* v_val_1379_; uint8_t v___x_1380_; 
v_val_1378_ = lean_ctor_get(v_x_1373_, 0);
v_val_1379_ = lean_ctor_get(v_x_1374_, 0);
v___x_1380_ = lean_string_dec_eq(v_val_1378_, v_val_1379_);
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_x_1381_, v_x_1382_);
lean_dec(v_x_1382_);
lean_dec(v_x_1381_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
if (lean_obj_tag(v_x_1386_) == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = 1;
return v___x_1387_;
}
else
{
uint8_t v___x_1388_; 
v___x_1388_ = 0;
return v___x_1388_;
}
}
else
{
if (lean_obj_tag(v_x_1386_) == 0)
{
uint8_t v___x_1389_; 
v___x_1389_ = 0;
return v___x_1389_;
}
else
{
lean_object* v_val_1390_; lean_object* v_val_1391_; uint8_t v___x_1392_; 
v_val_1390_ = lean_ctor_get(v_x_1385_, 0);
v_val_1391_ = lean_ctor_get(v_x_1386_, 0);
v___x_1392_ = l_Lean_Lsp_instBEqRange_beq(v_val_1390_, v_val_1391_);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
uint8_t v_res_1395_; lean_object* v_r_1396_; 
v_res_1395_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_x_1393_, v_x_1394_);
lean_dec(v_x_1394_);
lean_dec(v_x_1393_);
v_r_1396_ = lean_box(v_res_1395_);
return v_r_1396_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(lean_object* v_xs_1397_, lean_object* v_ys_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_zero_1400_; uint8_t v_isZero_1401_; 
v_zero_1400_ = lean_unsigned_to_nat(0u);
v_isZero_1401_ = lean_nat_dec_eq(v_x_1399_, v_zero_1400_);
if (v_isZero_1401_ == 1)
{
lean_dec(v_x_1399_);
return v_isZero_1401_;
}
else
{
lean_object* v_one_1402_; lean_object* v_n_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_one_1402_ = lean_unsigned_to_nat(1u);
v_n_1403_ = lean_nat_sub(v_x_1399_, v_one_1402_);
lean_dec(v_x_1399_);
v___x_1404_ = lean_array_fget_borrowed(v_xs_1397_, v_n_1403_);
v___x_1405_ = lean_array_fget_borrowed(v_ys_1398_, v_n_1403_);
v___x_1406_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_dec(v_n_1403_);
return v___x_1406_;
}
else
{
v_x_1399_ = v_n_1403_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_xs_1408_, lean_object* v_ys_1409_, lean_object* v_x_1410_){
_start:
{
uint8_t v_res_1411_; lean_object* v_r_1412_; 
v_res_1411_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1408_, v_ys_1409_, v_x_1410_);
lean_dec_ref(v_ys_1409_);
lean_dec_ref(v_xs_1408_);
v_r_1412_ = lean_box(v_res_1411_);
return v_r_1412_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
if (lean_obj_tag(v_x_1414_) == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = 1;
return v___x_1415_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = 0;
return v___x_1416_;
}
}
else
{
if (lean_obj_tag(v_x_1414_) == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; lean_object* v_val_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_val_1418_ = lean_ctor_get(v_x_1413_, 0);
v_val_1419_ = lean_ctor_get(v_x_1414_, 0);
v___x_1420_ = lean_array_get_size(v_val_1418_);
v___x_1421_ = lean_array_get_size(v_val_1419_);
v___x_1422_ = lean_nat_dec_eq(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
return v___x_1422_;
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_val_1418_, v_val_1419_, v___x_1420_);
return v___x_1423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_x_1424_, v_x_1425_);
lean_dec(v_x_1425_);
lean_dec(v_x_1424_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_range_1430_; lean_object* v_fullRange_x3f_1431_; lean_object* v_severity_x3f_1432_; lean_object* v_isSilent_x3f_1433_; lean_object* v_code_x3f_1434_; lean_object* v_source_x3f_1435_; lean_object* v_message_1436_; lean_object* v_tags_x3f_1437_; lean_object* v_leanTags_x3f_1438_; lean_object* v_relatedInformation_x3f_1439_; lean_object* v_data_x3f_1440_; lean_object* v_range_1441_; lean_object* v_fullRange_x3f_1442_; lean_object* v_severity_x3f_1443_; lean_object* v_isSilent_x3f_1444_; lean_object* v_code_x3f_1445_; lean_object* v_source_x3f_1446_; lean_object* v_message_1447_; lean_object* v_tags_x3f_1448_; lean_object* v_leanTags_x3f_1449_; lean_object* v_relatedInformation_x3f_1450_; lean_object* v_data_x3f_1451_; uint8_t v___x_1452_; 
v_range_1430_ = lean_ctor_get(v_x_1428_, 0);
v_fullRange_x3f_1431_ = lean_ctor_get(v_x_1428_, 1);
v_severity_x3f_1432_ = lean_ctor_get(v_x_1428_, 2);
v_isSilent_x3f_1433_ = lean_ctor_get(v_x_1428_, 3);
v_code_x3f_1434_ = lean_ctor_get(v_x_1428_, 4);
v_source_x3f_1435_ = lean_ctor_get(v_x_1428_, 5);
v_message_1436_ = lean_ctor_get(v_x_1428_, 6);
v_tags_x3f_1437_ = lean_ctor_get(v_x_1428_, 7);
v_leanTags_x3f_1438_ = lean_ctor_get(v_x_1428_, 8);
v_relatedInformation_x3f_1439_ = lean_ctor_get(v_x_1428_, 9);
v_data_x3f_1440_ = lean_ctor_get(v_x_1428_, 10);
v_range_1441_ = lean_ctor_get(v_x_1429_, 0);
v_fullRange_x3f_1442_ = lean_ctor_get(v_x_1429_, 1);
v_severity_x3f_1443_ = lean_ctor_get(v_x_1429_, 2);
v_isSilent_x3f_1444_ = lean_ctor_get(v_x_1429_, 3);
v_code_x3f_1445_ = lean_ctor_get(v_x_1429_, 4);
v_source_x3f_1446_ = lean_ctor_get(v_x_1429_, 5);
v_message_1447_ = lean_ctor_get(v_x_1429_, 6);
v_tags_x3f_1448_ = lean_ctor_get(v_x_1429_, 7);
v_leanTags_x3f_1449_ = lean_ctor_get(v_x_1429_, 8);
v_relatedInformation_x3f_1450_ = lean_ctor_get(v_x_1429_, 9);
v_data_x3f_1451_ = lean_ctor_get(v_x_1429_, 10);
v___x_1452_ = l_Lean_Lsp_instBEqRange_beq(v_range_1430_, v_range_1441_);
if (v___x_1452_ == 0)
{
return v___x_1452_;
}
else
{
uint8_t v___x_1453_; 
v___x_1453_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_fullRange_x3f_1431_, v_fullRange_x3f_1442_);
if (v___x_1453_ == 0)
{
return v___x_1453_;
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_severity_x3f_1432_, v_severity_x3f_1443_);
if (v___x_1454_ == 0)
{
return v___x_1454_;
}
else
{
uint8_t v___x_1455_; 
v___x_1455_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v___x_1454_, v_isSilent_x3f_1433_, v_isSilent_x3f_1444_);
if (v___x_1455_ == 0)
{
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_code_x3f_1434_, v_code_x3f_1445_);
if (v___x_1456_ == 0)
{
return v___x_1456_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_source_x3f_1435_, v_source_x3f_1446_);
if (v___x_1457_ == 0)
{
return v___x_1457_;
}
else
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_string_dec_eq(v_message_1436_, v_message_1447_);
if (v___x_1458_ == 0)
{
return v___x_1458_;
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_tags_x3f_1437_, v_tags_x3f_1448_);
if (v___x_1459_ == 0)
{
return v___x_1459_;
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_leanTags_x3f_1438_, v_leanTags_x3f_1449_);
if (v___x_1460_ == 0)
{
return v___x_1460_;
}
else
{
uint8_t v___x_1461_; 
v___x_1461_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_relatedInformation_x3f_1439_, v_relatedInformation_x3f_1450_);
if (v___x_1461_ == 0)
{
return v___x_1461_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_data_x3f_1440_, v_data_x3f_1451_);
return v___x_1462_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
uint8_t v_res_1465_; lean_object* v_r_1466_; 
v_res_1465_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v_x_1463_, v_x_1464_);
lean_dec_ref(v_x_1464_);
lean_dec_ref(v_x_1463_);
v_r_1466_ = lean_box(v_res_1465_);
return v_r_1466_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(lean_object* v_xs_1467_, lean_object* v_ys_1468_, lean_object* v_x_1469_){
_start:
{
lean_object* v_zero_1470_; uint8_t v_isZero_1471_; 
v_zero_1470_ = lean_unsigned_to_nat(0u);
v_isZero_1471_ = lean_nat_dec_eq(v_x_1469_, v_zero_1470_);
if (v_isZero_1471_ == 1)
{
lean_dec(v_x_1469_);
return v_isZero_1471_;
}
else
{
lean_object* v_one_1472_; lean_object* v_n_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_one_1472_ = lean_unsigned_to_nat(1u);
v_n_1473_ = lean_nat_sub(v_x_1469_, v_one_1472_);
lean_dec(v_x_1469_);
v___x_1474_ = lean_array_fget_borrowed(v_xs_1467_, v_n_1473_);
v___x_1475_ = lean_array_fget_borrowed(v_ys_1468_, v_n_1473_);
v___x_1476_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_dec(v_n_1473_);
return v___x_1476_;
}
else
{
v_x_1469_ = v_n_1473_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(lean_object* v_xs_1478_, lean_object* v_ys_1479_, lean_object* v_x_1480_){
_start:
{
uint8_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1478_, v_ys_1479_, v_x_1480_);
lean_dec_ref(v_ys_1479_);
lean_dec_ref(v_xs_1478_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
lean_object* v_uri_1485_; lean_object* v_version_x3f_1486_; lean_object* v_isIncremental_x3f_1487_; lean_object* v_diagnostics_1488_; lean_object* v_uri_1489_; lean_object* v_version_x3f_1490_; lean_object* v_isIncremental_x3f_1491_; lean_object* v_diagnostics_1492_; uint8_t v___x_1493_; 
v_uri_1485_ = lean_ctor_get(v_x_1483_, 0);
v_version_x3f_1486_ = lean_ctor_get(v_x_1483_, 1);
v_isIncremental_x3f_1487_ = lean_ctor_get(v_x_1483_, 2);
v_diagnostics_1488_ = lean_ctor_get(v_x_1483_, 3);
v_uri_1489_ = lean_ctor_get(v_x_1484_, 0);
v_version_x3f_1490_ = lean_ctor_get(v_x_1484_, 1);
v_isIncremental_x3f_1491_ = lean_ctor_get(v_x_1484_, 2);
v_diagnostics_1492_ = lean_ctor_get(v_x_1484_, 3);
v___x_1493_ = lean_string_dec_eq(v_uri_1485_, v_uri_1489_);
if (v___x_1493_ == 0)
{
return v___x_1493_;
}
else
{
uint8_t v___x_1494_; 
v___x_1494_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_version_x3f_1486_, v_version_x3f_1490_);
if (v___x_1494_ == 0)
{
return v___x_1494_;
}
else
{
uint8_t v___x_1495_; 
v___x_1495_ = l_instBEqOption_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v___x_1494_, v_isIncremental_x3f_1487_, v_isIncremental_x3f_1491_);
if (v___x_1495_ == 0)
{
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_array_get_size(v_diagnostics_1488_);
v___x_1497_ = lean_array_get_size(v_diagnostics_1492_);
v___x_1498_ = lean_nat_dec_eq(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
return v___x_1498_;
}
else
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_diagnostics_1488_, v_diagnostics_1492_, v___x_1496_);
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(v_x_1500_, v_x_1501_);
lean_dec_ref(v_x_1501_);
lean_dec_ref(v_x_1500_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(lean_object* v_xs_1504_, lean_object* v_ys_1505_, lean_object* v_hsz_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1504_, v_ys_1505_, v_x_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(lean_object* v_xs_1510_, lean_object* v_ys_1511_, lean_object* v_hsz_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_res_1515_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(v_xs_1510_, v_ys_1511_, v_hsz_1512_, v_x_1513_, v_x_1514_);
lean_dec_ref(v_ys_1511_);
lean_dec_ref(v_xs_1510_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(lean_object* v_xs_1517_, lean_object* v_ys_1518_, lean_object* v_hsz_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1517_, v_ys_1518_, v_x_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(lean_object* v_xs_1523_, lean_object* v_ys_1524_, lean_object* v_hsz_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
uint8_t v_res_1528_; lean_object* v_r_1529_; 
v_res_1528_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(v_xs_1523_, v_ys_1524_, v_hsz_1525_, v_x_1526_, v_x_1527_);
lean_dec_ref(v_ys_1524_);
lean_dec_ref(v_xs_1523_);
v_r_1529_ = lean_box(v_res_1528_);
return v_r_1529_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(lean_object* v_xs_1530_, lean_object* v_ys_1531_, lean_object* v_hsz_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
uint8_t v___x_1535_; 
v___x_1535_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1530_, v_ys_1531_, v_x_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(lean_object* v_xs_1536_, lean_object* v_ys_1537_, lean_object* v_hsz_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(v_xs_1536_, v_ys_1537_, v_hsz_1538_, v_x_1539_, v_x_1540_);
lean_dec_ref(v_ys_1537_);
lean_dec_ref(v_xs_1536_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(lean_object* v_xs_1543_, lean_object* v_ys_1544_, lean_object* v_hsz_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1543_, v_ys_1544_, v_x_1546_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(lean_object* v_xs_1549_, lean_object* v_ys_1550_, lean_object* v_hsz_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l_Array_isEqvAux___at___00instBEqOption_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(v_xs_1549_, v_ys_1550_, v_hsz_1551_, v_x_1552_, v_x_1553_);
lean_dec_ref(v_ys_1550_);
lean_dec_ref(v_xs_1549_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object* v_k_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v___x_1560_; 
lean_dec_ref(v_k_1558_);
v___x_1560_ = lean_box(0);
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1572_; 
v_val_1561_ = lean_ctor_get(v_x_1559_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1563_ = v_x_1559_;
v_isShared_1564_ = v_isSharedCheck_1572_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_val_1561_);
lean_dec(v_x_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1572_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = l_Lean_JsonNumber_fromInt(v_val_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 2);
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_k_1558_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
return v___x_1570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object* v_k_1573_, lean_object* v_x_1574_){
_start:
{
if (lean_obj_tag(v_x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v_k_1573_);
v___x_1575_ = lean_box(0);
return v___x_1575_;
}
else
{
lean_object* v_val_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_val_1576_ = lean_ctor_get(v_x_1574_, 0);
v___x_1577_ = lean_alloc_ctor(1, 0, 1);
v___x_1578_ = lean_unbox(v_val_1576_);
lean_ctor_set_uint8(v___x_1577_, 0, v___x_1578_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_k_1573_);
lean_ctor_set(v___x_1579_, 1, v___x_1577_);
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(lean_object* v_k_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v_k_1582_, v_x_1583_);
lean_dec(v_x_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(size_t v_sz_1585_, size_t v_i_1586_, lean_object* v_bs_1587_){
_start:
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
if (v___x_1588_ == 0)
{
return v_bs_1587_;
}
else
{
lean_object* v_v_1589_; lean_object* v___x_1590_; lean_object* v_bs_x27_1591_; lean_object* v___y_1593_; uint8_t v___x_1598_; 
v_v_1589_ = lean_array_uget(v_bs_1587_, v_i_1586_);
v___x_1590_ = lean_unsigned_to_nat(0u);
v_bs_x27_1591_ = lean_array_uset(v_bs_1587_, v_i_1586_, v___x_1590_);
v___x_1598_ = lean_unbox(v_v_1589_);
lean_dec(v_v_1589_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1593_ = v___x_1599_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1593_ = v___x_1600_;
goto v___jp_1592_;
}
v___jp_1592_:
{
size_t v___x_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = ((size_t)1ULL);
v___x_1595_ = lean_usize_add(v_i_1586_, v___x_1594_);
lean_inc(v___y_1593_);
v___x_1596_ = lean_array_uset(v_bs_x27_1591_, v_i_1586_, v___y_1593_);
v_i_1586_ = v___x_1595_;
v_bs_1587_ = v___x_1596_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_bs_1603_){
_start:
{
size_t v_sz_boxed_1604_; size_t v_i_boxed_1605_; lean_object* v_res_1606_; 
v_sz_boxed_1604_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1605_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_boxed_1604_, v_i_boxed_1605_, v_bs_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(lean_object* v_a_1607_){
_start:
{
size_t v_sz_1608_; size_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_sz_1608_ = lean_array_size(v_a_1607_);
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_1608_, v___x_1609_, v_a_1607_);
v___x_1611_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(lean_object* v_k_1612_, lean_object* v_x_1613_){
_start:
{
if (lean_obj_tag(v_x_1613_) == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v_k_1612_);
v___x_1614_ = lean_box(0);
return v___x_1614_;
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_val_1615_ = lean_ctor_get(v_x_1613_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v_x_1613_, 1);
v___x_1616_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(v_val_1615_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_k_1612_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(lean_object* v_k_1620_, lean_object* v_x_1621_){
_start:
{
if (lean_obj_tag(v_x_1621_) == 0)
{
lean_object* v___x_1622_; 
lean_dec_ref(v_k_1620_);
v___x_1622_ = lean_box(0);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_val_1623_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1624_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_1623_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_k_1620_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_bs_1630_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1631_ == 0)
{
return v_bs_1630_;
}
else
{
lean_object* v_v_1632_; lean_object* v___x_1633_; lean_object* v_bs_x27_1634_; lean_object* v___x_1635_; size_t v___x_1636_; size_t v___x_1637_; lean_object* v___x_1638_; 
v_v_1632_ = lean_array_uget(v_bs_1630_, v_i_1629_);
v___x_1633_ = lean_unsigned_to_nat(0u);
v_bs_x27_1634_ = lean_array_uset(v_bs_1630_, v_i_1629_, v___x_1633_);
v___x_1635_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_v_1632_);
v___x_1636_ = ((size_t)1ULL);
v___x_1637_ = lean_usize_add(v_i_1629_, v___x_1636_);
v___x_1638_ = lean_array_uset(v_bs_x27_1634_, v_i_1629_, v___x_1635_);
v_i_1629_ = v___x_1637_;
v_bs_1630_ = v___x_1638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_1640_, lean_object* v_i_1641_, lean_object* v_bs_1642_){
_start:
{
size_t v_sz_boxed_1643_; size_t v_i_boxed_1644_; lean_object* v_res_1645_; 
v_sz_boxed_1643_ = lean_unbox_usize(v_sz_1640_);
lean_dec(v_sz_1640_);
v_i_boxed_1644_ = lean_unbox_usize(v_i_1641_);
lean_dec(v_i_1641_);
v_res_1645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_boxed_1643_, v_i_boxed_1644_, v_bs_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(lean_object* v_a_1646_){
_start:
{
size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_sz_1647_ = lean_array_size(v_a_1646_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_1647_, v___x_1648_, v_a_1646_);
v___x_1650_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(lean_object* v_k_1651_, lean_object* v_x_1652_){
_start:
{
if (lean_obj_tag(v_x_1652_) == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v_k_1651_);
v___x_1653_ = lean_box(0);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_val_1654_ = lean_ctor_get(v_x_1652_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v_x_1652_, 1);
v___x_1655_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(v_val_1654_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_k_1651_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(lean_object* v_k_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref(v_k_1659_);
v___x_1661_ = lean_box(0);
return v___x_1661_;
}
else
{
lean_object* v_val_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_val_1662_ = lean_ctor_get(v_x_1660_, 0);
lean_inc(v_val_1662_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v_k_1659_);
lean_ctor_set(v___x_1663_, 1, v_val_1662_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(lean_object* v_k_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v_k_1666_, v_x_1667_);
lean_dec(v_x_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(lean_object* v_k_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v___y_1672_; 
if (lean_obj_tag(v_x_1670_) == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref(v_k_1669_);
v___x_1676_ = lean_box(0);
return v___x_1676_;
}
else
{
lean_object* v_val_1677_; 
v_val_1677_ = lean_ctor_get(v_x_1670_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v_x_1670_, 1);
if (lean_obj_tag(v_val_1677_) == 0)
{
lean_object* v_i_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_i_1678_ = lean_ctor_get(v_val_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_val_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v_val_1677_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_i_1678_);
lean_dec(v_val_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = l_Lean_JsonNumber_fromInt(v_i_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 2);
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
v___y_1672_ = v___x_1684_;
goto v___jp_1671_;
}
}
}
else
{
lean_object* v_s_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_s_1687_ = lean_ctor_get(v_val_1677_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_val_1677_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v_val_1677_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_s_1687_);
lean_dec(v_val_1677_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 3);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_s_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
v___y_1672_ = v___x_1692_;
goto v___jp_1671_;
}
}
}
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_k_1669_);
lean_ctor_set(v___x_1673_, 1, v___y_1672_);
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(lean_object* v_k_1695_, lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref(v_k_1695_);
v___x_1697_ = lean_box(0);
return v___x_1697_;
}
else
{
lean_object* v_val_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1708_; 
v_val_1698_ = lean_ctor_get(v_x_1696_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1700_ = v_x_1696_;
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_val_1698_);
lean_dec(v_x_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 3);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_val_1698_);
v___x_1703_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_k_1695_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
return v___x_1706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(lean_object* v_k_1709_, lean_object* v_x_1710_){
_start:
{
lean_object* v___y_1712_; 
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref(v_k_1709_);
v___x_1716_ = lean_box(0);
return v___x_1716_;
}
else
{
lean_object* v_val_1717_; uint8_t v___x_1718_; 
v_val_1717_ = lean_ctor_get(v_x_1710_, 0);
v___x_1718_ = lean_unbox(v_val_1717_);
switch(v___x_1718_)
{
case 0:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1712_ = v___x_1719_;
goto v___jp_1711_;
}
case 1:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1712_ = v___x_1720_;
goto v___jp_1711_;
}
case 2:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
v___y_1712_ = v___x_1721_;
goto v___jp_1711_;
}
default: 
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
v___y_1712_ = v___x_1722_;
goto v___jp_1711_;
}
}
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_inc(v___y_1712_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_k_1709_);
lean_ctor_set(v___x_1713_, 1, v___y_1712_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(lean_object* v_k_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v_k_1723_, v_x_1724_);
lean_dec(v_x_1724_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_bs_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1729_ == 0)
{
return v_bs_1728_;
}
else
{
lean_object* v_v_1730_; lean_object* v___x_1731_; lean_object* v_bs_x27_1732_; lean_object* v___y_1734_; uint8_t v___x_1739_; 
v_v_1730_ = lean_array_uget(v_bs_1728_, v_i_1727_);
v___x_1731_ = lean_unsigned_to_nat(0u);
v_bs_x27_1732_ = lean_array_uset(v_bs_1728_, v_i_1727_, v___x_1731_);
v___x_1739_ = lean_unbox(v_v_1730_);
lean_dec(v_v_1730_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1734_ = v___x_1740_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1734_ = v___x_1741_;
goto v___jp_1733_;
}
v___jp_1733_:
{
size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = ((size_t)1ULL);
v___x_1736_ = lean_usize_add(v_i_1727_, v___x_1735_);
lean_inc(v___y_1734_);
v___x_1737_ = lean_array_uset(v_bs_x27_1732_, v_i_1727_, v___y_1734_);
v_i_1727_ = v___x_1736_;
v_bs_1728_ = v___x_1737_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(lean_object* v_sz_1742_, lean_object* v_i_1743_, lean_object* v_bs_1744_){
_start:
{
size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1742_);
lean_dec(v_sz_1742_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1743_);
lean_dec(v_i_1743_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_boxed_1745_, v_i_boxed_1746_, v_bs_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(lean_object* v_a_1748_){
_start:
{
size_t v_sz_1749_; size_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_sz_1749_ = lean_array_size(v_a_1748_);
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_1749_, v___x_1750_, v_a_1748_);
v___x_1752_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(lean_object* v_k_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1754_) == 0)
{
lean_object* v___x_1755_; 
lean_dec_ref(v_k_1753_);
v___x_1755_ = lean_box(0);
return v___x_1755_;
}
else
{
lean_object* v_val_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_val_1756_ = lean_ctor_get(v_x_1754_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v_x_1754_, 1);
v___x_1757_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(v_val_1756_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_k_1753_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(lean_object* v_x_1761_){
_start:
{
lean_object* v_range_1762_; lean_object* v_fullRange_x3f_1763_; lean_object* v_severity_x3f_1764_; lean_object* v_isSilent_x3f_1765_; lean_object* v_code_x3f_1766_; lean_object* v_source_x3f_1767_; lean_object* v_message_1768_; lean_object* v_tags_x3f_1769_; lean_object* v_leanTags_x3f_1770_; lean_object* v_relatedInformation_x3f_1771_; lean_object* v_data_x3f_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_range_1762_ = lean_ctor_get(v_x_1761_, 0);
lean_inc_ref(v_range_1762_);
v_fullRange_x3f_1763_ = lean_ctor_get(v_x_1761_, 1);
lean_inc(v_fullRange_x3f_1763_);
v_severity_x3f_1764_ = lean_ctor_get(v_x_1761_, 2);
lean_inc(v_severity_x3f_1764_);
v_isSilent_x3f_1765_ = lean_ctor_get(v_x_1761_, 3);
lean_inc(v_isSilent_x3f_1765_);
v_code_x3f_1766_ = lean_ctor_get(v_x_1761_, 4);
lean_inc(v_code_x3f_1766_);
v_source_x3f_1767_ = lean_ctor_get(v_x_1761_, 5);
lean_inc(v_source_x3f_1767_);
v_message_1768_ = lean_ctor_get(v_x_1761_, 6);
lean_inc(v_message_1768_);
v_tags_x3f_1769_ = lean_ctor_get(v_x_1761_, 7);
lean_inc(v_tags_x3f_1769_);
v_leanTags_x3f_1770_ = lean_ctor_get(v_x_1761_, 8);
lean_inc(v_leanTags_x3f_1770_);
v_relatedInformation_x3f_1771_ = lean_ctor_get(v_x_1761_, 9);
lean_inc(v_relatedInformation_x3f_1771_);
v_data_x3f_1772_ = lean_ctor_get(v_x_1761_, 10);
lean_inc(v_data_x3f_1772_);
lean_dec_ref(v_x_1761_);
v___x_1773_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_1774_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1762_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_1779_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(v___x_1778_, v_fullRange_x3f_1763_);
v___x_1780_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_1781_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v___x_1780_, v_severity_x3f_1764_);
lean_dec(v_severity_x3f_1764_);
v___x_1782_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_1783_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1782_, v_isSilent_x3f_1765_);
lean_dec(v_isSilent_x3f_1765_);
v___x_1784_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_1785_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(v___x_1784_, v_code_x3f_1766_);
v___x_1786_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_1787_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(v___x_1786_, v_source_x3f_1767_);
v___x_1788_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_1789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_message_1768_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1776_);
v___x_1792_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_1793_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(v___x_1792_, v_tags_x3f_1769_);
v___x_1794_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_1795_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(v___x_1794_, v_leanTags_x3f_1770_);
v___x_1796_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_1797_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(v___x_1796_, v_relatedInformation_x3f_1771_);
v___x_1798_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1799_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v___x_1798_, v_data_x3f_1772_);
lean_dec(v_data_x3f_1772_);
v___x_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1776_);
v___x_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1797_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1795_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1793_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1791_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1787_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1785_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1783_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1781_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1779_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1777_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1812_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1810_, v___x_1811_);
v___x_1813_ = l_Lean_Json_mkObj(v___x_1812_);
lean_dec(v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(size_t v_sz_1814_, size_t v_i_1815_, lean_object* v_bs_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1815_, v_sz_1814_);
if (v___x_1817_ == 0)
{
return v_bs_1816_;
}
else
{
lean_object* v_v_1818_; lean_object* v___x_1819_; lean_object* v_bs_x27_1820_; lean_object* v___x_1821_; size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v_v_1818_ = lean_array_uget(v_bs_1816_, v_i_1815_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v_bs_x27_1820_ = lean_array_uset(v_bs_1816_, v_i_1815_, v___x_1819_);
v___x_1821_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(v_v_1818_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1815_, v___x_1822_);
v___x_1824_ = lean_array_uset(v_bs_x27_1820_, v_i_1815_, v___x_1821_);
v_i_1815_ = v___x_1823_;
v_bs_1816_ = v___x_1824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(lean_object* v_sz_1826_, lean_object* v_i_1827_, lean_object* v_bs_1828_){
_start:
{
size_t v_sz_boxed_1829_; size_t v_i_boxed_1830_; lean_object* v_res_1831_; 
v_sz_boxed_1829_ = lean_unbox_usize(v_sz_1826_);
lean_dec(v_sz_1826_);
v_i_boxed_1830_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_boxed_1829_, v_i_boxed_1830_, v_bs_1828_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(lean_object* v_a_1832_){
_start:
{
size_t v_sz_1833_; size_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_sz_1833_ = lean_array_size(v_a_1832_);
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_1833_, v___x_1834_, v_a_1832_);
v___x_1836_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object* v_x_1841_){
_start:
{
lean_object* v_uri_1842_; lean_object* v_version_x3f_1843_; lean_object* v_isIncremental_x3f_1844_; lean_object* v_diagnostics_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_uri_1842_ = lean_ctor_get(v_x_1841_, 0);
lean_inc_ref(v_uri_1842_);
v_version_x3f_1843_ = lean_ctor_get(v_x_1841_, 1);
lean_inc(v_version_x3f_1843_);
v_isIncremental_x3f_1844_ = lean_ctor_get(v_x_1841_, 2);
lean_inc(v_isIncremental_x3f_1844_);
v_diagnostics_1845_ = lean_ctor_get(v_x_1841_, 3);
lean_inc_ref(v_diagnostics_1845_);
lean_dec_ref(v_x_1841_);
v___x_1846_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
v___x_1847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_uri_1842_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
v___x_1852_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(v___x_1851_, v_version_x3f_1843_);
v___x_1853_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
v___x_1854_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1853_, v_isIncremental_x3f_1844_);
lean_dec(v_isIncremental_x3f_1844_);
v___x_1855_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_1856_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(v_diagnostics_1845_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1849_);
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1849_);
v___x_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1854_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1852_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1850_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1864_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1862_, v___x_1863_);
v___x_1865_ = l_Lean_Json_mkObj(v___x_1864_);
lean_dec(v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v___x_1871_; 
v___x_1871_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0));
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Json_getBool_x3f(v_x_1870_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_a_1881_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v___x_1872_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1872_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(lean_object* v_x_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v_x_1890_);
lean_dec(v_x_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object* v_j_1892_, lean_object* v_k_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = l_Lean_Json_getObjValD(v_j_1892_, v_k_1893_);
v___x_1895_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v___x_1894_);
lean_dec(v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_1896_, lean_object* v_k_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_j_1896_, v_k_1897_);
lean_dec_ref(v_k_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object* v_x_1901_){
_start:
{
if (lean_obj_tag(v_x_1901_) == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0));
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Json_getInt_x3f(v_x_1901_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
v_a_1912_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1914_ = v___x_1903_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1903_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_a_1912_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object* v_j_1921_, lean_object* v_k_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = l_Lean_Json_getObjValD(v_j_1921_, v_k_1922_);
v___x_1924_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_1925_, lean_object* v_k_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_j_1925_, v_k_1926_);
lean_dec_ref(v_k_1926_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(lean_object* v_x_1930_){
_start:
{
if (lean_obj_tag(v_x_1930_) == 0)
{
lean_object* v___x_1931_; 
v___x_1931_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0));
return v___x_1931_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_x_1930_);
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(lean_object* v_j_1934_, lean_object* v_k_1935_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = l_Lean_Json_getObjValD(v_j_1934_, v_k_1935_);
v___x_1937_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(lean_object* v_j_1938_, lean_object* v_k_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_j_1938_, v_k_1939_);
lean_dec_ref(v_k_1939_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(size_t v_sz_1943_, size_t v_i_1944_, lean_object* v_bs_1945_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_usize_dec_lt(v_i_1944_, v_sz_1943_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_bs_1945_);
return v___x_1949_;
}
else
{
lean_object* v_v_1950_; lean_object* v___x_1951_; 
v_v_1950_ = lean_array_uget_borrowed(v_bs_1945_, v_i_1944_);
lean_inc(v_v_1950_);
v___x_1951_ = l_Lean_Json_getNat_x3f(v_v_1950_);
if (lean_obj_tag(v___x_1951_) == 1)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v_bs_x27_1954_; uint8_t v_a_1956_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = lean_unsigned_to_nat(0u);
v_bs_x27_1954_ = lean_array_uset(v_bs_1945_, v_i_1944_, v___x_1953_);
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_dec_eq(v_a_1952_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = lean_unsigned_to_nat(2u);
v___x_1965_ = lean_nat_dec_eq(v_a_1952_, v___x_1964_);
lean_dec(v_a_1952_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v_bs_x27_1954_);
goto v___jp_1946_;
}
else
{
uint8_t v___x_1966_; 
v___x_1966_ = 1;
v_a_1956_ = v___x_1966_;
goto v___jp_1955_;
}
}
else
{
uint8_t v___x_1967_; 
lean_dec(v_a_1952_);
v___x_1967_ = 0;
v_a_1956_ = v___x_1967_;
goto v___jp_1955_;
}
v___jp_1955_:
{
size_t v___x_1957_; size_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1957_ = ((size_t)1ULL);
v___x_1958_ = lean_usize_add(v_i_1944_, v___x_1957_);
v___x_1959_ = lean_box(v_a_1956_);
v___x_1960_ = lean_array_uset(v_bs_x27_1954_, v_i_1944_, v___x_1959_);
v_i_1944_ = v___x_1958_;
v_bs_1945_ = v___x_1960_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_bs_1945_);
goto v___jp_1946_;
}
}
v___jp_1946_:
{
lean_object* v___x_1947_; 
v___x_1947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0));
return v___x_1947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(lean_object* v_sz_1968_, lean_object* v_i_1969_, lean_object* v_bs_1970_){
_start:
{
size_t v_sz_boxed_1971_; size_t v_i_boxed_1972_; lean_object* v_res_1973_; 
v_sz_boxed_1971_ = lean_unbox_usize(v_sz_1968_);
lean_dec(v_sz_1968_);
v_i_boxed_1972_ = lean_unbox_usize(v_i_1969_);
lean_dec(v_i_1969_);
v_res_1973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_boxed_1971_, v_i_boxed_1972_, v_bs_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(lean_object* v_x_1975_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 4)
{
lean_object* v_elems_1976_; size_t v_sz_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
v_elems_1976_ = lean_ctor_get(v_x_1975_, 0);
lean_inc_ref(v_elems_1976_);
lean_dec_ref_known(v_x_1975_, 1);
v_sz_1977_ = lean_array_size(v_elems_1976_);
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_1977_, v___x_1978_, v_elems_1976_);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1980_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_1981_ = lean_unsigned_to_nat(80u);
v___x_1982_ = l_Lean_Json_pretty(v_x_1975_, v___x_1981_);
v___x_1983_ = lean_string_append(v___x_1980_, v___x_1982_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_1985_ = lean_string_append(v___x_1983_, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(lean_object* v_x_1989_){
_start:
{
if (lean_obj_tag(v_x_1989_) == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0));
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(v_x_1989_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
v_a_2000_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2002_ = v___x_1991_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1991_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_a_2000_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(lean_object* v_j_2009_, lean_object* v_k_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = l_Lean_Json_getObjValD(v_j_2009_, v_k_2010_);
v___x_2012_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(lean_object* v_j_2013_, lean_object* v_k_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_j_2013_, v_k_2014_);
lean_dec_ref(v_k_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(lean_object* v_j_2016_, lean_object* v_k_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = l_Lean_Json_getObjValD(v_j_2016_, v_k_2017_);
v___x_2019_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_j_2020_, lean_object* v_k_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_j_2020_, v_k_2021_);
lean_dec_ref(v_k_2021_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2025_) == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0));
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_2025_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_a_2036_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2038_ = v___x_2027_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2027_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_a_2036_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(lean_object* v_j_2045_, lean_object* v_k_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = l_Lean_Json_getObjValD(v_j_2045_, v_k_2046_);
v___x_2048_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_j_2049_, lean_object* v_k_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_j_2049_, v_k_2050_);
lean_dec_ref(v_k_2050_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(lean_object* v_x_2054_){
_start:
{
uint8_t v_a_2064_; 
if (lean_obj_tag(v_x_2054_) == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0));
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; 
lean_inc(v_x_2054_);
v___x_2069_ = l_Lean_Json_getNat_x3f(v_x_2054_);
if (lean_obj_tag(v___x_2069_) == 1)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = lean_unsigned_to_nat(1u);
v___x_2072_ = lean_nat_dec_eq(v_a_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_unsigned_to_nat(2u);
v___x_2074_ = lean_nat_dec_eq(v_a_2070_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(3u);
v___x_2076_ = lean_nat_dec_eq(v_a_2070_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_unsigned_to_nat(4u);
v___x_2078_ = lean_nat_dec_eq(v_a_2070_, v___x_2077_);
lean_dec(v_a_2070_);
if (v___x_2078_ == 0)
{
goto v___jp_2055_;
}
else
{
uint8_t v___x_2079_; 
lean_dec(v_x_2054_);
v___x_2079_ = 3;
v_a_2064_ = v___x_2079_;
goto v___jp_2063_;
}
}
else
{
uint8_t v___x_2080_; 
lean_dec(v_a_2070_);
lean_dec(v_x_2054_);
v___x_2080_ = 2;
v_a_2064_ = v___x_2080_;
goto v___jp_2063_;
}
}
else
{
uint8_t v___x_2081_; 
lean_dec(v_a_2070_);
lean_dec(v_x_2054_);
v___x_2081_ = 1;
v_a_2064_ = v___x_2081_;
goto v___jp_2063_;
}
}
else
{
uint8_t v___x_2082_; 
lean_dec(v_a_2070_);
lean_dec(v_x_2054_);
v___x_2082_ = 0;
v_a_2064_ = v___x_2082_;
goto v___jp_2063_;
}
}
else
{
lean_dec_ref(v___x_2069_);
goto v___jp_2055_;
}
}
v___jp_2055_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2056_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
v___x_2057_ = lean_unsigned_to_nat(80u);
v___x_2058_ = l_Lean_Json_pretty(v_x_2054_, v___x_2057_);
v___x_2059_ = lean_string_append(v___x_2056_, v___x_2058_);
lean_dec_ref(v___x_2058_);
v___x_2060_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2061_ = lean_string_append(v___x_2059_, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
v___jp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(v_a_2064_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(lean_object* v_j_2083_, lean_object* v_k_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = l_Lean_Json_getObjValD(v_j_2083_, v_k_2084_);
v___x_2086_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_j_2087_, lean_object* v_k_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_j_2087_, v_k_2088_);
lean_dec_ref(v_k_2088_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(size_t v_sz_2092_, size_t v_i_2093_, lean_object* v_bs_2094_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_bs_2094_);
return v___x_2098_;
}
else
{
lean_object* v_v_2099_; lean_object* v___x_2100_; 
v_v_2099_ = lean_array_uget_borrowed(v_bs_2094_, v_i_2093_);
lean_inc(v_v_2099_);
v___x_2100_ = l_Lean_Json_getNat_x3f(v_v_2099_);
if (lean_obj_tag(v___x_2100_) == 1)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v_bs_x27_2103_; uint8_t v_a_2105_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = lean_unsigned_to_nat(0u);
v_bs_x27_2103_ = lean_array_uset(v_bs_2094_, v_i_2093_, v___x_2102_);
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_nat_dec_eq(v_a_2101_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(2u);
v___x_2114_ = lean_nat_dec_eq(v_a_2101_, v___x_2113_);
lean_dec(v_a_2101_);
if (v___x_2114_ == 0)
{
lean_dec_ref(v_bs_x27_2103_);
goto v___jp_2095_;
}
else
{
uint8_t v___x_2115_; 
v___x_2115_ = 1;
v_a_2105_ = v___x_2115_;
goto v___jp_2104_;
}
}
else
{
uint8_t v___x_2116_; 
lean_dec(v_a_2101_);
v___x_2116_ = 0;
v_a_2105_ = v___x_2116_;
goto v___jp_2104_;
}
v___jp_2104_:
{
size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2093_, v___x_2106_);
v___x_2108_ = lean_box(v_a_2105_);
v___x_2109_ = lean_array_uset(v_bs_x27_2103_, v_i_2093_, v___x_2108_);
v_i_2093_ = v___x_2107_;
v_bs_2094_ = v___x_2109_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2100_);
lean_dec_ref(v_bs_2094_);
goto v___jp_2095_;
}
}
v___jp_2095_:
{
lean_object* v___x_2096_; 
v___x_2096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0));
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(lean_object* v_sz_2117_, lean_object* v_i_2118_, lean_object* v_bs_2119_){
_start:
{
size_t v_sz_boxed_2120_; size_t v_i_boxed_2121_; lean_object* v_res_2122_; 
v_sz_boxed_2120_ = lean_unbox_usize(v_sz_2117_);
lean_dec(v_sz_2117_);
v_i_boxed_2121_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_boxed_2120_, v_i_boxed_2121_, v_bs_2119_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(lean_object* v_x_2123_){
_start:
{
if (lean_obj_tag(v_x_2123_) == 4)
{
lean_object* v_elems_2124_; size_t v_sz_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_elems_2124_ = lean_ctor_get(v_x_2123_, 0);
lean_inc_ref(v_elems_2124_);
lean_dec_ref_known(v_x_2123_, 1);
v_sz_2125_ = lean_array_size(v_elems_2124_);
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_2125_, v___x_2126_, v_elems_2124_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2128_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2129_ = lean_unsigned_to_nat(80u);
v___x_2130_ = l_Lean_Json_pretty(v_x_2123_, v___x_2129_);
v___x_2131_ = lean_string_append(v___x_2128_, v___x_2130_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2133_ = lean_string_append(v___x_2131_, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 0)
{
lean_object* v___x_2138_; 
v___x_2138_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0));
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(v_x_2137_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2156_; 
v_a_2148_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2150_ = v___x_2139_;
v_isShared_2151_ = v_isSharedCheck_2156_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2139_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2156_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_a_2148_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(lean_object* v_j_2157_, lean_object* v_k_2158_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = l_Lean_Json_getObjValD(v_j_2157_, v_k_2158_);
v___x_2160_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(lean_object* v_j_2161_, lean_object* v_k_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_j_2161_, v_k_2162_);
lean_dec_ref(v_k_2162_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0));
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Json_getStr_x3f(v_x_2166_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2185_; 
v_a_2177_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2179_ = v___x_2168_;
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2168_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_a_2177_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(lean_object* v_j_2186_, lean_object* v_k_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = l_Lean_Json_getObjValD(v_j_2186_, v_k_2187_);
v___x_2189_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(lean_object* v_j_2190_, lean_object* v_k_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_j_2190_, v_k_2191_);
lean_dec_ref(v_k_2191_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(size_t v_sz_2193_, size_t v_i_2194_, lean_object* v_bs_2195_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = lean_usize_dec_lt(v_i_2194_, v_sz_2193_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_bs_2195_);
return v___x_2197_;
}
else
{
lean_object* v_v_2198_; lean_object* v___x_2199_; 
v_v_2198_ = lean_array_uget_borrowed(v_bs_2195_, v_i_2194_);
lean_inc(v_v_2198_);
v___x_2199_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v_bs_2195_);
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2209_; lean_object* v_bs_x27_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_a_2208_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2209_ = lean_unsigned_to_nat(0u);
v_bs_x27_2210_ = lean_array_uset(v_bs_2195_, v_i_2194_, v___x_2209_);
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2194_, v___x_2211_);
v___x_2213_ = lean_array_uset(v_bs_x27_2210_, v_i_2194_, v_a_2208_);
v_i_2194_ = v___x_2212_;
v_bs_2195_ = v___x_2213_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(lean_object* v_sz_2215_, lean_object* v_i_2216_, lean_object* v_bs_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2215_);
lean_dec(v_sz_2215_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_boxed_2218_, v_i_boxed_2219_, v_bs_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(lean_object* v_x_2221_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 4)
{
lean_object* v_elems_2222_; size_t v_sz_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v_elems_2222_ = lean_ctor_get(v_x_2221_, 0);
lean_inc_ref(v_elems_2222_);
lean_dec_ref_known(v_x_2221_, 1);
v_sz_2223_ = lean_array_size(v_elems_2222_);
v___x_2224_ = ((size_t)0ULL);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_2223_, v___x_2224_, v_elems_2222_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2226_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2227_ = lean_unsigned_to_nat(80u);
v___x_2228_ = l_Lean_Json_pretty(v_x_2221_, v___x_2227_);
v___x_2229_ = lean_string_append(v___x_2226_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(lean_object* v_x_2235_){
_start:
{
if (lean_obj_tag(v_x_2235_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0));
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(v_x_2235_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2254_; 
v_a_2246_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2248_ = v___x_2237_;
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2237_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2254_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_a_2246_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2250_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(lean_object* v_j_2255_, lean_object* v_k_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = l_Lean_Json_getObjValD(v_j_2255_, v_k_2256_);
v___x_2258_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(lean_object* v_j_2259_, lean_object* v_k_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_j_2259_, v_k_2260_);
lean_dec_ref(v_k_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(lean_object* v_x_2264_){
_start:
{
lean_object* v_a_2266_; lean_object* v_j_2270_; 
if (lean_obj_tag(v_x_2264_) == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0));
return v___x_2278_;
}
else
{
switch(lean_obj_tag(v_x_2264_))
{
case 2:
{
lean_object* v_n_2279_; lean_object* v_mantissa_2280_; lean_object* v_exponent_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_n_2279_ = lean_ctor_get(v_x_2264_, 0);
v_mantissa_2280_ = lean_ctor_get(v_n_2279_, 0);
v_exponent_2281_ = lean_ctor_get(v_n_2279_, 1);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_nat_dec_eq(v_exponent_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
v_j_2270_ = v_x_2264_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2284_; 
lean_inc(v_mantissa_2280_);
lean_dec_ref_known(v_x_2264_, 1);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_mantissa_2280_);
v_a_2266_ = v___x_2284_;
goto v___jp_2265_;
}
}
case 3:
{
lean_object* v_s_2285_; lean_object* v___x_2286_; 
v_s_2285_ = lean_ctor_get(v_x_2264_, 0);
lean_inc_ref(v_s_2285_);
lean_dec_ref_known(v_x_2264_, 1);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_s_2285_);
v_a_2266_ = v___x_2286_;
goto v___jp_2265_;
}
default: 
{
v_j_2270_ = v_x_2264_;
goto v___jp_2269_;
}
}
}
v___jp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2266_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
v___jp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2271_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_2272_ = lean_unsigned_to_nat(80u);
v___x_2273_ = l_Lean_Json_pretty(v_j_2270_, v___x_2272_);
v___x_2274_ = lean_string_append(v___x_2271_, v___x_2273_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2276_ = lean_string_append(v___x_2274_, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(lean_object* v_j_2287_, lean_object* v_k_2288_){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = l_Lean_Json_getObjValD(v_j_2287_, v_k_2288_);
v___x_2290_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(lean_object* v_j_2291_, lean_object* v_k_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_j_2291_, v_k_2292_);
lean_dec_ref(v_k_2292_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(lean_object* v_json_2294_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_2294_);
v___x_2296_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_json_2294_, v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_json_2294_);
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2301_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_2302_ = lean_string_append(v___x_2301_, v_a_2297_);
lean_dec(v_a_2297_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2302_);
v___x_2304_ = v___x_2299_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2307_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2308_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_2294_);
v___x_2309_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_json_2294_, v___x_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2314_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_2315_ = lean_string_append(v___x_2314_, v_a_2310_);
lean_dec(v_a_2310_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2315_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_a_2320_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2321_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_2294_);
v___x_2322_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_json_2294_, v___x_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_2328_ = lean_string_append(v___x_2327_, v_a_2323_);
lean_dec(v_a_2323_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_a_2333_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2334_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_2294_);
v___x_2335_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2294_, v___x_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2345_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2345_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2340_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_2341_ = lean_string_append(v___x_2340_, v_a_2336_);
lean_dec(v_a_2336_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2341_);
v___x_2343_ = v___x_2338_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2346_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2347_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_2294_);
v___x_2348_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_json_2294_, v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_a_2346_);
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2358_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2358_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2353_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_2354_ = lean_string_append(v___x_2353_, v_a_2349_);
lean_dec(v_a_2349_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2354_);
v___x_2356_ = v___x_2351_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2359_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2360_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_2294_);
v___x_2361_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_json_2294_, v___x_2360_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2359_);
lean_dec(v_a_2346_);
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2371_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2371_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_2367_ = lean_string_append(v___x_2366_, v_a_2362_);
lean_dec(v_a_2362_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2367_);
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2372_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2373_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_2294_);
v___x_2374_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2294_, v___x_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2372_);
lean_dec(v_a_2359_);
lean_dec(v_a_2346_);
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2384_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2384_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2379_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_2380_ = lean_string_append(v___x_2379_, v_a_2375_);
lean_dec(v_a_2375_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2380_);
v___x_2382_ = v___x_2377_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_a_2385_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2386_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_2294_);
v___x_2387_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_json_2294_, v___x_2386_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_a_2385_);
lean_dec(v_a_2372_);
lean_dec(v_a_2359_);
lean_dec(v_a_2346_);
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2397_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2397_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2392_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_2393_ = lean_string_append(v___x_2392_, v_a_2388_);
lean_dec(v_a_2388_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_a_2398_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2399_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_2294_);
v___x_2400_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_json_2294_, v___x_2399_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_a_2398_);
lean_dec(v_a_2385_);
lean_dec(v_a_2372_);
lean_dec(v_a_2359_);
lean_dec(v_a_2346_);
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
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
v___x_2405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
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
lean_object* v_a_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_a_2411_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2412_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_2294_);
v___x_2413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_json_2294_, v___x_2412_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_a_2411_);
lean_dec(v_a_2398_);
lean_dec(v_a_2385_);
lean_dec(v_a_2372_);
lean_dec(v_a_2359_);
lean_dec(v_a_2346_);
lean_dec(v_a_2333_);
lean_dec(v_a_2320_);
lean_dec(v_a_2307_);
lean_dec(v_json_2294_);
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2423_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2423_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_2419_ = lean_string_append(v___x_2418_, v_a_2414_);
lean_dec(v_a_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2419_);
v___x_2421_ = v___x_2416_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_a_2424_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2413_, 1);
v___x_2425_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_2426_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_json_2294_, v___x_2425_);
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2431_, 0, v_a_2307_);
lean_ctor_set(v___x_2431_, 1, v_a_2320_);
lean_ctor_set(v___x_2431_, 2, v_a_2333_);
lean_ctor_set(v___x_2431_, 3, v_a_2346_);
lean_ctor_set(v___x_2431_, 4, v_a_2359_);
lean_ctor_set(v___x_2431_, 5, v_a_2372_);
lean_ctor_set(v___x_2431_, 6, v_a_2385_);
lean_ctor_set(v___x_2431_, 7, v_a_2398_);
lean_ctor_set(v___x_2431_, 8, v_a_2411_);
lean_ctor_set(v___x_2431_, 9, v_a_2424_);
lean_ctor_set(v___x_2431_, 10, v_a_2427_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(size_t v_sz_2436_, size_t v_i_2437_, lean_object* v_bs_2438_){
_start:
{
uint8_t v___x_2439_; 
v___x_2439_ = lean_usize_dec_lt(v_i_2437_, v_sz_2436_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_bs_2438_);
return v___x_2440_;
}
else
{
lean_object* v_v_2441_; lean_object* v___x_2442_; 
v_v_2441_ = lean_array_uget_borrowed(v_bs_2438_, v_i_2437_);
lean_inc(v_v_2441_);
v___x_2442_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(v_v_2441_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_bs_2438_);
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2452_; lean_object* v_bs_x27_2453_; size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
v_a_2451_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2452_ = lean_unsigned_to_nat(0u);
v_bs_x27_2453_ = lean_array_uset(v_bs_2438_, v_i_2437_, v___x_2452_);
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2437_, v___x_2454_);
v___x_2456_ = lean_array_uset(v_bs_x27_2453_, v_i_2437_, v_a_2451_);
v_i_2437_ = v___x_2455_;
v_bs_2438_ = v___x_2456_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2458_, lean_object* v_i_2459_, lean_object* v_bs_2460_){
_start:
{
size_t v_sz_boxed_2461_; size_t v_i_boxed_2462_; lean_object* v_res_2463_; 
v_sz_boxed_2461_ = lean_unbox_usize(v_sz_2458_);
lean_dec(v_sz_2458_);
v_i_boxed_2462_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_2461_, v_i_boxed_2462_, v_bs_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 4)
{
lean_object* v_elems_2465_; size_t v_sz_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v_elems_2465_ = lean_ctor_get(v_x_2464_, 0);
lean_inc_ref(v_elems_2465_);
lean_dec_ref_known(v_x_2464_, 1);
v_sz_2466_ = lean_array_size(v_elems_2465_);
v___x_2467_ = ((size_t)0ULL);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_2466_, v___x_2467_, v_elems_2465_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2469_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2470_ = lean_unsigned_to_nat(80u);
v___x_2471_ = l_Lean_Json_pretty(v_x_2464_, v___x_2470_);
v___x_2472_ = lean_string_append(v___x_2469_, v___x_2471_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2474_ = lean_string_append(v___x_2472_, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(lean_object* v_j_2476_, lean_object* v_k_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = l_Lean_Json_getObjValD(v_j_2476_, v_k_2477_);
v___x_2479_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(lean_object* v_j_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_j_2480_, v_k_2481_);
lean_dec_ref(v_k_2481_);
return v_res_2482_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = 1;
v___x_2489_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1));
v___x_2490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2489_, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_2492_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2);
v___x_2493_ = lean_string_append(v___x_2492_, v___x_2491_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = 1;
v___x_2497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4));
v___x_2498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5);
v___x_2500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2501_ = lean_string_append(v___x_2500_, v___x_2499_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6);
v___x_2504_ = lean_string_append(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = 1;
v___x_2509_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9));
v___x_2510_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2509_, v___x_2508_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10);
v___x_2512_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2513_ = lean_string_append(v___x_2512_, v___x_2511_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11);
v___x_2516_ = lean_string_append(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = 1;
v___x_2521_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14));
v___x_2522_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15);
v___x_2524_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2525_ = lean_string_append(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2527_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16);
v___x_2528_ = lean_string_append(v___x_2527_, v___x_2526_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = 1;
v___x_2532_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18));
v___x_2533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2532_, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19);
v___x_2535_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2536_ = lean_string_append(v___x_2535_, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2538_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20);
v___x_2539_ = lean_string_append(v___x_2538_, v___x_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object* v_json_2540_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
lean_inc(v_json_2540_);
v___x_2542_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2540_, v___x_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_json_2540_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2547_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7);
v___x_2548_ = lean_string_append(v___x_2547_, v_a_2543_);
lean_dec(v_a_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2548_);
v___x_2550_ = v___x_2545_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2554_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
lean_inc(v_json_2540_);
v___x_2555_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_json_2540_, v___x_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_a_2553_);
lean_dec(v_json_2540_);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2560_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12);
v___x_2561_ = lean_string_append(v___x_2560_, v_a_2556_);
lean_dec(v_a_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2561_);
v___x_2563_ = v___x_2558_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
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
v_a_2566_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2567_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
lean_inc(v_json_2540_);
v___x_2568_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2540_, v___x_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_a_2566_);
lean_dec(v_a_2553_);
lean_dec(v_json_2540_);
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
v___x_2573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17);
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
lean_object* v_a_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_a_2579_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2580_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_2581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_json_2540_, v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v_a_2579_);
lean_dec(v_a_2566_);
lean_dec(v_a_2553_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2586_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21);
v___x_2587_ = lean_string_append(v___x_2586_, v_a_2582_);
lean_dec(v_a_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_a_2592_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2594_ = v___x_2581_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2581_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2596_, 0, v_a_2553_);
lean_ctor_set(v___x_2596_, 1, v_a_2566_);
lean_ctor_set(v___x_2596_, 2, v_a_2579_);
lean_ctor_set(v___x_2596_, 3, v_a_2592_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
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
