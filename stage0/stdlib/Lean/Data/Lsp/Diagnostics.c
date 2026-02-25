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
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx___boxed(lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticSeverity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticSeverity_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown DiagnosticSeverity '"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value;
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticCode_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticCode___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3;
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
extern lean_object* l_Lean_Lsp_instInhabitedLocation_default;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation;
uint8_t l_Lean_Lsp_instBEqLocation_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
lean_object* l_Lean_Lsp_instToJsonLocation_toJson(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "DiagnosticRelatedInformation"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 67, 100, 141, 182, 93, 157, 48)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
uint8_t l_Lean_Lsp_instOrdLocation_ord(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value;
extern lean_object* l_Lean_Lsp_instInhabitedRange_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value;
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2;
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value;
lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instBEq___private__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value;
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRange_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value;
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value;
lean_object* l_Lean_instToJsonString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value;
lean_object* l_Array_toJson(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value;
lean_object* l_id___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRange_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value;
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)} };
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
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value)} };
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
lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value)} };
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
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value)} };
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
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0;
static lean_once_cell_t l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__3___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Json_instBEq___private__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10_spec__14(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "diagnostics"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26___closed__0_value;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24_spec__29(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10___closed__0_value;
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value;
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 43, 109, 94, 169, 251, 160, 225)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Lsp_DiagnosticSeverity_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_DiagnosticSeverity_error_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_DiagnosticSeverity_warning_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_DiagnosticSeverity_information_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_DiagnosticSeverity_hint_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticSeverity_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(x_1);
x_4 = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticSeverity_ord(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(x_1);
x_4 = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Lsp_instOrdDiagnosticSeverity_ord(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_dec_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(4u);
x_19 = lean_nat_dec_eq(x_11, x_18);
lean_dec(x_11);
if (x_19 == 0)
{
goto block_9;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2, &l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_1);
x_21 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_1);
x_22 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_1);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5);
return x_23;
}
}
else
{
lean_dec_ref(x_10);
goto block_9;
}
block_9:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
x_3 = lean_unsigned_to_nat(80u);
x_4 = l_Lean_Json_pretty(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticCode_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_DiagnosticCode_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedDiagnosticCode_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticCode_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_string_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instBEqDiagnosticCode_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticCode_ord(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_int_dec_eq(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = 2;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_string_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_string_dec_eq(x_12, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 2;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instOrdDiagnosticCode_ord(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
goto block_9;
}
else
{
uint8_t x_15; 
lean_inc(x_11);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_11);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
case 3:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_ctor_set_tag(x_1, 1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
default: 
{
goto block_9;
}
}
block_9:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
x_3 = lean_unsigned_to_nat(80u);
x_4 = l_Lean_Json_pretty(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_JsonNumber_fromInt(x_3);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_JsonNumber_fromInt(x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_DiagnosticTag_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticTag_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_DiagnosticTag_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Lsp_DiagnosticTag_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_DiagnosticTag_unnecessary_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_DiagnosticTag_deprecated_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticTag_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Lsp_DiagnosticTag_ctorIdx(x_1);
x_4 = l_Lean_Lsp_DiagnosticTag_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Lsp_instBEqDiagnosticTag_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticTag_ord(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Lsp_DiagnosticTag_ctorIdx(x_1);
x_4 = l_Lean_Lsp_DiagnosticTag_ctorIdx(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Lsp_instOrdDiagnosticTag_ord(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
goto block_3;
}
else
{
lean_object* x_10; 
x_10 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2, &l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3, &l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3);
return x_11;
}
}
else
{
lean_dec_ref(x_4);
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1));
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Lsp_LeanDiagnosticTag_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(x_1);
x_4 = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(x_1);
x_4 = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
goto block_3;
}
else
{
lean_object* x_10; 
x_10 = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2, &l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3, &l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3);
return x_11;
}
}
else
{
lean_dec_ref(x_4);
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1));
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0));
x_2 = l_Lean_Lsp_instInhabitedLocation_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Lsp_instBEqLocation_beq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
x_6 = l_Lean_Lsp_instToJsonLocation_toJson(x_3);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2, &l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2);
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
x_21 = l_Lean_Lsp_instToJsonLocation_toJson(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2, &l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2);
x_32 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(x_30, x_31);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_instFromJsonLocation_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Lsp_instOrdLocation_ord(x_3, x_5);
if (x_7 == 1)
{
uint8_t x_8; 
x_8 = lean_string_dec_lt(x_4, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_dec_eq(x_4, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Lsp_instInhabitedRange_default;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_3);
lean_ctor_set(x_4, 5, x_3);
lean_ctor_set(x_4, 6, x_1);
lean_ctor_set(x_4, 7, x_3);
lean_ctor_set(x_4, 8, x_3);
lean_ctor_set(x_4, 9, x_3);
lean_ctor_set(x_4, 10, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 6);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 8);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 9);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 10);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 7);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 8);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 9);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 10);
lean_inc(x_25);
lean_dec_ref(x_3);
x_26 = l_Lean_Lsp_instBEqRange_beq(x_4, x_15);
lean_dec_ref(x_15);
lean_dec_ref(x_4);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0));
x_28 = l_Option_instBEq_beq___redArg(x_27, x_5, x_16);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0));
x_30 = l_Option_instBEq_beq___redArg(x_29, x_6, x_17);
if (x_30 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1);
x_32 = l_Option_instBEq_beq___redArg(x_31, x_7, x_18);
if (x_32 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticCode___closed__0));
x_34 = l_Option_instBEq_beq___redArg(x_33, x_8, x_19);
if (x_34 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2);
x_36 = l_Option_instBEq_beq___redArg(x_35, x_9, x_20);
if (x_36 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_1);
return x_36;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_apply_2(x_1, x_10, x_21);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_39 = lean_unbox(x_37);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3));
x_41 = l_Option_instBEq_beq___redArg(x_40, x_11, x_22);
if (x_41 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4));
x_43 = l_Option_instBEq_beq___redArg(x_42, x_12, x_23);
if (x_43 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5));
x_45 = l_Option_instBEq_beq___redArg(x_44, x_13, x_24);
if (x_45 == 0)
{
lean_dec(x_25);
lean_dec(x_14);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6));
x_47 = l_Option_instBEq_beq___redArg(x_46, x_14, x_25);
return x_47;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Lsp_instBEqDiagnosticWith_beq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 6);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 7);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 8);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 9);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 10);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0));
x_15 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0));
x_16 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1));
x_17 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0));
x_18 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2));
x_19 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3));
x_20 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4));
x_21 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5));
x_22 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6));
x_23 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
x_24 = l_Lean_Lsp_instToJsonRange_toJson(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
x_29 = l_Lean_Json_opt___redArg(x_14, x_28, x_4);
x_30 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
x_31 = l_Lean_Json_opt___redArg(x_15, x_30, x_5);
x_32 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
x_33 = l_Lean_Json_opt___redArg(x_16, x_32, x_6);
x_34 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
x_35 = l_Lean_Json_opt___redArg(x_17, x_34, x_7);
x_36 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
x_37 = l_Lean_Json_opt___redArg(x_18, x_36, x_8);
x_38 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
x_39 = lean_apply_1(x_1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
x_42 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
x_43 = l_Lean_Json_opt___redArg(x_19, x_42, x_10);
x_44 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
x_45 = l_Lean_Json_opt___redArg(x_20, x_44, x_11);
x_46 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
x_47 = l_Lean_Json_opt___redArg(x_21, x_46, x_12);
x_48 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
x_49 = l_Lean_Json_opt___redArg(x_22, x_48, x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_26);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_31);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_29);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_27);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2, &l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2);
x_62 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), x_22, x_60, x_61);
x_63 = l_Lean_Json_mkObj(x_62);
return x_63;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0));
x_4 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1));
x_5 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(x_2);
x_6 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_ctor_set_tag(x_6, 0);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec_ref(x_6);
x_19 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(x_2);
x_20 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_4, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_ctor_set_tag(x_20, 0);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec_ref(x_20);
x_33 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15));
x_34 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(x_2);
x_35 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_44; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_ctor_set_tag(x_35, 0);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec_ref(x_35);
x_48 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22));
x_49 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(x_2);
x_50 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_48, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_59; 
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
lean_ctor_set_tag(x_50, 0);
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec_ref(x_50);
x_63 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28));
x_64 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(x_2);
x_65 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_63, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_74; 
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_ctor_set_tag(x_65, 0);
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
lean_dec_ref(x_65);
x_78 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35));
x_79 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(x_2);
x_80 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_78, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_89; 
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
lean_ctor_set_tag(x_80, 0);
return x_80;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_80, 0);
lean_inc(x_90);
lean_dec(x_80);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
lean_dec_ref(x_80);
x_93 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(x_2);
x_94 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_1, x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_98);
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
lean_dec(x_94);
x_100 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
else
{
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_103; 
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_94);
if (x_103 == 0)
{
lean_ctor_set_tag(x_94, 0);
return x_94;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_94, 0);
lean_inc(x_104);
lean_dec(x_94);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_94, 0);
lean_inc(x_106);
lean_dec_ref(x_94);
x_107 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44));
x_108 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(x_2);
x_109 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_107, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
x_113 = lean_string_append(x_112, x_111);
lean_dec(x_111);
lean_ctor_set(x_109, 0, x_113);
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
x_116 = lean_string_append(x_115, x_114);
lean_dec(x_114);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_109);
if (x_118 == 0)
{
lean_ctor_set_tag(x_109, 0);
return x_109;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
lean_dec(x_109);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_109, 0);
lean_inc(x_121);
lean_dec_ref(x_109);
x_122 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51));
x_123 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(x_2);
x_124 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_122, x_123);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
x_128 = lean_string_append(x_127, x_126);
lean_dec(x_126);
lean_ctor_set(x_124, 0, x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
else
{
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_133; 
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_124);
if (x_133 == 0)
{
lean_ctor_set_tag(x_124, 0);
return x_124;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_124, 0);
lean_inc(x_134);
lean_dec(x_124);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
lean_dec_ref(x_124);
x_137 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58));
x_138 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(x_2);
x_139 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_137, x_138);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
lean_dec(x_136);
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
x_143 = lean_string_append(x_142, x_141);
lean_dec(x_141);
lean_ctor_set(x_139, 0, x_143);
return x_139;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
lean_dec(x_139);
x_145 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
x_146 = lean_string_append(x_145, x_144);
lean_dec(x_144);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
else
{
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_148; 
lean_dec(x_136);
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_139);
if (x_148 == 0)
{
lean_ctor_set_tag(x_139, 0);
return x_139;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_139, 0);
lean_inc(x_149);
lean_dec(x_139);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_139, 0);
lean_inc(x_151);
lean_dec_ref(x_139);
x_152 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65));
x_153 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
x_154 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_152, x_153);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
lean_dec(x_151);
lean_dec(x_136);
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70);
x_158 = lean_string_append(x_157, x_156);
lean_dec(x_156);
lean_ctor_set(x_154, 0, x_158);
return x_154;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
lean_dec(x_154);
x_160 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70);
x_161 = lean_string_append(x_160, x_159);
lean_dec(x_159);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
else
{
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_163; 
lean_dec(x_151);
lean_dec(x_136);
lean_dec(x_121);
lean_dec(x_106);
lean_dec(x_92);
lean_dec(x_77);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_18);
x_163 = !lean_is_exclusive(x_154);
if (x_163 == 0)
{
lean_ctor_set_tag(x_154, 0);
return x_154;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_154, 0);
lean_inc(x_164);
lean_dec(x_154);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_154);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_154, 0);
x_168 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_168, 0, x_18);
lean_ctor_set(x_168, 1, x_32);
lean_ctor_set(x_168, 2, x_47);
lean_ctor_set(x_168, 3, x_62);
lean_ctor_set(x_168, 4, x_77);
lean_ctor_set(x_168, 5, x_92);
lean_ctor_set(x_168, 6, x_106);
lean_ctor_set(x_168, 7, x_121);
lean_ctor_set(x_168, 8, x_136);
lean_ctor_set(x_168, 9, x_151);
lean_ctor_set(x_168, 10, x_167);
lean_ctor_set(x_154, 0, x_168);
return x_154;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_154, 0);
lean_inc(x_169);
lean_dec(x_154);
x_170 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_170, 0, x_18);
lean_ctor_set(x_170, 1, x_32);
lean_ctor_set(x_170, 2, x_47);
lean_ctor_set(x_170, 3, x_62);
lean_ctor_set(x_170, 4, x_77);
lean_ctor_set(x_170, 5, x_92);
lean_ctor_set(x_170, 6, x_106);
lean_ctor_set(x_170, 7, x_121);
lean_ctor_set(x_170, 8, x_136);
lean_ctor_set(x_170, 9, x_151);
lean_ctor_set(x_170, 10, x_169);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_DiagnosticWith_fullRange(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0, &l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0);
x_2 = lean_box(0);
x_3 = ((lean_object*)(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1, &l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_int_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Lsp_instBEqDiagnosticCode_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_6);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Json_instBEq___private__1(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Lsp_instBEqRange_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg(x_6, x_7, x_8);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg(x_6, x_7, x_8);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_Lsp_instBEqDiagnosticTag_beq(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg(x_6, x_7, x_8);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_ctor_get(x_1, 9);
x_13 = lean_ctor_get(x_1, 10);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = lean_ctor_get(x_2, 4);
x_19 = lean_ctor_get(x_2, 5);
x_20 = lean_ctor_get(x_2, 6);
x_21 = lean_ctor_get(x_2, 7);
x_22 = lean_ctor_get(x_2, 8);
x_23 = lean_ctor_get(x_2, 9);
x_24 = lean_ctor_get(x_2, 10);
x_25 = l_Lean_Lsp_instBEqRange_beq(x_3, x_14);
if (x_25 == 0)
{
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__1(x_4, x_15);
if (x_26 == 0)
{
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__2(x_5, x_16);
if (x_27 == 0)
{
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__3(x_6, x_17);
if (x_28 == 0)
{
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__4(x_7, x_18);
if (x_29 == 0)
{
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__5(x_8, x_19);
if (x_30 == 0)
{
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_string_dec_eq(x_9, x_20);
if (x_31 == 0)
{
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6(x_10, x_21);
if (x_32 == 0)
{
return x_32;
}
else
{
uint8_t x_33; 
x_33 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7(x_11, x_22);
if (x_33 == 0)
{
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8(x_12, x_23);
if (x_34 == 0)
{
return x_34;
}
else
{
uint8_t x_35; 
x_35 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__9(x_13, x_24);
return x_35;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_string_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_array_get_size(x_8);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg(x_5, x_8, x_11);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__6_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__7_spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1_spec__8_spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_JsonNumber_fromInt(x_5);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_JsonNumber_fromInt(x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8_spec__11(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
x_8 = x_15;
goto block_13;
}
else
{
lean_object* x_16; 
x_16 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
x_8 = x_16;
goto block_13;
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8_spec__11(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8_spec__11(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7_spec__8(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10_spec__14(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
x_8 = x_15;
goto block_13;
}
else
{
lean_object* x_16; 
x_16 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
x_8 = x_16;
goto block_13;
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10_spec__14(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10_spec__14(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8_spec__10(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__10(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Lsp_instToJsonRange_toJson(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_ctor(1, 0, 1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, 0, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12_spec__17(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12_spec__17(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12_spec__17(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9_spec__12(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_JsonNumber_fromInt(x_11);
lean_ctor_set_tag(x_9, 2);
lean_ctor_set(x_9, 0, x_12);
x_3 = x_9;
goto block_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_JsonNumber_fromInt(x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_3 = x_15;
goto block_7;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_ctor_set_tag(x_9, 3);
x_3 = x_9;
goto block_7;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_3 = x_18;
goto block_7;
}
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; 
x_11 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
x_3 = x_11;
goto block_7;
}
case 1:
{
lean_object* x_12; 
x_12 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
x_3 = x_12;
goto block_7;
}
case 2:
{
lean_object* x_13; 
x_13 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
x_3 = x_13;
goto block_7;
}
default: 
{
lean_object* x_14; 
x_14 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
x_3 = x_14;
goto block_7;
}
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_ctor_set_tag(x_2, 3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 7);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 8);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 9);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 10);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
x_14 = l_Lean_Lsp_instToJsonRange_toJson(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
x_19 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__2(x_18, x_3);
x_20 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
x_21 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__3(x_20, x_4);
lean_dec(x_4);
x_22 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
x_23 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__4(x_22, x_5);
lean_dec(x_5);
x_24 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
x_25 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__5(x_24, x_6);
x_26 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
x_27 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__6(x_26, x_7);
x_28 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_16);
x_32 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
x_33 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__7(x_32, x_9);
x_34 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
x_35 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__8(x_34, x_10);
x_36 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
x_37 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__9(x_36, x_11);
x_38 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
x_39 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1_spec__10(x_38, x_12);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2, &l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2);
x_52 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(x_50, x_51);
x_53 = l_Lean_Json_mkObj(x_52);
return x_53;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__1(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1_spec__2(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
x_11 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(x_10, x_3);
x_12 = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
x_13 = l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2, &l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2);
x_20 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(x_18, x_19);
x_21 = l_Lean_Json_mkObj(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instFromJsonRange_fromJson(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5_spec__6(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_8);
x_9 = l_Lean_Json_getNat_x3f(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_10, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_dec_eq(x_10, x_22);
lean_dec(x_10);
if (x_23 == 0)
{
lean_dec_ref(x_12);
goto block_5;
}
else
{
uint8_t x_24; 
x_24 = 1;
x_13 = x_24;
goto block_19;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
x_25 = 0;
x_13 = x_25;
goto block_19;
}
block_19:
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_box(x_13);
x_17 = lean_array_uset(x_12, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_3);
goto block_5;
}
}
block_5:
{
lean_object* x_4; 
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26___closed__0));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21_spec__26(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22___closed__0));
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13_spec__22(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24_spec__29(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24_spec__29(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24_spec__29(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20_spec__24(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12_spec__20(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getBool_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7_spec__10(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9_spec__14(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8(lean_object* x_1) {
_start:
{
uint8_t x_10; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8___closed__0));
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_1);
x_16 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_dec_eq(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_dec_eq(x_17, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_nat_dec_eq(x_17, x_24);
lean_dec(x_17);
if (x_25 == 0)
{
goto block_9;
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = 3;
x_10 = x_26;
goto block_14;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_1);
x_27 = 2;
x_10 = x_27;
goto block_14;
}
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_1);
x_28 = 1;
x_10 = x_28;
goto block_14;
}
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_1);
x_29 = 0;
x_10 = x_29;
goto block_14;
}
}
else
{
lean_dec_ref(x_16);
goto block_9;
}
}
block_9:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
x_3 = lean_unsigned_to_nat(80u);
x_4 = l_Lean_Json_pretty(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6_spec__8(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_instFromJsonRange_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__4(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_8);
x_9 = l_Lean_Json_getNat_x3f(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_10, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_dec_eq(x_10, x_22);
lean_dec(x_10);
if (x_23 == 0)
{
lean_dec_ref(x_12);
goto block_5;
}
else
{
uint8_t x_24; 
x_24 = 1;
x_13 = x_24;
goto block_19;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
x_25 = 0;
x_13 = x_25;
goto block_19;
}
block_19:
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_box(x_13);
x_17 = lean_array_uset(x_12, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_3);
goto block_5;
}
}
block_5:
{
lean_object* x_4; 
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23___closed__0));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18_spec__23(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16_spec__18(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10_spec__16(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12___closed__0));
return x_15;
}
else
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
if (x_20 == 0)
{
x_6 = x_1;
goto block_14;
}
else
{
lean_object* x_21; 
lean_inc(x_17);
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_2 = x_21;
goto block_5;
}
}
case 3:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_2 = x_23;
goto block_5;
}
default: 
{
x_6 = x_1;
goto block_14;
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
x_8 = lean_unsigned_to_nat(80u);
x_9 = l_Lean_Json_pretty(x_6, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8_spec__12(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__4(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(x_1);
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__5(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec_ref(x_17);
x_30 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(x_1);
x_31 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__6(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_ctor_set_tag(x_31, 0);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec_ref(x_31);
x_44 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__7(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_54; 
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
lean_ctor_set_tag(x_45, 0);
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
lean_dec_ref(x_45);
x_58 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(x_1);
x_59 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__8(x_1, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_68; 
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
lean_ctor_set_tag(x_59, 0);
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
lean_dec_ref(x_59);
x_72 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(x_1);
x_73 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__9(x_1, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_77);
return x_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_82; 
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
lean_ctor_set_tag(x_73, 0);
return x_73;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
lean_dec(x_73);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_73, 0);
lean_inc(x_85);
lean_dec_ref(x_73);
x_86 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
x_91 = lean_string_append(x_90, x_89);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_96; 
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
lean_ctor_set_tag(x_87, 0);
return x_87;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
lean_dec_ref(x_87);
x_100 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(x_1);
x_101 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__10(x_1, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
lean_ctor_set(x_101, 0, x_105);
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
else
{
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_110; 
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
lean_ctor_set_tag(x_101, 0);
return x_101;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_101, 0);
lean_inc(x_111);
lean_dec(x_101);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
lean_dec_ref(x_101);
x_114 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(x_1);
x_115 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11(x_1, x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
lean_dec(x_113);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_119);
return x_115;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_124; 
lean_dec(x_113);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_115);
if (x_124 == 0)
{
lean_ctor_set_tag(x_115, 0);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_115, 0);
lean_inc(x_125);
lean_dec(x_115);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_115, 0);
lean_inc(x_127);
lean_dec_ref(x_115);
x_128 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__12(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_127);
lean_dec(x_113);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
x_133 = lean_string_append(x_132, x_131);
lean_dec(x_131);
lean_ctor_set(x_129, 0, x_133);
return x_129;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
else
{
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_138; 
lean_dec(x_127);
lean_dec(x_113);
lean_dec(x_99);
lean_dec(x_85);
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_129);
if (x_138 == 0)
{
lean_ctor_set_tag(x_129, 0);
return x_129;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_129, 0);
lean_inc(x_139);
lean_dec(x_129);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_129, 0);
lean_inc(x_141);
lean_dec_ref(x_129);
x_142 = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
x_143 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__13(x_1, x_142);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_146, 0, x_15);
lean_ctor_set(x_146, 1, x_29);
lean_ctor_set(x_146, 2, x_43);
lean_ctor_set(x_146, 3, x_57);
lean_ctor_set(x_146, 4, x_71);
lean_ctor_set(x_146, 5, x_85);
lean_ctor_set(x_146, 6, x_99);
lean_ctor_set(x_146, 7, x_113);
lean_ctor_set(x_146, 8, x_127);
lean_ctor_set(x_146, 9, x_141);
lean_ctor_set(x_146, 10, x_145);
lean_ctor_set(x_143, 0, x_146);
return x_143;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_148, 0, x_15);
lean_ctor_set(x_148, 1, x_29);
lean_ctor_set(x_148, 2, x_43);
lean_ctor_set(x_148, 3, x_57);
lean_ctor_set(x_148, 4, x_71);
lean_ctor_set(x_148, 5, x_85);
lean_ctor_set(x_148, 6, x_99);
lean_ctor_set(x_148, 7, x_113);
lean_ctor_set(x_148, 8, x_127);
lean_ctor_set(x_148, 9, x_141);
lean_ctor_set(x_148, 10, x_147);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__4(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2_spec__3_spec__11_spec__18_spec__21___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getInt_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
lean_inc(x_1);
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec_ref(x_17);
x_30 = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
x_31 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_15);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16);
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16);
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_15);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_ctor_set_tag(x_31, 0);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_31, 0, x_45);
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
}
}
}
}
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
l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default = _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default);
l_Lean_Lsp_instInhabitedPublishDiagnosticsParams = _init_l_Lean_Lsp_instInhabitedPublishDiagnosticsParams();
lean_mark_persistent(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
