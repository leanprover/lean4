// Lean compiler output
// Module: Init.Data.ToString.Basic
// Imports: public import Init.Data.Repr import Init.Data.Char.Basic
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
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_string_any(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringString___closed__0 = (const lean_object*)&l_instToStringString___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringString = (const lean_object*)&l_instToStringString___closed__0_value;
static const lean_closure_object l_instToStringRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Substring_Raw_Internal_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringRaw___closed__0 = (const lean_object*)&l_instToStringRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringRaw = (const lean_object*)&l_instToStringRaw___closed__0_value;
static const lean_string_object l_instToStringChar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_instToStringChar___lam__0___closed__0 = (const lean_object*)&l_instToStringChar___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringChar___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringChar___closed__0 = (const lean_object*)&l_instToStringChar___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringChar = (const lean_object*)&l_instToStringChar___closed__0_value;
static const lean_string_object l_instToStringBool___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_instToStringBool___lam__0___closed__0 = (const lean_object*)&l_instToStringBool___lam__0___closed__0_value;
static const lean_string_object l_instToStringBool___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_instToStringBool___lam__0___closed__1 = (const lean_object*)&l_instToStringBool___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringBool___closed__0 = (const lean_object*)&l_instToStringBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringBool = (const lean_object*)&l_instToStringBool___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringDecidable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringDecidable___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringDecidable___redArg___closed__0 = (const lean_object*)&l_instToStringDecidable___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg();
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object*);
static const lean_string_object l_instToStringPUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "()"};
static const lean_object* l_instToStringPUnit___lam__0___closed__0 = (const lean_object*)&l_instToStringPUnit___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object*);
static const lean_closure_object l_instToStringPUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringPUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringPUnit___closed__0 = (const lean_object*)&l_instToStringPUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringPUnit = (const lean_object*)&l_instToStringPUnit___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringULift(lean_object*, lean_object*);
static const lean_closure_object l_instToStringNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringNat___closed__0 = (const lean_object*)&l_instToStringNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringNat = (const lean_object*)&l_instToStringNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringRaw__1 = (const lean_object*)&l_instToStringNat___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringFin___redArg();
LEAN_EXPORT lean_object* l_instToStringFin___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFin(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt8___closed__0 = (const lean_object*)&l_instToStringUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt8 = (const lean_object*)&l_instToStringUInt8___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt16___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt16___closed__0 = (const lean_object*)&l_instToStringUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt16 = (const lean_object*)&l_instToStringUInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt32___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt32___closed__0 = (const lean_object*)&l_instToStringUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt32 = (const lean_object*)&l_instToStringUInt32___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt64___closed__0 = (const lean_object*)&l_instToStringUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt64 = (const lean_object*)&l_instToStringUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUSize___closed__0 = (const lean_object*)&l_instToStringUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUSize = (const lean_object*)&l_instToStringUSize___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object*);
static const lean_closure_object l_instToStringFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringFormat___closed__0 = (const lean_object*)&l_instToStringFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringFormat = (const lean_object*)&l_instToStringFormat___closed__0_value;
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object*);
static const lean_string_object l_addParenHeuristic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_addParenHeuristic___closed__0 = (const lean_object*)&l_addParenHeuristic___closed__0_value;
static const lean_string_object l_addParenHeuristic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_addParenHeuristic___closed__1 = (const lean_object*)&l_addParenHeuristic___closed__1_value;
static const lean_string_object l_addParenHeuristic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_addParenHeuristic___closed__2 = (const lean_object*)&l_addParenHeuristic___closed__2_value;
static const lean_string_object l_addParenHeuristic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_addParenHeuristic___closed__3 = (const lean_object*)&l_addParenHeuristic___closed__3_value;
static const lean_closure_object l_addParenHeuristic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_addParenHeuristic___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_addParenHeuristic___closed__4 = (const lean_object*)&l_addParenHeuristic___closed__4_value;
static const lean_string_object l_addParenHeuristic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_addParenHeuristic___closed__5 = (const lean_object*)&l_addParenHeuristic___closed__5_value;
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object*);
static const lean_string_object l_instToStringOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_instToStringOption___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringOption___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringOption___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_instToStringOption___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringOption___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption(lean_object*, lean_object*);
static const lean_string_object l_instToStringSum___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "(inl "};
static const lean_object* l_instToStringSum___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringSum___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringSum___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "(inr "};
static const lean_object* l_instToStringSum___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringSum___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instToStringProd___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_instToStringProd___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringProd___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instToStringSigma___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_instToStringSigma___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringSigma___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringSigma___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_instToStringSigma___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringSigma___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instToStringExcept___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_instToStringExcept___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringExcept___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringExcept___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ok: "};
static const lean_object* l_instToStringExcept___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringExcept___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instReprExcept___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Except.error "};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__0 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_instReprExcept___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprExcept___redArg___lam__0___closed__0_value)}};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__1 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__1_value;
static const lean_string_object l_instReprExcept___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Except.ok "};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__2 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_instReprExcept___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprExcept___redArg___lam__0___closed__2_value)}};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__3 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg(lean_object* v_inst_1_){
_start:
{
lean_inc_ref(v_inst_1_);
return v_inst_1_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg___boxed(lean_object* v_inst_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_instToStringId___aux__1___redArg(v_inst_2_);
lean_dec_ref(v_inst_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___aux__1(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_){
_start:
{
lean_inc_ref(v_inst_5_);
return v_inst_5_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___aux__1___boxed(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_instToStringId___aux__1(v_00_u03b1_6_, v_inst_7_);
lean_dec_ref(v_inst_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object* v_inst_9_){
_start:
{
lean_inc_ref(v_inst_9_);
return v_inst_9_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object* v_inst_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_instToStringId___redArg(v_inst_10_);
lean_dec_ref(v_inst_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_instToStringId(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_){
_start:
{
lean_inc_ref(v_inst_13_);
return v_inst_13_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_instToStringId(v_00_u03b1_14_, v_inst_15_);
lean_dec_ref(v_inst_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg(lean_object* v_inst_17_){
_start:
{
lean_inc_ref(v_inst_17_);
return v_inst_17_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg___boxed(lean_object* v_inst_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_instToStringId__1___aux__1___redArg(v_inst_18_);
lean_dec_ref(v_inst_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_){
_start:
{
lean_inc_ref(v_inst_21_);
return v_inst_21_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_instToStringId__1___aux__1(v_00_u03b1_22_, v_inst_23_);
lean_dec_ref(v_inst_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object* v_inst_25_){
_start:
{
lean_inc_ref(v_inst_25_);
return v_inst_25_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object* v_inst_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_instToStringId__1___redArg(v_inst_26_);
lean_dec_ref(v_inst_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_){
_start:
{
lean_inc_ref(v_inst_29_);
return v_inst_29_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_instToStringId__1(v_00_u03b1_30_, v_inst_31_);
lean_dec_ref(v_inst_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object* v_s_33_){
_start:
{
lean_inc_ref(v_s_33_);
return v_s_33_;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object* v_s_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_instToStringString___lam__0(v_s_34_);
lean_dec_ref(v_s_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t v_c_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l_instToStringChar___lam__0___closed__0));
v___x_43_ = lean_string_push(v___x_42_, v_c_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object* v_c_44_){
_start:
{
uint32_t v_c_boxed_45_; lean_object* v_res_46_; 
v_c_boxed_45_ = lean_unbox_uint32(v_c_44_);
lean_dec(v_c_44_);
v_res_46_ = l_instToStringChar___lam__0(v_c_boxed_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t v_b_51_){
_start:
{
if (v_b_51_ == 0)
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_52_;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object* v_b_54_){
_start:
{
uint8_t v_b_boxed_55_; lean_object* v_res_56_; 
v_b_boxed_55_ = lean_unbox(v_b_54_);
v_res_56_ = l_instToStringBool___lam__0(v_b_boxed_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___lam__0(uint8_t v_h_59_){
_start:
{
if (v_h_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
v___x_61_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___lam__0___boxed(lean_object* v_h_62_){
_start:
{
uint8_t v_h_boxed_63_; lean_object* v_res_64_; 
v_h_boxed_63_ = lean_unbox(v_h_62_);
v_res_64_ = l_instToStringDecidable___redArg___lam__0(v_h_boxed_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg(){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = ((lean_object*)(l_instToStringDecidable___redArg___closed__0));
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___boxed(lean_object* v___dummy_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_instToStringDecidable___redArg();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object* v_p_70_){
_start:
{
lean_object* v___f_71_; 
v___f_71_ = ((lean_object*)(l_instToStringDecidable___redArg___closed__0));
return v___f_71_;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l_instToStringPUnit___lam__0___closed__0));
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object* v_inst_77_, lean_object* v_v_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_1(v_inst_77_, v_v_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object* v_inst_80_){
_start:
{
lean_object* v___f_81_; 
v___f_81_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_81_, 0, v_inst_80_);
return v___f_81_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_){
_start:
{
lean_object* v___f_84_; 
v___f_84_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_84_, 0, v_inst_83_);
return v___f_84_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___redArg(){
_start:
{
lean_object* v___f_89_; 
v___f_89_ = ((lean_object*)(l_instToStringNat___closed__0));
return v___f_89_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_instToStringFin___redArg();
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin(lean_object* v_n_92_){
_start:
{
lean_object* v___f_93_; 
v___f_93_ = ((lean_object*)(l_instToStringNat___closed__0));
return v___f_93_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object* v_n_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_instToStringFin(v_n_94_);
lean_dec(v_n_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t v_n_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_uint8_to_nat(v_n_96_);
v___x_98_ = l_Nat_reprFast(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object* v_n_99_){
_start:
{
uint8_t v_n_boxed_100_; lean_object* v_res_101_; 
v_n_boxed_100_ = lean_unbox(v_n_99_);
v_res_101_ = l_instToStringUInt8___lam__0(v_n_boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t v_n_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_uint16_to_nat(v_n_104_);
v___x_106_ = l_Nat_reprFast(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object* v_n_107_){
_start:
{
uint16_t v_n_boxed_108_; lean_object* v_res_109_; 
v_n_boxed_108_ = lean_unbox(v_n_107_);
v_res_109_ = l_instToStringUInt16___lam__0(v_n_boxed_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t v_n_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_uint32_to_nat(v_n_112_);
v___x_114_ = l_Nat_reprFast(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object* v_n_115_){
_start:
{
uint32_t v_n_boxed_116_; lean_object* v_res_117_; 
v_n_boxed_116_ = lean_unbox_uint32(v_n_115_);
lean_dec(v_n_115_);
v_res_117_ = l_instToStringUInt32___lam__0(v_n_boxed_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t v_n_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_uint64_to_nat(v_n_120_);
v___x_122_ = l_Nat_reprFast(v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object* v_n_123_){
_start:
{
uint64_t v_n_boxed_124_; lean_object* v_res_125_; 
v_n_boxed_124_ = lean_unbox_uint64(v_n_123_);
lean_dec_ref(v_n_123_);
v_res_125_ = l_instToStringUInt64___lam__0(v_n_boxed_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t v_n_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_usize_to_nat(v_n_128_);
v___x_130_ = l_Nat_reprFast(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object* v_n_131_){
_start:
{
size_t v_n_boxed_132_; lean_object* v_res_133_; 
v_n_boxed_132_ = lean_unbox_usize(v_n_131_);
lean_dec(v_n_131_);
v_res_133_ = l_instToStringUSize___lam__0(v_n_boxed_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object* v_f_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = l_Std_Format_defWidth;
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = l_Std_Format_pretty(v_f_136_, v___x_137_, v___x_138_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t v___y_142_){
_start:
{
uint32_t v___x_143_; uint8_t v___x_144_; 
v___x_143_ = 32;
v___x_144_ = lean_uint32_dec_eq(v___y_142_, v___x_143_);
if (v___x_144_ == 0)
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 9;
v___x_146_ = lean_uint32_dec_eq(v___y_142_, v___x_145_);
if (v___x_146_ == 0)
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 13;
v___x_148_ = lean_uint32_dec_eq(v___y_142_, v___x_147_);
if (v___x_148_ == 0)
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 10;
v___x_150_ = lean_uint32_dec_eq(v___y_142_, v___x_149_);
return v___x_150_;
}
else
{
return v___x_148_;
}
}
else
{
return v___x_146_;
}
}
else
{
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object* v___y_151_){
_start:
{
uint32_t v___y_201__boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v___y_201__boxed_152_ = lean_unbox_uint32(v___y_151_);
lean_dec(v___y_151_);
v_res_153_ = l_addParenHeuristic___lam__0(v___y_201__boxed_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object* v_s_161_){
_start:
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = ((lean_object*)(l_addParenHeuristic___closed__0));
lean_inc_ref(v_s_161_);
v___x_163_ = lean_string_isprefixof(v___x_162_, v_s_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_addParenHeuristic___closed__1));
lean_inc_ref(v_s_161_);
v___x_165_ = lean_string_isprefixof(v___x_164_, v_s_161_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_addParenHeuristic___closed__2));
lean_inc_ref(v_s_161_);
v___x_167_ = lean_string_isprefixof(v___x_166_, v_s_161_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_addParenHeuristic___closed__3));
lean_inc_ref(v_s_161_);
v___x_169_ = lean_string_isprefixof(v___x_168_, v_s_161_);
if (v___x_169_ == 0)
{
lean_object* v___f_170_; uint8_t v___x_171_; 
v___f_170_ = ((lean_object*)(l_addParenHeuristic___closed__4));
lean_inc_ref(v_s_161_);
v___x_171_ = lean_string_any(v_s_161_, v___f_170_);
if (v___x_171_ == 0)
{
return v_s_161_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_string_append(v___x_162_, v_s_161_);
lean_dec_ref(v_s_161_);
v___x_173_ = ((lean_object*)(l_addParenHeuristic___closed__5));
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
return v___x_174_;
}
}
else
{
return v_s_161_;
}
}
else
{
return v_s_161_;
}
}
else
{
return v_s_161_;
}
}
else
{
return v_s_161_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object* v_inst_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_179_; 
lean_dec_ref(v_inst_177_);
v___x_179_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__0));
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_val_180_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v_x_178_, 1);
v___x_181_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__1));
v___x_182_ = lean_apply_1(v_inst_177_, v_val_180_);
v___x_183_ = l_addParenHeuristic(v___x_182_);
v___x_184_ = lean_string_append(v___x_181_, v___x_183_);
lean_dec_ref(v___x_183_);
v___x_185_ = ((lean_object*)(l_addParenHeuristic___closed__5));
v___x_186_ = lean_string_append(v___x_184_, v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object* v_inst_187_){
_start:
{
lean_object* v___f_188_; 
v___f_188_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_188_, 0, v_inst_187_);
return v___f_188_;
}
}
LEAN_EXPORT lean_object* l_instToStringOption(lean_object* v_00_u03b1_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_191_, 0, v_inst_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_val_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref(v_inst_195_);
v_val_197_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v_x_196_, 1);
v___x_198_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__0));
v___x_199_ = lean_apply_1(v_inst_194_, v_val_197_);
v___x_200_ = l_addParenHeuristic(v___x_199_);
v___x_201_ = lean_string_append(v___x_198_, v___x_200_);
lean_dec_ref(v___x_200_);
v___x_202_ = ((lean_object*)(l_addParenHeuristic___closed__5));
v___x_203_ = lean_string_append(v___x_201_, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v_val_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v_inst_194_);
v_val_204_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v_x_196_, 1);
v___x_205_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__1));
v___x_206_ = lean_apply_1(v_inst_195_, v_val_204_);
v___x_207_ = l_addParenHeuristic(v___x_206_);
v___x_208_ = lean_string_append(v___x_205_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l_addParenHeuristic___closed__5));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object* v_inst_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_213_, 0, v_inst_211_);
lean_closure_set(v___f_213_, 1, v_inst_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_218_, 0, v_inst_216_);
lean_closure_set(v___f_218_, 1, v_inst_217_);
return v___f_218_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_fst_223_; lean_object* v_snd_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_fst_223_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_fst_223_);
v_snd_224_ = lean_ctor_get(v_x_222_, 1);
lean_inc(v_snd_224_);
lean_dec_ref(v_x_222_);
v___x_225_ = ((lean_object*)(l_addParenHeuristic___closed__0));
v___x_226_ = lean_apply_1(v_inst_220_, v_fst_223_);
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
v___x_230_ = lean_apply_1(v_inst_221_, v_snd_224_);
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_232_ = ((lean_object*)(l_addParenHeuristic___closed__5));
v___x_233_ = lean_string_append(v___x_231_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; 
v___f_236_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_236_, 0, v_inst_234_);
lean_closure_set(v___f_236_, 1, v_inst_235_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_inst_239_, lean_object* v_inst_240_){
_start:
{
lean_object* v___f_241_; 
v___f_241_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_241_, 0, v_inst_239_);
lean_closure_set(v___f_241_, 1, v_inst_240_);
return v___f_241_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_x_246_){
_start:
{
lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_fst_247_ = lean_ctor_get(v_x_246_, 0);
lean_inc_n(v_fst_247_, 2);
v_snd_248_ = lean_ctor_get(v_x_246_, 1);
lean_inc(v_snd_248_);
lean_dec_ref(v_x_246_);
v___x_249_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__0));
v___x_250_ = lean_apply_1(v_inst_244_, v_fst_247_);
v___x_251_ = lean_string_append(v___x_249_, v___x_250_);
lean_dec_ref(v___x_250_);
v___x_252_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_253_ = lean_string_append(v___x_251_, v___x_252_);
v___x_254_ = lean_apply_2(v_inst_245_, v_fst_247_, v_snd_248_);
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
lean_dec_ref(v___x_254_);
v___x_256_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__1));
v___x_257_ = lean_string_append(v___x_255_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object* v_inst_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_260_, 0, v_inst_258_);
lean_closure_set(v___f_260_, 1, v_inst_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_inst_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_265_, 0, v_inst_263_);
lean_closure_set(v___f_265_, 1, v_inst_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object* v_inst_266_, lean_object* v_s_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_apply_1(v_inst_266_, v_s_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object* v_inst_269_){
_start:
{
lean_object* v___f_270_; 
v___f_270_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_270_, 0, v_inst_269_);
return v___f_270_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object* v_00_u03b1_271_, lean_object* v_p_272_, lean_object* v_inst_273_){
_start:
{
lean_object* v___f_274_; 
v___f_274_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_274_, 0, v_inst_273_);
return v___f_274_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v_inst_278_);
v_a_280_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v_x_279_, 1);
v___x_281_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__0));
v___x_282_ = lean_apply_1(v_inst_277_, v_a_280_);
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
lean_dec_ref(v___x_282_);
return v___x_283_;
}
else
{
lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v_inst_277_);
v_a_284_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v_x_279_, 1);
v___x_285_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__1));
v___x_286_ = lean_apply_1(v_inst_278_, v_a_284_);
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
lean_dec_ref(v___x_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object* v_inst_288_, lean_object* v_inst_289_){
_start:
{
lean_object* v___f_290_; 
v___f_290_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_290_, 0, v_inst_288_);
lean_closure_set(v___f_290_, 1, v_inst_289_);
return v___f_290_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object* v_00_u03b5_291_, lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_inst_294_){
_start:
{
lean_object* v___f_295_; 
v___f_295_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_295_, 0, v_inst_293_);
lean_closure_set(v___f_295_, 1, v_inst_294_);
return v___f_295_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v_inst_303_);
v_a_306_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v_x_304_, 1);
v___x_307_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__1));
v___x_308_ = lean_unsigned_to_nat(1024u);
v___x_309_ = lean_apply_2(v_inst_302_, v_a_306_, v___x_308_);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_307_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = l_Repr_addAppParen(v___x_310_, v_x_305_);
return v___x_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec_ref(v_inst_302_);
v_a_312_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v_x_304_, 1);
v___x_313_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__3));
v___x_314_ = lean_unsigned_to_nat(1024u);
v___x_315_ = lean_apply_2(v_inst_303_, v_a_312_, v___x_314_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_313_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Repr_addAppParen(v___x_316_, v_x_305_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_instReprExcept___redArg___lam__0(v_inst_318_, v_inst_319_, v_x_320_, v_x_321_);
lean_dec(v_x_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object* v_inst_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v___f_325_; 
v___f_325_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_325_, 0, v_inst_323_);
lean_closure_set(v___f_325_, 1, v_inst_324_);
return v___f_325_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept(lean_object* v_00_u03b5_326_, lean_object* v_00_u03b1_327_, lean_object* v_inst_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v___f_330_; 
v___f_330_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_330_, 0, v_inst_328_);
lean_closure_set(v___f_330_, 1, v_inst_329_);
return v___f_330_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ToString_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
