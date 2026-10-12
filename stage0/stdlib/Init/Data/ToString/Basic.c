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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
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
static const lean_closure_object l_addParenHeuristic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_addParenHeuristic___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_addParenHeuristic___closed__0 = (const lean_object*)&l_addParenHeuristic___closed__0_value;
static const lean_string_object l_addParenHeuristic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_addParenHeuristic___closed__1 = (const lean_object*)&l_addParenHeuristic___closed__1_value;
static const lean_string_object l_addParenHeuristic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_addParenHeuristic___closed__2 = (const lean_object*)&l_addParenHeuristic___closed__2_value;
static const lean_string_object l_addParenHeuristic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_addParenHeuristic___closed__3 = (const lean_object*)&l_addParenHeuristic___closed__3_value;
static const lean_string_object l_addParenHeuristic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_addParenHeuristic___closed__4 = (const lean_object*)&l_addParenHeuristic___closed__4_value;
static const lean_string_object l_addParenHeuristic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
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
lean_object* l_instToStringChar___lam__0(uint32_t v_c_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l_instToStringChar___lam__0___closed__0));
v___x_43_ = lean_string_push(v___x_42_, v_c_41_);
return v___x_43_;
}
}
LEAN_EXPORT void l_instToStringChar___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_41_ = stack[0].m_num;
lean_object* v_res_44_;
v_res_44_ = l_instToStringChar___lam__0(v_c_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object* v_c_45_){
_start:
{
uint32_t v_c_boxed_46_; lean_object* v_res_47_; 
v_c_boxed_46_ = lean_unbox_uint32(v_c_45_);
lean_dec(v_c_45_);
v_res_47_ = l_instToStringChar___lam__0(v_c_boxed_46_);
return v_res_47_;
}
}
lean_object* l_instToStringBool___lam__0(uint8_t v_b_52_){
_start:
{
if (v_b_52_ == 0)
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_53_;
}
else
{
lean_object* v___x_54_; 
v___x_54_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_54_;
}
}
}
LEAN_EXPORT void l_instToStringBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_52_ = stack[0].m_num;
lean_object* v_res_55_;
v_res_55_ = l_instToStringBool___lam__0(v_b_52_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object* v_b_56_){
_start:
{
uint8_t v_b_boxed_57_; lean_object* v_res_58_; 
v_b_boxed_57_ = lean_unbox(v_b_56_);
v_res_58_ = l_instToStringBool___lam__0(v_b_boxed_57_);
return v_res_58_;
}
}
lean_object* l_instToStringDecidable___redArg___lam__0(uint8_t v_h_61_){
_start:
{
if (v_h_61_ == 0)
{
lean_object* v___x_62_; 
v___x_62_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_62_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_63_;
}
}
}
LEAN_EXPORT void l_instToStringDecidable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_h_61_ = stack[0].m_num;
lean_object* v_res_64_;
v_res_64_ = l_instToStringDecidable___redArg___lam__0(v_h_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___lam__0___boxed(lean_object* v_h_65_){
_start:
{
uint8_t v_h_boxed_66_; lean_object* v_res_67_; 
v_h_boxed_66_ = lean_unbox(v_h_65_);
v_res_67_ = l_instToStringDecidable___redArg___lam__0(v_h_boxed_66_);
return v_res_67_;
}
}
lean_object* l_instToStringDecidable___redArg(){
_start:
{
lean_object* v___f_70_; 
v___f_70_ = ((lean_object*)(l_instToStringDecidable___redArg___closed__0));
return v___f_70_;
}
}
LEAN_EXPORT void l_instToStringDecidable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_71_;
v_res_71_ = l_instToStringDecidable___redArg();
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_instToStringDecidable___redArg___boxed(lean_object* v___dummy_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_instToStringDecidable___redArg();
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object* v_p_74_){
_start:
{
lean_object* v___f_75_; 
v___f_75_ = ((lean_object*)(l_instToStringDecidable___redArg___closed__0));
return v___f_75_;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object* v_x_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = ((lean_object*)(l_instToStringPUnit___lam__0___closed__0));
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object* v_inst_81_, lean_object* v_v_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_apply_1(v_inst_81_, v_v_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object* v_inst_84_){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_85_, 0, v_inst_84_);
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift(lean_object* v_00_u03b1_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v___f_88_; 
v___f_88_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_88_, 0, v_inst_87_);
return v___f_88_;
}
}
lean_object* l_instToStringFin___redArg(){
_start:
{
lean_object* v___f_93_; 
v___f_93_ = ((lean_object*)(l_instToStringNat___closed__0));
return v___f_93_;
}
}
LEAN_EXPORT void l_instToStringFin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_94_;
v_res_94_ = l_instToStringFin___redArg();
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l_instToStringFin___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_instToStringFin___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin(lean_object* v_n_97_){
_start:
{
lean_object* v___f_98_; 
v___f_98_ = ((lean_object*)(l_instToStringNat___closed__0));
return v___f_98_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object* v_n_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_instToStringFin(v_n_99_);
lean_dec(v_n_99_);
return v_res_100_;
}
}
lean_object* l_instToStringUInt8___lam__0(uint8_t v_n_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_uint8_to_nat(v_n_101_);
v___x_103_ = l_Nat_reprFast(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l_instToStringUInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_101_ = stack[0].m_num;
lean_object* v_res_104_;
v_res_104_ = l_instToStringUInt8___lam__0(v_n_101_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object* v_n_105_){
_start:
{
uint8_t v_n_boxed_106_; lean_object* v_res_107_; 
v_n_boxed_106_ = lean_unbox(v_n_105_);
v_res_107_ = l_instToStringUInt8___lam__0(v_n_boxed_106_);
return v_res_107_;
}
}
lean_object* l_instToStringUInt16___lam__0(uint16_t v_n_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_uint16_to_nat(v_n_110_);
v___x_112_ = l_Nat_reprFast(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT void l_instToStringUInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_110_ = stack[0].m_num;
lean_object* v_res_113_;
v_res_113_ = l_instToStringUInt16___lam__0(v_n_110_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object* v_n_114_){
_start:
{
uint16_t v_n_boxed_115_; lean_object* v_res_116_; 
v_n_boxed_115_ = lean_unbox(v_n_114_);
v_res_116_ = l_instToStringUInt16___lam__0(v_n_boxed_115_);
return v_res_116_;
}
}
lean_object* l_instToStringUInt32___lam__0(uint32_t v_n_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_uint32_to_nat(v_n_119_);
v___x_121_ = l_Nat_reprFast(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l_instToStringUInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_119_ = stack[0].m_num;
lean_object* v_res_122_;
v_res_122_ = l_instToStringUInt32___lam__0(v_n_119_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object* v_n_123_){
_start:
{
uint32_t v_n_boxed_124_; lean_object* v_res_125_; 
v_n_boxed_124_ = lean_unbox_uint32(v_n_123_);
lean_dec(v_n_123_);
v_res_125_ = l_instToStringUInt32___lam__0(v_n_boxed_124_);
return v_res_125_;
}
}
lean_object* l_instToStringUInt64___lam__0(uint64_t v_n_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_uint64_to_nat(v_n_128_);
v___x_130_ = l_Nat_reprFast(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_instToStringUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_128_ = stack[0].m_num;
lean_object* v_res_131_;
v_res_131_ = l_instToStringUInt64___lam__0(v_n_128_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object* v_n_132_){
_start:
{
uint64_t v_n_boxed_133_; lean_object* v_res_134_; 
v_n_boxed_133_ = lean_unbox_uint64(v_n_132_);
lean_dec_ref(v_n_132_);
v_res_134_ = l_instToStringUInt64___lam__0(v_n_boxed_133_);
return v_res_134_;
}
}
lean_object* l_instToStringUSize___lam__0(size_t v_n_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_usize_to_nat(v_n_137_);
v___x_139_ = l_Nat_reprFast(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l_instToStringUSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_n_137_ = stack[0].m_num;
lean_object* v_res_140_;
v_res_140_ = l_instToStringUSize___lam__0(v_n_137_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object* v_n_141_){
_start:
{
size_t v_n_boxed_142_; lean_object* v_res_143_; 
v_n_boxed_142_ = lean_unbox_usize(v_n_141_);
lean_dec(v_n_141_);
v_res_143_ = l_instToStringUSize___lam__0(v_n_boxed_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object* v_f_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = l_Std_Format_defWidth;
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_Std_Format_pretty(v_f_146_, v___x_147_, v___x_148_, v___x_148_);
return v___x_149_;
}
}
uint8_t l_addParenHeuristic___lam__0(uint32_t v___y_152_){
_start:
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 32;
v___x_154_ = lean_uint32_dec_eq(v___y_152_, v___x_153_);
if (v___x_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 9;
v___x_156_ = lean_uint32_dec_eq(v___y_152_, v___x_155_);
if (v___x_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 13;
v___x_158_ = lean_uint32_dec_eq(v___y_152_, v___x_157_);
if (v___x_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 10;
v___x_160_ = lean_uint32_dec_eq(v___y_152_, v___x_159_);
return v___x_160_;
}
else
{
return v___x_158_;
}
}
else
{
return v___x_156_;
}
}
else
{
return v___x_154_;
}
}
}
LEAN_EXPORT void l_addParenHeuristic___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___y_152_ = stack[0].m_num;
uint8_t v_res_161_;
v_res_161_ = l_addParenHeuristic___lam__0(v___y_152_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object* v___y_162_){
_start:
{
uint32_t v___y_191__boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v___y_191__boxed_163_ = lean_unbox_uint32(v___y_162_);
lean_dec(v___y_162_);
v_res_164_ = l_addParenHeuristic___lam__0(v___y_191__boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object* v_s_172_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; uint8_t v___y_176_; uint8_t v___x_185_; 
v___f_173_ = ((lean_object*)(l_addParenHeuristic___closed__0));
v___x_174_ = ((lean_object*)(l_addParenHeuristic___closed__1));
lean_inc_ref(v_s_172_);
v___x_185_ = lean_string_isprefixof(v___x_174_, v_s_172_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_addParenHeuristic___closed__5));
lean_inc_ref(v_s_172_);
v___x_187_ = lean_string_isprefixof(v___x_186_, v_s_172_);
v___y_176_ = v___x_187_;
goto v___jp_175_;
}
else
{
v___y_176_ = v___x_185_;
goto v___jp_175_;
}
v___jp_175_:
{
if (v___y_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_addParenHeuristic___closed__2));
lean_inc_ref(v_s_172_);
v___x_178_ = lean_string_isprefixof(v___x_177_, v_s_172_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_addParenHeuristic___closed__3));
lean_inc_ref(v_s_172_);
v___x_180_ = lean_string_isprefixof(v___x_179_, v_s_172_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; 
lean_inc_ref(v_s_172_);
v___x_181_ = lean_string_any(v_s_172_, v___f_173_);
if (v___x_181_ == 0)
{
return v_s_172_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_string_append(v___x_174_, v_s_172_);
lean_dec_ref(v_s_172_);
v___x_183_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_184_ = lean_string_append(v___x_182_, v___x_183_);
return v___x_184_;
}
}
else
{
return v_s_172_;
}
}
else
{
return v_s_172_;
}
}
else
{
return v_s_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object* v_inst_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_192_; 
lean_dec_ref(v_inst_190_);
v___x_192_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__0));
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_val_193_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v_x_191_, 1);
v___x_194_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__1));
v___x_195_ = lean_apply_1(v_inst_190_, v_val_193_);
v___x_196_ = l_addParenHeuristic(v___x_195_);
v___x_197_ = lean_string_append(v___x_194_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_199_ = lean_string_append(v___x_197_, v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object* v_inst_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_201_, 0, v_inst_200_);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_instToStringOption(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___f_204_; 
v___f_204_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_204_, 0, v_inst_203_);
return v___f_204_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_val_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec_ref(v_inst_208_);
v_val_210_ = lean_ctor_get(v_x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v_x_209_, 1);
v___x_211_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__0));
v___x_212_ = lean_apply_1(v_inst_207_, v_val_210_);
v___x_213_ = l_addParenHeuristic(v___x_212_);
v___x_214_ = lean_string_append(v___x_211_, v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v_inst_207_);
v_val_217_ = lean_ctor_get(v_x_209_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v_x_209_, 1);
v___x_218_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__1));
v___x_219_ = lean_apply_1(v_inst_208_, v_val_217_);
v___x_220_ = l_addParenHeuristic(v___x_219_);
v___x_221_ = lean_string_append(v___x_218_, v___x_220_);
lean_dec_ref(v___x_220_);
v___x_222_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_223_ = lean_string_append(v___x_221_, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object* v_inst_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___f_226_; 
v___f_226_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_226_, 0, v_inst_224_);
lean_closure_set(v___f_226_, 1, v_inst_225_);
return v___f_226_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_231_, 0, v_inst_229_);
lean_closure_set(v___f_231_, 1, v_inst_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_fst_236_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_snd_237_);
lean_dec_ref(v_x_235_);
v___x_238_ = ((lean_object*)(l_addParenHeuristic___closed__1));
v___x_239_ = lean_apply_1(v_inst_233_, v_fst_236_);
v___x_240_ = lean_string_append(v___x_238_, v___x_239_);
lean_dec_ref(v___x_239_);
v___x_241_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
v___x_243_ = lean_apply_1(v_inst_234_, v_snd_237_);
v___x_244_ = lean_string_append(v___x_242_, v___x_243_);
lean_dec_ref(v___x_243_);
v___x_245_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object* v_inst_247_, lean_object* v_inst_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_249_, 0, v_inst_247_);
lean_closure_set(v___f_249_, 1, v_inst_248_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_inst_252_, lean_object* v_inst_253_){
_start:
{
lean_object* v___f_254_; 
v___f_254_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_254_, 0, v_inst_252_);
lean_closure_set(v___f_254_, 1, v_inst_253_);
return v___f_254_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_fst_260_ = lean_ctor_get(v_x_259_, 0);
lean_inc_n(v_fst_260_, 2);
v_snd_261_ = lean_ctor_get(v_x_259_, 1);
lean_inc(v_snd_261_);
lean_dec_ref(v_x_259_);
v___x_262_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__0));
v___x_263_ = lean_apply_1(v_inst_257_, v_fst_260_);
v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
lean_dec_ref(v___x_263_);
v___x_265_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
v___x_267_ = lean_apply_2(v_inst_258_, v_fst_260_, v_snd_261_);
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__1));
v___x_270_ = lean_string_append(v___x_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object* v_inst_271_, lean_object* v_inst_272_){
_start:
{
lean_object* v___f_273_; 
v___f_273_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_273_, 0, v_inst_271_);
lean_closure_set(v___f_273_, 1, v_inst_272_);
return v___f_273_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_inst_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_278_, 0, v_inst_276_);
lean_closure_set(v___f_278_, 1, v_inst_277_);
return v___f_278_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object* v_inst_279_, lean_object* v_s_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_apply_1(v_inst_279_, v_s_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object* v_inst_282_){
_start:
{
lean_object* v___f_283_; 
v___f_283_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_283_, 0, v_inst_282_);
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object* v_00_u03b1_284_, lean_object* v_p_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_287_, 0, v_inst_286_);
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_inst_291_);
v_a_293_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v_x_292_, 1);
v___x_294_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__0));
v___x_295_ = lean_apply_1(v_inst_290_, v_a_293_);
v___x_296_ = lean_string_append(v___x_294_, v___x_295_);
lean_dec_ref(v___x_295_);
return v___x_296_;
}
else
{
lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_inst_290_);
v_a_297_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v_x_292_, 1);
v___x_298_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__1));
v___x_299_ = lean_apply_1(v_inst_291_, v_a_297_);
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
lean_dec_ref(v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object* v_inst_301_, lean_object* v_inst_302_){
_start:
{
lean_object* v___f_303_; 
v___f_303_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_303_, 0, v_inst_301_);
lean_closure_set(v___f_303_, 1, v_inst_302_);
return v___f_303_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object* v_00_u03b5_304_, lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v___f_308_; 
v___f_308_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_308_, 0, v_inst_306_);
lean_closure_set(v___f_308_, 1, v_inst_307_);
return v___f_308_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v_inst_316_);
v_a_319_ = lean_ctor_get(v_x_317_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v_x_317_, 1);
v___x_320_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__1));
v___x_321_ = lean_unsigned_to_nat(1024u);
v___x_322_ = lean_apply_2(v_inst_315_, v_a_319_, v___x_321_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Repr_addAppParen(v___x_323_, v_x_318_);
return v___x_324_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_inst_315_);
v_a_325_ = lean_ctor_get(v_x_317_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v_x_317_, 1);
v___x_326_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__3));
v___x_327_ = lean_unsigned_to_nat(1024u);
v___x_328_ = lean_apply_2(v_inst_316_, v_a_325_, v___x_327_);
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_326_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Repr_addAppParen(v___x_329_, v_x_318_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_instReprExcept___redArg___lam__0(v_inst_331_, v_inst_332_, v_x_333_, v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object* v_inst_336_, lean_object* v_inst_337_){
_start:
{
lean_object* v___f_338_; 
v___f_338_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_338_, 0, v_inst_336_);
lean_closure_set(v___f_338_, 1, v_inst_337_);
return v___f_338_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept(lean_object* v_00_u03b5_339_, lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v___f_343_; 
v___f_343_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_343_, 0, v_inst_341_);
lean_closure_set(v___f_343_, 1, v_inst_342_);
return v___f_343_;
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
