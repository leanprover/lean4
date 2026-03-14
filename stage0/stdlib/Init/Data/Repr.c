// Lean compiler output
// Module: Init.Data.Repr
// Imports: public import Init.Data.Format.Basic public import Init.Control.Id public import Init.Data.UInt.BasicAux import Init.Data.Char.Basic
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
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t lean_string_isempty(lean_object*);
lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprStr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprStr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reprArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprEmpty___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprEmpty___closed__0 = (const lean_object*)&l_instReprEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprEmpty = (const lean_object*)&l_instReprEmpty___closed__0_value;
static const lean_string_object l_Bool_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Bool_repr___redArg___closed__0 = (const lean_object*)&l_Bool_repr___redArg___closed__0_value;
static const lean_ctor_object l_Bool_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Bool_repr___redArg___closed__0_value)}};
static const lean_object* l_Bool_repr___redArg___closed__1 = (const lean_object*)&l_Bool_repr___redArg___closed__1_value;
static const lean_string_object l_Bool_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Bool_repr___redArg___closed__2 = (const lean_object*)&l_Bool_repr___redArg___closed__2_value;
static const lean_ctor_object l_Bool_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Bool_repr___redArg___closed__2_value)}};
static const lean_object* l_Bool_repr___redArg___closed__3 = (const lean_object*)&l_Bool_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Bool_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprBool___closed__0 = (const lean_object*)&l_instReprBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprBool = (const lean_object*)&l_instReprBool___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Repr_addAppParen_spec__0(lean_object*);
static const lean_string_object l_Repr_addAppParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Repr_addAppParen___closed__0 = (const lean_object*)&l_Repr_addAppParen___closed__0_value;
static const lean_string_object l_Repr_addAppParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Repr_addAppParen___closed__1 = (const lean_object*)&l_Repr_addAppParen___closed__1_value;
static lean_once_cell_t l_Repr_addAppParen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Repr_addAppParen___closed__2;
static lean_once_cell_t l_Repr_addAppParen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Repr_addAppParen___closed__3;
static const lean_ctor_object l_Repr_addAppParen___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Repr_addAppParen___closed__0_value)}};
static const lean_object* l_Repr_addAppParen___closed__4 = (const lean_object*)&l_Repr_addAppParen___closed__4_value;
static const lean_ctor_object l_Repr_addAppParen___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Repr_addAppParen___closed__1_value)}};
static const lean_object* l_Repr_addAppParen___closed__5 = (const lean_object*)&l_Repr_addAppParen___closed__5_value;
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object*, lean_object*);
static const lean_string_object l_Decidable_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isFalse _"};
static const lean_object* l_Decidable_repr___redArg___closed__0 = (const lean_object*)&l_Decidable_repr___redArg___closed__0_value;
static const lean_ctor_object l_Decidable_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Decidable_repr___redArg___closed__0_value)}};
static const lean_object* l_Decidable_repr___redArg___closed__1 = (const lean_object*)&l_Decidable_repr___redArg___closed__1_value;
static const lean_string_object l_Decidable_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isTrue _"};
static const lean_object* l_Decidable_repr___redArg___closed__2 = (const lean_object*)&l_Decidable_repr___redArg___closed__2_value;
static const lean_ctor_object l_Decidable_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Decidable_repr___redArg___closed__2_value)}};
static const lean_object* l_Decidable_repr___redArg___closed__3 = (const lean_object*)&l_Decidable_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Decidable_repr___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_repr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instReprDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Decidable_repr___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instReprDecidable___closed__0 = (const lean_object*)&l_instReprDecidable___closed__0_value;
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object*);
static const lean_string_object l_instReprPUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PUnit.unit"};
static const lean_object* l_instReprPUnit___lam__0___closed__0 = (const lean_object*)&l_instReprPUnit___lam__0___closed__0_value;
static const lean_ctor_object l_instReprPUnit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprPUnit___lam__0___closed__0_value)}};
static const lean_object* l_instReprPUnit___lam__0___closed__1 = (const lean_object*)&l_instReprPUnit___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprPUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprPUnit___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprPUnit___closed__0 = (const lean_object*)&l_instReprPUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprPUnit = (const lean_object*)&l_instReprPUnit___closed__0_value;
static const lean_string_object l_instReprULift___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ULift.up "};
static const lean_object* l_instReprULift___redArg___lam__0___closed__0 = (const lean_object*)&l_instReprULift___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_instReprULift___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprULift___redArg___lam__0___closed__0_value)}};
static const lean_object* l_instReprULift___redArg___lam__0___closed__1 = (const lean_object*)&l_instReprULift___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprULift(lean_object*, lean_object*);
static const lean_string_object l_instReprUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "()"};
static const lean_object* l_instReprUnit___lam__0___closed__0 = (const lean_object*)&l_instReprUnit___lam__0___closed__0_value;
static const lean_ctor_object l_instReprUnit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprUnit___lam__0___closed__0_value)}};
static const lean_object* l_instReprUnit___lam__0___closed__1 = (const lean_object*)&l_instReprUnit___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUnit___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUnit___closed__0 = (const lean_object*)&l_instReprUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUnit = (const lean_object*)&l_instReprUnit___closed__0_value;
static const lean_string_object l_Option_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___redArg___closed__0 = (const lean_object*)&l_Option_repr___redArg___closed__0_value;
static const lean_ctor_object l_Option_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___redArg___closed__0_value)}};
static const lean_object* l_Option_repr___redArg___closed__1 = (const lean_object*)&l_Option_repr___redArg___closed__1_value;
static const lean_string_object l_Option_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___redArg___closed__2 = (const lean_object*)&l_Option_repr___redArg___closed__2_value;
static const lean_ctor_object l_Option_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___redArg___closed__2_value)}};
static const lean_object* l_Option_repr___redArg___closed__3 = (const lean_object*)&l_Option_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprOption(lean_object*, lean_object*);
static const lean_string_object l_Sum_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Sum.inl "};
static const lean_object* l_Sum_repr___redArg___closed__0 = (const lean_object*)&l_Sum_repr___redArg___closed__0_value;
static const lean_ctor_object l_Sum_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sum_repr___redArg___closed__0_value)}};
static const lean_object* l_Sum_repr___redArg___closed__1 = (const lean_object*)&l_Sum_repr___redArg___closed__1_value;
static const lean_string_object l_Sum_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Sum.inr "};
static const lean_object* l_Sum_repr___redArg___closed__2 = (const lean_object*)&l_Sum_repr___redArg___closed__2_value;
static const lean_ctor_object l_Sum_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sum_repr___redArg___closed__2_value)}};
static const lean_object* l_Sum_repr___redArg___closed__3 = (const lean_object*)&l_Sum_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Prod_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToFormatFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Prod_repr___redArg___closed__0 = (const lean_object*)&l_Prod_repr___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Prod_repr___redArg___closed__1 = (const lean_object*)&l_Prod_repr___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___redArg___closed__2 = (const lean_object*)&l_Prod_repr___redArg___closed__2_value;
static const lean_ctor_object l_Prod_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Prod_repr___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___redArg___closed__3 = (const lean_object*)&l_Prod_repr___redArg___closed__3_value;
static lean_once_cell_t l_Prod_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Sigma_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Sigma_repr___redArg___closed__0 = (const lean_object*)&l_Sigma_repr___redArg___closed__0_value;
static const lean_string_object l_Sigma_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Sigma_repr___redArg___closed__1 = (const lean_object*)&l_Sigma_repr___redArg___closed__1_value;
static const lean_ctor_object l_Sigma_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sigma_repr___redArg___closed__1_value)}};
static const lean_object* l_Sigma_repr___redArg___closed__2 = (const lean_object*)&l_Sigma_repr___redArg___closed__2_value;
static const lean_string_object l_Sigma_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Sigma_repr___redArg___closed__3 = (const lean_object*)&l_Sigma_repr___redArg___closed__3_value;
static lean_once_cell_t l_Sigma_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Sigma_repr___redArg___closed__4;
static lean_once_cell_t l_Sigma_repr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Sigma_repr___redArg___closed__5;
static const lean_ctor_object l_Sigma_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sigma_repr___redArg___closed__0_value)}};
static const lean_object* l_Sigma_repr___redArg___closed__6 = (const lean_object*)&l_Sigma_repr___redArg___closed__6_value;
static const lean_ctor_object l_Sigma_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Sigma_repr___redArg___closed__3_value)}};
static const lean_object* l_Sigma_repr___redArg___closed__7 = (const lean_object*)&l_Sigma_repr___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSigma(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object*, lean_object*);
lean_object* lean_string_of_usize(size_t);
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__0;
static lean_once_cell_t l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__1;
static lean_once_cell_t l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Nat_reprArray;
static lean_once_cell_t l_Nat_reprFast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reprFast___closed__0;
static lean_once_cell_t l_Nat_reprFast___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reprFast___closed__1;
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT uint32_t l_Nat_superDigitChar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object*);
LEAN_EXPORT uint32_t l_Nat_subDigitChar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object*);
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprNat___closed__0 = (const lean_object*)&l_instReprNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprNat = (const lean_object*)&l_instReprNat___closed__0_value;
static lean_once_cell_t l_Int_repr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_repr___closed__0;
static const lean_string_object l_Int_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Int_repr___closed__1 = (const lean_object*)&l_Int_repr___closed__1_value;
LEAN_EXPORT lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Int_repr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt___closed__0 = (const lean_object*)&l_instReprInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt = (const lean_object*)&l_instReprInt___closed__0_value;
static const lean_string_object l_hexDigitRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_hexDigitRepr___closed__0 = (const lean_object*)&l_hexDigitRepr___closed__0_value;
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object*);
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(lean_object*);
static const lean_string_object l_Char_quoteCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\x"};
static const lean_object* l_Char_quoteCore___closed__0 = (const lean_object*)&l_Char_quoteCore___closed__0_value;
static const lean_string_object l_Char_quoteCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\'"};
static const lean_object* l_Char_quoteCore___closed__1 = (const lean_object*)&l_Char_quoteCore___closed__1_value;
static const lean_string_object l_Char_quoteCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\""};
static const lean_object* l_Char_quoteCore___closed__2 = (const lean_object*)&l_Char_quoteCore___closed__2_value;
static const lean_string_object l_Char_quoteCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\\"};
static const lean_object* l_Char_quoteCore___closed__3 = (const lean_object*)&l_Char_quoteCore___closed__3_value;
static const lean_string_object l_Char_quoteCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\t"};
static const lean_object* l_Char_quoteCore___closed__4 = (const lean_object*)&l_Char_quoteCore___closed__4_value;
static const lean_string_object l_Char_quoteCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\n"};
static const lean_object* l_Char_quoteCore___closed__5 = (const lean_object*)&l_Char_quoteCore___closed__5_value;
LEAN_EXPORT lean_object* l_Char_quoteCore(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object*, lean_object*);
static const lean_string_object l_Char_quote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Char_quote___closed__0 = (const lean_object*)&l_Char_quote___closed__0_value;
LEAN_EXPORT lean_object* l_Char_quote(uint32_t);
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprChar___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprChar___closed__0 = (const lean_object*)&l_instReprChar___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprChar = (const lean_object*)&l_instReprChar___closed__0_value;
LEAN_EXPORT lean_object* l_Char_repr(uint32_t);
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_quote___lam__0(uint8_t, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_quote___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_quote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_quote___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_String_quote___closed__0 = (const lean_object*)&l_String_quote___closed__0_value;
static const lean_string_object l_String_quote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_String_quote___closed__1 = (const lean_object*)&l_String_quote___closed__1_value;
static const lean_string_object l_String_quote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\"\""};
static const lean_object* l_String_quote___closed__2 = (const lean_object*)&l_String_quote___closed__2_value;
LEAN_EXPORT lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprString___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprString___closed__0 = (const lean_object*)&l_instReprString___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprString = (const lean_object*)&l_instReprString___closed__0_value;
static const lean_string_object l_instReprRaw___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ byteIdx := "};
static const lean_object* l_instReprRaw___lam__0___closed__0 = (const lean_object*)&l_instReprRaw___lam__0___closed__0_value;
static const lean_ctor_object l_instReprRaw___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprRaw___lam__0___closed__0_value)}};
static const lean_object* l_instReprRaw___lam__0___closed__1 = (const lean_object*)&l_instReprRaw___lam__0___closed__1_value;
static const lean_string_object l_instReprRaw___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_instReprRaw___lam__0___closed__2 = (const lean_object*)&l_instReprRaw___lam__0___closed__2_value;
static const lean_ctor_object l_instReprRaw___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprRaw___lam__0___closed__2_value)}};
static const lean_object* l_instReprRaw___lam__0___closed__3 = (const lean_object*)&l_instReprRaw___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_instReprRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprRaw___closed__0 = (const lean_object*)&l_instReprRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprRaw = (const lean_object*)&l_instReprRaw___closed__0_value;
static const lean_string_object l_instReprRaw__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ".toRawSubstring"};
static const lean_object* l_instReprRaw__1___lam__0___closed__0 = (const lean_object*)&l_instReprRaw__1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprRaw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprRaw__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprRaw__1___closed__0 = (const lean_object*)&l_instReprRaw__1___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprRaw__1 = (const lean_object*)&l_instReprRaw__1___closed__0_value;
LEAN_EXPORT lean_object* l_instReprFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprFin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprFin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprFin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprFin___closed__0 = (const lean_object*)&l_instReprFin___closed__0_value;
LEAN_EXPORT lean_object* l_instReprFin(lean_object*);
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUInt8___closed__0 = (const lean_object*)&l_instReprUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUInt8 = (const lean_object*)&l_instReprUInt8___closed__0_value;
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUInt16___closed__0 = (const lean_object*)&l_instReprUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUInt16 = (const lean_object*)&l_instReprUInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUInt32___closed__0 = (const lean_object*)&l_instReprUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUInt32 = (const lean_object*)&l_instReprUInt32___closed__0_value;
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUInt64___closed__0 = (const lean_object*)&l_instReprUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUInt64 = (const lean_object*)&l_instReprUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instReprUSize___lam__0(size_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUSize___closed__0 = (const lean_object*)&l_instReprUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUSize = (const lean_object*)&l_instReprUSize___closed__0_value;
static const lean_string_object l_List_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___redArg___closed__0 = (const lean_object*)&l_List_repr___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___redArg___closed__0_value)}};
static const lean_object* l_List_repr___redArg___closed__1 = (const lean_object*)&l_List_repr___redArg___closed__1_value;
static const lean_string_object l_List_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___redArg___closed__2 = (const lean_object*)&l_List_repr___redArg___closed__2_value;
static const lean_string_object l_List_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___redArg___closed__3 = (const lean_object*)&l_List_repr___redArg___closed__3_value;
static lean_once_cell_t l_List_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___redArg___closed__4;
static lean_once_cell_t l_List_repr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___redArg___closed__5;
static const lean_ctor_object l_List_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___redArg___closed__2_value)}};
static const lean_object* l_List_repr___redArg___closed__6 = (const lean_object*)&l_List_repr___redArg___closed__6_value;
static const lean_ctor_object l_List_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___redArg___closed__3_value)}};
static const lean_object* l_List_repr___redArg___closed__7 = (const lean_object*)&l_List_repr___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprAtomBool;
LEAN_EXPORT lean_object* l_instReprAtomNat;
LEAN_EXPORT lean_object* l_instReprAtomInt;
LEAN_EXPORT lean_object* l_instReprAtomChar;
LEAN_EXPORT lean_object* l_instReprAtomString;
LEAN_EXPORT lean_object* l_instReprAtomUInt8;
LEAN_EXPORT lean_object* l_instReprAtomUInt16;
LEAN_EXPORT lean_object* l_instReprAtomUInt32;
LEAN_EXPORT lean_object* l_instReprAtomUInt64;
LEAN_EXPORT lean_object* l_instReprAtomUSize;
static const lean_string_object l_instReprSourceInfo_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.SourceInfo.none"};
static const lean_object* l_instReprSourceInfo_repr___closed__0 = (const lean_object*)&l_instReprSourceInfo_repr___closed__0_value;
static const lean_ctor_object l_instReprSourceInfo_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprSourceInfo_repr___closed__0_value)}};
static const lean_object* l_instReprSourceInfo_repr___closed__1 = (const lean_object*)&l_instReprSourceInfo_repr___closed__1_value;
static const lean_string_object l_instReprSourceInfo_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.SourceInfo.original"};
static const lean_object* l_instReprSourceInfo_repr___closed__2 = (const lean_object*)&l_instReprSourceInfo_repr___closed__2_value;
static const lean_ctor_object l_instReprSourceInfo_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprSourceInfo_repr___closed__2_value)}};
static const lean_object* l_instReprSourceInfo_repr___closed__3 = (const lean_object*)&l_instReprSourceInfo_repr___closed__3_value;
static const lean_ctor_object l_instReprSourceInfo_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_instReprSourceInfo_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_instReprSourceInfo_repr___closed__4 = (const lean_object*)&l_instReprSourceInfo_repr___closed__4_value;
static lean_once_cell_t l_instReprSourceInfo_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprSourceInfo_repr___closed__5;
static lean_once_cell_t l_instReprSourceInfo_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprSourceInfo_repr___closed__6;
static const lean_string_object l_instReprSourceInfo_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.SourceInfo.synthetic"};
static const lean_object* l_instReprSourceInfo_repr___closed__7 = (const lean_object*)&l_instReprSourceInfo_repr___closed__7_value;
static const lean_ctor_object l_instReprSourceInfo_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprSourceInfo_repr___closed__7_value)}};
static const lean_object* l_instReprSourceInfo_repr___closed__8 = (const lean_object*)&l_instReprSourceInfo_repr___closed__8_value;
static const lean_ctor_object l_instReprSourceInfo_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_instReprSourceInfo_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_instReprSourceInfo_repr___closed__9 = (const lean_object*)&l_instReprSourceInfo_repr___closed__9_value;
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprSourceInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprSourceInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprSourceInfo___closed__0 = (const lean_object*)&l_instReprSourceInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprSourceInfo = (const lean_object*)&l_instReprSourceInfo___closed__0_value;
LEAN_EXPORT lean_object* l_repr___redArg(lean_object* v_inst_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_apply_2(v_inst_1_, v_a_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_repr(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_apply_2(v_inst_6_, v_a_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_reprStr___redArg(lean_object* v_inst_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_apply_2(v_inst_10_, v_a_11_, v___x_12_);
v___x_14_ = l_Std_Format_defWidth;
v___x_15_ = l_Std_Format_pretty(v___x_13_, v___x_14_, v___x_12_, v___x_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_reprStr(lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_apply_2(v_inst_17_, v_a_18_, v___x_19_);
v___x_21_ = l_Std_Format_defWidth;
v___x_22_ = l_Std_Format_pretty(v___x_20_, v___x_21_, v___x_19_, v___x_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_reprArg___redArg(lean_object* v_inst_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(1024u);
v___x_26_ = lean_apply_2(v_inst_23_, v_a_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_reprArg(lean_object* v_00_u03b1_27_, lean_object* v_inst_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(1024u);
v___x_31_ = lean_apply_2(v_inst_28_, v_a_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object* v_inst_32_){
_start:
{
lean_inc_ref(v_inst_32_);
return v_inst_32_;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object* v_inst_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_instReprId___redArg(v_inst_33_);
lean_dec_ref(v_inst_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_instReprId(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_){
_start:
{
lean_inc_ref(v_inst_36_);
return v_inst_36_;
}
}
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_instReprId(v_00_u03b1_37_, v_inst_38_);
lean_dec_ref(v_inst_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg(lean_object* v_inst_40_){
_start:
{
lean_inc_ref(v_inst_40_);
return v_inst_40_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg___boxed(lean_object* v_inst_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_instReprId__1___redArg(v_inst_41_);
lean_dec_ref(v_inst_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_){
_start:
{
lean_inc_ref(v_inst_44_);
return v_inst_44_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___boxed(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_instReprId__1(v_00_u03b1_45_, v_inst_46_);
lean_dec_ref(v_inst_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0(uint8_t v_a_48_, lean_object* v_a_49_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
uint8_t v_a_8__boxed_52_; lean_object* v_res_53_; 
v_a_8__boxed_52_ = lean_unbox(v_a_50_);
v_res_53_ = l_instReprEmpty___lam__0(v_a_8__boxed_52_, v_a_51_);
lean_dec(v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg(uint8_t v_x_62_){
_start:
{
if (v_x_62_ == 0)
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_Bool_repr___redArg___closed__1));
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_Bool_repr___redArg___closed__3));
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object* v_x_65_){
_start:
{
uint8_t v_x_36__boxed_66_; lean_object* v_res_67_; 
v_x_36__boxed_66_ = lean_unbox(v_x_65_);
v_res_67_ = l_Bool_repr___redArg(v_x_36__boxed_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Bool_repr(uint8_t v_x_68_, lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Bool_repr___redArg(v_x_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_x_49__boxed_73_; lean_object* v_res_74_; 
v_x_49__boxed_73_ = lean_unbox(v_x_71_);
v_res_74_ = l_Bool_repr(v_x_49__boxed_73_, v_x_72_);
lean_dec(v_x_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Repr_addAppParen_spec__0(lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_nat_to_int(v_a_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__2(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Repr_addAppParen___closed__0));
v___x_82_ = lean_string_length(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__3(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object* v_f_89_, lean_object* v_prec_90_){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1024u);
v___x_92_ = lean_nat_dec_le(v___x_91_, v_prec_90_);
if (v___x_92_ == 0)
{
return v_f_89_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; 
v___x_93_ = lean_obj_once(&l_Repr_addAppParen___closed__3, &l_Repr_addAppParen___closed__3_once, _init_l_Repr_addAppParen___closed__3);
v___x_94_ = ((lean_object*)(l_Repr_addAppParen___closed__4));
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_f_89_);
v___x_96_ = ((lean_object*)(l_Repr_addAppParen___closed__5));
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_93_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object* v_f_101_, lean_object* v_prec_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Repr_addAppParen(v_f_101_, v_prec_102_);
lean_dec(v_prec_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg(uint8_t v_x_110_, lean_object* v_x_111_){
_start:
{
if (v_x_110_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l_Decidable_repr___redArg___closed__1));
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_x_111_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l_Decidable_repr___redArg___closed__3));
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_x_111_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_x_42__boxed_118_; lean_object* v_res_119_; 
v_x_42__boxed_118_ = lean_unbox(v_x_116_);
v_res_119_ = l_Decidable_repr___redArg(v_x_42__boxed_118_, v_x_117_);
lean_dec(v_x_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr(lean_object* v_p_120_, uint8_t v_x_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Decidable_repr___redArg(v_x_121_, v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object* v_p_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_x_62__boxed_127_; lean_object* v_res_128_; 
v_x_62__boxed_127_ = lean_unbox(v_x_125_);
v_res_128_ = l_Decidable_repr(v_p_124_, v_x_62__boxed_127_, v_x_126_);
lean_dec(v_x_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object* v_p_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_instReprDecidable___closed__0));
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = ((lean_object*)(l_instReprPUnit___lam__0___closed__1));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_instReprPUnit___lam__0(v_x_138_, v_x_139_);
lean_dec(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object* v_inst_146_, lean_object* v_v_147_, lean_object* v_prec_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_149_ = ((lean_object*)(l_instReprULift___redArg___lam__0___closed__1));
v___x_150_ = lean_unsigned_to_nat(1024u);
v___x_151_ = lean_apply_2(v_inst_146_, v_v_147_, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_149_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Repr_addAppParen(v___x_152_, v_prec_148_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object* v_inst_154_, lean_object* v_v_155_, lean_object* v_prec_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_instReprULift___redArg___lam__0(v_inst_154_, v_v_155_, v_prec_156_);
lean_dec(v_prec_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_159_, 0, v_inst_158_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_instReprULift(lean_object* v_00_u03b1_160_, lean_object* v_inst_161_){
_start:
{
lean_object* v___f_162_; 
v___f_162_ = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_162_, 0, v_inst_161_);
return v___f_162_;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_instReprUnit___lam__0___closed__1));
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_instReprUnit___lam__0(v_x_169_, v_x_170_);
lean_dec(v_x_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object* v_inst_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_183_; 
lean_dec_ref(v_inst_180_);
v___x_183_ = ((lean_object*)(l_Option_repr___redArg___closed__1));
return v___x_183_;
}
else
{
lean_object* v_val_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_val_184_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_val_184_);
lean_dec_ref(v_x_181_);
v___x_185_ = ((lean_object*)(l_Option_repr___redArg___closed__3));
v___x_186_ = lean_unsigned_to_nat(1024u);
v___x_187_ = lean_apply_2(v_inst_180_, v_val_184_, v___x_186_);
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_185_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Repr_addAppParen(v___x_188_, v_x_182_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object* v_inst_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Option_repr___redArg(v_inst_190_, v_x_191_, v_x_192_);
lean_dec(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Option_repr(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Option_repr___redArg(v_inst_195_, v_x_196_, v_x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Option_repr(v_00_u03b1_199_, v_inst_200_, v_x_201_, v_x_202_);
lean_dec(v_x_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object* v_inst_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(v___x_205_, 0, lean_box(0));
lean_closure_set(v___x_205_, 1, v_inst_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_instReprOption(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(v___x_208_, 0, lean_box(0));
lean_closure_set(v___x_208_, 1, v_inst_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v_val_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec_ref(v_inst_216_);
v_val_219_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v_x_217_);
v___x_220_ = ((lean_object*)(l_Sum_repr___redArg___closed__1));
v___x_221_ = lean_unsigned_to_nat(1024u);
v___x_222_ = lean_apply_2(v_inst_215_, v_val_219_, v___x_221_);
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_220_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Repr_addAppParen(v___x_223_, v_x_218_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec_ref(v_inst_215_);
v_val_225_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v_x_217_);
v___x_226_ = ((lean_object*)(l_Sum_repr___redArg___closed__3));
v___x_227_ = lean_unsigned_to_nat(1024u);
v___x_228_ = lean_apply_2(v_inst_216_, v_val_225_, v___x_227_);
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_226_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l_Repr_addAppParen(v___x_229_, v_x_218_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Sum_repr___redArg(v_inst_231_, v_inst_232_, v_x_233_, v_x_234_);
lean_dec(v_x_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Sum_repr___redArg(v_inst_238_, v_inst_239_, v_x_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Sum_repr(v_00_u03b1_243_, v_00_u03b2_244_, v_inst_245_, v_inst_246_, v_x_247_, v_x_248_);
lean_dec(v_x_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object* v_inst_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(v___x_252_, 0, lean_box(0));
lean_closure_set(v___x_252_, 1, lean_box(0));
lean_closure_set(v___x_252_, 2, v_inst_250_);
lean_closure_set(v___x_252_, 3, v_inst_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_instReprSum(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_inst_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(v___x_257_, 0, lean_box(0));
lean_closure_set(v___x_257_, 1, lean_box(0));
lean_closure_set(v___x_257_, 2, v_inst_255_);
lean_closure_set(v___x_257_, 3, v_inst_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object* v_inst_258_, lean_object* v_a_259_, lean_object* v_xs_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_apply_2(v_inst_258_, v_a_259_, v___x_261_);
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_xs_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_265_, 0, v_inst_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object* v_00_u03b1_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___f_268_; 
v___f_268_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_268_, 0, v_inst_267_);
return v___f_268_;
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_284_; 
v_fst_273_ = lean_ctor_get(v_x_271_, 0);
v_snd_274_ = lean_ctor_get(v_x_271_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_284_ == 0)
{
v___x_276_ = v_x_271_;
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snd_274_);
lean_inc(v_fst_273_);
lean_dec(v_x_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_284_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_apply_2(v_inst_269_, v_fst_273_, v___x_278_);
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 1);
lean_ctor_set(v___x_276_, 1, v_x_272_);
lean_ctor_set(v___x_276_, 0, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_x_272_);
v___x_281_ = v_reuseFailAlloc_283_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; 
v___x_282_ = lean_apply_2(v_inst_270_, v_snd_274_, v___x_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Prod_reprTuple___redArg(v_inst_287_, v_inst_288_, v_x_289_, v_x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object* v_inst_292_, lean_object* v_inst_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(v___x_294_, 0, lean_box(0));
lean_closure_set(v___x_294_, 1, lean_box(0));
lean_closure_set(v___x_294_, 2, v_inst_292_);
lean_closure_set(v___x_294_, 3, v_inst_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_inst_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(v___x_299_, 0, lean_box(0));
lean_closure_set(v___x_299_, 1, lean_box(0));
lean_closure_set(v___x_299_, 2, v_inst_297_);
lean_closure_set(v___x_299_, 3, v_inst_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
v___x_308_ = lean_nat_to_int(v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_fst_312_; lean_object* v_snd_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_336_; 
v_fst_312_ = lean_ctor_get(v_x_311_, 0);
v_snd_313_ = lean_ctor_get(v_x_311_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_336_ == 0)
{
v___x_315_ = v_x_311_;
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snd_313_);
lean_inc(v_fst_312_);
lean_dec(v_x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___f_317_ = ((lean_object*)(l_Prod_repr___redArg___closed__0));
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_apply_2(v_inst_309_, v_fst_312_, v___x_318_);
v___x_320_ = lean_box(0);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 1, v___x_320_);
lean_ctor_set(v___x_315_, 0, v___x_319_);
v___x_322_ = v___x_315_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_335_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v___x_323_ = lean_apply_2(v_inst_310_, v_snd_313_, v___x_322_);
v___x_324_ = l_List_reverse___redArg(v___x_323_);
v___x_325_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_326_ = l_Std_Format_joinSep___redArg(v___f_317_, v___x_324_, v___x_325_);
v___x_327_ = lean_obj_once(&l_Prod_repr___redArg___closed__4, &l_Prod_repr___redArg___closed__4_once, _init_l_Prod_repr___redArg___closed__4);
v___x_328_ = ((lean_object*)(l_Repr_addAppParen___closed__4));
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_326_);
v___x_330_ = ((lean_object*)(l_Repr_addAppParen___closed__5));
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_327_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Prod_repr___redArg(v_inst_339_, v_inst_340_, v_x_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Prod_repr(v_00_u03b1_344_, v_00_u03b2_345_, v_inst_346_, v_inst_347_, v_x_348_, v_x_349_);
lean_dec(v_x_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object* v_inst_351_, lean_object* v_inst_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_353_, 0, lean_box(0));
lean_closure_set(v___x_353_, 1, lean_box(0));
lean_closure_set(v___x_353_, 2, v_inst_351_);
lean_closure_set(v___x_353_, 3, v_inst_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_358_, 0, lean_box(0));
lean_closure_set(v___x_358_, 1, lean_box(0));
lean_closure_set(v___x_358_, 2, v_inst_356_);
lean_closure_set(v___x_358_, 3, v_inst_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Sigma_repr___redArg___closed__0));
v___x_365_ = lean_string_length(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l_Sigma_repr___redArg___closed__4, &l_Sigma_repr___redArg___closed__4_once, _init_l_Sigma_repr___redArg___closed__4);
v___x_367_ = lean_nat_to_int(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_fst_375_; lean_object* v_snd_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_396_; 
v_fst_375_ = lean_ctor_get(v_x_374_, 0);
v_snd_376_ = lean_ctor_get(v_x_374_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_396_ == 0)
{
v___x_378_ = v_x_374_;
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snd_376_);
lean_inc(v_fst_375_);
lean_dec(v_x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_380_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_375_);
v___x_381_ = lean_apply_2(v_inst_372_, v_fst_375_, v___x_380_);
v___x_382_ = ((lean_object*)(l_Sigma_repr___redArg___closed__2));
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 5);
lean_ctor_set(v___x_378_, 1, v___x_382_);
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_384_ = v___x_378_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_395_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; 
v___x_385_ = lean_apply_3(v_inst_373_, v_fst_375_, v_snd_376_, v___x_380_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Sigma_repr___redArg___closed__5, &l_Sigma_repr___redArg___closed__5_once, _init_l_Sigma_repr___redArg___closed__5);
v___x_388_ = ((lean_object*)(l_Sigma_repr___redArg___closed__6));
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_386_);
v___x_390_ = ((lean_object*)(l_Sigma_repr___redArg___closed__7));
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_387_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = 0;
v___x_394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*1, v___x_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Sigma_repr___redArg(v_inst_399_, v_inst_400_, v_x_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Sigma_repr(v_00_u03b1_404_, v_00_u03b2_405_, v_inst_406_, v_inst_407_, v_x_408_, v_x_409_);
lean_dec(v_x_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object* v_inst_411_, lean_object* v_inst_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_413_, 0, lean_box(0));
lean_closure_set(v___x_413_, 1, lean_box(0));
lean_closure_set(v___x_413_, 2, v_inst_411_);
lean_closure_set(v___x_413_, 3, v_inst_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_instReprSigma(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_inst_416_, lean_object* v_inst_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_418_, 0, lean_box(0));
lean_closure_set(v___x_418_, 1, lean_box(0));
lean_closure_set(v___x_418_, 2, v_inst_416_);
lean_closure_set(v___x_418_, 3, v_inst_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object* v_inst_419_, lean_object* v_s_420_, lean_object* v_prec_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_apply_2(v_inst_419_, v_s_420_, v_prec_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object* v_inst_423_){
_start:
{
lean_object* v___f_424_; 
v___f_424_ = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(v___f_424_, 0, v_inst_423_);
return v___f_424_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object* v_00_u03b1_425_, lean_object* v_p_426_, lean_object* v_inst_427_){
_start:
{
lean_object* v___f_428_; 
v___f_428_ = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(v___f_428_, 0, v_inst_427_);
return v___f_428_;
}
}
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object* v_n_429_){
_start:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_nat_dec_eq(v_n_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_dec_eq(v_n_429_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(2u);
v___x_435_ = lean_nat_dec_eq(v_n_429_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(3u);
v___x_437_ = lean_nat_dec_eq(v_n_429_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(4u);
v___x_439_ = lean_nat_dec_eq(v_n_429_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(5u);
v___x_441_ = lean_nat_dec_eq(v_n_429_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(6u);
v___x_443_ = lean_nat_dec_eq(v_n_429_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(7u);
v___x_445_ = lean_nat_dec_eq(v_n_429_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(8u);
v___x_447_ = lean_nat_dec_eq(v_n_429_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(9u);
v___x_449_ = lean_nat_dec_eq(v_n_429_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(10u);
v___x_451_ = lean_nat_dec_eq(v_n_429_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(11u);
v___x_453_ = lean_nat_dec_eq(v_n_429_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(12u);
v___x_455_ = lean_nat_dec_eq(v_n_429_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(13u);
v___x_457_ = lean_nat_dec_eq(v_n_429_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(14u);
v___x_459_ = lean_nat_dec_eq(v_n_429_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(15u);
v___x_461_ = lean_nat_dec_eq(v_n_429_, v___x_460_);
if (v___x_461_ == 0)
{
uint32_t v___x_462_; 
v___x_462_ = 42;
return v___x_462_;
}
else
{
uint32_t v___x_463_; 
v___x_463_ = 102;
return v___x_463_;
}
}
else
{
uint32_t v___x_464_; 
v___x_464_ = 101;
return v___x_464_;
}
}
else
{
uint32_t v___x_465_; 
v___x_465_ = 100;
return v___x_465_;
}
}
else
{
uint32_t v___x_466_; 
v___x_466_ = 99;
return v___x_466_;
}
}
else
{
uint32_t v___x_467_; 
v___x_467_ = 98;
return v___x_467_;
}
}
else
{
uint32_t v___x_468_; 
v___x_468_ = 97;
return v___x_468_;
}
}
else
{
uint32_t v___x_469_; 
v___x_469_ = 57;
return v___x_469_;
}
}
else
{
uint32_t v___x_470_; 
v___x_470_ = 56;
return v___x_470_;
}
}
else
{
uint32_t v___x_471_; 
v___x_471_ = 55;
return v___x_471_;
}
}
else
{
uint32_t v___x_472_; 
v___x_472_ = 54;
return v___x_472_;
}
}
else
{
uint32_t v___x_473_; 
v___x_473_ = 53;
return v___x_473_;
}
}
else
{
uint32_t v___x_474_; 
v___x_474_ = 52;
return v___x_474_;
}
}
else
{
uint32_t v___x_475_; 
v___x_475_ = 51;
return v___x_475_;
}
}
else
{
uint32_t v___x_476_; 
v___x_476_ = 50;
return v___x_476_;
}
}
else
{
uint32_t v___x_477_; 
v___x_477_ = 49;
return v___x_477_;
}
}
else
{
uint32_t v___x_478_; 
v___x_478_ = 48;
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object* v_n_479_){
_start:
{
uint32_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Nat_digitChar(v_n_479_);
lean_dec(v_n_479_);
v_r_481_ = lean_box_uint32(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object* v_base_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_zero_486_; uint8_t v_isZero_487_; 
v_zero_486_ = lean_unsigned_to_nat(0u);
v_isZero_487_ = lean_nat_dec_eq(v_x_483_, v_zero_486_);
if (v_isZero_487_ == 1)
{
lean_dec(v_x_484_);
lean_dec(v_x_483_);
return v_x_485_;
}
else
{
lean_object* v___x_488_; uint32_t v_d_489_; lean_object* v_n_x27_490_; uint8_t v___x_491_; 
v___x_488_ = lean_nat_mod(v_x_484_, v_base_482_);
v_d_489_ = l_Nat_digitChar(v___x_488_);
lean_dec(v___x_488_);
v_n_x27_490_ = lean_nat_div(v_x_484_, v_base_482_);
lean_dec(v_x_484_);
v___x_491_ = lean_nat_dec_eq(v_n_x27_490_, v_zero_486_);
if (v___x_491_ == 0)
{
lean_object* v_one_492_; lean_object* v_n_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_one_492_ = lean_unsigned_to_nat(1u);
v_n_493_ = lean_nat_sub(v_x_483_, v_one_492_);
lean_dec(v_x_483_);
v___x_494_ = lean_box_uint32(v_d_489_);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_x_485_);
v_x_483_ = v_n_493_;
v_x_484_ = v_n_x27_490_;
v_x_485_ = v___x_495_;
goto _start;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_n_x27_490_);
lean_dec(v_x_483_);
v___x_497_ = lean_box_uint32(v_d_489_);
v___x_498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_x_485_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object* v_base_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Nat_toDigitsCore(v_base_499_, v_x_500_, v_x_501_, v_x_502_);
lean_dec(v_base_499_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object* v_base_504_, lean_object* v_n_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_n_505_, v___x_506_);
v___x_508_ = lean_box(0);
v___x_509_ = l_Nat_toDigitsCore(v_base_504_, v___x_507_, v_n_505_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object* v_base_510_, lean_object* v_n_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Nat_toDigits(v_base_510_, v_n_511_);
lean_dec(v_base_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object* v_n_514_){
_start:
{
size_t v_n_boxed_515_; lean_object* v_res_516_; 
v_n_boxed_515_ = lean_unbox_usize(v_n_514_);
lean_dec(v_n_514_);
v_res_516_ = lean_string_of_usize(v_n_boxed_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
if (lean_obj_tag(v_a_517_) == 0)
{
lean_object* v___x_519_; 
v___x_519_ = l_List_reverse___redArg(v_a_518_);
return v___x_519_;
}
else
{
lean_object* v_head_520_; lean_object* v_tail_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_531_; 
v_head_520_ = lean_ctor_get(v_a_517_, 0);
v_tail_521_ = lean_ctor_get(v_a_517_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_a_517_);
if (v_isSharedCheck_531_ == 0)
{
v___x_523_ = v_a_517_;
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_tail_521_);
lean_inc(v_head_520_);
lean_dec(v_a_517_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
size_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_525_ = lean_usize_of_nat(v_head_520_);
lean_dec(v_head_520_);
v___x_526_ = lean_string_of_usize(v___x_525_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_a_518_);
lean_ctor_set(v___x_523_, 0, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_518_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_517_ = v_tail_521_;
v_a_518_ = v___x_528_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(128u);
v___x_533_ = l_List_range(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_box(0);
v___x_535_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__0, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0);
v___x_536_ = l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(v___x_535_, v___x_534_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__1, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1);
v___x_538_ = lean_array_mk(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__2, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2);
return v___x_539_;
}
}
static lean_object* _init_l_Nat_reprFast___closed__0(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = l___private_Init_Data_Repr_0__Nat_reprArray;
v___x_541_ = lean_array_get_size(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Nat_reprFast___closed__1(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = l_System_Platform_numBits;
v___x_543_ = lean_unsigned_to_nat(2u);
v___x_544_ = lean_nat_pow(v___x_543_, v___x_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object* v_n_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = l___private_Init_Data_Repr_0__Nat_reprArray;
v___x_547_ = lean_obj_once(&l_Nat_reprFast___closed__0, &l_Nat_reprFast___closed__0_once, _init_l_Nat_reprFast___closed__0);
v___x_548_ = lean_nat_dec_lt(v_n_545_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_obj_once(&l_Nat_reprFast___closed__1, &l_Nat_reprFast___closed__1_once, _init_l_Nat_reprFast___closed__1);
v___x_550_ = lean_nat_dec_lt(v_n_545_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_unsigned_to_nat(10u);
v___x_552_ = l_Nat_toDigits(v___x_551_, v_n_545_);
v___x_553_ = lean_string_mk(v___x_552_);
return v___x_553_;
}
else
{
size_t v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_usize_of_nat(v_n_545_);
lean_dec(v_n_545_);
v___x_555_ = lean_string_of_usize(v___x_554_);
return v___x_555_;
}
}
else
{
lean_object* v___x_556_; 
v___x_556_ = lean_array_fget(v___x_546_, v_n_545_);
lean_dec(v_n_545_);
return v___x_556_;
}
}
}
LEAN_EXPORT uint32_t l_Nat_superDigitChar(lean_object* v_n_557_){
_start:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_nat_dec_eq(v_n_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_dec_eq(v_n_557_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(2u);
v___x_563_ = lean_nat_dec_eq(v_n_557_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_dec_eq(v_n_557_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = lean_nat_dec_eq(v_n_557_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(5u);
v___x_569_ = lean_nat_dec_eq(v_n_557_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(6u);
v___x_571_ = lean_nat_dec_eq(v_n_557_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(7u);
v___x_573_ = lean_nat_dec_eq(v_n_557_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(8u);
v___x_575_ = lean_nat_dec_eq(v_n_557_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(9u);
v___x_577_ = lean_nat_dec_eq(v_n_557_, v___x_576_);
if (v___x_577_ == 0)
{
uint32_t v___x_578_; 
v___x_578_ = 42;
return v___x_578_;
}
else
{
uint32_t v___x_579_; 
v___x_579_ = 8313;
return v___x_579_;
}
}
else
{
uint32_t v___x_580_; 
v___x_580_ = 8312;
return v___x_580_;
}
}
else
{
uint32_t v___x_581_; 
v___x_581_ = 8311;
return v___x_581_;
}
}
else
{
uint32_t v___x_582_; 
v___x_582_ = 8310;
return v___x_582_;
}
}
else
{
uint32_t v___x_583_; 
v___x_583_ = 8309;
return v___x_583_;
}
}
else
{
uint32_t v___x_584_; 
v___x_584_ = 8308;
return v___x_584_;
}
}
else
{
uint32_t v___x_585_; 
v___x_585_ = 179;
return v___x_585_;
}
}
else
{
uint32_t v___x_586_; 
v___x_586_ = 178;
return v___x_586_;
}
}
else
{
uint32_t v___x_587_; 
v___x_587_ = 185;
return v___x_587_;
}
}
else
{
uint32_t v___x_588_; 
v___x_588_ = 8304;
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object* v_n_589_){
_start:
{
uint32_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_Nat_superDigitChar(v_n_589_);
lean_dec(v_n_589_);
v_r_591_ = lean_box_uint32(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; uint32_t v_d_596_; lean_object* v_n_x27_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_594_ = lean_unsigned_to_nat(10u);
v___x_595_ = lean_nat_mod(v_x_592_, v___x_594_);
v_d_596_ = l_Nat_superDigitChar(v___x_595_);
lean_dec(v___x_595_);
v_n_x27_597_ = lean_nat_div(v_x_592_, v___x_594_);
lean_dec(v_x_592_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_dec_eq(v_n_x27_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_box_uint32(v_d_596_);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_x_593_);
v_x_592_ = v_n_x27_597_;
v_x_593_ = v___x_601_;
goto _start;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_n_x27_597_);
v___x_603_ = lean_box_uint32(v_d_596_);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_x_593_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object* v_n_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = l_Nat_toSuperDigitsAux(v_n_605_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object* v_n_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = l_Nat_toSuperDigits(v_n_608_);
v___x_610_ = lean_string_mk(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT uint32_t l_Nat_subDigitChar(lean_object* v_n_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_eq(v_n_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_dec_eq(v_n_611_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(2u);
v___x_617_ = lean_nat_dec_eq(v_n_611_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(3u);
v___x_619_ = lean_nat_dec_eq(v_n_611_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(4u);
v___x_621_ = lean_nat_dec_eq(v_n_611_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(5u);
v___x_623_ = lean_nat_dec_eq(v_n_611_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(6u);
v___x_625_ = lean_nat_dec_eq(v_n_611_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(7u);
v___x_627_ = lean_nat_dec_eq(v_n_611_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(8u);
v___x_629_ = lean_nat_dec_eq(v_n_611_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(9u);
v___x_631_ = lean_nat_dec_eq(v_n_611_, v___x_630_);
if (v___x_631_ == 0)
{
uint32_t v___x_632_; 
v___x_632_ = 42;
return v___x_632_;
}
else
{
uint32_t v___x_633_; 
v___x_633_ = 8329;
return v___x_633_;
}
}
else
{
uint32_t v___x_634_; 
v___x_634_ = 8328;
return v___x_634_;
}
}
else
{
uint32_t v___x_635_; 
v___x_635_ = 8327;
return v___x_635_;
}
}
else
{
uint32_t v___x_636_; 
v___x_636_ = 8326;
return v___x_636_;
}
}
else
{
uint32_t v___x_637_; 
v___x_637_ = 8325;
return v___x_637_;
}
}
else
{
uint32_t v___x_638_; 
v___x_638_ = 8324;
return v___x_638_;
}
}
else
{
uint32_t v___x_639_; 
v___x_639_ = 8323;
return v___x_639_;
}
}
else
{
uint32_t v___x_640_; 
v___x_640_ = 8322;
return v___x_640_;
}
}
else
{
uint32_t v___x_641_; 
v___x_641_ = 8321;
return v___x_641_;
}
}
else
{
uint32_t v___x_642_; 
v___x_642_ = 8320;
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object* v_n_643_){
_start:
{
uint32_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Nat_subDigitChar(v_n_643_);
lean_dec(v_n_643_);
v_r_645_ = lean_box_uint32(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; uint32_t v_d_650_; lean_object* v_n_x27_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_648_ = lean_unsigned_to_nat(10u);
v___x_649_ = lean_nat_mod(v_x_646_, v___x_648_);
v_d_650_ = l_Nat_subDigitChar(v___x_649_);
lean_dec(v___x_649_);
v_n_x27_651_ = lean_nat_div(v_x_646_, v___x_648_);
lean_dec(v_x_646_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_nat_dec_eq(v_n_x27_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box_uint32(v_d_650_);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_x_647_);
v_x_646_ = v_n_x27_651_;
v_x_647_ = v___x_655_;
goto _start;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v_n_x27_651_);
v___x_657_ = lean_box_uint32(v_d_650_);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v_x_647_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object* v_n_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = l_Nat_toSubDigitsAux(v_n_659_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object* v_n_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = l_Nat_toSubDigits(v_n_662_);
v___x_664_ = lean_string_mk(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object* v_n_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = l_Nat_reprFast(v_n_665_);
v___x_668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object* v_n_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_instReprNat___lam__0(v_n_669_, v_x_670_);
lean_dec(v_x_670_);
return v_res_671_;
}
}
static lean_object* _init_l_Int_repr___closed__0(void){
_start:
{
lean_object* v_natZero_674_; lean_object* v_intZero_675_; 
v_natZero_674_ = lean_unsigned_to_nat(0u);
v_intZero_675_ = lean_nat_to_int(v_natZero_674_);
return v_intZero_675_;
}
}
LEAN_EXPORT lean_object* l_Int_repr(lean_object* v_x_677_){
_start:
{
lean_object* v_intZero_678_; uint8_t v_isNeg_679_; 
v_intZero_678_ = lean_obj_once(&l_Int_repr___closed__0, &l_Int_repr___closed__0_once, _init_l_Int_repr___closed__0);
v_isNeg_679_ = lean_int_dec_lt(v_x_677_, v_intZero_678_);
if (v_isNeg_679_ == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_nat_abs(v_x_677_);
v___x_681_ = l_Nat_reprFast(v_a_680_);
return v___x_681_;
}
else
{
lean_object* v_abs_682_; lean_object* v_one_683_; lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_abs_682_ = lean_nat_abs(v_x_677_);
v_one_683_ = lean_unsigned_to_nat(1u);
v_a_684_ = lean_nat_sub(v_abs_682_, v_one_683_);
lean_dec(v_abs_682_);
v___x_685_ = ((lean_object*)(l_Int_repr___closed__1));
v___x_686_ = lean_nat_add(v_a_684_, v_one_683_);
lean_dec(v_a_684_);
v___x_687_ = l_Nat_reprFast(v___x_686_);
v___x_688_ = lean_string_append(v___x_685_, v___x_687_);
lean_dec_ref(v___x_687_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Int_repr___boxed(lean_object* v_x_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Int_repr(v_x_689_);
lean_dec(v_x_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_instReprInt___lam__0(lean_object* v_i_691_, lean_object* v_prec_692_){
_start:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_obj_once(&l_Int_repr___closed__0, &l_Int_repr___closed__0_once, _init_l_Int_repr___closed__0);
v___x_694_ = lean_int_dec_lt(v_i_691_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = l_Int_repr(v_i_691_);
v___x_696_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = l_Int_repr(v_i_691_);
v___x_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
v___x_699_ = l_Repr_addAppParen(v___x_698_, v_prec_692_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt___lam__0___boxed(lean_object* v_i_700_, lean_object* v_prec_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_instReprInt___lam__0(v_i_700_, v_prec_701_);
lean_dec(v_prec_701_);
lean_dec(v_i_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object* v_n_706_){
_start:
{
uint32_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = l_Nat_digitChar(v_n_706_);
v___x_708_ = ((lean_object*)(l_hexDigitRepr___closed__0));
v___x_709_ = lean_string_push(v___x_708_, v___x_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object* v_n_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_hexDigitRepr(v_n_710_);
lean_dec(v_n_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t v_c_712_){
_start:
{
lean_object* v_n_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_d2_716_; lean_object* v_d1_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_n_713_ = lean_uint32_to_nat(v_c_712_);
v___x_714_ = lean_unsigned_to_nat(16u);
v___x_715_ = lean_unsigned_to_nat(4u);
v_d2_716_ = lean_nat_shiftr(v_n_713_, v___x_715_);
v_d1_717_ = lean_nat_mod(v_n_713_, v___x_714_);
lean_dec(v_n_713_);
v___x_718_ = l_hexDigitRepr(v_d2_716_);
lean_dec(v_d2_716_);
v___x_719_ = l_hexDigitRepr(v_d1_717_);
lean_dec(v_d1_717_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(lean_object* v_c_721_){
_start:
{
uint32_t v_c_boxed_722_; lean_object* v_res_723_; 
v_c_boxed_722_ = lean_unbox_uint32(v_c_721_);
lean_dec(v_c_721_);
v_res_723_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_boxed_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore(uint32_t v_c_730_, uint8_t v_inString_731_){
_start:
{
uint32_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = 10;
v___x_745_ = lean_uint32_dec_eq(v_c_730_, v___x_744_);
if (v___x_745_ == 0)
{
uint32_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 9;
v___x_747_ = lean_uint32_dec_eq(v_c_730_, v___x_746_);
if (v___x_747_ == 0)
{
uint32_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 92;
v___x_749_ = lean_uint32_dec_eq(v_c_730_, v___x_748_);
if (v___x_749_ == 0)
{
uint32_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = 34;
v___x_751_ = lean_uint32_dec_eq(v_c_730_, v___x_750_);
if (v___x_751_ == 0)
{
if (v_inString_731_ == 0)
{
uint32_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 39;
v___x_753_ = lean_uint32_dec_eq(v_c_730_, v___x_752_);
if (v___x_753_ == 0)
{
goto v___jp_736_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Char_quoteCore___closed__1));
return v___x_754_;
}
}
else
{
goto v___jp_736_;
}
}
else
{
lean_object* v___x_755_; 
v___x_755_ = ((lean_object*)(l_Char_quoteCore___closed__2));
return v___x_755_;
}
}
else
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l_Char_quoteCore___closed__3));
return v___x_756_;
}
}
else
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Char_quoteCore___closed__4));
return v___x_757_;
}
}
else
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l_Char_quoteCore___closed__5));
return v___x_758_;
}
v___jp_732_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = ((lean_object*)(l_Char_quoteCore___closed__0));
v___x_734_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_730_);
v___x_735_ = lean_string_append(v___x_733_, v___x_734_);
lean_dec_ref(v___x_734_);
return v___x_735_;
}
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_uint32_to_nat(v_c_730_);
v___x_738_ = lean_unsigned_to_nat(31u);
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_738_);
lean_dec(v___x_737_);
if (v___x_739_ == 0)
{
uint32_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = 127;
v___x_741_ = lean_uint32_dec_eq(v_c_730_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_hexDigitRepr___closed__0));
v___x_743_ = lean_string_push(v___x_742_, v_c_730_);
return v___x_743_;
}
else
{
goto v___jp_732_;
}
}
else
{
goto v___jp_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object* v_c_759_, lean_object* v_inString_760_){
_start:
{
uint32_t v_c_boxed_761_; uint8_t v_inString_boxed_762_; lean_object* v_res_763_; 
v_c_boxed_761_ = lean_unbox_uint32(v_c_759_);
lean_dec(v_c_759_);
v_inString_boxed_762_ = lean_unbox(v_inString_760_);
v_res_763_ = l_Char_quoteCore(v_c_boxed_761_, v_inString_boxed_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Char_quote(uint32_t v_c_765_){
_start:
{
lean_object* v___x_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_766_ = ((lean_object*)(l_Char_quote___closed__0));
v___x_767_ = 0;
v___x_768_ = l_Char_quoteCore(v_c_765_, v___x_767_);
v___x_769_ = lean_string_append(v___x_766_, v___x_768_);
lean_dec_ref(v___x_768_);
v___x_770_ = lean_string_append(v___x_769_, v___x_766_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object* v_c_771_){
_start:
{
uint32_t v_c_boxed_772_; lean_object* v_res_773_; 
v_c_boxed_772_ = lean_unbox_uint32(v_c_771_);
lean_dec(v_c_771_);
v_res_773_ = l_Char_quote(v_c_boxed_772_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0(uint32_t v_c_774_, lean_object* v_x_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Char_quote(v_c_774_);
v___x_777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object* v_c_778_, lean_object* v_x_779_){
_start:
{
uint32_t v_c_boxed_780_; lean_object* v_res_781_; 
v_c_boxed_780_ = lean_unbox_uint32(v_c_778_);
lean_dec(v_c_778_);
v_res_781_ = l_instReprChar___lam__0(v_c_boxed_780_, v_x_779_);
lean_dec(v_x_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Char_repr(uint32_t v_c_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Char_quote(v_c_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object* v_c_786_){
_start:
{
uint32_t v_c_boxed_787_; lean_object* v_res_788_; 
v_c_boxed_787_ = lean_unbox_uint32(v_c_786_);
lean_dec(v_c_786_);
v_res_788_ = l_Char_repr(v_c_boxed_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_String_quote___lam__0(uint8_t v___x_789_, lean_object* v_s_790_, uint32_t v_c_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_Char_quoteCore(v_c_791_, v___x_789_);
v___x_793_ = lean_string_append(v_s_790_, v___x_792_);
lean_dec_ref(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_String_quote___lam__0___boxed(lean_object* v___x_794_, lean_object* v_s_795_, lean_object* v_c_796_){
_start:
{
uint8_t v___x_43__boxed_797_; uint32_t v_c_boxed_798_; lean_object* v_res_799_; 
v___x_43__boxed_797_ = lean_unbox(v___x_794_);
v_c_boxed_798_ = lean_unbox_uint32(v_c_796_);
lean_dec(v_c_796_);
v_res_799_ = l_String_quote___lam__0(v___x_43__boxed_797_, v_s_795_, v_c_boxed_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_String_quote(lean_object* v_s_805_){
_start:
{
uint8_t v___x_806_; 
lean_inc_ref(v_s_805_);
v___x_806_ = lean_string_isempty(v_s_805_);
if (v___x_806_ == 0)
{
lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___f_807_ = ((lean_object*)(l_String_quote___closed__0));
v___x_808_ = ((lean_object*)(l_String_quote___closed__1));
v___x_809_ = lean_string_foldl(v___f_807_, v___x_808_, v_s_805_);
v___x_810_ = lean_string_append(v___x_809_, v___x_808_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; 
lean_dec_ref(v_s_805_);
v___x_811_ = ((lean_object*)(l_String_quote___closed__2));
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object* v_s_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = l_String_quote(v_s_812_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object* v_s_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_instReprString___lam__0(v_s_816_, v_x_817_);
lean_dec(v_x_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0(lean_object* v_p_827_, lean_object* v_x_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_829_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_830_ = l_Nat_reprFast(v_p_827_);
v___x_831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_829_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0___boxed(lean_object* v_p_835_, lean_object* v_x_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_instReprRaw___lam__0(v_p_835_, v_x_836_);
lean_dec(v_x_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0(lean_object* v_s_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = lean_substring_tostring(v_s_841_);
v___x_844_ = l_String_quote(v___x_843_);
v___x_845_ = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
v___x_846_ = lean_string_append(v___x_844_, v___x_845_);
v___x_847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0___boxed(lean_object* v_s_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_instReprRaw__1___lam__0(v_s_848_, v_x_849_);
lean_dec(v_x_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0(lean_object* v_f_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = l_Nat_reprFast(v_f_853_);
v___x_856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0___boxed(lean_object* v_f_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_instReprFin___lam__0(v_f_857_, v_x_858_);
lean_dec(v_x_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_instReprFin(lean_object* v_n_861_){
_start:
{
lean_object* v___f_862_; 
v___f_862_ = ((lean_object*)(l_instReprFin___closed__0));
return v___f_862_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object* v_n_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_instReprFin(v_n_863_);
lean_dec(v_n_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t v_n_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_uint8_to_nat(v_n_865_);
v___x_868_ = l_Nat_reprFast(v___x_867_);
v___x_869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object* v_n_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_n_boxed_872_; lean_object* v_res_873_; 
v_n_boxed_872_ = lean_unbox(v_n_870_);
v_res_873_ = l_instReprUInt8___lam__0(v_n_boxed_872_, v_x_871_);
lean_dec(v_x_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0(uint16_t v_n_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = lean_uint16_to_nat(v_n_876_);
v___x_879_ = l_Nat_reprFast(v___x_878_);
v___x_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object* v_n_881_, lean_object* v_x_882_){
_start:
{
uint16_t v_n_boxed_883_; lean_object* v_res_884_; 
v_n_boxed_883_ = lean_unbox(v_n_881_);
v_res_884_ = l_instReprUInt16___lam__0(v_n_boxed_883_, v_x_882_);
lean_dec(v_x_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0(uint32_t v_n_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_uint32_to_nat(v_n_887_);
v___x_890_ = l_Nat_reprFast(v___x_889_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object* v_n_892_, lean_object* v_x_893_){
_start:
{
uint32_t v_n_boxed_894_; lean_object* v_res_895_; 
v_n_boxed_894_ = lean_unbox_uint32(v_n_892_);
lean_dec(v_n_892_);
v_res_895_ = l_instReprUInt32___lam__0(v_n_boxed_894_, v_x_893_);
lean_dec(v_x_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t v_n_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_uint64_to_nat(v_n_898_);
v___x_901_ = l_Nat_reprFast(v___x_900_);
v___x_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object* v_n_903_, lean_object* v_x_904_){
_start:
{
uint64_t v_n_boxed_905_; lean_object* v_res_906_; 
v_n_boxed_905_ = lean_unbox_uint64(v_n_903_);
lean_dec_ref(v_n_903_);
v_res_906_ = l_instReprUInt64___lam__0(v_n_boxed_905_, v_x_904_);
lean_dec(v_x_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0(size_t v_n_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_usize_to_nat(v_n_909_);
v___x_912_ = l_Nat_reprFast(v___x_911_);
v___x_913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object* v_n_914_, lean_object* v_x_915_){
_start:
{
size_t v_n_boxed_916_; lean_object* v_res_917_; 
v_n_boxed_916_ = lean_unbox_usize(v_n_914_);
lean_dec(v_n_914_);
v_res_917_ = l_instReprUSize___lam__0(v_n_boxed_916_, v_x_915_);
lean_dec(v_x_915_);
return v_res_917_;
}
}
static lean_object* _init_l_List_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_List_repr___redArg___closed__2));
v___x_926_ = lean_string_length(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_List_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l_List_repr___redArg___closed__4, &l_List_repr___redArg___closed__4_once, _init_l_List_repr___redArg___closed__4);
v___x_928_ = lean_nat_to_int(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object* v_inst_933_, lean_object* v_a_934_){
_start:
{
if (lean_obj_tag(v_a_934_) == 0)
{
lean_object* v___x_935_; 
lean_dec_ref(v_inst_933_);
v___x_935_ = ((lean_object*)(l_List_repr___redArg___closed__1));
return v___x_935_;
}
else
{
lean_object* v_x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; 
v_x_936_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_936_, 0, lean_box(0));
lean_closure_set(v_x_936_, 1, v_inst_933_);
v___x_937_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_938_ = l_Std_Format_joinSep___redArg(v_x_936_, v_a_934_, v___x_937_);
v___x_939_ = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
v___x_940_ = ((lean_object*)(l_List_repr___redArg___closed__6));
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_938_);
v___x_942_ = ((lean_object*)(l_List_repr___redArg___closed__7));
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = 0;
v___x_946_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*1, v___x_945_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_List_repr(lean_object* v_00_u03b1_947_, lean_object* v_inst_948_, lean_object* v_a_949_, lean_object* v_n_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_List_repr___redArg(v_inst_948_, v_a_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object* v_00_u03b1_952_, lean_object* v_inst_953_, lean_object* v_a_954_, lean_object* v_n_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_List_repr(v_00_u03b1_952_, v_inst_953_, v_a_954_, v_n_955_);
lean_dec(v_n_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object* v_inst_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(v___x_958_, 0, lean_box(0));
lean_closure_set(v___x_958_, 1, v_inst_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_instReprList(lean_object* v_00_u03b1_959_, lean_object* v_inst_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(v___x_961_, 0, lean_box(0));
lean_closure_set(v___x_961_, 1, v_inst_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object* v_inst_962_, lean_object* v_a_963_){
_start:
{
if (lean_obj_tag(v_a_963_) == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v_inst_962_);
v___x_964_ = ((lean_object*)(l_List_repr___redArg___closed__1));
return v___x_964_;
}
else
{
lean_object* v_x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_x_965_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_965_, 0, lean_box(0));
lean_closure_set(v_x_965_, 1, v_inst_962_);
v___x_966_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_967_ = l_Std_Format_joinSep___redArg(v_x_965_, v_a_963_, v___x_966_);
v___x_968_ = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
v___x_969_ = ((lean_object*)(l_List_repr___redArg___closed__6));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_967_);
v___x_971_ = ((lean_object*)(l_List_repr___redArg___closed__7));
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_968_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Std_Format_fill(v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object* v_00_u03b1_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_a_978_, lean_object* v_n_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_List_repr_x27___redArg(v_inst_976_, v_a_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object* v_00_u03b1_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_a_984_, lean_object* v_n_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_List_repr_x27(v_00_u03b1_981_, v_inst_982_, v_inst_983_, v_a_984_, v_n_985_);
lean_dec(v_n_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object* v_inst_987_, lean_object* v_inst_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(v___x_989_, 0, lean_box(0));
lean_closure_set(v___x_989_, 1, v_inst_987_);
lean_closure_set(v___x_989_, 2, v_inst_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object* v_00_u03b1_990_, lean_object* v_inst_991_, lean_object* v_inst_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(v___x_993_, 0, lean_box(0));
lean_closure_set(v___x_993_, 1, v_inst_991_);
lean_closure_set(v___x_993_, 2, v_inst_992_);
return v___x_993_;
}
}
static lean_object* _init_l_instReprAtomBool(void){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_box(0);
return v___x_994_;
}
}
static lean_object* _init_l_instReprAtomNat(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
static lean_object* _init_l_instReprAtomInt(void){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
static lean_object* _init_l_instReprAtomChar(void){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_box(0);
return v___x_997_;
}
}
static lean_object* _init_l_instReprAtomString(void){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_box(0);
return v___x_998_;
}
}
static lean_object* _init_l_instReprAtomUInt8(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
}
static lean_object* _init_l_instReprAtomUInt16(void){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_box(0);
return v___x_1000_;
}
}
static lean_object* _init_l_instReprAtomUInt32(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
static lean_object* _init_l_instReprAtomUInt64(void){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_box(0);
return v___x_1002_;
}
}
static lean_object* _init_l_instReprAtomUSize(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__5(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(2u);
v___x_1014_ = lean_nat_to_int(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__6(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_to_int(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr(lean_object* v_x_1023_, lean_object* v_prec_1024_){
_start:
{
lean_object* v___y_1026_; 
switch(lean_obj_tag(v_x_1023_))
{
case 0:
{
lean_object* v_leading_1032_; lean_object* v_pos_1033_; lean_object* v_trailing_1034_; lean_object* v_endPos_1035_; lean_object* v___y_1037_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_leading_1032_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_leading_1032_);
v_pos_1033_ = lean_ctor_get(v_x_1023_, 1);
lean_inc(v_pos_1033_);
v_trailing_1034_ = lean_ctor_get(v_x_1023_, 2);
lean_inc_ref(v_trailing_1034_);
v_endPos_1035_ = lean_ctor_get(v_x_1023_, 3);
lean_inc(v_endPos_1035_);
lean_dec_ref(v_x_1023_);
v___x_1070_ = lean_unsigned_to_nat(1024u);
v___x_1071_ = lean_nat_dec_le(v___x_1070_, v_prec_1024_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1037_ = v___x_1072_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1037_ = v___x_1073_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1038_ = lean_box(1);
v___x_1039_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__4));
v___x_1040_ = lean_substring_tostring(v_leading_1032_);
v___x_1041_ = l_String_quote(v___x_1040_);
v___x_1042_ = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1039_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1038_);
v___x_1047_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_1048_ = l_Nat_reprFast(v_pos_1033_);
v___x_1049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1047_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1046_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1038_);
v___x_1055_ = lean_substring_tostring(v_trailing_1034_);
v___x_1056_ = l_String_quote(v___x_1055_);
v___x_1057_ = lean_string_append(v___x_1056_, v___x_1042_);
v___x_1058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1054_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1038_);
v___x_1061_ = l_Nat_reprFast(v_endPos_1035_);
v___x_1062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1047_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1051_);
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1060_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___y_1037_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = 0;
v___x_1068_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*1, v___x_1067_);
v___x_1069_ = l_Repr_addAppParen(v___x_1068_, v_prec_1024_);
return v___x_1069_;
}
}
case 1:
{
lean_object* v_pos_1074_; lean_object* v_endPos_1075_; uint8_t v_canonical_1076_; lean_object* v___y_1078_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_pos_1074_ = lean_ctor_get(v_x_1023_, 0);
lean_inc(v_pos_1074_);
v_endPos_1075_ = lean_ctor_get(v_x_1023_, 1);
lean_inc(v_endPos_1075_);
v_canonical_1076_ = lean_ctor_get_uint8(v_x_1023_, sizeof(void*)*2);
lean_dec_ref(v_x_1023_);
v___x_1101_ = lean_unsigned_to_nat(1024u);
v___x_1102_ = lean_nat_dec_le(v___x_1101_, v_prec_1024_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1078_ = v___x_1103_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1078_ = v___x_1104_;
goto v___jp_1077_;
}
v___jp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1079_ = lean_box(1);
v___x_1080_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__9));
v___x_1081_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_1082_ = l_Nat_reprFast(v_pos_1074_);
v___x_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1080_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1079_);
v___x_1089_ = l_Nat_reprFast(v_endPos_1075_);
v___x_1090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1081_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1085_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1088_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1079_);
v___x_1095_ = l_Bool_repr___redArg(v_canonical_1076_);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___y_1078_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = 0;
v___x_1099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1, v___x_1098_);
v___x_1100_ = l_Repr_addAppParen(v___x_1099_, v_prec_1024_);
return v___x_1100_;
}
}
default: 
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(1024u);
v___x_1106_ = lean_nat_dec_le(v___x_1105_, v_prec_1024_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1026_ = v___x_1107_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1026_ = v___x_1108_;
goto v___jp_1025_;
}
}
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1027_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__1));
v___x_1028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = 0;
v___x_1030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1029_);
v___x_1031_ = l_Repr_addAppParen(v___x_1030_, v_prec_1024_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr___boxed(lean_object* v_x_1109_, lean_object* v_prec_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_instReprSourceInfo_repr(v_x_1109_, v_prec_1110_);
lean_dec(v_prec_1110_);
return v_res_1111_;
}
}
lean_object* runtime_initialize_Init_Data_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Repr_0__Nat_reprArray = _init_l___private_Init_Data_Repr_0__Nat_reprArray();
lean_mark_persistent(l___private_Init_Data_Repr_0__Nat_reprArray);
l_instReprAtomBool = _init_l_instReprAtomBool();
lean_mark_persistent(l_instReprAtomBool);
l_instReprAtomNat = _init_l_instReprAtomNat();
lean_mark_persistent(l_instReprAtomNat);
l_instReprAtomInt = _init_l_instReprAtomInt();
lean_mark_persistent(l_instReprAtomInt);
l_instReprAtomChar = _init_l_instReprAtomChar();
lean_mark_persistent(l_instReprAtomChar);
l_instReprAtomString = _init_l_instReprAtomString();
lean_mark_persistent(l_instReprAtomString);
l_instReprAtomUInt8 = _init_l_instReprAtomUInt8();
lean_mark_persistent(l_instReprAtomUInt8);
l_instReprAtomUInt16 = _init_l_instReprAtomUInt16();
lean_mark_persistent(l_instReprAtomUInt16);
l_instReprAtomUInt32 = _init_l_instReprAtomUInt32();
lean_mark_persistent(l_instReprAtomUInt32);
l_instReprAtomUInt64 = _init_l_instReprAtomUInt64();
lean_mark_persistent(l_instReprAtomUInt64);
l_instReprAtomUSize = _init_l_instReprAtomUSize();
lean_mark_persistent(l_instReprAtomUSize);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Repr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Format_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Id(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Repr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Repr(builtin);
}
#ifdef __cplusplus
}
#endif
