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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t lean_string_isempty(lean_object*);
lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instReprId___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprId___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprId__1___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instReprId___aux__1___redArg(lean_object* v_inst_32_){
_start:
{
lean_inc_ref(v_inst_32_);
return v_inst_32_;
}
}
LEAN_EXPORT lean_object* l_instReprId___aux__1___redArg___boxed(lean_object* v_inst_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_instReprId___aux__1___redArg(v_inst_33_);
lean_dec_ref(v_inst_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_instReprId___aux__1(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_){
_start:
{
lean_inc_ref(v_inst_36_);
return v_inst_36_;
}
}
LEAN_EXPORT lean_object* l_instReprId___aux__1___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_instReprId___aux__1(v_00_u03b1_37_, v_inst_38_);
lean_dec_ref(v_inst_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object* v_inst_40_){
_start:
{
lean_inc_ref(v_inst_40_);
return v_inst_40_;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object* v_inst_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_instReprId___redArg(v_inst_41_);
lean_dec_ref(v_inst_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_instReprId(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_){
_start:
{
lean_inc_ref(v_inst_44_);
return v_inst_44_;
}
}
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_instReprId(v_00_u03b1_45_, v_inst_46_);
lean_dec_ref(v_inst_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___aux__1___redArg(lean_object* v_inst_48_){
_start:
{
lean_inc_ref(v_inst_48_);
return v_inst_48_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___aux__1___redArg___boxed(lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_instReprId__1___aux__1___redArg(v_inst_49_);
lean_dec_ref(v_inst_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___aux__1(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_){
_start:
{
lean_inc_ref(v_inst_52_);
return v_inst_52_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___aux__1___boxed(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_instReprId__1___aux__1(v_00_u03b1_53_, v_inst_54_);
lean_dec_ref(v_inst_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg(lean_object* v_inst_56_){
_start:
{
lean_inc_ref(v_inst_56_);
return v_inst_56_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg___boxed(lean_object* v_inst_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_instReprId__1___redArg(v_inst_57_);
lean_dec_ref(v_inst_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_){
_start:
{
lean_inc_ref(v_inst_60_);
return v_inst_60_;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___boxed(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_instReprId__1(v_00_u03b1_61_, v_inst_62_);
lean_dec_ref(v_inst_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0(uint8_t v_a_64_, lean_object* v_a_65_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
uint8_t v_a_8__boxed_68_; lean_object* v_res_69_; 
v_a_8__boxed_68_ = lean_unbox(v_a_66_);
v_res_69_ = l_instReprEmpty___lam__0(v_a_8__boxed_68_, v_a_67_);
lean_dec(v_a_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg(uint8_t v_x_78_){
_start:
{
if (v_x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = ((lean_object*)(l_Bool_repr___redArg___closed__1));
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = ((lean_object*)(l_Bool_repr___redArg___closed__3));
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object* v_x_81_){
_start:
{
uint8_t v_x_36__boxed_82_; lean_object* v_res_83_; 
v_x_36__boxed_82_ = lean_unbox(v_x_81_);
v_res_83_ = l_Bool_repr___redArg(v_x_36__boxed_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Bool_repr(uint8_t v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Bool_repr___redArg(v_x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_x_49__boxed_89_; lean_object* v_res_90_; 
v_x_49__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Bool_repr(v_x_49__boxed_89_, v_x_88_);
lean_dec(v_x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Repr_addAppParen_spec__0(lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_nat_to_int(v_a_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__2(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Repr_addAppParen___closed__0));
v___x_98_ = lean_string_length(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__3(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
v___x_100_ = lean_nat_to_int(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object* v_f_105_, lean_object* v_prec_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_106_);
if (v___x_108_ == 0)
{
return v_f_105_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; 
v___x_109_ = lean_obj_once(&l_Repr_addAppParen___closed__3, &l_Repr_addAppParen___closed__3_once, _init_l_Repr_addAppParen___closed__3);
v___x_110_ = ((lean_object*)(l_Repr_addAppParen___closed__4));
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_f_105_);
v___x_112_ = ((lean_object*)(l_Repr_addAppParen___closed__5));
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_109_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = 0;
v___x_116_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*1, v___x_115_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object* v_f_117_, lean_object* v_prec_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Repr_addAppParen(v_f_117_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg(uint8_t v_x_126_, lean_object* v_x_127_){
_start:
{
if (v_x_126_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Decidable_repr___redArg___closed__1));
v___x_129_ = l_Repr_addAppParen(v___x_128_, v_x_127_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Decidable_repr___redArg___closed__3));
v___x_131_ = l_Repr_addAppParen(v___x_130_, v_x_127_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_x_42__boxed_134_; lean_object* v_res_135_; 
v_x_42__boxed_134_ = lean_unbox(v_x_132_);
v_res_135_ = l_Decidable_repr___redArg(v_x_42__boxed_134_, v_x_133_);
lean_dec(v_x_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr(lean_object* v_p_136_, uint8_t v_x_137_, lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Decidable_repr___redArg(v_x_137_, v_x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object* v_p_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
uint8_t v_x_62__boxed_143_; lean_object* v_res_144_; 
v_x_62__boxed_143_ = lean_unbox(v_x_141_);
v_res_144_ = l_Decidable_repr(v_p_140_, v_x_62__boxed_143_, v_x_142_);
lean_dec(v_x_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object* v_p_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_instReprDecidable___closed__0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_instReprPUnit___lam__0___closed__1));
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_instReprPUnit___lam__0(v_x_154_, v_x_155_);
lean_dec(v_x_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object* v_inst_162_, lean_object* v_v_163_, lean_object* v_prec_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = ((lean_object*)(l_instReprULift___redArg___lam__0___closed__1));
v___x_166_ = lean_unsigned_to_nat(1024u);
v___x_167_ = lean_apply_2(v_inst_162_, v_v_163_, v___x_166_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v_prec_164_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object* v_inst_170_, lean_object* v_v_171_, lean_object* v_prec_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_instReprULift___redArg___lam__0(v_inst_170_, v_v_171_, v_prec_172_);
lean_dec(v_prec_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object* v_inst_174_){
_start:
{
lean_object* v___f_175_; 
v___f_175_ = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_175_, 0, v_inst_174_);
return v___f_175_;
}
}
LEAN_EXPORT lean_object* l_instReprULift(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___f_178_; 
v___f_178_ = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_178_, 0, v_inst_177_);
return v___f_178_;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_instReprUnit___lam__0___closed__1));
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_instReprUnit___lam__0(v_x_185_, v_x_186_);
lean_dec(v_x_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object* v_inst_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_199_; 
lean_dec_ref(v_inst_196_);
v___x_199_ = ((lean_object*)(l_Option_repr___redArg___closed__1));
return v___x_199_;
}
else
{
lean_object* v_val_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_val_200_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v_x_197_, 1);
v___x_201_ = ((lean_object*)(l_Option_repr___redArg___closed__3));
v___x_202_ = lean_unsigned_to_nat(1024u);
v___x_203_ = lean_apply_2(v_inst_196_, v_val_200_, v___x_202_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_201_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v_x_198_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object* v_inst_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Option_repr___redArg(v_inst_206_, v_x_207_, v_x_208_);
lean_dec(v_x_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Option_repr(lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Option_repr___redArg(v_inst_211_, v_x_212_, v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Option_repr(v_00_u03b1_215_, v_inst_216_, v_x_217_, v_x_218_);
lean_dec(v_x_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, v_inst_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_instReprOption(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, v_inst_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
lean_object* v_val_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v_inst_232_);
v_val_235_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_x_233_, 1);
v___x_236_ = ((lean_object*)(l_Sum_repr___redArg___closed__1));
v___x_237_ = lean_unsigned_to_nat(1024u);
v___x_238_ = lean_apply_2(v_inst_231_, v_val_235_, v___x_237_);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_236_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l_Repr_addAppParen(v___x_239_, v_x_234_);
return v___x_240_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref(v_inst_231_);
v_val_241_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v_x_233_, 1);
v___x_242_ = ((lean_object*)(l_Sum_repr___redArg___closed__3));
v___x_243_ = lean_unsigned_to_nat(1024u);
v___x_244_ = lean_apply_2(v_inst_232_, v_val_241_, v___x_243_);
v___x_245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_242_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = l_Repr_addAppParen(v___x_245_, v_x_234_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Sum_repr___redArg(v_inst_247_, v_inst_248_, v_x_249_, v_x_250_);
lean_dec(v_x_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Sum_repr___redArg(v_inst_254_, v_inst_255_, v_x_256_, v_x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Sum_repr(v_00_u03b1_259_, v_00_u03b2_260_, v_inst_261_, v_inst_262_, v_x_263_, v_x_264_);
lean_dec(v_x_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(v___x_268_, 0, lean_box(0));
lean_closure_set(v___x_268_, 1, lean_box(0));
lean_closure_set(v___x_268_, 2, v_inst_266_);
lean_closure_set(v___x_268_, 3, v_inst_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_instReprSum(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(v___x_273_, 0, lean_box(0));
lean_closure_set(v___x_273_, 1, lean_box(0));
lean_closure_set(v___x_273_, 2, v_inst_271_);
lean_closure_set(v___x_273_, 3, v_inst_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object* v_inst_274_, lean_object* v_a_275_, lean_object* v_xs_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_apply_2(v_inst_274_, v_a_275_, v___x_277_);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_xs_276_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object* v_inst_280_){
_start:
{
lean_object* v___f_281_; 
v___f_281_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_281_, 0, v_inst_280_);
return v___f_281_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_){
_start:
{
lean_object* v___f_284_; 
v___f_284_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_284_, 0, v_inst_283_);
return v___f_284_;
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v_fst_289_ = lean_ctor_get(v_x_287_, 0);
v_snd_290_ = lean_ctor_get(v_x_287_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_287_);
if (v_isSharedCheck_300_ == 0)
{
v___x_292_ = v_x_287_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_snd_290_);
lean_inc(v_fst_289_);
lean_dec(v_x_287_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_apply_2(v_inst_285_, v_fst_289_, v___x_294_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 1);
lean_ctor_set(v___x_292_, 1, v_x_288_);
lean_ctor_set(v___x_292_, 0, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_x_288_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; 
v___x_298_ = lean_apply_2(v_inst_286_, v_snd_290_, v___x_297_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Prod_reprTuple___redArg(v_inst_303_, v_inst_304_, v_x_305_, v_x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object* v_inst_308_, lean_object* v_inst_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(v___x_310_, 0, lean_box(0));
lean_closure_set(v___x_310_, 1, lean_box(0));
lean_closure_set(v___x_310_, 2, v_inst_308_);
lean_closure_set(v___x_310_, 3, v_inst_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_inst_313_, lean_object* v_inst_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(v___x_315_, 0, lean_box(0));
lean_closure_set(v___x_315_, 1, lean_box(0));
lean_closure_set(v___x_315_, 2, v_inst_313_);
lean_closure_set(v___x_315_, 3, v_inst_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_352_; 
v_fst_328_ = lean_ctor_get(v_x_327_, 0);
v_snd_329_ = lean_ctor_get(v_x_327_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_352_ == 0)
{
v___x_331_ = v_x_327_;
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snd_329_);
lean_inc(v_fst_328_);
lean_dec(v_x_327_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___f_333_ = ((lean_object*)(l_Prod_repr___redArg___closed__0));
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_apply_2(v_inst_325_, v_fst_328_, v___x_334_);
v___x_336_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set_tag(v___x_331_, 1);
lean_ctor_set(v___x_331_, 1, v___x_336_);
lean_ctor_set(v___x_331_, 0, v___x_335_);
v___x_338_ = v___x_331_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_351_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_339_ = lean_apply_2(v_inst_326_, v_snd_329_, v___x_338_);
v___x_340_ = l_List_reverse___redArg(v___x_339_);
v___x_341_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_342_ = l_Std_Format_joinSep___redArg(v___f_333_, v___x_340_, v___x_341_);
v___x_343_ = lean_obj_once(&l_Prod_repr___redArg___closed__4, &l_Prod_repr___redArg___closed__4_once, _init_l_Prod_repr___redArg___closed__4);
v___x_344_ = ((lean_object*)(l_Repr_addAppParen___closed__4));
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_342_);
v___x_346_ = ((lean_object*)(l_Repr_addAppParen___closed__5));
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_343_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = 0;
v___x_350_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*1, v___x_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr(lean_object* v_00_u03b1_353_, lean_object* v_00_u03b2_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Prod_repr___redArg(v_inst_355_, v_inst_356_, v_x_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Prod_repr(v_00_u03b1_360_, v_00_u03b2_361_, v_inst_362_, v_inst_363_, v_x_364_, v_x_365_);
lean_dec(v_x_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object* v_inst_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, lean_box(0));
lean_closure_set(v___x_369_, 2, v_inst_367_);
lean_closure_set(v___x_369_, 3, v_inst_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_inst_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_374_, 0, lean_box(0));
lean_closure_set(v___x_374_, 1, lean_box(0));
lean_closure_set(v___x_374_, 2, v_inst_372_);
lean_closure_set(v___x_374_, 3, v_inst_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Sigma_repr___redArg___closed__0));
v___x_381_ = lean_string_length(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Sigma_repr___redArg___closed__4, &l_Sigma_repr___redArg___closed__4_once, _init_l_Sigma_repr___redArg___closed__4);
v___x_383_ = lean_nat_to_int(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_412_; 
v_fst_391_ = lean_ctor_get(v_x_390_, 0);
v_snd_392_ = lean_ctor_get(v_x_390_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_412_ == 0)
{
v___x_394_ = v_x_390_;
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_snd_392_);
lean_inc(v_fst_391_);
lean_dec(v_x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_396_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_391_);
v___x_397_ = lean_apply_2(v_inst_388_, v_fst_391_, v___x_396_);
v___x_398_ = ((lean_object*)(l_Sigma_repr___redArg___closed__2));
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 5);
lean_ctor_set(v___x_394_, 1, v___x_398_);
lean_ctor_set(v___x_394_, 0, v___x_397_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_411_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; 
v___x_401_ = lean_apply_3(v_inst_389_, v_fst_391_, v_snd_392_, v___x_396_);
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_obj_once(&l_Sigma_repr___redArg___closed__5, &l_Sigma_repr___redArg___closed__5_once, _init_l_Sigma_repr___redArg___closed__5);
v___x_404_ = ((lean_object*)(l_Sigma_repr___redArg___closed__6));
v___x_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_402_);
v___x_406_ = ((lean_object*)(l_Sigma_repr___redArg___closed__7));
v___x_407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_403_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = 0;
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_409_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object* v_00_u03b1_413_, lean_object* v_00_u03b2_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Sigma_repr___redArg(v_inst_415_, v_inst_416_, v_x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Sigma_repr(v_00_u03b1_420_, v_00_u03b2_421_, v_inst_422_, v_inst_423_, v_x_424_, v_x_425_);
lean_dec(v_x_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_429_, 0, lean_box(0));
lean_closure_set(v___x_429_, 1, lean_box(0));
lean_closure_set(v___x_429_, 2, v_inst_427_);
lean_closure_set(v___x_429_, 3, v_inst_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_instReprSigma(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_inst_432_, lean_object* v_inst_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_434_, 0, lean_box(0));
lean_closure_set(v___x_434_, 1, lean_box(0));
lean_closure_set(v___x_434_, 2, v_inst_432_);
lean_closure_set(v___x_434_, 3, v_inst_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object* v_inst_435_, lean_object* v_s_436_, lean_object* v_prec_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lean_apply_2(v_inst_435_, v_s_436_, v_prec_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object* v_inst_439_){
_start:
{
lean_object* v___f_440_; 
v___f_440_ = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(v___f_440_, 0, v_inst_439_);
return v___f_440_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object* v_00_u03b1_441_, lean_object* v_p_442_, lean_object* v_inst_443_){
_start:
{
lean_object* v___f_444_; 
v___f_444_ = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(v___f_444_, 0, v_inst_443_);
return v___f_444_;
}
}
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object* v_n_445_){
_start:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_nat_dec_eq(v_n_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_dec_eq(v_n_445_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(2u);
v___x_451_ = lean_nat_dec_eq(v_n_445_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = lean_nat_dec_eq(v_n_445_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(4u);
v___x_455_ = lean_nat_dec_eq(v_n_445_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(5u);
v___x_457_ = lean_nat_dec_eq(v_n_445_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(6u);
v___x_459_ = lean_nat_dec_eq(v_n_445_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(7u);
v___x_461_ = lean_nat_dec_eq(v_n_445_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(8u);
v___x_463_ = lean_nat_dec_eq(v_n_445_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(9u);
v___x_465_ = lean_nat_dec_eq(v_n_445_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(10u);
v___x_467_ = lean_nat_dec_eq(v_n_445_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(11u);
v___x_469_ = lean_nat_dec_eq(v_n_445_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(12u);
v___x_471_ = lean_nat_dec_eq(v_n_445_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(13u);
v___x_473_ = lean_nat_dec_eq(v_n_445_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(14u);
v___x_475_ = lean_nat_dec_eq(v_n_445_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(15u);
v___x_477_ = lean_nat_dec_eq(v_n_445_, v___x_476_);
if (v___x_477_ == 0)
{
uint32_t v___x_478_; 
v___x_478_ = 42;
return v___x_478_;
}
else
{
uint32_t v___x_479_; 
v___x_479_ = 102;
return v___x_479_;
}
}
else
{
uint32_t v___x_480_; 
v___x_480_ = 101;
return v___x_480_;
}
}
else
{
uint32_t v___x_481_; 
v___x_481_ = 100;
return v___x_481_;
}
}
else
{
uint32_t v___x_482_; 
v___x_482_ = 99;
return v___x_482_;
}
}
else
{
uint32_t v___x_483_; 
v___x_483_ = 98;
return v___x_483_;
}
}
else
{
uint32_t v___x_484_; 
v___x_484_ = 97;
return v___x_484_;
}
}
else
{
uint32_t v___x_485_; 
v___x_485_ = 57;
return v___x_485_;
}
}
else
{
uint32_t v___x_486_; 
v___x_486_ = 56;
return v___x_486_;
}
}
else
{
uint32_t v___x_487_; 
v___x_487_ = 55;
return v___x_487_;
}
}
else
{
uint32_t v___x_488_; 
v___x_488_ = 54;
return v___x_488_;
}
}
else
{
uint32_t v___x_489_; 
v___x_489_ = 53;
return v___x_489_;
}
}
else
{
uint32_t v___x_490_; 
v___x_490_ = 52;
return v___x_490_;
}
}
else
{
uint32_t v___x_491_; 
v___x_491_ = 51;
return v___x_491_;
}
}
else
{
uint32_t v___x_492_; 
v___x_492_ = 50;
return v___x_492_;
}
}
else
{
uint32_t v___x_493_; 
v___x_493_ = 49;
return v___x_493_;
}
}
else
{
uint32_t v___x_494_; 
v___x_494_ = 48;
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object* v_n_495_){
_start:
{
uint32_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Nat_digitChar(v_n_495_);
lean_dec(v_n_495_);
v_r_497_ = lean_box_uint32(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object* v_base_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_zero_502_; uint8_t v_isZero_503_; 
v_zero_502_ = lean_unsigned_to_nat(0u);
v_isZero_503_ = lean_nat_dec_eq(v_x_499_, v_zero_502_);
if (v_isZero_503_ == 1)
{
lean_dec(v_x_500_);
lean_dec(v_x_499_);
return v_x_501_;
}
else
{
lean_object* v___x_504_; uint32_t v_d_505_; lean_object* v_n_x27_506_; uint8_t v___x_507_; 
v___x_504_ = lean_nat_mod(v_x_500_, v_base_498_);
v_d_505_ = l_Nat_digitChar(v___x_504_);
lean_dec(v___x_504_);
v_n_x27_506_ = lean_nat_div(v_x_500_, v_base_498_);
lean_dec(v_x_500_);
v___x_507_ = lean_nat_dec_eq(v_n_x27_506_, v_zero_502_);
if (v___x_507_ == 0)
{
lean_object* v_one_508_; lean_object* v_n_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_one_508_ = lean_unsigned_to_nat(1u);
v_n_509_ = lean_nat_sub(v_x_499_, v_one_508_);
lean_dec(v_x_499_);
v___x_510_ = lean_box_uint32(v_d_505_);
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_x_501_);
v_x_499_ = v_n_509_;
v_x_500_ = v_n_x27_506_;
v_x_501_ = v___x_511_;
goto _start;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_n_x27_506_);
lean_dec(v_x_499_);
v___x_513_ = lean_box_uint32(v_d_505_);
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_x_501_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object* v_base_515_, lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Nat_toDigitsCore(v_base_515_, v_x_516_, v_x_517_, v_x_518_);
lean_dec(v_base_515_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object* v_base_520_, lean_object* v_n_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_n_521_, v___x_522_);
v___x_524_ = lean_box(0);
v___x_525_ = l_Nat_toDigitsCore(v_base_520_, v___x_523_, v_n_521_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object* v_base_526_, lean_object* v_n_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Nat_toDigits(v_base_526_, v_n_527_);
lean_dec(v_base_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object* v_n_530_){
_start:
{
size_t v_n_boxed_531_; lean_object* v_res_532_; 
v_n_boxed_531_ = lean_unbox_usize(v_n_530_);
lean_dec(v_n_530_);
v_res_532_ = lean_string_of_usize(v_n_boxed_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v___x_535_; 
v___x_535_ = l_List_reverse___redArg(v_a_534_);
return v___x_535_;
}
else
{
lean_object* v_head_536_; lean_object* v_tail_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
v_head_536_ = lean_ctor_get(v_a_533_, 0);
v_tail_537_ = lean_ctor_get(v_a_533_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_a_533_);
if (v_isSharedCheck_547_ == 0)
{
v___x_539_ = v_a_533_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_tail_537_);
lean_inc(v_head_536_);
lean_dec(v_a_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
size_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_usize_of_nat(v_head_536_);
lean_dec(v_head_536_);
v___x_542_ = lean_string_of_usize(v___x_541_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_a_534_);
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_534_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_533_ = v_tail_537_;
v_a_534_ = v___x_544_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(128u);
v___x_549_ = l_List_range(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
v___x_551_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__0, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0);
v___x_552_ = l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__1, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1);
v___x_554_ = lean_array_mk(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray(void){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__2, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2);
return v___x_555_;
}
}
static lean_object* _init_l_Nat_reprFast___closed__0(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = l___private_Init_Data_Repr_0__Nat_reprArray;
v___x_557_ = lean_array_get_size(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Nat_reprFast___closed__1(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = l_System_Platform_numBits;
v___x_559_ = lean_unsigned_to_nat(2u);
v___x_560_ = lean_nat_pow(v___x_559_, v___x_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object* v_n_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = l___private_Init_Data_Repr_0__Nat_reprArray;
v___x_563_ = lean_obj_once(&l_Nat_reprFast___closed__0, &l_Nat_reprFast___closed__0_once, _init_l_Nat_reprFast___closed__0);
v___x_564_ = lean_nat_dec_lt(v_n_561_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_obj_once(&l_Nat_reprFast___closed__1, &l_Nat_reprFast___closed__1_once, _init_l_Nat_reprFast___closed__1);
v___x_566_ = lean_nat_dec_lt(v_n_561_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(10u);
v___x_568_ = l_Nat_toDigits(v___x_567_, v_n_561_);
v___x_569_ = lean_string_mk(v___x_568_);
return v___x_569_;
}
else
{
size_t v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_usize_of_nat(v_n_561_);
lean_dec(v_n_561_);
v___x_571_ = lean_string_of_usize(v___x_570_);
return v___x_571_;
}
}
else
{
lean_object* v___x_572_; 
v___x_572_ = lean_array_fget_borrowed(v___x_562_, v_n_561_);
lean_dec(v_n_561_);
lean_inc(v___x_572_);
return v___x_572_;
}
}
}
LEAN_EXPORT uint32_t l_Nat_superDigitChar(lean_object* v_n_573_){
_start:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_dec_eq(v_n_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_dec_eq(v_n_573_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_nat_dec_eq(v_n_573_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = lean_nat_dec_eq(v_n_573_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(4u);
v___x_583_ = lean_nat_dec_eq(v_n_573_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(5u);
v___x_585_ = lean_nat_dec_eq(v_n_573_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(6u);
v___x_587_ = lean_nat_dec_eq(v_n_573_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(7u);
v___x_589_ = lean_nat_dec_eq(v_n_573_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(8u);
v___x_591_ = lean_nat_dec_eq(v_n_573_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(9u);
v___x_593_ = lean_nat_dec_eq(v_n_573_, v___x_592_);
if (v___x_593_ == 0)
{
uint32_t v___x_594_; 
v___x_594_ = 42;
return v___x_594_;
}
else
{
uint32_t v___x_595_; 
v___x_595_ = 8313;
return v___x_595_;
}
}
else
{
uint32_t v___x_596_; 
v___x_596_ = 8312;
return v___x_596_;
}
}
else
{
uint32_t v___x_597_; 
v___x_597_ = 8311;
return v___x_597_;
}
}
else
{
uint32_t v___x_598_; 
v___x_598_ = 8310;
return v___x_598_;
}
}
else
{
uint32_t v___x_599_; 
v___x_599_ = 8309;
return v___x_599_;
}
}
else
{
uint32_t v___x_600_; 
v___x_600_ = 8308;
return v___x_600_;
}
}
else
{
uint32_t v___x_601_; 
v___x_601_ = 179;
return v___x_601_;
}
}
else
{
uint32_t v___x_602_; 
v___x_602_ = 178;
return v___x_602_;
}
}
else
{
uint32_t v___x_603_; 
v___x_603_ = 185;
return v___x_603_;
}
}
else
{
uint32_t v___x_604_; 
v___x_604_ = 8304;
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object* v_n_605_){
_start:
{
uint32_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Nat_superDigitChar(v_n_605_);
lean_dec(v_n_605_);
v_r_607_ = lean_box_uint32(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint32_t v_d_612_; lean_object* v_n_x27_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_610_ = lean_unsigned_to_nat(10u);
v___x_611_ = lean_nat_mod(v_x_608_, v___x_610_);
v_d_612_ = l_Nat_superDigitChar(v___x_611_);
lean_dec(v___x_611_);
v_n_x27_613_ = lean_nat_div(v_x_608_, v___x_610_);
lean_dec(v_x_608_);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_eq(v_n_x27_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_box_uint32(v_d_612_);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v_x_609_);
v_x_608_ = v_n_x27_613_;
v_x_609_ = v___x_617_;
goto _start;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_n_x27_613_);
v___x_619_ = lean_box_uint32(v_d_612_);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_x_609_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object* v_n_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(0);
v___x_623_ = l_Nat_toSuperDigitsAux(v_n_621_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object* v_n_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = l_Nat_toSuperDigits(v_n_624_);
v___x_626_ = lean_string_mk(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT uint32_t l_Nat_subDigitChar(lean_object* v_n_627_){
_start:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v_n_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_dec_eq(v_n_627_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(2u);
v___x_633_ = lean_nat_dec_eq(v_n_627_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(3u);
v___x_635_ = lean_nat_dec_eq(v_n_627_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(4u);
v___x_637_ = lean_nat_dec_eq(v_n_627_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(5u);
v___x_639_ = lean_nat_dec_eq(v_n_627_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(6u);
v___x_641_ = lean_nat_dec_eq(v_n_627_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(7u);
v___x_643_ = lean_nat_dec_eq(v_n_627_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(8u);
v___x_645_ = lean_nat_dec_eq(v_n_627_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(9u);
v___x_647_ = lean_nat_dec_eq(v_n_627_, v___x_646_);
if (v___x_647_ == 0)
{
uint32_t v___x_648_; 
v___x_648_ = 42;
return v___x_648_;
}
else
{
uint32_t v___x_649_; 
v___x_649_ = 8329;
return v___x_649_;
}
}
else
{
uint32_t v___x_650_; 
v___x_650_ = 8328;
return v___x_650_;
}
}
else
{
uint32_t v___x_651_; 
v___x_651_ = 8327;
return v___x_651_;
}
}
else
{
uint32_t v___x_652_; 
v___x_652_ = 8326;
return v___x_652_;
}
}
else
{
uint32_t v___x_653_; 
v___x_653_ = 8325;
return v___x_653_;
}
}
else
{
uint32_t v___x_654_; 
v___x_654_ = 8324;
return v___x_654_;
}
}
else
{
uint32_t v___x_655_; 
v___x_655_ = 8323;
return v___x_655_;
}
}
else
{
uint32_t v___x_656_; 
v___x_656_ = 8322;
return v___x_656_;
}
}
else
{
uint32_t v___x_657_; 
v___x_657_ = 8321;
return v___x_657_;
}
}
else
{
uint32_t v___x_658_; 
v___x_658_ = 8320;
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object* v_n_659_){
_start:
{
uint32_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Nat_subDigitChar(v_n_659_);
lean_dec(v_n_659_);
v_r_661_ = lean_box_uint32(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; uint32_t v_d_666_; lean_object* v_n_x27_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_664_ = lean_unsigned_to_nat(10u);
v___x_665_ = lean_nat_mod(v_x_662_, v___x_664_);
v_d_666_ = l_Nat_subDigitChar(v___x_665_);
lean_dec(v___x_665_);
v_n_x27_667_ = lean_nat_div(v_x_662_, v___x_664_);
lean_dec(v_x_662_);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_nat_dec_eq(v_n_x27_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box_uint32(v_d_666_);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_x_663_);
v_x_662_ = v_n_x27_667_;
v_x_663_ = v___x_671_;
goto _start;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_n_x27_667_);
v___x_673_ = lean_box_uint32(v_d_666_);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_x_663_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object* v_n_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_box(0);
v___x_677_ = l_Nat_toSubDigitsAux(v_n_675_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object* v_n_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = l_Nat_toSubDigits(v_n_678_);
v___x_680_ = lean_string_mk(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object* v_n_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l_Nat_reprFast(v_n_681_);
v___x_684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object* v_n_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_instReprNat___lam__0(v_n_685_, v_x_686_);
lean_dec(v_x_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object* v_n_691_){
_start:
{
uint32_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = l_Nat_digitChar(v_n_691_);
v___x_693_ = ((lean_object*)(l_hexDigitRepr___closed__0));
v___x_694_ = lean_string_push(v___x_693_, v___x_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object* v_n_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_hexDigitRepr(v_n_695_);
lean_dec(v_n_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t v_c_697_){
_start:
{
lean_object* v_n_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_d2_701_; lean_object* v_d1_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_n_698_ = lean_uint32_to_nat(v_c_697_);
v___x_699_ = lean_unsigned_to_nat(16u);
v___x_700_ = lean_unsigned_to_nat(4u);
v_d2_701_ = lean_nat_shiftr(v_n_698_, v___x_700_);
v_d1_702_ = lean_nat_mod(v_n_698_, v___x_699_);
lean_dec(v_n_698_);
v___x_703_ = l_hexDigitRepr(v_d2_701_);
lean_dec(v_d2_701_);
v___x_704_ = l_hexDigitRepr(v_d1_702_);
lean_dec(v_d1_702_);
v___x_705_ = lean_string_append(v___x_703_, v___x_704_);
lean_dec_ref(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(lean_object* v_c_706_){
_start:
{
uint32_t v_c_boxed_707_; lean_object* v_res_708_; 
v_c_boxed_707_ = lean_unbox_uint32(v_c_706_);
lean_dec(v_c_706_);
v_res_708_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_boxed_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore(uint32_t v_c_715_, uint8_t v_inString_716_){
_start:
{
uint8_t v___y_722_; uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 10;
v___x_732_ = lean_uint32_dec_eq(v_c_715_, v___x_731_);
if (v___x_732_ == 0)
{
uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 9;
v___x_734_ = lean_uint32_dec_eq(v_c_715_, v___x_733_);
if (v___x_734_ == 0)
{
uint32_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 92;
v___x_736_ = lean_uint32_dec_eq(v_c_715_, v___x_735_);
if (v___x_736_ == 0)
{
uint32_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = 34;
v___x_738_ = lean_uint32_dec_eq(v_c_715_, v___x_737_);
if (v___x_738_ == 0)
{
uint8_t v___x_739_; 
v___x_739_ = lean_bool_not(v_inString_716_);
if (v___x_739_ == 0)
{
v___y_722_ = v___x_739_;
goto v___jp_721_;
}
else
{
uint32_t v___x_740_; uint8_t v___x_741_; 
v___x_740_ = 39;
v___x_741_ = lean_uint32_dec_eq(v_c_715_, v___x_740_);
v___y_722_ = v___x_741_;
goto v___jp_721_;
}
}
else
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Char_quoteCore___closed__2));
return v___x_742_;
}
}
else
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Char_quoteCore___closed__3));
return v___x_743_;
}
}
else
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Char_quoteCore___closed__4));
return v___x_744_;
}
}
else
{
lean_object* v___x_745_; 
v___x_745_ = ((lean_object*)(l_Char_quoteCore___closed__5));
return v___x_745_;
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((lean_object*)(l_Char_quoteCore___closed__0));
v___x_719_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_715_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
return v___x_720_;
}
v___jp_721_:
{
if (v___y_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_uint32_to_nat(v_c_715_);
v___x_724_ = lean_unsigned_to_nat(31u);
v___x_725_ = lean_nat_dec_le(v___x_723_, v___x_724_);
lean_dec(v___x_723_);
if (v___x_725_ == 0)
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 127;
v___x_727_ = lean_uint32_dec_eq(v_c_715_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_hexDigitRepr___closed__0));
v___x_729_ = lean_string_push(v___x_728_, v_c_715_);
return v___x_729_;
}
else
{
goto v___jp_717_;
}
}
else
{
goto v___jp_717_;
}
}
else
{
lean_object* v___x_730_; 
v___x_730_ = ((lean_object*)(l_Char_quoteCore___closed__1));
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object* v_c_746_, lean_object* v_inString_747_){
_start:
{
uint32_t v_c_boxed_748_; uint8_t v_inString_boxed_749_; lean_object* v_res_750_; 
v_c_boxed_748_ = lean_unbox_uint32(v_c_746_);
lean_dec(v_c_746_);
v_inString_boxed_749_ = lean_unbox(v_inString_747_);
v_res_750_ = l_Char_quoteCore(v_c_boxed_748_, v_inString_boxed_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Char_quote(uint32_t v_c_752_){
_start:
{
lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_753_ = ((lean_object*)(l_Char_quote___closed__0));
v___x_754_ = 0;
v___x_755_ = l_Char_quoteCore(v_c_752_, v___x_754_);
v___x_756_ = lean_string_append(v___x_753_, v___x_755_);
lean_dec_ref(v___x_755_);
v___x_757_ = lean_string_append(v___x_756_, v___x_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object* v_c_758_){
_start:
{
uint32_t v_c_boxed_759_; lean_object* v_res_760_; 
v_c_boxed_759_ = lean_unbox_uint32(v_c_758_);
lean_dec(v_c_758_);
v_res_760_ = l_Char_quote(v_c_boxed_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0(uint32_t v_c_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = l_Char_quote(v_c_761_);
v___x_764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object* v_c_765_, lean_object* v_x_766_){
_start:
{
uint32_t v_c_boxed_767_; lean_object* v_res_768_; 
v_c_boxed_767_ = lean_unbox_uint32(v_c_765_);
lean_dec(v_c_765_);
v_res_768_ = l_instReprChar___lam__0(v_c_boxed_767_, v_x_766_);
lean_dec(v_x_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Char_repr(uint32_t v_c_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Char_quote(v_c_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object* v_c_773_){
_start:
{
uint32_t v_c_boxed_774_; lean_object* v_res_775_; 
v_c_boxed_774_ = lean_unbox_uint32(v_c_773_);
lean_dec(v_c_773_);
v_res_775_ = l_Char_repr(v_c_boxed_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_String_quote___lam__0(uint8_t v___x_776_, lean_object* v_s_777_, uint32_t v_c_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = l_Char_quoteCore(v_c_778_, v___x_776_);
v___x_780_ = lean_string_append(v_s_777_, v___x_779_);
lean_dec_ref(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_String_quote___lam__0___boxed(lean_object* v___x_781_, lean_object* v_s_782_, lean_object* v_c_783_){
_start:
{
uint8_t v___x_43__boxed_784_; uint32_t v_c_boxed_785_; lean_object* v_res_786_; 
v___x_43__boxed_784_ = lean_unbox(v___x_781_);
v_c_boxed_785_ = lean_unbox_uint32(v_c_783_);
lean_dec(v_c_783_);
v_res_786_ = l_String_quote___lam__0(v___x_43__boxed_784_, v_s_782_, v_c_boxed_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_String_quote(lean_object* v_s_792_){
_start:
{
uint8_t v___x_793_; 
lean_inc_ref(v_s_792_);
v___x_793_ = lean_string_isempty(v_s_792_);
if (v___x_793_ == 0)
{
lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___f_794_ = ((lean_object*)(l_String_quote___closed__0));
v___x_795_ = ((lean_object*)(l_String_quote___closed__1));
v___x_796_ = lean_string_foldl(v___f_794_, v___x_795_, v_s_792_);
v___x_797_ = lean_string_append(v___x_796_, v___x_795_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; 
lean_dec_ref(v_s_792_);
v___x_798_ = ((lean_object*)(l_String_quote___closed__2));
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object* v_s_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_String_quote(v_s_799_);
v___x_802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object* v_s_803_, lean_object* v_x_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_instReprString___lam__0(v_s_803_, v_x_804_);
lean_dec(v_x_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0(lean_object* v_p_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_816_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_817_ = l_Nat_reprFast(v_p_814_);
v___x_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_816_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0___boxed(lean_object* v_p_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_instReprRaw___lam__0(v_p_822_, v_x_823_);
lean_dec(v_x_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0(lean_object* v_s_828_, lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_830_ = lean_substring_tostring(v_s_828_);
v___x_831_ = l_String_quote(v___x_830_);
v___x_832_ = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
v___x_833_ = lean_string_append(v___x_831_, v___x_832_);
v___x_834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0___boxed(lean_object* v_s_835_, lean_object* v_x_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_instReprRaw__1___lam__0(v_s_835_, v_x_836_);
lean_dec(v_x_836_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0(lean_object* v_f_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = l_Nat_reprFast(v_f_840_);
v___x_843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0___boxed(lean_object* v_f_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_instReprFin___lam__0(v_f_844_, v_x_845_);
lean_dec(v_x_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_instReprFin(lean_object* v_n_848_){
_start:
{
lean_object* v___f_849_; 
v___f_849_ = ((lean_object*)(l_instReprFin___closed__0));
return v___f_849_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object* v_n_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_instReprFin(v_n_850_);
lean_dec(v_n_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t v_n_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_uint8_to_nat(v_n_852_);
v___x_855_ = l_Nat_reprFast(v___x_854_);
v___x_856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object* v_n_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_n_boxed_859_; lean_object* v_res_860_; 
v_n_boxed_859_ = lean_unbox(v_n_857_);
v_res_860_ = l_instReprUInt8___lam__0(v_n_boxed_859_, v_x_858_);
lean_dec(v_x_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0(uint16_t v_n_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_uint16_to_nat(v_n_863_);
v___x_866_ = l_Nat_reprFast(v___x_865_);
v___x_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object* v_n_868_, lean_object* v_x_869_){
_start:
{
uint16_t v_n_boxed_870_; lean_object* v_res_871_; 
v_n_boxed_870_ = lean_unbox(v_n_868_);
v_res_871_ = l_instReprUInt16___lam__0(v_n_boxed_870_, v_x_869_);
lean_dec(v_x_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0(uint32_t v_n_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = lean_uint32_to_nat(v_n_874_);
v___x_877_ = l_Nat_reprFast(v___x_876_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object* v_n_879_, lean_object* v_x_880_){
_start:
{
uint32_t v_n_boxed_881_; lean_object* v_res_882_; 
v_n_boxed_881_ = lean_unbox_uint32(v_n_879_);
lean_dec(v_n_879_);
v_res_882_ = l_instReprUInt32___lam__0(v_n_boxed_881_, v_x_880_);
lean_dec(v_x_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t v_n_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_uint64_to_nat(v_n_885_);
v___x_888_ = l_Nat_reprFast(v___x_887_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object* v_n_890_, lean_object* v_x_891_){
_start:
{
uint64_t v_n_boxed_892_; lean_object* v_res_893_; 
v_n_boxed_892_ = lean_unbox_uint64(v_n_890_);
lean_dec_ref(v_n_890_);
v_res_893_ = l_instReprUInt64___lam__0(v_n_boxed_892_, v_x_891_);
lean_dec(v_x_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0(size_t v_n_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_usize_to_nat(v_n_896_);
v___x_899_ = l_Nat_reprFast(v___x_898_);
v___x_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object* v_n_901_, lean_object* v_x_902_){
_start:
{
size_t v_n_boxed_903_; lean_object* v_res_904_; 
v_n_boxed_903_ = lean_unbox_usize(v_n_901_);
lean_dec(v_n_901_);
v_res_904_ = l_instReprUSize___lam__0(v_n_boxed_903_, v_x_902_);
lean_dec(v_x_902_);
return v_res_904_;
}
}
static lean_object* _init_l_List_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_List_repr___redArg___closed__2));
v___x_913_ = lean_string_length(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_List_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_obj_once(&l_List_repr___redArg___closed__4, &l_List_repr___redArg___closed__4_once, _init_l_List_repr___redArg___closed__4);
v___x_915_ = lean_nat_to_int(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object* v_inst_920_, lean_object* v_a_921_){
_start:
{
if (lean_obj_tag(v_a_921_) == 0)
{
lean_object* v___x_922_; 
lean_dec_ref(v_inst_920_);
v___x_922_ = ((lean_object*)(l_List_repr___redArg___closed__1));
return v___x_922_;
}
else
{
lean_object* v_x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v_x_923_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_923_, 0, lean_box(0));
lean_closure_set(v_x_923_, 1, v_inst_920_);
v___x_924_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_925_ = l_Std_Format_joinSep___redArg(v_x_923_, v_a_921_, v___x_924_);
v___x_926_ = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
v___x_927_ = ((lean_object*)(l_List_repr___redArg___closed__6));
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_925_);
v___x_929_ = ((lean_object*)(l_List_repr___redArg___closed__7));
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_926_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = 0;
v___x_933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_List_repr(lean_object* v_00_u03b1_934_, lean_object* v_inst_935_, lean_object* v_a_936_, lean_object* v_n_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_List_repr___redArg(v_inst_935_, v_a_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object* v_00_u03b1_939_, lean_object* v_inst_940_, lean_object* v_a_941_, lean_object* v_n_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_List_repr(v_00_u03b1_939_, v_inst_940_, v_a_941_, v_n_942_);
lean_dec(v_n_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object* v_inst_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(v___x_945_, 0, lean_box(0));
lean_closure_set(v___x_945_, 1, v_inst_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_instReprList(lean_object* v_00_u03b1_946_, lean_object* v_inst_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, v_inst_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object* v_inst_949_, lean_object* v_a_950_){
_start:
{
if (lean_obj_tag(v_a_950_) == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v_inst_949_);
v___x_951_ = ((lean_object*)(l_List_repr___redArg___closed__1));
return v___x_951_;
}
else
{
lean_object* v_x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_x_952_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_952_, 0, lean_box(0));
lean_closure_set(v_x_952_, 1, v_inst_949_);
v___x_953_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_954_ = l_Std_Format_joinSep___redArg(v_x_952_, v_a_950_, v___x_953_);
v___x_955_ = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
v___x_956_ = ((lean_object*)(l_List_repr___redArg___closed__6));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_954_);
v___x_958_ = ((lean_object*)(l_List_repr___redArg___closed__7));
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_955_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Std_Format_fill(v___x_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_a_965_, lean_object* v_n_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_List_repr_x27___redArg(v_inst_963_, v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object* v_00_u03b1_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_a_971_, lean_object* v_n_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_List_repr_x27(v_00_u03b1_968_, v_inst_969_, v_inst_970_, v_a_971_, v_n_972_);
lean_dec(v_n_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object* v_inst_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(v___x_976_, 0, lean_box(0));
lean_closure_set(v___x_976_, 1, v_inst_974_);
lean_closure_set(v___x_976_, 2, v_inst_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object* v_00_u03b1_977_, lean_object* v_inst_978_, lean_object* v_inst_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(v___x_980_, 0, lean_box(0));
lean_closure_set(v___x_980_, 1, v_inst_978_);
lean_closure_set(v___x_980_, 2, v_inst_979_);
return v___x_980_;
}
}
static lean_object* _init_l_instReprAtomBool(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = lean_box(0);
return v___x_981_;
}
}
static lean_object* _init_l_instReprAtomNat(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_box(0);
return v___x_982_;
}
}
static lean_object* _init_l_instReprAtomInt(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_box(0);
return v___x_983_;
}
}
static lean_object* _init_l_instReprAtomChar(void){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_box(0);
return v___x_984_;
}
}
static lean_object* _init_l_instReprAtomString(void){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_box(0);
return v___x_985_;
}
}
static lean_object* _init_l_instReprAtomUInt8(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_box(0);
return v___x_986_;
}
}
static lean_object* _init_l_instReprAtomUInt16(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
static lean_object* _init_l_instReprAtomUInt32(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_box(0);
return v___x_988_;
}
}
static lean_object* _init_l_instReprAtomUInt64(void){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_box(0);
return v___x_989_;
}
}
static lean_object* _init_l_instReprAtomUSize(void){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = lean_box(0);
return v___x_990_;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(2u);
v___x_1001_ = lean_nat_to_int(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__6(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_to_int(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr(lean_object* v_x_1010_, lean_object* v_prec_1011_){
_start:
{
lean_object* v___y_1013_; 
switch(lean_obj_tag(v_x_1010_))
{
case 0:
{
lean_object* v_leading_1019_; lean_object* v_pos_1020_; lean_object* v_trailing_1021_; lean_object* v_endPos_1022_; lean_object* v___y_1024_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_leading_1019_ = lean_ctor_get(v_x_1010_, 0);
lean_inc_ref(v_leading_1019_);
v_pos_1020_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_pos_1020_);
v_trailing_1021_ = lean_ctor_get(v_x_1010_, 2);
lean_inc_ref(v_trailing_1021_);
v_endPos_1022_ = lean_ctor_get(v_x_1010_, 3);
lean_inc(v_endPos_1022_);
lean_dec_ref_known(v_x_1010_, 4);
v___x_1057_ = lean_unsigned_to_nat(1024u);
v___x_1058_ = lean_nat_dec_le(v___x_1057_, v_prec_1011_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1024_ = v___x_1059_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1024_ = v___x_1060_;
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1025_ = lean_box(1);
v___x_1026_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__4));
v___x_1027_ = lean_substring_tostring(v_leading_1019_);
v___x_1028_ = l_String_quote(v___x_1027_);
v___x_1029_ = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1026_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_1025_);
v___x_1034_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_1035_ = l_Nat_reprFast(v_pos_1020_);
v___x_1036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1034_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1033_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1025_);
v___x_1042_ = lean_substring_tostring(v_trailing_1021_);
v___x_1043_ = l_String_quote(v___x_1042_);
v___x_1044_ = lean_string_append(v___x_1043_, v___x_1029_);
v___x_1045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1041_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1025_);
v___x_1048_ = l_Nat_reprFast(v_endPos_1022_);
v___x_1049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1034_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1038_);
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1047_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
lean_inc(v___y_1024_);
v___x_1053_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1024_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = 0;
v___x_1055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*1, v___x_1054_);
v___x_1056_ = l_Repr_addAppParen(v___x_1055_, v_prec_1011_);
return v___x_1056_;
}
}
case 1:
{
lean_object* v_pos_1061_; lean_object* v_endPos_1062_; uint8_t v_canonical_1063_; lean_object* v___y_1065_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_pos_1061_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_pos_1061_);
v_endPos_1062_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_endPos_1062_);
v_canonical_1063_ = lean_ctor_get_uint8(v_x_1010_, sizeof(void*)*2);
lean_dec_ref_known(v_x_1010_, 2);
v___x_1088_ = lean_unsigned_to_nat(1024u);
v___x_1089_ = lean_nat_dec_le(v___x_1088_, v_prec_1011_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1065_ = v___x_1090_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1065_ = v___x_1091_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1066_ = lean_box(1);
v___x_1067_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__9));
v___x_1068_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_1069_ = l_Nat_reprFast(v_pos_1061_);
v___x_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1068_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1067_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1066_);
v___x_1076_ = l_Nat_reprFast(v_endPos_1062_);
v___x_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1068_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1072_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1075_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1066_);
v___x_1082_ = l_Bool_repr___redArg(v_canonical_1063_);
v___x_1083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
lean_inc(v___y_1065_);
v___x_1084_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___y_1065_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = 0;
v___x_1086_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set_uint8(v___x_1086_, sizeof(void*)*1, v___x_1085_);
v___x_1087_ = l_Repr_addAppParen(v___x_1086_, v_prec_1011_);
return v___x_1087_;
}
}
default: 
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(1024u);
v___x_1093_ = lean_nat_dec_le(v___x_1092_, v_prec_1011_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1013_ = v___x_1094_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1013_ = v___x_1095_;
goto v___jp_1012_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1014_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__1));
lean_inc(v___y_1013_);
v___x_1015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___y_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = 0;
v___x_1017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v___x_1016_);
v___x_1018_ = l_Repr_addAppParen(v___x_1017_, v_prec_1011_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr___boxed(lean_object* v_x_1096_, lean_object* v_prec_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_instReprSourceInfo_repr(v_x_1096_, v_prec_1097_);
lean_dec(v_prec_1097_);
return v_res_1098_;
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
