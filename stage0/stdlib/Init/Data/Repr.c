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
static const lean_closure_object l_instReprDecidable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Decidable_repr___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instReprDecidable___redArg___closed__0 = (const lean_object*)&l_instReprDecidable___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instReprDecidable___redArg();
LEAN_EXPORT lean_object* l_instReprDecidable___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instReprFin___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprFin___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprFin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprFin___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprFin___redArg___closed__0 = (const lean_object*)&l_instReprFin___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instReprFin___redArg();
LEAN_EXPORT lean_object* l_instReprFin___redArg___boxed(lean_object*);
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
lean_object* l_instReprEmpty___lam__0(uint8_t v_a_64_, lean_object* v_a_65_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_instReprEmpty___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_64_ = stack[0].m_num;
lean_object* v_a_65_ = stack[1].m_obj;
lean_object* v_res_66_;
v_res_66_ = l_instReprEmpty___lam__0(v_a_64_, v_a_65_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
uint8_t v_a_8__boxed_69_; lean_object* v_res_70_; 
v_a_8__boxed_69_ = lean_unbox(v_a_67_);
v_res_70_ = l_instReprEmpty___lam__0(v_a_8__boxed_69_, v_a_68_);
lean_dec(v_a_68_);
return v_res_70_;
}
}
lean_object* l_Bool_repr___redArg(uint8_t v_x_79_){
_start:
{
if (v_x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = ((lean_object*)(l_Bool_repr___redArg___closed__1));
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Bool_repr___redArg___closed__3));
return v___x_81_;
}
}
}
LEAN_EXPORT void l_Bool_repr___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_79_ = stack[0].m_num;
lean_object* v_res_82_;
v_res_82_ = l_Bool_repr___redArg(v_x_79_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object* v_x_83_){
_start:
{
uint8_t v_x_36__boxed_84_; lean_object* v_res_85_; 
v_x_36__boxed_84_ = lean_unbox(v_x_83_);
v_res_85_ = l_Bool_repr___redArg(v_x_36__boxed_84_);
return v_res_85_;
}
}
lean_object* l_Bool_repr(uint8_t v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Bool_repr___redArg(v_x_86_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Bool_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_86_ = stack[0].m_num;
lean_object* v_x_87_ = stack[1].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Bool_repr(v_x_86_, v_x_87_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
uint8_t v_x_59__boxed_92_; lean_object* v_res_93_; 
v_x_59__boxed_92_ = lean_unbox(v_x_90_);
v_res_93_ = l_Bool_repr(v_x_59__boxed_92_, v_x_91_);
lean_dec(v_x_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Repr_addAppParen_spec__0(lean_object* v_a_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_nat_to_int(v_a_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__2(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Repr_addAppParen___closed__0));
v___x_101_ = lean_string_length(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__3(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object* v_f_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_109_);
if (v___x_111_ == 0)
{
return v_f_108_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_112_ = lean_obj_once(&l_Repr_addAppParen___closed__3, &l_Repr_addAppParen___closed__3_once, _init_l_Repr_addAppParen___closed__3);
v___x_113_ = ((lean_object*)(l_Repr_addAppParen___closed__4));
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_f_108_);
v___x_115_ = ((lean_object*)(l_Repr_addAppParen___closed__5));
v___x_116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_112_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object* v_f_120_, lean_object* v_prec_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Repr_addAppParen(v_f_120_, v_prec_121_);
lean_dec(v_prec_121_);
return v_res_122_;
}
}
lean_object* l_Decidable_repr___redArg(uint8_t v_x_129_, lean_object* v_x_130_){
_start:
{
if (v_x_129_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Decidable_repr___redArg___closed__1));
v___x_132_ = l_Repr_addAppParen(v___x_131_, v_x_130_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Decidable_repr___redArg___closed__3));
v___x_134_ = l_Repr_addAppParen(v___x_133_, v_x_130_);
return v___x_134_;
}
}
}
LEAN_EXPORT void l_Decidable_repr___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_129_ = stack[0].m_num;
lean_object* v_x_130_ = stack[1].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_Decidable_repr___redArg(v_x_129_, v_x_130_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_x_43__boxed_138_; lean_object* v_res_139_; 
v_x_43__boxed_138_ = lean_unbox(v_x_136_);
v_res_139_ = l_Decidable_repr___redArg(v_x_43__boxed_138_, v_x_137_);
lean_dec(v_x_137_);
return v_res_139_;
}
}
lean_object* l_Decidable_repr(lean_object* v_p_140_, uint8_t v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Decidable_repr___redArg(v_x_141_, v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT void l_Decidable_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_141_ = stack[1].m_num;
lean_object* v_x_142_ = stack[2].m_obj;
lean_object* v_res_144_;
v_res_144_ = l_Decidable_repr(lean_box(0), v_x_141_, v_x_142_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object* v_p_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_x_77__boxed_148_; lean_object* v_res_149_; 
v_x_77__boxed_148_ = lean_unbox(v_x_146_);
v_res_149_ = l_Decidable_repr(v_p_145_, v_x_77__boxed_148_, v_x_147_);
lean_dec(v_x_147_);
return v_res_149_;
}
}
lean_object* l_instReprDecidable___redArg(){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_instReprDecidable___redArg___closed__0));
return v___x_152_;
}
}
LEAN_EXPORT void l_instReprDecidable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_153_;
v_res_153_ = l_instReprDecidable___redArg();
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_instReprDecidable___redArg___boxed(lean_object* v___dummy_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_instReprDecidable___redArg();
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object* v_p_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_instReprDecidable___redArg___closed__0));
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_instReprPUnit___lam__0___closed__1));
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_instReprPUnit___lam__0(v_x_164_, v_x_165_);
lean_dec(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object* v_inst_172_, lean_object* v_v_173_, lean_object* v_prec_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_175_ = ((lean_object*)(l_instReprULift___redArg___lam__0___closed__1));
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_apply_2(v_inst_172_, v_v_173_, v___x_176_);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_175_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Repr_addAppParen(v___x_178_, v_prec_174_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object* v_inst_180_, lean_object* v_v_181_, lean_object* v_prec_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_instReprULift___redArg___lam__0(v_inst_180_, v_v_181_, v_prec_182_);
lean_dec(v_prec_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object* v_inst_184_){
_start:
{
lean_object* v___f_185_; 
v___f_185_ = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_185_, 0, v_inst_184_);
return v___f_185_;
}
}
LEAN_EXPORT lean_object* l_instReprULift(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_){
_start:
{
lean_object* v___f_188_; 
v___f_188_ = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_188_, 0, v_inst_187_);
return v___f_188_;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l_instReprUnit___lam__0___closed__1));
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_instReprUnit___lam__0(v_x_195_, v_x_196_);
lean_dec(v_x_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object* v_inst_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v_inst_206_);
v___x_209_ = ((lean_object*)(l_Option_repr___redArg___closed__1));
return v___x_209_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_val_210_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v_x_207_, 1);
v___x_211_ = ((lean_object*)(l_Option_repr___redArg___closed__3));
v___x_212_ = lean_unsigned_to_nat(1024u);
v___x_213_ = lean_apply_2(v_inst_206_, v_val_210_, v___x_212_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_211_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = l_Repr_addAppParen(v___x_214_, v_x_208_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object* v_inst_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Option_repr___redArg(v_inst_216_, v_x_217_, v_x_218_);
lean_dec(v_x_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Option_repr(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Option_repr___redArg(v_inst_221_, v_x_222_, v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Option_repr(v_00_u03b1_225_, v_inst_226_, v_x_227_, v_x_228_);
lean_dec(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object* v_inst_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(v___x_231_, 0, lean_box(0));
lean_closure_set(v___x_231_, 1, v_inst_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_instReprOption(lean_object* v_00_u03b1_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(v___x_234_, 0, lean_box(0));
lean_closure_set(v___x_234_, 1, v_inst_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v_val_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_inst_242_);
v_val_245_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v_x_243_, 1);
v___x_246_ = ((lean_object*)(l_Sum_repr___redArg___closed__1));
v___x_247_ = lean_unsigned_to_nat(1024u);
v___x_248_ = lean_apply_2(v_inst_241_, v_val_245_, v___x_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = l_Repr_addAppParen(v___x_249_, v_x_244_);
return v___x_250_;
}
else
{
lean_object* v_val_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_inst_241_);
v_val_251_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v_x_243_, 1);
v___x_252_ = ((lean_object*)(l_Sum_repr___redArg___closed__3));
v___x_253_ = lean_unsigned_to_nat(1024u);
v___x_254_ = lean_apply_2(v_inst_242_, v_val_251_, v___x_253_);
v___x_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_252_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Repr_addAppParen(v___x_255_, v_x_244_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Sum_repr___redArg(v_inst_257_, v_inst_258_, v_x_259_, v_x_260_);
lean_dec(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Sum_repr___redArg(v_inst_264_, v_inst_265_, v_x_266_, v_x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Sum_repr(v_00_u03b1_269_, v_00_u03b2_270_, v_inst_271_, v_inst_272_, v_x_273_, v_x_274_);
lean_dec(v_x_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object* v_inst_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(v___x_278_, 0, lean_box(0));
lean_closure_set(v___x_278_, 1, lean_box(0));
lean_closure_set(v___x_278_, 2, v_inst_276_);
lean_closure_set(v___x_278_, 3, v_inst_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_instReprSum(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_inst_281_, lean_object* v_inst_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(v___x_283_, 0, lean_box(0));
lean_closure_set(v___x_283_, 1, lean_box(0));
lean_closure_set(v___x_283_, 2, v_inst_281_);
lean_closure_set(v___x_283_, 3, v_inst_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object* v_inst_284_, lean_object* v_a_285_, lean_object* v_xs_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_apply_2(v_inst_284_, v_a_285_, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_xs_286_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object* v_inst_290_){
_start:
{
lean_object* v___f_291_; 
v___f_291_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_291_, 0, v_inst_290_);
return v___f_291_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_){
_start:
{
lean_object* v___f_294_; 
v___f_294_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_294_, 0, v_inst_293_);
return v___f_294_;
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v_fst_299_ = lean_ctor_get(v_x_297_, 0);
v_snd_300_ = lean_ctor_get(v_x_297_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v_x_297_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snd_300_);
lean_inc(v_fst_299_);
lean_dec(v_x_297_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_apply_2(v_inst_295_, v_fst_299_, v___x_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 1);
lean_ctor_set(v___x_302_, 1, v_x_298_);
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_x_298_);
v___x_307_ = v_reuseFailAlloc_309_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_apply_2(v_inst_296_, v_snd_300_, v___x_307_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Prod_reprTuple___redArg(v_inst_313_, v_inst_314_, v_x_315_, v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object* v_inst_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(v___x_320_, 0, lean_box(0));
lean_closure_set(v___x_320_, 1, lean_box(0));
lean_closure_set(v___x_320_, 2, v_inst_318_);
lean_closure_set(v___x_320_, 3, v_inst_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_inst_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, lean_box(0));
lean_closure_set(v___x_325_, 2, v_inst_323_);
lean_closure_set(v___x_325_, 3, v_inst_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_362_; 
v_fst_338_ = lean_ctor_get(v_x_337_, 0);
v_snd_339_ = lean_ctor_get(v_x_337_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_362_ == 0)
{
v___x_341_ = v_x_337_;
v_isShared_342_ = v_isSharedCheck_362_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_339_);
lean_inc(v_fst_338_);
lean_dec(v_x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_362_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___f_343_ = ((lean_object*)(l_Prod_repr___redArg___closed__0));
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_apply_2(v_inst_335_, v_fst_338_, v___x_344_);
v___x_346_ = lean_box(0);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
lean_ctor_set(v___x_341_, 1, v___x_346_);
lean_ctor_set(v___x_341_, 0, v___x_345_);
v___x_348_ = v___x_341_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_346_);
v___x_348_ = v_reuseFailAlloc_361_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_349_ = lean_apply_2(v_inst_336_, v_snd_339_, v___x_348_);
v___x_350_ = l_List_reverse___redArg(v___x_349_);
v___x_351_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_352_ = l_Std_Format_joinSep___redArg(v___f_343_, v___x_350_, v___x_351_);
v___x_353_ = lean_obj_once(&l_Prod_repr___redArg___closed__4, &l_Prod_repr___redArg___closed__4_once, _init_l_Prod_repr___redArg___closed__4);
v___x_354_ = ((lean_object*)(l_Repr_addAppParen___closed__4));
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_352_);
v___x_356_ = ((lean_object*)(l_Repr_addAppParen___closed__5));
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_353_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = 0;
v___x_360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*1, v___x_359_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Prod_repr___redArg(v_inst_365_, v_inst_366_, v_x_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Prod_repr(v_00_u03b1_370_, v_00_u03b2_371_, v_inst_372_, v_inst_373_, v_x_374_, v_x_375_);
lean_dec(v_x_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object* v_inst_377_, lean_object* v_inst_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_379_, 0, lean_box(0));
lean_closure_set(v___x_379_, 1, lean_box(0));
lean_closure_set(v___x_379_, 2, v_inst_377_);
lean_closure_set(v___x_379_, 3, v_inst_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_inst_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_384_, 0, lean_box(0));
lean_closure_set(v___x_384_, 1, lean_box(0));
lean_closure_set(v___x_384_, 2, v_inst_382_);
lean_closure_set(v___x_384_, 3, v_inst_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Sigma_repr___redArg___closed__0));
v___x_391_ = lean_string_length(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_obj_once(&l_Sigma_repr___redArg___closed__4, &l_Sigma_repr___redArg___closed__4_once, _init_l_Sigma_repr___redArg___closed__4);
v___x_393_ = lean_nat_to_int(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_x_400_){
_start:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_422_; 
v_fst_401_ = lean_ctor_get(v_x_400_, 0);
v_snd_402_ = lean_ctor_get(v_x_400_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_422_ == 0)
{
v___x_404_ = v_x_400_;
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_406_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_401_);
v___x_407_ = lean_apply_2(v_inst_398_, v_fst_401_, v___x_406_);
v___x_408_ = ((lean_object*)(l_Sigma_repr___redArg___closed__2));
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 5);
lean_ctor_set(v___x_404_, 1, v___x_408_);
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_421_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; 
v___x_411_ = lean_apply_3(v_inst_399_, v_fst_401_, v_snd_402_, v___x_406_);
v___x_412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_obj_once(&l_Sigma_repr___redArg___closed__5, &l_Sigma_repr___redArg___closed__5_once, _init_l_Sigma_repr___redArg___closed__5);
v___x_414_ = ((lean_object*)(l_Sigma_repr___redArg___closed__6));
v___x_415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_412_);
v___x_416_ = ((lean_object*)(l_Sigma_repr___redArg___closed__7));
v___x_417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_413_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = 0;
v___x_420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Sigma_repr___redArg(v_inst_425_, v_inst_426_, v_x_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Sigma_repr(v_00_u03b1_430_, v_00_u03b2_431_, v_inst_432_, v_inst_433_, v_x_434_, v_x_435_);
lean_dec(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object* v_inst_437_, lean_object* v_inst_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_439_, 0, lean_box(0));
lean_closure_set(v___x_439_, 1, lean_box(0));
lean_closure_set(v___x_439_, 2, v_inst_437_);
lean_closure_set(v___x_439_, 3, v_inst_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_instReprSigma(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_inst_442_, lean_object* v_inst_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_444_, 0, lean_box(0));
lean_closure_set(v___x_444_, 1, lean_box(0));
lean_closure_set(v___x_444_, 2, v_inst_442_);
lean_closure_set(v___x_444_, 3, v_inst_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object* v_inst_445_, lean_object* v_s_446_, lean_object* v_prec_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_apply_2(v_inst_445_, v_s_446_, v_prec_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object* v_inst_449_){
_start:
{
lean_object* v___f_450_; 
v___f_450_ = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(v___f_450_, 0, v_inst_449_);
return v___f_450_;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object* v_00_u03b1_451_, lean_object* v_p_452_, lean_object* v_inst_453_){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(v___f_454_, 0, v_inst_453_);
return v___f_454_;
}
}
uint32_t l_Nat_digitChar(lean_object* v_n_455_){
_start:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v_n_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_dec_eq(v_n_455_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(2u);
v___x_461_ = lean_nat_dec_eq(v_n_455_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(3u);
v___x_463_ = lean_nat_dec_eq(v_n_455_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(4u);
v___x_465_ = lean_nat_dec_eq(v_n_455_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(5u);
v___x_467_ = lean_nat_dec_eq(v_n_455_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(6u);
v___x_469_ = lean_nat_dec_eq(v_n_455_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(7u);
v___x_471_ = lean_nat_dec_eq(v_n_455_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(8u);
v___x_473_ = lean_nat_dec_eq(v_n_455_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(9u);
v___x_475_ = lean_nat_dec_eq(v_n_455_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(10u);
v___x_477_ = lean_nat_dec_eq(v_n_455_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(11u);
v___x_479_ = lean_nat_dec_eq(v_n_455_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(12u);
v___x_481_ = lean_nat_dec_eq(v_n_455_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(13u);
v___x_483_ = lean_nat_dec_eq(v_n_455_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(14u);
v___x_485_ = lean_nat_dec_eq(v_n_455_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(15u);
v___x_487_ = lean_nat_dec_eq(v_n_455_, v___x_486_);
if (v___x_487_ == 0)
{
uint32_t v___x_488_; 
v___x_488_ = 42;
return v___x_488_;
}
else
{
uint32_t v___x_489_; 
v___x_489_ = 102;
return v___x_489_;
}
}
else
{
uint32_t v___x_490_; 
v___x_490_ = 101;
return v___x_490_;
}
}
else
{
uint32_t v___x_491_; 
v___x_491_ = 100;
return v___x_491_;
}
}
else
{
uint32_t v___x_492_; 
v___x_492_ = 99;
return v___x_492_;
}
}
else
{
uint32_t v___x_493_; 
v___x_493_ = 98;
return v___x_493_;
}
}
else
{
uint32_t v___x_494_; 
v___x_494_ = 97;
return v___x_494_;
}
}
else
{
uint32_t v___x_495_; 
v___x_495_ = 57;
return v___x_495_;
}
}
else
{
uint32_t v___x_496_; 
v___x_496_ = 56;
return v___x_496_;
}
}
else
{
uint32_t v___x_497_; 
v___x_497_ = 55;
return v___x_497_;
}
}
else
{
uint32_t v___x_498_; 
v___x_498_ = 54;
return v___x_498_;
}
}
else
{
uint32_t v___x_499_; 
v___x_499_ = 53;
return v___x_499_;
}
}
else
{
uint32_t v___x_500_; 
v___x_500_ = 52;
return v___x_500_;
}
}
else
{
uint32_t v___x_501_; 
v___x_501_ = 51;
return v___x_501_;
}
}
else
{
uint32_t v___x_502_; 
v___x_502_ = 50;
return v___x_502_;
}
}
else
{
uint32_t v___x_503_; 
v___x_503_ = 49;
return v___x_503_;
}
}
else
{
uint32_t v___x_504_; 
v___x_504_ = 48;
return v___x_504_;
}
}
}
LEAN_EXPORT void l_Nat_digitChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_455_ = stack[0].m_obj;
uint32_t v_res_505_;
v_res_505_ = l_Nat_digitChar(v_n_455_);
stack->m_num = v_res_505_;
}
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object* v_n_506_){
_start:
{
uint32_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Nat_digitChar(v_n_506_);
lean_dec(v_n_506_);
v_r_508_ = lean_box_uint32(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object* v_base_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
lean_object* v_zero_513_; uint8_t v_isZero_514_; 
v_zero_513_ = lean_unsigned_to_nat(0u);
v_isZero_514_ = lean_nat_dec_eq(v_x_510_, v_zero_513_);
if (v_isZero_514_ == 1)
{
lean_dec(v_x_511_);
lean_dec(v_x_510_);
return v_x_512_;
}
else
{
lean_object* v___x_515_; uint32_t v_d_516_; lean_object* v_n_x27_517_; uint8_t v___x_518_; 
v___x_515_ = lean_nat_mod(v_x_511_, v_base_509_);
v_d_516_ = l_Nat_digitChar(v___x_515_);
lean_dec(v___x_515_);
v_n_x27_517_ = lean_nat_div(v_x_511_, v_base_509_);
lean_dec(v_x_511_);
v___x_518_ = lean_nat_dec_eq(v_n_x27_517_, v_zero_513_);
if (v___x_518_ == 0)
{
lean_object* v_one_519_; lean_object* v_n_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_one_519_ = lean_unsigned_to_nat(1u);
v_n_520_ = lean_nat_sub(v_x_510_, v_one_519_);
lean_dec(v_x_510_);
v___x_521_ = lean_box_uint32(v_d_516_);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_x_512_);
v_x_510_ = v_n_520_;
v_x_511_ = v_n_x27_517_;
v_x_512_ = v___x_522_;
goto _start;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_n_x27_517_);
lean_dec(v_x_510_);
v___x_524_ = lean_box_uint32(v_d_516_);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v_x_512_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object* v_base_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Nat_toDigitsCore(v_base_526_, v_x_527_, v_x_528_, v_x_529_);
lean_dec(v_base_526_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object* v_base_531_, lean_object* v_n_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_n_532_, v___x_533_);
v___x_535_ = lean_box(0);
v___x_536_ = l_Nat_toDigitsCore(v_base_531_, v___x_534_, v_n_532_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object* v_base_537_, lean_object* v_n_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Nat_toDigits(v_base_537_, v_n_538_);
lean_dec(v_base_537_);
return v_res_539_;
}
}
LEAN_EXPORT void l_USize_repr_0interp(lean_interpreter_value* stack)
{
size_t v_n_540_ = stack[0].m_num;
lean_object* v_res_541_;
v_res_541_ = lean_string_of_usize(v_n_540_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object* v_n_542_){
_start:
{
size_t v_n_boxed_543_; lean_object* v_res_544_; 
v_n_boxed_543_ = lean_unbox_usize(v_n_542_);
lean_dec(v_n_542_);
v_res_544_ = lean_string_of_usize(v_n_boxed_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = l_List_reverse___redArg(v_a_546_);
return v___x_547_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_head_548_ = lean_ctor_get(v_a_545_, 0);
v_tail_549_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_559_ == 0)
{
v___x_551_ = v_a_545_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_tail_549_);
lean_inc(v_head_548_);
lean_dec(v_a_545_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
size_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = lean_usize_of_nat(v_head_548_);
lean_dec(v_head_548_);
v___x_554_ = lean_string_of_usize(v___x_553_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_a_546_);
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_a_546_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
v_a_545_ = v_tail_549_;
v_a_546_ = v___x_556_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(128u);
v___x_561_ = l_List_range(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__0, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0);
v___x_564_ = l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(v___x_563_, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__1, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1);
v___x_566_ = lean_array_mk(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__2, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2);
return v___x_567_;
}
}
static lean_object* _init_l_Nat_reprFast___closed__0(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = l___private_Init_Data_Repr_0__Nat_reprArray;
v___x_569_ = lean_array_get_size(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Nat_reprFast___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = l_System_Platform_numBits;
v___x_571_ = lean_unsigned_to_nat(2u);
v___x_572_ = lean_nat_pow(v___x_571_, v___x_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object* v_n_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = l___private_Init_Data_Repr_0__Nat_reprArray;
v___x_575_ = lean_obj_once(&l_Nat_reprFast___closed__0, &l_Nat_reprFast___closed__0_once, _init_l_Nat_reprFast___closed__0);
v___x_576_ = lean_nat_dec_lt(v_n_573_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_obj_once(&l_Nat_reprFast___closed__1, &l_Nat_reprFast___closed__1_once, _init_l_Nat_reprFast___closed__1);
v___x_578_ = lean_nat_dec_lt(v_n_573_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(10u);
v___x_580_ = l_Nat_toDigits(v___x_579_, v_n_573_);
v___x_581_ = lean_string_mk(v___x_580_);
return v___x_581_;
}
else
{
size_t v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_usize_of_nat(v_n_573_);
lean_dec(v_n_573_);
v___x_583_ = lean_string_of_usize(v___x_582_);
return v___x_583_;
}
}
else
{
lean_object* v___x_584_; 
v___x_584_ = lean_array_fget_borrowed(v___x_574_, v_n_573_);
lean_dec(v_n_573_);
lean_inc(v___x_584_);
return v___x_584_;
}
}
}
uint32_t l_Nat_superDigitChar(lean_object* v_n_585_){
_start:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_nat_dec_eq(v_n_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_dec_eq(v_n_585_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(2u);
v___x_591_ = lean_nat_dec_eq(v_n_585_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(3u);
v___x_593_ = lean_nat_dec_eq(v_n_585_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(4u);
v___x_595_ = lean_nat_dec_eq(v_n_585_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(5u);
v___x_597_ = lean_nat_dec_eq(v_n_585_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(6u);
v___x_599_ = lean_nat_dec_eq(v_n_585_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(7u);
v___x_601_ = lean_nat_dec_eq(v_n_585_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(8u);
v___x_603_ = lean_nat_dec_eq(v_n_585_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(9u);
v___x_605_ = lean_nat_dec_eq(v_n_585_, v___x_604_);
if (v___x_605_ == 0)
{
uint32_t v___x_606_; 
v___x_606_ = 42;
return v___x_606_;
}
else
{
uint32_t v___x_607_; 
v___x_607_ = 8313;
return v___x_607_;
}
}
else
{
uint32_t v___x_608_; 
v___x_608_ = 8312;
return v___x_608_;
}
}
else
{
uint32_t v___x_609_; 
v___x_609_ = 8311;
return v___x_609_;
}
}
else
{
uint32_t v___x_610_; 
v___x_610_ = 8310;
return v___x_610_;
}
}
else
{
uint32_t v___x_611_; 
v___x_611_ = 8309;
return v___x_611_;
}
}
else
{
uint32_t v___x_612_; 
v___x_612_ = 8308;
return v___x_612_;
}
}
else
{
uint32_t v___x_613_; 
v___x_613_ = 179;
return v___x_613_;
}
}
else
{
uint32_t v___x_614_; 
v___x_614_ = 178;
return v___x_614_;
}
}
else
{
uint32_t v___x_615_; 
v___x_615_ = 185;
return v___x_615_;
}
}
else
{
uint32_t v___x_616_; 
v___x_616_ = 8304;
return v___x_616_;
}
}
}
LEAN_EXPORT void l_Nat_superDigitChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_585_ = stack[0].m_obj;
uint32_t v_res_617_;
v_res_617_ = l_Nat_superDigitChar(v_n_585_);
stack->m_num = v_res_617_;
}
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object* v_n_618_){
_start:
{
uint32_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Nat_superDigitChar(v_n_618_);
lean_dec(v_n_618_);
v_r_620_ = lean_box_uint32(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint32_t v_d_625_; lean_object* v_n_x27_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_623_ = lean_unsigned_to_nat(10u);
v___x_624_ = lean_nat_mod(v_x_621_, v___x_623_);
v_d_625_ = l_Nat_superDigitChar(v___x_624_);
lean_dec(v___x_624_);
v_n_x27_626_ = lean_nat_div(v_x_621_, v___x_623_);
lean_dec(v_x_621_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_eq(v_n_x27_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box_uint32(v_d_625_);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_x_622_);
v_x_621_ = v_n_x27_626_;
v_x_622_ = v___x_630_;
goto _start;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_n_x27_626_);
v___x_632_ = lean_box_uint32(v_d_625_);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_x_622_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object* v_n_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(0);
v___x_636_ = l_Nat_toSuperDigitsAux(v_n_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object* v_n_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = l_Nat_toSuperDigits(v_n_637_);
v___x_639_ = lean_string_mk(v___x_638_);
return v___x_639_;
}
}
uint32_t l_Nat_subDigitChar(lean_object* v_n_640_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_nat_dec_eq(v_n_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_dec_eq(v_n_640_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(2u);
v___x_646_ = lean_nat_dec_eq(v_n_640_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = lean_nat_dec_eq(v_n_640_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_nat_dec_eq(v_n_640_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(5u);
v___x_652_ = lean_nat_dec_eq(v_n_640_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(6u);
v___x_654_ = lean_nat_dec_eq(v_n_640_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(7u);
v___x_656_ = lean_nat_dec_eq(v_n_640_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(8u);
v___x_658_ = lean_nat_dec_eq(v_n_640_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(9u);
v___x_660_ = lean_nat_dec_eq(v_n_640_, v___x_659_);
if (v___x_660_ == 0)
{
uint32_t v___x_661_; 
v___x_661_ = 42;
return v___x_661_;
}
else
{
uint32_t v___x_662_; 
v___x_662_ = 8329;
return v___x_662_;
}
}
else
{
uint32_t v___x_663_; 
v___x_663_ = 8328;
return v___x_663_;
}
}
else
{
uint32_t v___x_664_; 
v___x_664_ = 8327;
return v___x_664_;
}
}
else
{
uint32_t v___x_665_; 
v___x_665_ = 8326;
return v___x_665_;
}
}
else
{
uint32_t v___x_666_; 
v___x_666_ = 8325;
return v___x_666_;
}
}
else
{
uint32_t v___x_667_; 
v___x_667_ = 8324;
return v___x_667_;
}
}
else
{
uint32_t v___x_668_; 
v___x_668_ = 8323;
return v___x_668_;
}
}
else
{
uint32_t v___x_669_; 
v___x_669_ = 8322;
return v___x_669_;
}
}
else
{
uint32_t v___x_670_; 
v___x_670_ = 8321;
return v___x_670_;
}
}
else
{
uint32_t v___x_671_; 
v___x_671_ = 8320;
return v___x_671_;
}
}
}
LEAN_EXPORT void l_Nat_subDigitChar_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_640_ = stack[0].m_obj;
uint32_t v_res_672_;
v_res_672_ = l_Nat_subDigitChar(v_n_640_);
stack->m_num = v_res_672_;
}
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object* v_n_673_){
_start:
{
uint32_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Nat_subDigitChar(v_n_673_);
lean_dec(v_n_673_);
v_r_675_ = lean_box_uint32(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; uint32_t v_d_680_; lean_object* v_n_x27_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_678_ = lean_unsigned_to_nat(10u);
v___x_679_ = lean_nat_mod(v_x_676_, v___x_678_);
v_d_680_ = l_Nat_subDigitChar(v___x_679_);
lean_dec(v___x_679_);
v_n_x27_681_ = lean_nat_div(v_x_676_, v___x_678_);
lean_dec(v_x_676_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_eq(v_n_x27_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_box_uint32(v_d_680_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v_x_677_);
v_x_676_ = v_n_x27_681_;
v_x_677_ = v___x_685_;
goto _start;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_n_x27_681_);
v___x_687_ = lean_box_uint32(v_d_680_);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v_x_677_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object* v_n_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Nat_toSubDigitsAux(v_n_689_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object* v_n_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Nat_toSubDigits(v_n_692_);
v___x_694_ = lean_string_mk(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object* v_n_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = l_Nat_reprFast(v_n_695_);
v___x_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object* v_n_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_instReprNat___lam__0(v_n_699_, v_x_700_);
lean_dec(v_x_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object* v_n_705_){
_start:
{
uint32_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = l_Nat_digitChar(v_n_705_);
v___x_707_ = ((lean_object*)(l_hexDigitRepr___closed__0));
v___x_708_ = lean_string_push(v___x_707_, v___x_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object* v_n_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_hexDigitRepr(v_n_709_);
lean_dec(v_n_709_);
return v_res_710_;
}
}
lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t v_c_711_){
_start:
{
lean_object* v_n_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_d2_715_; lean_object* v_d1_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_n_712_ = lean_uint32_to_nat(v_c_711_);
v___x_713_ = lean_unsigned_to_nat(16u);
v___x_714_ = lean_unsigned_to_nat(4u);
v_d2_715_ = lean_nat_shiftr(v_n_712_, v___x_714_);
v_d1_716_ = lean_nat_mod(v_n_712_, v___x_713_);
lean_dec(v_n_712_);
v___x_717_ = l_hexDigitRepr(v_d2_715_);
lean_dec(v_d2_715_);
v___x_718_ = l_hexDigitRepr(v_d1_716_);
lean_dec(v_d1_716_);
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
lean_dec_ref(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT void l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_711_ = stack[0].m_num;
lean_object* v_res_720_;
v_res_720_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_711_);
stack->m_obj
 = v_res_720_;
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
lean_object* l_Char_quoteCore(uint32_t v_c_730_, uint8_t v_inString_731_){
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
LEAN_EXPORT void l_Char_quoteCore_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_730_ = stack[0].m_num;
uint8_t v_inString_731_ = stack[1].m_num;
lean_object* v_res_759_;
v_res_759_ = l_Char_quoteCore(v_c_730_, v_inString_731_);
stack->m_obj
 = v_res_759_;
}
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object* v_c_760_, lean_object* v_inString_761_){
_start:
{
uint32_t v_c_boxed_762_; uint8_t v_inString_boxed_763_; lean_object* v_res_764_; 
v_c_boxed_762_ = lean_unbox_uint32(v_c_760_);
lean_dec(v_c_760_);
v_inString_boxed_763_ = lean_unbox(v_inString_761_);
v_res_764_ = l_Char_quoteCore(v_c_boxed_762_, v_inString_boxed_763_);
return v_res_764_;
}
}
lean_object* l_Char_quote(uint32_t v_c_766_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_767_ = ((lean_object*)(l_Char_quote___closed__0));
v___x_768_ = 0;
v___x_769_ = l_Char_quoteCore(v_c_766_, v___x_768_);
v___x_770_ = lean_string_append(v___x_767_, v___x_769_);
lean_dec_ref(v___x_769_);
v___x_771_ = lean_string_append(v___x_770_, v___x_767_);
return v___x_771_;
}
}
LEAN_EXPORT void l_Char_quote_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_766_ = stack[0].m_num;
lean_object* v_res_772_;
v_res_772_ = l_Char_quote(v_c_766_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object* v_c_773_){
_start:
{
uint32_t v_c_boxed_774_; lean_object* v_res_775_; 
v_c_boxed_774_ = lean_unbox_uint32(v_c_773_);
lean_dec(v_c_773_);
v_res_775_ = l_Char_quote(v_c_boxed_774_);
return v_res_775_;
}
}
lean_object* l_instReprChar___lam__0(uint32_t v_c_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = l_Char_quote(v_c_776_);
v___x_779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT void l_instReprChar___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_776_ = stack[0].m_num;
lean_object* v_x_777_ = stack[1].m_obj;
lean_object* v_res_780_;
v_res_780_ = l_instReprChar___lam__0(v_c_776_, v_x_777_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object* v_c_781_, lean_object* v_x_782_){
_start:
{
uint32_t v_c_boxed_783_; lean_object* v_res_784_; 
v_c_boxed_783_ = lean_unbox_uint32(v_c_781_);
lean_dec(v_c_781_);
v_res_784_ = l_instReprChar___lam__0(v_c_boxed_783_, v_x_782_);
lean_dec(v_x_782_);
return v_res_784_;
}
}
lean_object* l_Char_repr(uint32_t v_c_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Char_quote(v_c_787_);
return v___x_788_;
}
}
LEAN_EXPORT void l_Char_repr_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_787_ = stack[0].m_num;
lean_object* v_res_789_;
v_res_789_ = l_Char_repr(v_c_787_);
stack->m_obj
 = v_res_789_;
}
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object* v_c_790_){
_start:
{
uint32_t v_c_boxed_791_; lean_object* v_res_792_; 
v_c_boxed_791_ = lean_unbox_uint32(v_c_790_);
lean_dec(v_c_790_);
v_res_792_ = l_Char_repr(v_c_boxed_791_);
return v_res_792_;
}
}
lean_object* l_String_quote___lam__0(uint8_t v___x_793_, lean_object* v_s_794_, uint32_t v_c_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = l_Char_quoteCore(v_c_795_, v___x_793_);
v___x_797_ = lean_string_append(v_s_794_, v___x_796_);
lean_dec_ref(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT void l_String_quote___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_793_ = stack[0].m_num;
lean_object* v_s_794_ = stack[1].m_obj;
uint32_t v_c_795_ = stack[2].m_num;
lean_object* v_res_798_;
v_res_798_ = l_String_quote___lam__0(v___x_793_, v_s_794_, v_c_795_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l_String_quote___lam__0___boxed(lean_object* v___x_799_, lean_object* v_s_800_, lean_object* v_c_801_){
_start:
{
uint8_t v___x_21__boxed_802_; uint32_t v_c_boxed_803_; lean_object* v_res_804_; 
v___x_21__boxed_802_ = lean_unbox(v___x_799_);
v_c_boxed_803_ = lean_unbox_uint32(v_c_801_);
lean_dec(v_c_801_);
v_res_804_ = l_String_quote___lam__0(v___x_21__boxed_802_, v_s_800_, v_c_boxed_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_String_quote(lean_object* v_s_810_){
_start:
{
uint8_t v___x_811_; 
lean_inc_ref(v_s_810_);
v___x_811_ = lean_string_isempty(v_s_810_);
if (v___x_811_ == 0)
{
lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___f_812_ = ((lean_object*)(l_String_quote___closed__0));
v___x_813_ = ((lean_object*)(l_String_quote___closed__1));
v___x_814_ = lean_string_foldl(v___f_812_, v___x_813_, v_s_810_);
v___x_815_ = lean_string_append(v___x_814_, v___x_813_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; 
lean_dec_ref(v_s_810_);
v___x_816_ = ((lean_object*)(l_String_quote___closed__2));
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object* v_s_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = l_String_quote(v_s_817_);
v___x_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object* v_s_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_instReprString___lam__0(v_s_821_, v_x_822_);
lean_dec(v_x_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0(lean_object* v_p_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_835_ = l_Nat_reprFast(v_p_832_);
v___x_836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_834_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0___boxed(lean_object* v_p_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_instReprRaw___lam__0(v_p_840_, v_x_841_);
lean_dec(v_x_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0(lean_object* v_s_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_848_ = lean_substring_tostring(v_s_846_);
v___x_849_ = l_String_quote(v___x_848_);
v___x_850_ = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
v___x_851_ = lean_string_append(v___x_849_, v___x_850_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0___boxed(lean_object* v_s_853_, lean_object* v_x_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_instReprRaw__1___lam__0(v_s_853_, v_x_854_);
lean_dec(v_x_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___redArg___lam__0(lean_object* v_f_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = l_Nat_reprFast(v_f_858_);
v___x_861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___redArg___lam__0___boxed(lean_object* v_f_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_instReprFin___redArg___lam__0(v_f_862_, v_x_863_);
lean_dec(v_x_863_);
return v_res_864_;
}
}
lean_object* l_instReprFin___redArg(){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = ((lean_object*)(l_instReprFin___redArg___closed__0));
return v___f_867_;
}
}
LEAN_EXPORT void l_instReprFin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_868_;
v_res_868_ = l_instReprFin___redArg();
stack->m_obj
 = v_res_868_;
}
LEAN_EXPORT lean_object* l_instReprFin___redArg___boxed(lean_object* v___dummy_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_instReprFin___redArg();
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_instReprFin(lean_object* v_n_871_){
_start:
{
lean_object* v___f_872_; 
v___f_872_ = ((lean_object*)(l_instReprFin___redArg___closed__0));
return v___f_872_;
}
}
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object* v_n_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_instReprFin(v_n_873_);
lean_dec(v_n_873_);
return v_res_874_;
}
}
lean_object* l_instReprUInt8___lam__0(uint8_t v_n_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = lean_uint8_to_nat(v_n_875_);
v___x_878_ = l_Nat_reprFast(v___x_877_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l_instReprUInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_875_ = stack[0].m_num;
lean_object* v_x_876_ = stack[1].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_instReprUInt8___lam__0(v_n_875_, v_x_876_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object* v_n_881_, lean_object* v_x_882_){
_start:
{
uint8_t v_n_boxed_883_; lean_object* v_res_884_; 
v_n_boxed_883_ = lean_unbox(v_n_881_);
v_res_884_ = l_instReprUInt8___lam__0(v_n_boxed_883_, v_x_882_);
lean_dec(v_x_882_);
return v_res_884_;
}
}
lean_object* l_instReprUInt16___lam__0(uint16_t v_n_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_uint16_to_nat(v_n_887_);
v___x_890_ = l_Nat_reprFast(v___x_889_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT void l_instReprUInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_887_ = stack[0].m_num;
lean_object* v_x_888_ = stack[1].m_obj;
lean_object* v_res_892_;
v_res_892_ = l_instReprUInt16___lam__0(v_n_887_, v_x_888_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object* v_n_893_, lean_object* v_x_894_){
_start:
{
uint16_t v_n_boxed_895_; lean_object* v_res_896_; 
v_n_boxed_895_ = lean_unbox(v_n_893_);
v_res_896_ = l_instReprUInt16___lam__0(v_n_boxed_895_, v_x_894_);
lean_dec(v_x_894_);
return v_res_896_;
}
}
lean_object* l_instReprUInt32___lam__0(uint32_t v_n_899_, lean_object* v_x_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_uint32_to_nat(v_n_899_);
v___x_902_ = l_Nat_reprFast(v___x_901_);
v___x_903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT void l_instReprUInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_899_ = stack[0].m_num;
lean_object* v_x_900_ = stack[1].m_obj;
lean_object* v_res_904_;
v_res_904_ = l_instReprUInt32___lam__0(v_n_899_, v_x_900_);
stack->m_obj
 = v_res_904_;
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object* v_n_905_, lean_object* v_x_906_){
_start:
{
uint32_t v_n_boxed_907_; lean_object* v_res_908_; 
v_n_boxed_907_ = lean_unbox_uint32(v_n_905_);
lean_dec(v_n_905_);
v_res_908_ = l_instReprUInt32___lam__0(v_n_boxed_907_, v_x_906_);
lean_dec(v_x_906_);
return v_res_908_;
}
}
lean_object* l_instReprUInt64___lam__0(uint64_t v_n_911_, lean_object* v_x_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_uint64_to_nat(v_n_911_);
v___x_914_ = l_Nat_reprFast(v___x_913_);
v___x_915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT void l_instReprUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_911_ = stack[0].m_num;
lean_object* v_x_912_ = stack[1].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_instReprUInt64___lam__0(v_n_911_, v_x_912_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object* v_n_917_, lean_object* v_x_918_){
_start:
{
uint64_t v_n_boxed_919_; lean_object* v_res_920_; 
v_n_boxed_919_ = lean_unbox_uint64(v_n_917_);
lean_dec_ref(v_n_917_);
v_res_920_ = l_instReprUInt64___lam__0(v_n_boxed_919_, v_x_918_);
lean_dec(v_x_918_);
return v_res_920_;
}
}
lean_object* l_instReprUSize___lam__0(size_t v_n_923_, lean_object* v_x_924_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_usize_to_nat(v_n_923_);
v___x_926_ = l_Nat_reprFast(v___x_925_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT void l_instReprUSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_n_923_ = stack[0].m_num;
lean_object* v_x_924_ = stack[1].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_instReprUSize___lam__0(v_n_923_, v_x_924_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object* v_n_929_, lean_object* v_x_930_){
_start:
{
size_t v_n_boxed_931_; lean_object* v_res_932_; 
v_n_boxed_931_ = lean_unbox_usize(v_n_929_);
lean_dec(v_n_929_);
v_res_932_ = l_instReprUSize___lam__0(v_n_boxed_931_, v_x_930_);
lean_dec(v_x_930_);
return v_res_932_;
}
}
static lean_object* _init_l_List_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_List_repr___redArg___closed__2));
v___x_941_ = lean_string_length(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_List_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l_List_repr___redArg___closed__4, &l_List_repr___redArg___closed__4_once, _init_l_List_repr___redArg___closed__4);
v___x_943_ = lean_nat_to_int(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object* v_inst_948_, lean_object* v_a_949_){
_start:
{
if (lean_obj_tag(v_a_949_) == 0)
{
lean_object* v___x_950_; 
lean_dec_ref(v_inst_948_);
v___x_950_ = ((lean_object*)(l_List_repr___redArg___closed__1));
return v___x_950_;
}
else
{
lean_object* v_x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; 
v_x_951_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_951_, 0, lean_box(0));
lean_closure_set(v_x_951_, 1, v_inst_948_);
v___x_952_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_953_ = l_Std_Format_joinSep___redArg(v_x_951_, v_a_949_, v___x_952_);
v___x_954_ = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
v___x_955_ = ((lean_object*)(l_List_repr___redArg___closed__6));
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_953_);
v___x_957_ = ((lean_object*)(l_List_repr___redArg___closed__7));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_954_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = 0;
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_List_repr(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_a_964_, lean_object* v_n_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_List_repr___redArg(v_inst_963_, v_a_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object* v_00_u03b1_967_, lean_object* v_inst_968_, lean_object* v_a_969_, lean_object* v_n_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_List_repr(v_00_u03b1_967_, v_inst_968_, v_a_969_, v_n_970_);
lean_dec(v_n_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object* v_inst_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(v___x_973_, 0, lean_box(0));
lean_closure_set(v___x_973_, 1, v_inst_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_instReprList(lean_object* v_00_u03b1_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(v___x_976_, 0, lean_box(0));
lean_closure_set(v___x_976_, 1, v_inst_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object* v_inst_977_, lean_object* v_a_978_){
_start:
{
if (lean_obj_tag(v_a_978_) == 0)
{
lean_object* v___x_979_; 
lean_dec_ref(v_inst_977_);
v___x_979_ = ((lean_object*)(l_List_repr___redArg___closed__1));
return v___x_979_;
}
else
{
lean_object* v_x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_x_980_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_980_, 0, lean_box(0));
lean_closure_set(v_x_980_, 1, v_inst_977_);
v___x_981_ = ((lean_object*)(l_Prod_repr___redArg___closed__3));
v___x_982_ = l_Std_Format_joinSep___redArg(v_x_980_, v_a_978_, v___x_981_);
v___x_983_ = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
v___x_984_ = ((lean_object*)(l_List_repr___redArg___closed__6));
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_982_);
v___x_986_ = ((lean_object*)(l_List_repr___redArg___closed__7));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_983_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Std_Format_fill(v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object* v_00_u03b1_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_a_993_, lean_object* v_n_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_List_repr_x27___redArg(v_inst_991_, v_a_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object* v_00_u03b1_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_a_999_, lean_object* v_n_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_List_repr_x27(v_00_u03b1_996_, v_inst_997_, v_inst_998_, v_a_999_, v_n_1000_);
lean_dec(v_n_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(v___x_1004_, 0, lean_box(0));
lean_closure_set(v___x_1004_, 1, v_inst_1002_);
lean_closure_set(v___x_1004_, 2, v_inst_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(v___x_1008_, 0, lean_box(0));
lean_closure_set(v___x_1008_, 1, v_inst_1006_);
lean_closure_set(v___x_1008_, 2, v_inst_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_instReprAtomBool(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_box(0);
return v___x_1009_;
}
}
static lean_object* _init_l_instReprAtomNat(void){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_box(0);
return v___x_1010_;
}
}
static lean_object* _init_l_instReprAtomInt(void){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_box(0);
return v___x_1011_;
}
}
static lean_object* _init_l_instReprAtomChar(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_box(0);
return v___x_1012_;
}
}
static lean_object* _init_l_instReprAtomString(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_box(0);
return v___x_1013_;
}
}
static lean_object* _init_l_instReprAtomUInt8(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
}
static lean_object* _init_l_instReprAtomUInt16(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_box(0);
return v___x_1015_;
}
}
static lean_object* _init_l_instReprAtomUInt32(void){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_box(0);
return v___x_1016_;
}
}
static lean_object* _init_l_instReprAtomUInt64(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_box(0);
return v___x_1017_;
}
}
static lean_object* _init_l_instReprAtomUSize(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__5(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_unsigned_to_nat(2u);
v___x_1029_ = lean_nat_to_int(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__6(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_to_int(v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr(lean_object* v_x_1038_, lean_object* v_prec_1039_){
_start:
{
lean_object* v___y_1041_; 
switch(lean_obj_tag(v_x_1038_))
{
case 0:
{
lean_object* v_leading_1047_; lean_object* v_pos_1048_; lean_object* v_trailing_1049_; lean_object* v_endPos_1050_; lean_object* v___y_1052_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_leading_1047_ = lean_ctor_get(v_x_1038_, 0);
lean_inc_ref(v_leading_1047_);
v_pos_1048_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_pos_1048_);
v_trailing_1049_ = lean_ctor_get(v_x_1038_, 2);
lean_inc_ref(v_trailing_1049_);
v_endPos_1050_ = lean_ctor_get(v_x_1038_, 3);
lean_inc(v_endPos_1050_);
lean_dec_ref_known(v_x_1038_, 4);
v___x_1085_ = lean_unsigned_to_nat(1024u);
v___x_1086_ = lean_nat_dec_le(v___x_1085_, v_prec_1039_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1052_ = v___x_1087_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1052_ = v___x_1088_;
goto v___jp_1051_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1053_ = lean_box(1);
v___x_1054_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__4));
v___x_1055_ = lean_substring_tostring(v_leading_1047_);
v___x_1056_ = l_String_quote(v___x_1055_);
v___x_1057_ = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
v___x_1058_ = lean_string_append(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1054_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1053_);
v___x_1062_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_1063_ = l_Nat_reprFast(v_pos_1048_);
v___x_1064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1061_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1053_);
v___x_1070_ = lean_substring_tostring(v_trailing_1049_);
v___x_1071_ = l_String_quote(v___x_1070_);
v___x_1072_ = lean_string_append(v___x_1071_, v___x_1057_);
v___x_1073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1069_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1053_);
v___x_1076_ = l_Nat_reprFast(v_endPos_1050_);
v___x_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1062_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1066_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1075_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
lean_inc(v___y_1052_);
v___x_1081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1052_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = 0;
v___x_1083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
v___x_1084_ = l_Repr_addAppParen(v___x_1083_, v_prec_1039_);
return v___x_1084_;
}
}
case 1:
{
lean_object* v_pos_1089_; lean_object* v_endPos_1090_; uint8_t v_canonical_1091_; lean_object* v___y_1093_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_pos_1089_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_pos_1089_);
v_endPos_1090_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_endPos_1090_);
v_canonical_1091_ = lean_ctor_get_uint8(v_x_1038_, sizeof(void*)*2);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1116_ = lean_unsigned_to_nat(1024u);
v___x_1117_ = lean_nat_dec_le(v___x_1116_, v_prec_1039_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1093_ = v___x_1118_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1093_ = v___x_1119_;
goto v___jp_1092_;
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1094_ = lean_box(1);
v___x_1095_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__9));
v___x_1096_ = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
v___x_1097_ = l_Nat_reprFast(v_pos_1089_);
v___x_1098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1096_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
v___x_1101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1095_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1094_);
v___x_1104_ = l_Nat_reprFast(v_endPos_1090_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1096_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1100_);
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1103_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1094_);
v___x_1110_ = l_Bool_repr___redArg(v_canonical_1091_);
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_inc(v___y_1093_);
v___x_1112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1093_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = 0;
v___x_1114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*1, v___x_1113_);
v___x_1115_ = l_Repr_addAppParen(v___x_1114_, v_prec_1039_);
return v___x_1115_;
}
}
default: 
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_unsigned_to_nat(1024u);
v___x_1121_ = lean_nat_dec_le(v___x_1120_, v_prec_1039_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
v___y_1041_ = v___x_1122_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
v___y_1041_ = v___x_1123_;
goto v___jp_1040_;
}
}
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1042_ = ((lean_object*)(l_instReprSourceInfo_repr___closed__1));
lean_inc(v___y_1041_);
v___x_1043_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___y_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = 0;
v___x_1045_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*1, v___x_1044_);
v___x_1046_ = l_Repr_addAppParen(v___x_1045_, v_prec_1039_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr___boxed(lean_object* v_x_1124_, lean_object* v_prec_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_instReprSourceInfo_repr(v_x_1124_, v_prec_1125_);
lean_dec(v_prec_1125_);
return v_res_1126_;
}
}
lean_object* runtime_initialize_Init_Data_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
