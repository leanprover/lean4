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
LEAN_EXPORT lean_object* l_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Repr_addAppParen_spec__0(lean_object*);
static const lean_string_object l_Repr_addAppParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Repr_addAppParen___closed__0 = (const lean_object*)&l_Repr_addAppParen___closed__0_value;
static const lean_string_object l_Repr_addAppParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Repr_addAppParen___closed__1 = (const lean_object*)&l_Repr_addAppParen___closed__1_value;
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l_Repr_addAppParen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Repr_addAppParen___closed__2;
static lean_once_cell_t l_Repr_addAppParen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Repr_addAppParen___closed__3;
static const lean_ctor_object l_Repr_addAppParen___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Repr_addAppParen___closed__0_value)}};
static const lean_object* l_Repr_addAppParen___closed__4 = (const lean_object*)&l_Repr_addAppParen___closed__4_value;
static const lean_ctor_object l_Repr_addAppParen___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Repr_addAppParen___closed__1_value)}};
static const lean_object* l_Repr_addAppParen___closed__5 = (const lean_object*)&l_Repr_addAppParen___closed__5_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object*, lean_object*);
lean_object* lean_string_of_usize(size_t);
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
static lean_once_cell_t l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__0;
static lean_once_cell_t l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__1;
lean_object* lean_array_mk(lean_object*);
static lean_once_cell_t l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Repr_0__Nat_reprArray___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Nat_reprArray;
lean_object* lean_array_get_size(lean_object*);
static lean_once_cell_t l_Nat_reprFast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reprFast___closed__0;
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
static lean_once_cell_t l_Nat_reprFast___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Nat_reprFast___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Int_repr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instReprInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt___closed__0 = (const lean_object*)&l_instReprInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt = (const lean_object*)&l_instReprInt___closed__0_value;
static const lean_string_object l_hexDigitRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_hexDigitRepr___closed__0 = (const lean_object*)&l_hexDigitRepr___closed__0_value;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object*);
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
static lean_once_cell_t l_String_quote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_quote___closed__0;
static const lean_string_object l_String_quote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_String_quote___closed__1 = (const lean_object*)&l_String_quote___closed__1_value;
static const lean_string_object l_String_quote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\"\""};
static const lean_object* l_String_quote___closed__2 = (const lean_object*)&l_String_quote___closed__2_value;
uint8_t lean_string_isempty(lean_object*);
lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_substring_tostring(lean_object*);
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
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUInt8___closed__0 = (const lean_object*)&l_instReprUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUInt8 = (const lean_object*)&l_instReprUInt8___closed__0_value;
lean_object* lean_uint16_to_nat(uint16_t);
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
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprUInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprUInt64___closed__0 = (const lean_object*)&l_instReprUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprUInt64 = (const lean_object*)&l_instReprUInt64___closed__0_value;
lean_object* lean_usize_to_nat(size_t);
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
lean_object* l_Std_Format_fill(lean_object*);
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
LEAN_EXPORT lean_object* l_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_reprStr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = l_Std_Format_defWidth;
x_6 = l_Std_Format_pretty(x_4, x_5, x_3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_reprStr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = l_Std_Format_defWidth;
x_7 = l_Std_Format_pretty(x_5, x_6, x_4, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_reprArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_reprArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprId___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprId(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprId__1___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprId__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprId__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instReprEmpty___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprEmpty___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Bool_repr___redArg___closed__1));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Bool_repr___redArg___closed__3));
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_repr___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Bool_repr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Bool_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Bool_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Repr_addAppParen_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Repr_addAppParen___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Repr_addAppParen___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_obj_once(&l_Repr_addAppParen___closed__3, &l_Repr_addAppParen___closed__3_once, _init_l_Repr_addAppParen___closed__3);
x_6 = ((lean_object*)(l_Repr_addAppParen___closed__4));
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = ((lean_object*)(l_Repr_addAppParen___closed__5));
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Repr_addAppParen___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Repr_addAppParen(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Decidable_repr___redArg___closed__1));
x_4 = l_Repr_addAppParen(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l_Decidable_repr___redArg___closed__3));
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Decidable_repr___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Decidable_repr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Decidable_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Decidable_repr(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprDecidable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instReprDecidable___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_instReprPUnit___lam__0___closed__1));
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprPUnit___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprPUnit___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_instReprULift___redArg___lam__0___closed__1));
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_apply_2(x_1, x_2, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instReprULift___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprULift___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprULift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instReprULift___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_instReprUnit___lam__0___closed__1));
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprUnit___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprUnit___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Option_repr___redArg___closed__1));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = ((lean_object*)(l_Option_repr___redArg___closed__3));
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_repr___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Option_repr___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Option_repr(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_repr___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = ((lean_object*)(l_Sum_repr___redArg___closed__1));
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = ((lean_object*)(l_Sum_repr___redArg___closed__3));
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_apply_2(x_2, x_11, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Sum_repr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Sum_repr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Sum_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sum_repr___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Sum_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sum_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprSum___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Sum_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprTupleOfRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_2(x_1, x_6, x_8);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
x_10 = lean_apply_2(x_2, x_7, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_apply_2(x_1, x_11, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_apply_2(x_2, x_12, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Prod_reprTuple___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprTupleProdOfRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Prod_reprTuple), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Prod_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Repr_addAppParen___closed__2, &l_Repr_addAppParen___closed__2_once, _init_l_Repr_addAppParen___closed__2);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = ((lean_object*)(l_Prod_repr___redArg___closed__0));
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
x_11 = lean_apply_2(x_2, x_6, x_3);
x_12 = l_List_reverse___redArg(x_11);
x_13 = ((lean_object*)(l_Prod_repr___redArg___closed__3));
x_14 = l_Std_Format_joinSep___redArg(x_7, x_12, x_13);
x_15 = lean_obj_once(&l_Prod_repr___redArg___closed__4, &l_Prod_repr___redArg___closed__4_once, _init_l_Prod_repr___redArg___closed__4);
x_16 = ((lean_object*)(l_Repr_addAppParen___closed__4));
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = ((lean_object*)(l_Repr_addAppParen___closed__5));
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = 0;
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = ((lean_object*)(l_Prod_repr___redArg___closed__0));
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_apply_2(x_1, x_23, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_apply_2(x_2, x_24, x_29);
x_31 = l_List_reverse___redArg(x_30);
x_32 = ((lean_object*)(l_Prod_repr___redArg___closed__3));
x_33 = l_Std_Format_joinSep___redArg(x_25, x_31, x_32);
x_34 = lean_obj_once(&l_Prod_repr___redArg___closed__4, &l_Prod_repr___redArg___closed__4_once, _init_l_Prod_repr___redArg___closed__4);
x_35 = ((lean_object*)(l_Repr_addAppParen___closed__4));
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = ((lean_object*)(l_Repr_addAppParen___closed__5));
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Prod_repr___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Prod_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprProdOfReprTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Sigma_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Sigma_repr___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Sigma_repr___redArg___closed__4, &l_Sigma_repr___redArg___closed__4_once, _init_l_Sigma_repr___redArg___closed__4);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = ((lean_object*)(l_Sigma_repr___redArg___closed__2));
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
x_10 = lean_apply_3(x_2, x_5, x_6, x_7);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_obj_once(&l_Sigma_repr___redArg___closed__5, &l_Sigma_repr___redArg___closed__5_once, _init_l_Sigma_repr___redArg___closed__5);
x_13 = ((lean_object*)(l_Sigma_repr___redArg___closed__6));
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = ((lean_object*)(l_Sigma_repr___redArg___closed__7));
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
x_23 = lean_apply_2(x_1, x_20, x_22);
x_24 = ((lean_object*)(l_Sigma_repr___redArg___closed__2));
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_3(x_2, x_20, x_21, x_22);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_obj_once(&l_Sigma_repr___redArg___closed__5, &l_Sigma_repr___redArg___closed__5_once, _init_l_Sigma_repr___redArg___closed__5);
x_29 = ((lean_object*)(l_Sigma_repr___redArg___closed__6));
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = ((lean_object*)(l_Sigma_repr___redArg___closed__7));
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Sigma_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sigma_repr___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Sigma_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Sigma_repr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprSigma___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprSigma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprSubtype(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instReprSubtype___redArg___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Nat_digitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(10u);
x_23 = lean_nat_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(11u);
x_25 = lean_nat_dec_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(12u);
x_27 = lean_nat_dec_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(13u);
x_29 = lean_nat_dec_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(14u);
x_31 = lean_nat_dec_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(15u);
x_33 = lean_nat_dec_eq(x_1, x_32);
if (x_33 == 0)
{
uint32_t x_34; 
x_34 = 42;
return x_34;
}
else
{
uint32_t x_35; 
x_35 = 102;
return x_35;
}
}
else
{
uint32_t x_36; 
x_36 = 101;
return x_36;
}
}
else
{
uint32_t x_37; 
x_37 = 100;
return x_37;
}
}
else
{
uint32_t x_38; 
x_38 = 99;
return x_38;
}
}
else
{
uint32_t x_39; 
x_39 = 98;
return x_39;
}
}
else
{
uint32_t x_40; 
x_40 = 97;
return x_40;
}
}
else
{
uint32_t x_41; 
x_41 = 57;
return x_41;
}
}
else
{
uint32_t x_42; 
x_42 = 56;
return x_42;
}
}
else
{
uint32_t x_43; 
x_43 = 55;
return x_43;
}
}
else
{
uint32_t x_44; 
x_44 = 54;
return x_44;
}
}
else
{
uint32_t x_45; 
x_45 = 53;
return x_45;
}
}
else
{
uint32_t x_46; 
x_46 = 52;
return x_46;
}
}
else
{
uint32_t x_47; 
x_47 = 51;
return x_47;
}
}
else
{
uint32_t x_48; 
x_48 = 50;
return x_48;
}
}
else
{
uint32_t x_49; 
x_49 = 49;
return x_49;
}
}
else
{
uint32_t x_50; 
x_50 = 48;
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Nat_digitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_digitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_nat_mod(x_3, x_1);
x_8 = l_Nat_digitChar(x_7);
lean_dec(x_7);
x_9 = lean_nat_div(x_3, x_1);
lean_dec(x_3);
x_10 = lean_nat_dec_eq(x_9, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_13 = lean_box_uint32(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_2 = x_12;
x_3 = x_9;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_2);
x_16 = lean_box_uint32(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_toDigitsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_toDigitsCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Nat_toDigitsCore(x_1, x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_toDigits___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_toDigits(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_repr___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_string_of_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_8 = lean_string_of_usize(x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_13 = lean_string_of_usize(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = l_List_range(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__0, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0);
x_3 = l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__1, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Repr_0__Nat_reprArray(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Repr_0__Nat_reprArray___closed__2, &l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once, _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2);
return x_1;
}
}
static lean_object* _init_l_Nat_reprFast___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Repr_0__Nat_reprArray;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_reprFast___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_reprFast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Init_Data_Repr_0__Nat_reprArray;
x_3 = lean_obj_once(&l_Nat_reprFast___closed__0, &l_Nat_reprFast___closed__0_once, _init_l_Nat_reprFast___closed__0);
x_4 = lean_nat_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_obj_once(&l_Nat_reprFast___closed__1, &l_Nat_reprFast___closed__1_once, _init_l_Nat_reprFast___closed__1);
x_6 = lean_nat_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(10u);
x_8 = l_Nat_toDigits(x_7, x_1);
x_9 = lean_string_mk(x_8);
return x_9;
}
else
{
size_t x_10; lean_object* x_11; 
x_10 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_11 = lean_string_of_usize(x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_2, x_1);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT uint32_t l_Nat_superDigitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; 
x_22 = 42;
return x_22;
}
else
{
uint32_t x_23; 
x_23 = 8313;
return x_23;
}
}
else
{
uint32_t x_24; 
x_24 = 8312;
return x_24;
}
}
else
{
uint32_t x_25; 
x_25 = 8311;
return x_25;
}
}
else
{
uint32_t x_26; 
x_26 = 8310;
return x_26;
}
}
else
{
uint32_t x_27; 
x_27 = 8309;
return x_27;
}
}
else
{
uint32_t x_28; 
x_28 = 8308;
return x_28;
}
}
else
{
uint32_t x_29; 
x_29 = 179;
return x_29;
}
}
else
{
uint32_t x_30; 
x_30 = 178;
return x_30;
}
}
else
{
uint32_t x_31; 
x_31 = 185;
return x_31;
}
}
else
{
uint32_t x_32; 
x_32 = 8304;
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Nat_superDigitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_superDigitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigitsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_nat_mod(x_1, x_3);
x_5 = l_Nat_superDigitChar(x_4);
lean_dec(x_4);
x_6 = lean_nat_div(x_1, x_3);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box_uint32(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_box_uint32(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Nat_toSuperDigitsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSuperscriptString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_toSuperDigits(x_1);
x_3 = lean_string_mk(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Nat_subDigitChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_nat_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; 
x_22 = 42;
return x_22;
}
else
{
uint32_t x_23; 
x_23 = 8329;
return x_23;
}
}
else
{
uint32_t x_24; 
x_24 = 8328;
return x_24;
}
}
else
{
uint32_t x_25; 
x_25 = 8327;
return x_25;
}
}
else
{
uint32_t x_26; 
x_26 = 8326;
return x_26;
}
}
else
{
uint32_t x_27; 
x_27 = 8325;
return x_27;
}
}
else
{
uint32_t x_28; 
x_28 = 8324;
return x_28;
}
}
else
{
uint32_t x_29; 
x_29 = 8323;
return x_29;
}
}
else
{
uint32_t x_30; 
x_30 = 8322;
return x_30;
}
}
else
{
uint32_t x_31; 
x_31 = 8321;
return x_31;
}
}
else
{
uint32_t x_32; 
x_32 = 8320;
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Nat_subDigitChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_subDigitChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigitsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_nat_mod(x_1, x_3);
x_5 = l_Nat_subDigitChar(x_4);
lean_dec(x_4);
x_6 = lean_nat_div(x_1, x_3);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box_uint32(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_1 = x_6;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_box_uint32(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_toSubDigits(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Nat_toSubDigitsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_toSubscriptString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_toSubDigits(x_1);
x_3 = lean_string_mk(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprNat___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_repr___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_Int_repr___closed__0, &l_Int_repr___closed__0_once, _init_l_Int_repr___closed__0);
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = l_Nat_reprFast(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = ((lean_object*)(l_Int_repr___closed__1));
x_10 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_11 = l_Nat_reprFast(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Int_repr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_repr(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_obj_once(&l_Int_repr___closed__0, &l_Int_repr___closed__0_once, _init_l_Int_repr___closed__0);
x_4 = lean_int_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Int_repr(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Int_repr(x_1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Repr_addAppParen(x_8, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprInt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_digitChar(x_1);
x_3 = ((lean_object*)(l_hexDigitRepr___closed__0));
x_4 = lean_string_push(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_hexDigitRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_hexDigitRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_nat_shiftr(x_2, x_4);
x_6 = lean_nat_mod(x_2, x_3);
lean_dec(x_2);
x_7 = l_hexDigitRepr(x_5);
lean_dec(x_5);
x_8 = l_hexDigitRepr(x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore(uint32_t x_1, uint8_t x_2) {
_start:
{
uint32_t x_15; uint8_t x_16; 
x_15 = 10;
x_16 = lean_uint32_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 9;
x_18 = lean_uint32_dec_eq(x_1, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 92;
x_20 = lean_uint32_dec_eq(x_1, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 34;
x_22 = lean_uint32_dec_eq(x_1, x_21);
if (x_22 == 0)
{
if (x_2 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 39;
x_24 = lean_uint32_dec_eq(x_1, x_23);
if (x_24 == 0)
{
goto block_14;
}
else
{
lean_object* x_25; 
x_25 = ((lean_object*)(l_Char_quoteCore___closed__1));
return x_25;
}
}
else
{
goto block_14;
}
}
else
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_Char_quoteCore___closed__2));
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = ((lean_object*)(l_Char_quoteCore___closed__3));
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = ((lean_object*)(l_Char_quoteCore___closed__4));
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = ((lean_object*)(l_Char_quoteCore___closed__5));
return x_29;
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(l_Char_quoteCore___closed__0));
x_4 = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(x_1);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_uint32_to_nat(x_1);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_nat_dec_le(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 127;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = ((lean_object*)(l_hexDigitRepr___closed__0));
x_13 = lean_string_push(x_12, x_1);
return x_13;
}
else
{
goto block_6;
}
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Char_quoteCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Char_quoteCore(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Char_quote(uint32_t x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = ((lean_object*)(l_Char_quote___closed__0));
x_3 = 0;
x_4 = l_Char_quoteCore(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = lean_string_append(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Char_quote___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_quote(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_quote(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_instReprChar___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Char_repr(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Char_quote(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Char_repr___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_repr(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_quote___lam__0(uint8_t x_1, lean_object* x_2, uint32_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Char_quoteCore(x_3, x_1);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_quote___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint32_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_String_quote___lam__0(x_4, x_2, x_5);
return x_6;
}
}
static lean_object* _init_l_String_quote___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_String_quote___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_quote(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = lean_string_isempty(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_obj_once(&l_String_quote___closed__0, &l_String_quote___closed__0_once, _init_l_String_quote___closed__0);
x_4 = ((lean_object*)(l_String_quote___closed__1));
x_5 = lean_string_foldl(x_3, x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_1);
x_7 = ((lean_object*)(l_String_quote___closed__2));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_quote(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprString___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprString___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instReprRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprRaw___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_substring_tostring(x_1);
x_4 = l_String_quote(x_3);
x_5 = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instReprRaw__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprRaw__1___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprFin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprFin___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instReprFin___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instReprFin(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint8_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprUInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprUInt8___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint16_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprUInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprUInt16___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint32_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprUInt32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_instReprUInt32___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint64_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprUInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_instReprUInt64___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_usize_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprUSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_instReprUSize___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_List_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_repr___redArg___closed__2));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_List_repr___redArg___closed__4, &l_List_repr___redArg___closed__4_once, _init_l_List_repr___redArg___closed__4);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l_List_repr___redArg___closed__1));
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
x_5 = ((lean_object*)(l_Prod_repr___redArg___closed__3));
x_6 = l_Std_Format_joinSep___redArg(x_4, x_2, x_5);
x_7 = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
x_8 = ((lean_object*)(l_List_repr___redArg___closed__6));
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = ((lean_object*)(l_List_repr___redArg___closed__7));
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_repr___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_repr(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instReprList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_repr___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l_List_repr___redArg___closed__1));
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
x_5 = ((lean_object*)(l_Prod_repr___redArg___closed__3));
x_6 = l_Std_Format_joinSep___redArg(x_4, x_2, x_5);
x_7 = lean_obj_once(&l_List_repr___redArg___closed__5, &l_List_repr___redArg___closed__5_once, _init_l_List_repr___redArg___closed__5);
x_8 = ((lean_object*)(l_List_repr___redArg___closed__6));
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = ((lean_object*)(l_List_repr___redArg___closed__7));
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Format_fill(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_repr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_repr_x27___redArg(x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_repr_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
lean_closure_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprListOfReprAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_repr_x27___boxed), 5, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_instReprAtomBool(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomNat(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomInt(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomChar(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomString(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt8(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt16(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt32(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUInt64(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprAtomUSize(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_instReprSourceInfo_repr___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_48; uint8_t x_49; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec_ref(x_1);
x_48 = lean_unsigned_to_nat(1024u);
x_49 = lean_nat_dec_le(x_48, x_2);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
x_14 = x_50;
goto block_47;
}
else
{
lean_object* x_51; 
x_51 = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
x_14 = x_51;
goto block_47;
}
block_47:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_15 = lean_box(1);
x_16 = ((lean_object*)(l_instReprSourceInfo_repr___closed__4));
x_17 = lean_substring_tostring(x_10);
x_18 = l_String_quote(x_17);
x_19 = ((lean_object*)(l_instReprRaw__1___lam__0___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
x_24 = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
x_25 = l_Nat_reprFast(x_11);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_15);
x_32 = lean_substring_tostring(x_12);
x_33 = l_String_quote(x_32);
x_34 = lean_string_append(x_33, x_19);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_15);
x_38 = l_Nat_reprFast(x_13);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_42);
x_44 = 0;
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = l_Repr_addAppParen(x_45, x_2);
return x_46;
}
}
case 1:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_79; uint8_t x_80; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_79 = lean_unsigned_to_nat(1024u);
x_80 = lean_nat_dec_le(x_79, x_2);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
x_55 = x_81;
goto block_78;
}
else
{
lean_object* x_82; 
x_82 = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
x_55 = x_82;
goto block_78;
}
block_78:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_56 = lean_box(1);
x_57 = ((lean_object*)(l_instReprSourceInfo_repr___closed__9));
x_58 = ((lean_object*)(l_instReprRaw___lam__0___closed__1));
x_59 = l_Nat_reprFast(x_52);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = ((lean_object*)(l_instReprRaw___lam__0___closed__3));
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_56);
x_66 = l_Nat_reprFast(x_53);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_56);
x_72 = l_Bool_repr___redArg(x_54);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_55);
lean_ctor_set(x_74, 1, x_73);
x_75 = 0;
x_76 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = l_Repr_addAppParen(x_76, x_2);
return x_77;
}
}
default: 
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_unsigned_to_nat(1024u);
x_84 = lean_nat_dec_le(x_83, x_2);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_obj_once(&l_instReprSourceInfo_repr___closed__5, &l_instReprSourceInfo_repr___closed__5_once, _init_l_instReprSourceInfo_repr___closed__5);
x_3 = x_85;
goto block_9;
}
else
{
lean_object* x_86; 
x_86 = lean_obj_once(&l_instReprSourceInfo_repr___closed__6, &l_instReprSourceInfo_repr___closed__6_once, _init_l_instReprSourceInfo_repr___closed__6);
x_3 = x_86;
goto block_9;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_instReprSourceInfo_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instReprSourceInfo_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprSourceInfo_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
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
#ifdef __cplusplus
}
#endif
