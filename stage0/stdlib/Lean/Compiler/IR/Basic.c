// Lean compiler output
// Module: Lean.Compiler.IR.Basic
// Imports: public import Lean.Compiler.ExternAttr import Init.Data.Range.Polymorphic.Iterators
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedVarId_default;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedVarId;
LEAN_EXPORT uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqVarId___closed__0 = (const lean_object*)&l_Lean_IR_instBEqVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqVarId = (const lean_object*)&l_Lean_IR_instBEqVarId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_IR_instHashableVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_IR_instHashableVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instHashableVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instHashableVarId___closed__0 = (const lean_object*)&l_Lean_IR_instHashableVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instHashableVarId = (const lean_object*)&l_Lean_IR_instHashableVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_instReprVarId_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_instReprVarId_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__0 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_IR_instReprVarId_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__1 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_IR_instReprVarId_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__2 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_IR_instReprVarId_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__3 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_IR_instReprVarId_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__4 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_IR_instReprVarId_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__5 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_IR_instReprVarId_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__3_value),((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__6 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_IR_instReprVarId_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__7;
static const lean_string_object l_Lean_IR_instReprVarId_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__8 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_IR_instReprVarId_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_IR_instReprVarId_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_IR_instReprVarId_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__11 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_IR_instReprVarId_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_IR_instReprVarId_repr___redArg___closed__12 = (const lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instReprVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instReprVarId_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instReprVarId___closed__0 = (const lean_object*)&l_Lean_IR_instReprVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instReprVarId = (const lean_object*)&l_Lean_IR_instReprVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedJoinPointId_default;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedJoinPointId;
LEAN_EXPORT uint8_t l_Lean_IR_instBEqJoinPointId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqJoinPointId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqJoinPointId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqJoinPointId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqJoinPointId___closed__0 = (const lean_object*)&l_Lean_IR_instBEqJoinPointId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqJoinPointId = (const lean_object*)&l_Lean_IR_instBEqJoinPointId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_IR_instHashableJoinPointId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instHashableJoinPointId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_IR_instHashableJoinPointId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instHashableJoinPointId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instHashableJoinPointId___closed__0 = (const lean_object*)&l_Lean_IR_instHashableJoinPointId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instHashableJoinPointId = (const lean_object*)&l_Lean_IR_instHashableJoinPointId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instReprJoinPointId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instReprJoinPointId_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instReprJoinPointId___closed__0 = (const lean_object*)&l_Lean_IR_instReprJoinPointId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instReprJoinPointId = (const lean_object*)&l_Lean_IR_instReprJoinPointId___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_Index_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Index_lt___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_instToStringVarId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "x_"};
static const lean_object* l_Lean_IR_instToStringVarId___lam__0___closed__0 = (const lean_object*)&l_Lean_IR_instToStringVarId___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToStringVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToStringVarId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToStringVarId___closed__0 = (const lean_object*)&l_Lean_IR_instToStringVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToStringVarId = (const lean_object*)&l_Lean_IR_instToStringVarId___closed__0_value;
static const lean_string_object l_Lean_IR_instToStringJoinPointId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "block_"};
static const lean_object* l_Lean_IR_instToStringJoinPointId___lam__0___closed__0 = (const lean_object*)&l_Lean_IR_instToStringJoinPointId___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId___lam__0(lean_object*);
static const lean_closure_object l_Lean_IR_instToStringJoinPointId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instToStringJoinPointId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instToStringJoinPointId___closed__0 = (const lean_object*)&l_Lean_IR_instToStringJoinPointId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instToStringJoinPointId = (const lean_object*)&l_Lean_IR_instToStringJoinPointId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint8_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint8_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint16_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint16_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint32_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint32_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint64_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint64_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_usize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_usize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_object_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_object_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tobject_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tobject_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float32_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float32_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_struct_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_struct_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_union_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_union_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tagged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tagged_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_void_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_void_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedIRType_default;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedIRType;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqIRType_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqIRType_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqIRType___closed__0 = (const lean_object*)&l_Lean_IR_instBEqIRType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqIRType = (const lean_object*)&l_Lean_IR_instBEqIRType___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.IR.IRType.float"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__0 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__0_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__0_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__1 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__1_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.IR.IRType.uint8"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__2 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__2_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__2_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__3 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__3_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.uint16"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__4 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__4_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__4_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__5 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__5_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.uint32"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__6 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__6_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__6_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__7 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__7_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.uint64"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__8 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__8_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__8_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__9 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__9_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.IR.IRType.usize"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__10 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__10_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__10_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__11 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__11_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.erased"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__12 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__12_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__12_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__13 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__13_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.object"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__14 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__14_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__14_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__15 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__15_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.IR.IRType.tobject"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__16 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__16_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__16_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__17 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__17_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.IR.IRType.float32"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__18 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__18_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__18_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__19 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__19_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.tagged"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__20 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__20_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__20_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__21 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__21_value;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.IR.IRType.void"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__22 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__22_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__22_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__23 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__23_value;
static lean_once_cell_t l_Lean_IR_instReprIRType_repr___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprIRType_repr___closed__24;
static lean_once_cell_t l_Lean_IR_instReprIRType_repr___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprIRType_repr___closed__25;
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IR.IRType.struct"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__26 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__26_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__26_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__27 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__27_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__28 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__28_value;
static const lean_string_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_IR_instReprIRType_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.IR.IRType.union"};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__29 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__29_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__29_value)}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__30 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__30_value;
static const lean_ctor_object l_Lean_IR_instReprIRType_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_IR_instReprIRType_repr___closed__30_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_IR_instReprIRType_repr___closed__31 = (const lean_object*)&l_Lean_IR_instReprIRType_repr___closed__31_value;
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instReprIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instReprIRType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instReprIRType___closed__0 = (const lean_object*)&l_Lean_IR_instReprIRType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instReprIRType = (const lean_object*)&l_Lean_IR_instReprIRType___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isPossibleRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isPossibleRef___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isDefiniteRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isDefiniteRef___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isErased___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isVoid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isVoid___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_boxed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_IR_instInhabitedArg_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_instInhabitedArg_default___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedArg_default = (const lean_object*)&l_Lean_IR_instInhabitedArg_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedArg = (const lean_object*)&l_Lean_IR_instInhabitedArg_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_instBEqArg_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqArg_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqArg_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqArg___closed__0 = (const lean_object*)&l_Lean_IR_instBEqArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqArg = (const lean_object*)&l_Lean_IR_instBEqArg___closed__0_value;
static const lean_string_object l_Lean_IR_instReprArg_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.IR.Arg.erased"};
static const lean_object* l_Lean_IR_instReprArg_repr___closed__0 = (const lean_object*)&l_Lean_IR_instReprArg_repr___closed__0_value;
static const lean_ctor_object l_Lean_IR_instReprArg_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprArg_repr___closed__0_value)}};
static const lean_object* l_Lean_IR_instReprArg_repr___closed__1 = (const lean_object*)&l_Lean_IR_instReprArg_repr___closed__1_value;
static const lean_string_object l_Lean_IR_instReprArg_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.IR.Arg.var"};
static const lean_object* l_Lean_IR_instReprArg_repr___closed__2 = (const lean_object*)&l_Lean_IR_instReprArg_repr___closed__2_value;
static const lean_ctor_object l_Lean_IR_instReprArg_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprArg_repr___closed__2_value)}};
static const lean_object* l_Lean_IR_instReprArg_repr___closed__3 = (const lean_object*)&l_Lean_IR_instReprArg_repr___closed__3_value;
static const lean_ctor_object l_Lean_IR_instReprArg_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_IR_instReprArg_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_IR_instReprArg_repr___closed__4 = (const lean_object*)&l_Lean_IR_instReprArg_repr___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_IR_instReprArg_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprArg_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instReprArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instReprArg_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instReprArg___closed__0 = (const lean_object*)&l_Lean_IR_instReprArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instReprArg = (const lean_object*)&l_Lean_IR_instReprArg___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_IR_instInhabitedLitVal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_instInhabitedLitVal_default___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedLitVal_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedLitVal_default = (const lean_object*)&l_Lean_IR_instInhabitedLitVal_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedLitVal = (const lean_object*)&l_Lean_IR_instInhabitedLitVal_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_instBEqLitVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqLitVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqLitVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqLitVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqLitVal___closed__0 = (const lean_object*)&l_Lean_IR_instBEqLitVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqLitVal = (const lean_object*)&l_Lean_IR_instBEqLitVal___closed__0_value;
static const lean_ctor_object l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_instInhabitedCtorInfo_default___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedCtorInfo_default = (const lean_object*)&l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedCtorInfo = (const lean_object*)&l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_instBEqCtorInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqCtorInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqCtorInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqCtorInfo___closed__0 = (const lean_object*)&l_Lean_IR_instBEqCtorInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqCtorInfo = (const lean_object*)&l_Lean_IR_instBEqCtorInfo___closed__0_value;
static const lean_string_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4;
static const lean_string_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "usize"};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11;
static const lean_string_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ssize"};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instReprCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instReprCtorInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instReprCtorInfo___closed__0 = (const lean_object*)&l_Lean_IR_instReprCtorInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instReprCtorInfo = (const lean_object*)&l_Lean_IR_instReprCtorInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_instInhabitedExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_instInhabitedExpr_default___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedExpr_default___closed__0_value;
static const lean_ctor_object l_Lean_IR_instInhabitedExpr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value),((lean_object*)&l_Lean_IR_instInhabitedExpr_default___closed__0_value)}};
static const lean_object* l_Lean_IR_instInhabitedExpr_default___closed__1 = (const lean_object*)&l_Lean_IR_instInhabitedExpr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedExpr_default = (const lean_object*)&l_Lean_IR_instInhabitedExpr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedExpr = (const lean_object*)&l_Lean_IR_instInhabitedExpr_default___closed__1_value;
static const lean_ctor_object l_Lean_IR_instInhabitedParam_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_IR_instInhabitedParam_default___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedParam_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedParam_default = (const lean_object*)&l_Lean_IR_instInhabitedParam_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedParam = (const lean_object*)&l_Lean_IR_instInhabitedParam_default___closed__0_value;
static const lean_string_object l_Lean_IR_instReprParam_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__0 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_IR_instReprParam_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__1 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_IR_instReprParam_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__2 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_IR_instReprParam_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__2_value),((lean_object*)&l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__3 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_IR_instReprParam_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__4;
static const lean_string_object l_Lean_IR_instReprParam_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "borrow"};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__5 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_IR_instReprParam_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__6 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_IR_instReprParam_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__7;
static const lean_string_object l_Lean_IR_instReprParam_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ty"};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__8 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_IR_instReprParam_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__9 = (const lean_object*)&l_Lean_IR_instReprParam_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_IR_instReprParam_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_instReprParam_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instReprParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instReprParam_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instReprParam___closed__0 = (const lean_object*)&l_Lean_IR_instReprParam___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instReprParam = (const lean_object*)&l_Lean_IR_instReprParam___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_instInhabitedFnBody_default__1___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value;
static const lean_ctor_object l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 9}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value)}};
static const lean_object* l_Lean_IR_instInhabitedFnBody_default__1___closed__1 = (const lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedFnBody_default__1 = (const lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedFnBody = (const lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value;
static const lean_ctor_object l_Lean_IR_instInhabitedAlt_default__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value),((lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)}};
static const lean_object* l_Lean_IR_instInhabitedAlt_default__1___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedAlt_default__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedAlt_default__1 = (const lean_object*)&l_Lean_IR_instInhabitedAlt_default__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedAlt = (const lean_object*)&l_Lean_IR_instInhabitedAlt_default__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_nil;
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(lean_object*);
static const lean_closure_object l_Lean_IR_Alt_modifyBodyM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_Alt_modifyBodyM___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___closed__0 = (const lean_object*)&l_Lean_IR_Alt_modifyBodyM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_FnBody_flatten___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_FnBody_flatten___closed__0 = (const lean_object*)&l_Lean_IR_FnBody_flatten___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_reshapeAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Init.Data.Array.Basic"};
static const lean_object* l_Lean_IR_reshapeAux___closed__0 = (const lean_object*)&l_Lean_IR_reshapeAux___closed__0_value;
static const lean_string_object l_Lean_IR_reshapeAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Array.swapAt!"};
static const lean_object* l_Lean_IR_reshapeAux___closed__1 = (const lean_object*)&l_Lean_IR_reshapeAux___closed__1_value;
static const lean_string_object l_Lean_IR_reshapeAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l_Lean_IR_reshapeAux___closed__2 = (const lean_object*)&l_Lean_IR_reshapeAux___closed__2_value;
static const lean_string_object l_Lean_IR_reshapeAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " out of bounds"};
static const lean_object* l_Lean_IR_reshapeAux___closed__3 = (const lean_object*)&l_Lean_IR_reshapeAux___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_modifyJPs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__0 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__0_value;
static const lean_closure_object l_Lean_IR_modifyJPs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__1 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__1_value;
static const lean_closure_object l_Lean_IR_modifyJPs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__2 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__2_value;
static const lean_closure_object l_Lean_IR_modifyJPs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__3 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__3_value;
static const lean_closure_object l_Lean_IR_modifyJPs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__4 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__4_value;
static const lean_closure_object l_Lean_IR_modifyJPs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__5 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__5_value;
static const lean_closure_object l_Lean_IR_modifyJPs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_modifyJPs___closed__6 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__6_value;
static const lean_ctor_object l_Lean_IR_modifyJPs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_modifyJPs___closed__0_value),((lean_object*)&l_Lean_IR_modifyJPs___closed__1_value)}};
static const lean_object* l_Lean_IR_modifyJPs___closed__7 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__7_value;
static const lean_ctor_object l_Lean_IR_modifyJPs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_modifyJPs___closed__7_value),((lean_object*)&l_Lean_IR_modifyJPs___closed__2_value),((lean_object*)&l_Lean_IR_modifyJPs___closed__3_value),((lean_object*)&l_Lean_IR_modifyJPs___closed__4_value),((lean_object*)&l_Lean_IR_modifyJPs___closed__5_value)}};
static const lean_object* l_Lean_IR_modifyJPs___closed__8 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__8_value;
static const lean_ctor_object l_Lean_IR_modifyJPs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_modifyJPs___closed__8_value),((lean_object*)&l_Lean_IR_modifyJPs___closed__6_value)}};
static const lean_object* l_Lean_IR_modifyJPs___closed__9 = (const lean_object*)&l_Lean_IR_modifyJPs___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_instInhabitedDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_instInhabitedDecl_default___closed__0 = (const lean_object*)&l_Lean_IR_instInhabitedDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_IR_instInhabitedDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instInhabitedDecl_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_instInhabitedDecl_default___closed__1 = (const lean_object*)&l_Lean_IR_instInhabitedDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedDecl_default = (const lean_object*)&l_Lean_IR_instInhabitedDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instInhabitedDecl = (const lean_object*)&l_Lean_IR_instInhabitedDecl_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_Decl_updateBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Compiler.IR.Basic"};
static const lean_object* l_Lean_IR_Decl_updateBody_x21___closed__0 = (const lean_object*)&l_Lean_IR_Decl_updateBody_x21___closed__0_value;
static const lean_string_object l_Lean_IR_Decl_updateBody_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.IR.Decl.updateBody!"};
static const lean_object* l_Lean_IR_Decl_updateBody_x21___closed__1 = (const lean_object*)&l_Lean_IR_Decl_updateBody_x21___closed__1_value;
static const lean_string_object l_Lean_IR_Decl_updateBody_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected definition"};
static const lean_object* l_Lean_IR_Decl_updateBody_x21___closed__2 = (const lean_object*)&l_Lean_IR_Decl_updateBody_x21___closed__2_value;
static lean_once_cell_t l_Lean_IR_Decl_updateBody_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instAlphaEqvVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_VarId_alphaEqv___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instAlphaEqvVarId___closed__0 = (const lean_object*)&l_Lean_IR_instAlphaEqvVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instAlphaEqvVarId = (const lean_object*)&l_Lean_IR_instAlphaEqvVarId___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instAlphaEqvArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_Arg_alphaEqv___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instAlphaEqvArg___closed__0 = (const lean_object*)&l_Lean_IR_instAlphaEqvArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instAlphaEqvArg = (const lean_object*)&l_Lean_IR_instAlphaEqvArg___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instAlphaEqvArrayArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_args_alphaEqv___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instAlphaEqvArrayArg___closed__0 = (const lean_object*)&l_Lean_IR_instAlphaEqvArrayArg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instAlphaEqvArrayArg = (const lean_object*)&l_Lean_IR_instAlphaEqvArrayArg___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instAlphaEqvExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_Expr_alphaEqv___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instAlphaEqvExpr___closed__0 = (const lean_object*)&l_Lean_IR_instAlphaEqvExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instAlphaEqvExpr = (const lean_object*)&l_Lean_IR_instAlphaEqvExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_instBEqFnBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_FnBody_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_instBEqFnBody___closed__0 = (const lean_object*)&l_Lean_IR_instBEqFnBody___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_instBEqFnBody = (const lean_object*)&l_Lean_IR_instBEqFnBody___closed__0_value;
static const lean_string_object l_Lean_IR_mkIf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_IR_mkIf___closed__0 = (const lean_object*)&l_Lean_IR_mkIf___closed__0_value;
static const lean_ctor_object l_Lean_IR_mkIf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_mkIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_IR_mkIf___closed__1 = (const lean_object*)&l_Lean_IR_mkIf___closed__1_value;
static const lean_string_object l_Lean_IR_mkIf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_IR_mkIf___closed__2 = (const lean_object*)&l_Lean_IR_mkIf___closed__2_value;
static const lean_ctor_object l_Lean_IR_mkIf___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_mkIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_IR_mkIf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_mkIf___closed__3_value_aux_0),((lean_object*)&l_Lean_IR_mkIf___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_IR_mkIf___closed__3 = (const lean_object*)&l_Lean_IR_mkIf___closed__3_value;
static const lean_ctor_object l_Lean_IR_mkIf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_mkIf___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_mkIf___closed__4 = (const lean_object*)&l_Lean_IR_mkIf___closed__4_value;
static const lean_string_object l_Lean_IR_mkIf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_IR_mkIf___closed__5 = (const lean_object*)&l_Lean_IR_mkIf___closed__5_value;
static const lean_ctor_object l_Lean_IR_mkIf___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_mkIf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_IR_mkIf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_mkIf___closed__6_value_aux_0),((lean_object*)&l_Lean_IR_mkIf___closed__5_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_IR_mkIf___closed__6 = (const lean_object*)&l_Lean_IR_mkIf___closed__6_value;
static const lean_ctor_object l_Lean_IR_mkIf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_mkIf___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_mkIf___closed__7 = (const lean_object*)&l_Lean_IR_mkIf___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_getUnboxOpName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_unbox_usize"};
static const lean_object* l_Lean_IR_getUnboxOpName___closed__0 = (const lean_object*)&l_Lean_IR_getUnboxOpName___closed__0_value;
static const lean_string_object l_Lean_IR_getUnboxOpName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lean_unbox_uint32"};
static const lean_object* l_Lean_IR_getUnboxOpName___closed__1 = (const lean_object*)&l_Lean_IR_getUnboxOpName___closed__1_value;
static const lean_string_object l_Lean_IR_getUnboxOpName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "lean_unbox_uint64"};
static const lean_object* l_Lean_IR_getUnboxOpName___closed__2 = (const lean_object*)&l_Lean_IR_getUnboxOpName___closed__2_value;
static const lean_string_object l_Lean_IR_getUnboxOpName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "lean_unbox_float"};
static const lean_object* l_Lean_IR_getUnboxOpName___closed__3 = (const lean_object*)&l_Lean_IR_getUnboxOpName___closed__3_value;
static const lean_string_object l_Lean_IR_getUnboxOpName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lean_unbox_float32"};
static const lean_object* l_Lean_IR_getUnboxOpName___closed__4 = (const lean_object*)&l_Lean_IR_getUnboxOpName___closed__4_value;
static const lean_string_object l_Lean_IR_getUnboxOpName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lean_unbox"};
static const lean_object* l_Lean_IR_getUnboxOpName___closed__5 = (const lean_object*)&l_Lean_IR_getUnboxOpName___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object*);
static lean_object* _init_l_Lean_IR_instInhabitedVarId_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(0u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedVarId(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqVarId_beq(lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_eq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId_beq___boxed(lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_IR_instBEqVarId_beq(v_x_6_, v_x_7_);
lean_dec(v_x_7_);
lean_dec(v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_instHashableVarId_hash(lean_object* v_x_12_){
_start:
{
uint64_t v___x_13_; uint64_t v___x_14_; uint64_t v___x_15_; 
v___x_13_ = 0ULL;
v___x_14_ = lean_uint64_of_nat(v_x_12_);
v___x_15_ = lean_uint64_mix_hash(v___x_13_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId_hash___boxed(lean_object* v_x_16_){
_start:
{
uint64_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_IR_instHashableVarId_hash(v_x_16_);
lean_dec(v_x_16_);
v_r_18_ = lean_box_uint64(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_instReprVarId_repr_spec__0(lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_nat_to_int(v_a_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(7u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_IR_instReprVarId_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__0));
v___x_40_ = lean_string_length(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__9, &l_Lean_IR_instReprVarId_repr___redArg___closed__9_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__9);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId_repr___redArg(lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_48_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__6));
v___x_49_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__7, &l_Lean_IR_instReprVarId_repr___redArg___closed__7_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7);
v___x_50_ = l_Nat_reprFast(v_x_47_);
v___x_51_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
v___x_52_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_49_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = 0;
v___x_54_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*1, v___x_53_);
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_48_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_57_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_55_);
v___x_59_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_56_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*1, v___x_53_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId_repr(lean_object* v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId_repr___boxed(lean_object* v_x_66_, lean_object* v_prec_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_IR_instReprVarId_repr(v_x_66_, v_prec_67_);
lean_dec(v_prec_67_);
return v_res_68_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedJoinPointId_default(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_unsigned_to_nat(0u);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedJoinPointId(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_unsigned_to_nat(0u);
return v___x_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqJoinPointId_beq(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_nat_dec_eq(v_x_73_, v_x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqJoinPointId_beq___boxed(lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_IR_instBEqJoinPointId_beq(v_x_76_, v_x_77_);
lean_dec(v_x_77_);
lean_dec(v_x_76_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_instHashableJoinPointId_hash(lean_object* v_x_82_){
_start:
{
uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; 
v___x_83_ = 0ULL;
v___x_84_ = lean_uint64_of_nat(v_x_82_);
v___x_85_ = lean_uint64_mix_hash(v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instHashableJoinPointId_hash___boxed(lean_object* v_x_86_){
_start:
{
uint64_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_IR_instHashableJoinPointId_hash(v_x_86_);
lean_dec(v_x_86_);
v_r_88_ = lean_box_uint64(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId_repr___redArg(lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_92_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__6));
v___x_93_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__7, &l_Lean_IR_instReprVarId_repr___redArg___closed__7_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7);
v___x_94_ = l_Nat_reprFast(v_x_91_);
v___x_95_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_93_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_92_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_101_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_99_);
v___x_103_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_100_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_97_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId_repr(lean_object* v_x_107_, lean_object* v_prec_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_IR_instReprJoinPointId_repr___redArg(v_x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_IR_instReprJoinPointId_repr(v_x_110_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Index_lt(lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_nat_dec_lt(v_a_115_, v_b_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Index_lt___boxed(lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_IR_Index_lt(v_a_118_, v_b_119_);
lean_dec(v_b_119_);
lean_dec(v_a_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId___lam__0(lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((lean_object*)(l_Lean_IR_instToStringVarId___lam__0___closed__0));
v___x_125_ = l_Nat_reprFast(v_a_123_);
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
lean_dec_ref(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId___lam__0(lean_object* v_a_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((lean_object*)(l_Lean_IR_instToStringJoinPointId___lam__0___closed__0));
v___x_132_ = l_Nat_reprFast(v_a_130_);
v___x_133_ = lean_string_append(v___x_131_, v___x_132_);
lean_dec_ref(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx(lean_object* v_x_136_){
_start:
{
switch(lean_obj_tag(v_x_136_))
{
case 0:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(0u);
return v___x_137_;
}
case 1:
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(1u);
return v___x_138_;
}
case 2:
{
lean_object* v___x_139_; 
v___x_139_ = lean_unsigned_to_nat(2u);
return v___x_139_;
}
case 3:
{
lean_object* v___x_140_; 
v___x_140_ = lean_unsigned_to_nat(3u);
return v___x_140_;
}
case 4:
{
lean_object* v___x_141_; 
v___x_141_ = lean_unsigned_to_nat(4u);
return v___x_141_;
}
case 5:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(5u);
return v___x_142_;
}
case 6:
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(6u);
return v___x_143_;
}
case 7:
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(7u);
return v___x_144_;
}
case 8:
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(8u);
return v___x_145_;
}
case 9:
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(9u);
return v___x_146_;
}
case 10:
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(10u);
return v___x_147_;
}
case 11:
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(11u);
return v___x_148_;
}
case 12:
{
lean_object* v___x_149_; 
v___x_149_ = lean_unsigned_to_nat(12u);
return v___x_149_;
}
default: 
{
lean_object* v___x_150_; 
v___x_150_ = lean_unsigned_to_nat(13u);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx___boxed(lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_IR_IRType_ctorIdx(v_x_151_);
lean_dec(v_x_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim___redArg(lean_object* v_t_153_, lean_object* v_k_154_){
_start:
{
switch(lean_obj_tag(v_t_153_))
{
case 10:
{
lean_object* v_leanTypeName_155_; lean_object* v_types_156_; lean_object* v___x_157_; 
v_leanTypeName_155_ = lean_ctor_get(v_t_153_, 0);
lean_inc(v_leanTypeName_155_);
v_types_156_ = lean_ctor_get(v_t_153_, 1);
lean_inc_ref(v_types_156_);
lean_dec_ref_known(v_t_153_, 2);
v___x_157_ = lean_apply_2(v_k_154_, v_leanTypeName_155_, v_types_156_);
return v___x_157_;
}
case 11:
{
lean_object* v_leanTypeName_158_; lean_object* v_types_159_; lean_object* v___x_160_; 
v_leanTypeName_158_ = lean_ctor_get(v_t_153_, 0);
lean_inc(v_leanTypeName_158_);
v_types_159_ = lean_ctor_get(v_t_153_, 1);
lean_inc_ref(v_types_159_);
lean_dec_ref_known(v_t_153_, 2);
v___x_160_ = lean_apply_2(v_k_154_, v_leanTypeName_158_, v_types_159_);
return v___x_160_;
}
default: 
{
lean_dec(v_t_153_);
return v_k_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim(lean_object* v_motive__1_161_, lean_object* v_ctorIdx_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_k_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_163_, v_k_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim___boxed(lean_object* v_motive__1_167_, lean_object* v_ctorIdx_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_k_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_IR_IRType_ctorElim(v_motive__1_167_, v_ctorIdx_168_, v_t_169_, v_h_170_, v_k_171_);
lean_dec(v_ctorIdx_168_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float_elim___redArg(lean_object* v_t_173_, lean_object* v_float_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_173_, v_float_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float_elim(lean_object* v_motive__1_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_float_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_177_, v_float_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint8_elim___redArg(lean_object* v_t_181_, lean_object* v_uint8_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_181_, v_uint8_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint8_elim(lean_object* v_motive__1_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_uint8_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_185_, v_uint8_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint16_elim___redArg(lean_object* v_t_189_, lean_object* v_uint16_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_189_, v_uint16_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint16_elim(lean_object* v_motive__1_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_uint16_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_193_, v_uint16_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint32_elim___redArg(lean_object* v_t_197_, lean_object* v_uint32_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_197_, v_uint32_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint32_elim(lean_object* v_motive__1_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_uint32_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_201_, v_uint32_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint64_elim___redArg(lean_object* v_t_205_, lean_object* v_uint64_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_205_, v_uint64_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint64_elim(lean_object* v_motive__1_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_uint64_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_209_, v_uint64_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_usize_elim___redArg(lean_object* v_t_213_, lean_object* v_usize_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_213_, v_usize_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_usize_elim(lean_object* v_motive__1_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_usize_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_217_, v_usize_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_erased_elim___redArg(lean_object* v_t_221_, lean_object* v_erased_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_221_, v_erased_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_erased_elim(lean_object* v_motive__1_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_erased_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_225_, v_erased_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_object_elim___redArg(lean_object* v_t_229_, lean_object* v_object_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_229_, v_object_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_object_elim(lean_object* v_motive__1_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_object_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_233_, v_object_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tobject_elim___redArg(lean_object* v_t_237_, lean_object* v_tobject_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_237_, v_tobject_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tobject_elim(lean_object* v_motive__1_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_tobject_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_241_, v_tobject_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float32_elim___redArg(lean_object* v_t_245_, lean_object* v_float32_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_245_, v_float32_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float32_elim(lean_object* v_motive__1_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_float32_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_249_, v_float32_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_struct_elim___redArg(lean_object* v_t_253_, lean_object* v_struct_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_253_, v_struct_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_struct_elim(lean_object* v_motive__1_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_struct_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_257_, v_struct_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_union_elim___redArg(lean_object* v_t_261_, lean_object* v_union_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_261_, v_union_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_union_elim(lean_object* v_motive__1_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_union_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_265_, v_union_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tagged_elim___redArg(lean_object* v_t_269_, lean_object* v_tagged_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_269_, v_tagged_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tagged_elim(lean_object* v_motive__1_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_tagged_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_273_, v_tagged_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_void_elim___redArg(lean_object* v_t_277_, lean_object* v_void_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_277_, v_void_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_void_elim(lean_object* v_motive__1_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_void_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_281_, v_void_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedIRType_default(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_box(0);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedIRType(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
if (lean_obj_tag(v_x_288_) == 0)
{
uint8_t v___x_289_; 
v___x_289_ = 1;
return v___x_289_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = 0;
return v___x_290_;
}
}
else
{
if (lean_obj_tag(v_x_288_) == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 0;
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v_val_293_; uint8_t v___x_294_; 
v_val_292_ = lean_ctor_get(v_x_287_, 0);
v_val_293_ = lean_ctor_get(v_x_288_, 0);
v___x_294_ = lean_name_eq(v_val_292_, v_val_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0___boxed(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(v_x_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec(v_x_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqIRType_beq(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_Lean_IR_IRType_ctorIdx(v_x_299_);
v___x_302_ = l_Lean_IR_IRType_ctorIdx(v_x_300_);
v___x_303_ = lean_nat_dec_eq(v___x_301_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v___x_301_);
if (v___x_303_ == 0)
{
return v___x_303_;
}
else
{
switch(lean_obj_tag(v_x_299_))
{
case 10:
{
lean_object* v_leanTypeName_304_; lean_object* v_types_305_; lean_object* v_leanTypeName_306_; lean_object* v_types_307_; uint8_t v___x_308_; 
v_leanTypeName_304_ = lean_ctor_get(v_x_299_, 0);
v_types_305_ = lean_ctor_get(v_x_299_, 1);
v_leanTypeName_306_ = lean_ctor_get(v_x_300_, 0);
v_types_307_ = lean_ctor_get(v_x_300_, 1);
v___x_308_ = l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(v_leanTypeName_304_, v_leanTypeName_306_);
if (v___x_308_ == 0)
{
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_array_get_size(v_types_305_);
v___x_310_ = lean_array_get_size(v_types_307_);
v___x_311_ = lean_nat_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_types_305_, v_types_307_, v___x_309_);
return v___x_312_;
}
}
}
case 11:
{
lean_object* v_leanTypeName_313_; lean_object* v_types_314_; lean_object* v_leanTypeName_315_; lean_object* v_types_316_; uint8_t v___x_317_; 
v_leanTypeName_313_ = lean_ctor_get(v_x_299_, 0);
v_types_314_ = lean_ctor_get(v_x_299_, 1);
v_leanTypeName_315_ = lean_ctor_get(v_x_300_, 0);
v_types_316_ = lean_ctor_get(v_x_300_, 1);
v___x_317_ = lean_name_eq(v_leanTypeName_313_, v_leanTypeName_315_);
if (v___x_317_ == 0)
{
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_array_get_size(v_types_314_);
v___x_319_ = lean_array_get_size(v_types_316_);
v___x_320_ = lean_nat_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
return v___x_320_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_types_314_, v_types_316_, v___x_318_);
return v___x_321_;
}
}
}
default: 
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(lean_object* v_xs_322_, lean_object* v_ys_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_zero_325_; uint8_t v_isZero_326_; 
v_zero_325_ = lean_unsigned_to_nat(0u);
v_isZero_326_ = lean_nat_dec_eq(v_x_324_, v_zero_325_);
if (v_isZero_326_ == 1)
{
lean_dec(v_x_324_);
return v_isZero_326_;
}
else
{
lean_object* v_one_327_; lean_object* v_n_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_one_327_ = lean_unsigned_to_nat(1u);
v_n_328_ = lean_nat_sub(v_x_324_, v_one_327_);
lean_dec(v_x_324_);
v___x_329_ = lean_array_fget_borrowed(v_xs_322_, v_n_328_);
v___x_330_ = lean_array_fget_borrowed(v_ys_323_, v_n_328_);
v___x_331_ = l_Lean_IR_instBEqIRType_beq(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_dec(v_n_328_);
return v___x_331_;
}
else
{
v_x_324_ = v_n_328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg___boxed(lean_object* v_xs_333_, lean_object* v_ys_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_xs_333_, v_ys_334_, v_x_335_);
lean_dec_ref(v_ys_334_);
lean_dec_ref(v_xs_333_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqIRType_beq___boxed(lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lean_IR_instBEqIRType_beq(v_x_338_, v_x_339_);
lean_dec(v_x_339_);
lean_dec(v_x_338_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(lean_object* v_xs_342_, lean_object* v_ys_343_, lean_object* v_hsz_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_xs_342_, v_ys_343_, v_x_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___boxed(lean_object* v_xs_348_, lean_object* v_ys_349_, lean_object* v_hsz_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(v_xs_348_, v_ys_349_, v_hsz_350_, v_x_351_, v_x_352_);
lean_dec_ref(v_ys_349_);
lean_dec_ref(v_xs_348_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v___x_365_; 
v___x_365_ = ((lean_object*)(l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1));
return v___x_365_;
}
else
{
lean_object* v_val_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_val_366_ = lean_ctor_get(v_x_363_, 0);
lean_inc(v_val_366_);
lean_dec_ref_known(v_x_363_, 1);
v___x_367_ = ((lean_object*)(l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3));
v___x_368_ = lean_unsigned_to_nat(1024u);
v___x_369_ = l_Lean_Name_reprPrec(v_val_366_, v___x_368_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_367_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_Repr_addAppParen(v___x_370_, v_x_364_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___boxed(lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(v_x_372_, v_x_373_);
lean_dec(v_x_373_);
return v_res_374_;
}
}
static lean_object* _init_l_Lean_IR_instReprIRType_repr___closed__24(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(2u);
v___x_412_ = lean_nat_to_int(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_IR_instReprIRType_repr___closed__25(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_to_int(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_dec(v_x_427_);
return v_x_428_;
}
else
{
lean_object* v_head_430_; lean_object* v_tail_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_442_; 
v_head_430_ = lean_ctor_get(v_x_429_, 0);
v_tail_431_ = lean_ctor_get(v_x_429_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_442_ == 0)
{
v___x_433_ = v_x_429_;
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_tail_431_);
lean_inc(v_head_430_);
lean_dec(v_x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_442_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
lean_inc(v_x_427_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 5);
lean_ctor_set(v___x_433_, 1, v_x_427_);
lean_ctor_set(v___x_433_, 0, v_x_428_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_x_428_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_x_427_);
v___x_436_ = v_reuseFailAlloc_441_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = l_Lean_IR_instReprIRType_repr(v_head_430_, v___x_437_);
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_436_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v_x_428_ = v___x_439_;
v_x_429_ = v_tail_431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_dec(v_x_443_);
return v_x_444_;
}
else
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_458_; 
v_head_446_ = lean_ctor_get(v_x_445_, 0);
v_tail_447_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_458_ == 0)
{
v___x_449_ = v_x_445_;
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_tail_447_);
lean_inc(v_head_446_);
lean_dec(v_x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_458_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
lean_inc(v_x_443_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 5);
lean_ctor_set(v___x_449_, 1, v_x_443_);
lean_ctor_set(v___x_449_, 0, v_x_444_);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_x_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_x_443_);
v___x_452_ = v_reuseFailAlloc_457_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = l_Lean_IR_instReprIRType_repr(v_head_446_, v___x_453_);
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_452_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(v_x_443_, v___x_455_, v_tail_447_);
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_461_; 
lean_dec(v_x_460_);
v___x_461_ = lean_box(0);
return v___x_461_;
}
else
{
lean_object* v_tail_462_; 
v_tail_462_ = lean_ctor_get(v_x_459_, 1);
if (lean_obj_tag(v_tail_462_) == 0)
{
lean_object* v_head_463_; lean_object* v___x_464_; 
lean_dec(v_x_460_);
v_head_463_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_head_463_);
lean_dec_ref_known(v_x_459_, 2);
v___x_464_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_463_);
return v___x_464_;
}
else
{
lean_object* v_head_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_inc(v_tail_462_);
v_head_465_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_head_465_);
lean_dec_ref_known(v_x_459_, 2);
v___x_466_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_465_);
v___x_467_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(v_x_460_, v___x_466_, v_tail_462_);
return v___x_467_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0));
v___x_470_ = lean_string_length(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5, &l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5);
v___x_472_ = lean_nat_to_int(v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(lean_object* v_xs_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_482_ = lean_array_get_size(v_xs_481_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_485_ = lean_array_to_list(v_xs_481_);
v___x_486_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3));
v___x_487_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(v___x_485_, v___x_486_);
v___x_488_ = lean_obj_once(&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6, &l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6);
v___x_489_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7));
v___x_490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_487_);
v___x_491_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8));
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_488_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Std_Format_fill(v___x_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; 
lean_dec_ref(v_xs_481_);
v___x_495_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10));
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType_repr(lean_object* v_x_502_, lean_object* v_prec_503_){
_start:
{
lean_object* v___y_505_; lean_object* v___y_512_; lean_object* v___y_519_; lean_object* v___y_526_; lean_object* v___y_533_; lean_object* v___y_540_; lean_object* v___y_547_; lean_object* v___y_554_; lean_object* v___y_561_; lean_object* v___y_568_; lean_object* v___y_575_; lean_object* v___y_582_; 
switch(lean_obj_tag(v_x_502_))
{
case 0:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1024u);
v___x_589_ = lean_nat_dec_le(v___x_588_, v_prec_503_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_505_ = v___x_590_;
goto v___jp_504_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_505_ = v___x_591_;
goto v___jp_504_;
}
}
case 1:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1024u);
v___x_593_ = lean_nat_dec_le(v___x_592_, v_prec_503_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_512_ = v___x_594_;
goto v___jp_511_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_512_ = v___x_595_;
goto v___jp_511_;
}
}
case 2:
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(1024u);
v___x_597_ = lean_nat_dec_le(v___x_596_, v_prec_503_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_519_ = v___x_598_;
goto v___jp_518_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_519_ = v___x_599_;
goto v___jp_518_;
}
}
case 3:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1024u);
v___x_601_ = lean_nat_dec_le(v___x_600_, v_prec_503_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_526_ = v___x_602_;
goto v___jp_525_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_526_ = v___x_603_;
goto v___jp_525_;
}
}
case 4:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1024u);
v___x_605_ = lean_nat_dec_le(v___x_604_, v_prec_503_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_533_ = v___x_606_;
goto v___jp_532_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_533_ = v___x_607_;
goto v___jp_532_;
}
}
case 5:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1024u);
v___x_609_ = lean_nat_dec_le(v___x_608_, v_prec_503_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_540_ = v___x_610_;
goto v___jp_539_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_540_ = v___x_611_;
goto v___jp_539_;
}
}
case 6:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(1024u);
v___x_613_ = lean_nat_dec_le(v___x_612_, v_prec_503_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_547_ = v___x_614_;
goto v___jp_546_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_547_ = v___x_615_;
goto v___jp_546_;
}
}
case 7:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1024u);
v___x_617_ = lean_nat_dec_le(v___x_616_, v_prec_503_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_554_ = v___x_618_;
goto v___jp_553_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_554_ = v___x_619_;
goto v___jp_553_;
}
}
case 8:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(1024u);
v___x_621_ = lean_nat_dec_le(v___x_620_, v_prec_503_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_561_ = v___x_622_;
goto v___jp_560_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_561_ = v___x_623_;
goto v___jp_560_;
}
}
case 9:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_unsigned_to_nat(1024u);
v___x_625_ = lean_nat_dec_le(v___x_624_, v_prec_503_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_568_ = v___x_626_;
goto v___jp_567_;
}
else
{
lean_object* v___x_627_; 
v___x_627_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_568_ = v___x_627_;
goto v___jp_567_;
}
}
case 10:
{
lean_object* v_leanTypeName_628_; lean_object* v_types_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_653_; 
v_leanTypeName_628_ = lean_ctor_get(v_x_502_, 0);
v_types_629_ = lean_ctor_get(v_x_502_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_653_ == 0)
{
v___x_631_ = v_x_502_;
v_isShared_632_ = v_isSharedCheck_653_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_types_629_);
lean_inc(v_leanTypeName_628_);
lean_dec(v_x_502_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_653_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___y_634_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1024u);
v___x_650_ = lean_nat_dec_le(v___x_649_, v_prec_503_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_634_ = v___x_651_;
goto v___jp_633_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_634_ = v___x_652_;
goto v___jp_633_;
}
v___jp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_635_ = lean_box(1);
v___x_636_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__28));
v___x_637_ = lean_unsigned_to_nat(1024u);
v___x_638_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(v_leanTypeName_628_, v___x_637_);
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 5);
lean_ctor_set(v___x_631_, 1, v___x_638_);
lean_ctor_set(v___x_631_, 0, v___x_636_);
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_648_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_635_);
v___x_642_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_629_);
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_inc(v___y_634_);
v___x_644_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_634_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = 0;
v___x_646_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_645_);
v___x_647_ = l_Repr_addAppParen(v___x_646_, v_prec_503_);
return v___x_647_;
}
}
}
}
case 11:
{
lean_object* v_leanTypeName_654_; lean_object* v_types_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_679_; 
v_leanTypeName_654_ = lean_ctor_get(v_x_502_, 0);
v_types_655_ = lean_ctor_get(v_x_502_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_679_ == 0)
{
v___x_657_ = v_x_502_;
v_isShared_658_ = v_isSharedCheck_679_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_types_655_);
lean_inc(v_leanTypeName_654_);
lean_dec(v_x_502_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_679_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___y_660_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(1024u);
v___x_676_ = lean_nat_dec_le(v___x_675_, v_prec_503_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_660_ = v___x_677_;
goto v___jp_659_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_660_ = v___x_678_;
goto v___jp_659_;
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_661_ = lean_box(1);
v___x_662_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__31));
v___x_663_ = lean_unsigned_to_nat(1024u);
v___x_664_ = l_Lean_Name_reprPrec(v_leanTypeName_654_, v___x_663_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 5);
lean_ctor_set(v___x_657_, 1, v___x_664_);
lean_ctor_set(v___x_657_, 0, v___x_662_);
v___x_666_ = v___x_657_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_674_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_661_);
v___x_668_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_655_);
v___x_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_inc(v___y_660_);
v___x_670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_670_, 0, v___y_660_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = 0;
v___x_672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*1, v___x_671_);
v___x_673_ = l_Repr_addAppParen(v___x_672_, v_prec_503_);
return v___x_673_;
}
}
}
}
case 12:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(1024u);
v___x_681_ = lean_nat_dec_le(v___x_680_, v_prec_503_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_575_ = v___x_682_;
goto v___jp_574_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_575_ = v___x_683_;
goto v___jp_574_;
}
}
default: 
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(1024u);
v___x_685_ = lean_nat_dec_le(v___x_684_, v_prec_503_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_582_ = v___x_686_;
goto v___jp_581_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_582_ = v___x_687_;
goto v___jp_581_;
}
}
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_506_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__1));
lean_inc(v___y_505_);
v___x_507_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_507_, 0, v___y_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = 0;
v___x_509_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*1, v___x_508_);
v___x_510_ = l_Repr_addAppParen(v___x_509_, v_prec_503_);
return v___x_510_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_513_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__3));
lean_inc(v___y_512_);
v___x_514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_514_, 0, v___y_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = 0;
v___x_516_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*1, v___x_515_);
v___x_517_ = l_Repr_addAppParen(v___x_516_, v_prec_503_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_520_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__5));
lean_inc(v___y_519_);
v___x_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_521_, 0, v___y_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = 0;
v___x_523_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*1, v___x_522_);
v___x_524_ = l_Repr_addAppParen(v___x_523_, v_prec_503_);
return v___x_524_;
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_527_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__7));
lean_inc(v___y_526_);
v___x_528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_528_, 0, v___y_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = 0;
v___x_530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_529_);
v___x_531_ = l_Repr_addAppParen(v___x_530_, v_prec_503_);
return v___x_531_;
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_534_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__9));
lean_inc(v___y_533_);
v___x_535_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_535_, 0, v___y_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = 0;
v___x_537_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*1, v___x_536_);
v___x_538_ = l_Repr_addAppParen(v___x_537_, v_prec_503_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_541_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__11));
lean_inc(v___y_540_);
v___x_542_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_542_, 0, v___y_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = 0;
v___x_544_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*1, v___x_543_);
v___x_545_ = l_Repr_addAppParen(v___x_544_, v_prec_503_);
return v___x_545_;
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_548_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__13));
lean_inc(v___y_547_);
v___x_549_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_549_, 0, v___y_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = 0;
v___x_551_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*1, v___x_550_);
v___x_552_ = l_Repr_addAppParen(v___x_551_, v_prec_503_);
return v___x_552_;
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__15));
lean_inc(v___y_554_);
v___x_556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = 0;
v___x_558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*1, v___x_557_);
v___x_559_ = l_Repr_addAppParen(v___x_558_, v_prec_503_);
return v___x_559_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_562_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__17));
lean_inc(v___y_561_);
v___x_563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = 0;
v___x_565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_564_);
v___x_566_ = l_Repr_addAppParen(v___x_565_, v_prec_503_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__19));
lean_inc(v___y_568_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_503_);
return v___x_573_;
}
v___jp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_576_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__21));
lean_inc(v___y_575_);
v___x_577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_577_, 0, v___y_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = 0;
v___x_579_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*1, v___x_578_);
v___x_580_ = l_Repr_addAppParen(v___x_579_, v_prec_503_);
return v___x_580_;
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_583_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__23));
lean_inc(v___y_582_);
v___x_584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_584_, 0, v___y_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = 0;
v___x_586_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set_uint8(v___x_586_, sizeof(void*)*1, v___x_585_);
v___x_587_ = l_Repr_addAppParen(v___x_586_, v_prec_503_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(lean_object* v___y_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = l_Lean_IR_instReprIRType_repr(v___y_688_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType_repr___boxed(lean_object* v_x_691_, lean_object* v_prec_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_IR_instReprIRType_repr(v_x_691_, v_prec_692_);
lean_dec(v_prec_692_);
return v_res_693_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object* v_x_696_){
_start:
{
switch(lean_obj_tag(v_x_696_))
{
case 0:
{
uint8_t v___x_697_; 
v___x_697_ = 1;
return v___x_697_;
}
case 9:
{
uint8_t v___x_698_; 
v___x_698_ = 1;
return v___x_698_;
}
case 1:
{
uint8_t v___x_699_; 
v___x_699_ = 1;
return v___x_699_;
}
case 2:
{
uint8_t v___x_700_; 
v___x_700_ = 1;
return v___x_700_;
}
case 3:
{
uint8_t v___x_701_; 
v___x_701_ = 1;
return v___x_701_;
}
case 4:
{
uint8_t v___x_702_; 
v___x_702_ = 1;
return v___x_702_;
}
case 5:
{
uint8_t v___x_703_; 
v___x_703_ = 1;
return v___x_703_;
}
default: 
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object* v_x_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Lean_IR_IRType_isScalar(v_x_705_);
lean_dec(v_x_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isObj(lean_object* v_x_708_){
_start:
{
switch(lean_obj_tag(v_x_708_))
{
case 7:
{
uint8_t v___x_709_; 
v___x_709_ = 1;
return v___x_709_;
}
case 12:
{
uint8_t v___x_710_; 
v___x_710_ = 1;
return v___x_710_;
}
case 8:
{
uint8_t v___x_711_; 
v___x_711_ = 1;
return v___x_711_;
}
case 13:
{
uint8_t v___x_712_; 
v___x_712_ = 1;
return v___x_712_;
}
default: 
{
uint8_t v___x_713_; 
v___x_713_ = 0;
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object* v_x_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lean_IR_IRType_isObj(v_x_714_);
lean_dec(v_x_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isPossibleRef(lean_object* v_x_717_){
_start:
{
switch(lean_obj_tag(v_x_717_))
{
case 7:
{
uint8_t v___x_718_; 
v___x_718_ = 1;
return v___x_718_;
}
case 8:
{
uint8_t v___x_719_; 
v___x_719_ = 1;
return v___x_719_;
}
default: 
{
uint8_t v___x_720_; 
v___x_720_ = 0;
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isPossibleRef___boxed(lean_object* v_x_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Lean_IR_IRType_isPossibleRef(v_x_721_);
lean_dec(v_x_721_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isDefiniteRef(lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 7)
{
uint8_t v___x_725_; 
v___x_725_ = 1;
return v___x_725_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = 0;
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isDefiniteRef___boxed(lean_object* v_x_727_){
_start:
{
uint8_t v_res_728_; lean_object* v_r_729_; 
v_res_728_ = l_Lean_IR_IRType_isDefiniteRef(v_x_727_);
lean_dec(v_x_727_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isErased(lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 6)
{
uint8_t v___x_731_; 
v___x_731_ = 1;
return v___x_731_;
}
else
{
uint8_t v___x_732_; 
v___x_732_ = 0;
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isErased___boxed(lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Lean_IR_IRType_isErased(v_x_733_);
lean_dec(v_x_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isVoid(lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 13)
{
uint8_t v___x_737_; 
v___x_737_ = 1;
return v___x_737_;
}
else
{
uint8_t v___x_738_; 
v___x_738_ = 0;
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isVoid___boxed(lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Lean_IR_IRType_isVoid(v_x_739_);
lean_dec(v_x_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_boxed(lean_object* v_x_742_){
_start:
{
switch(lean_obj_tag(v_x_742_))
{
case 7:
{
return v_x_742_;
}
case 0:
{
lean_object* v___x_743_; 
v___x_743_ = lean_box(7);
return v___x_743_;
}
case 9:
{
lean_object* v___x_744_; 
v___x_744_ = lean_box(7);
return v___x_744_;
}
case 13:
{
lean_object* v___x_745_; 
v___x_745_ = lean_box(12);
return v___x_745_;
}
case 12:
{
return v_x_742_;
}
case 1:
{
lean_object* v___x_746_; 
v___x_746_ = lean_box(12);
return v___x_746_;
}
case 2:
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(12);
return v___x_747_;
}
default: 
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(8);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_boxed___boxed(lean_object* v_x_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_IR_IRType_boxed(v_x_749_);
lean_dec(v_x_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx(lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v___x_752_; 
v___x_752_ = lean_unsigned_to_nat(0u);
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_unsigned_to_nat(1u);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx___boxed(lean_object* v_x_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_IR_Arg_ctorIdx(v_x_754_);
lean_dec(v_x_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim___redArg(lean_object* v_t_756_, lean_object* v_k_757_){
_start:
{
if (lean_obj_tag(v_t_756_) == 0)
{
lean_object* v_id_758_; lean_object* v___x_759_; 
v_id_758_ = lean_ctor_get(v_t_756_, 0);
lean_inc(v_id_758_);
lean_dec_ref_known(v_t_756_, 1);
v___x_759_ = lean_apply_1(v_k_757_, v_id_758_);
return v___x_759_;
}
else
{
return v_k_757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim(lean_object* v_motive_760_, lean_object* v_ctorIdx_761_, lean_object* v_t_762_, lean_object* v_h_763_, lean_object* v_k_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_762_, v_k_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim___boxed(lean_object* v_motive_766_, lean_object* v_ctorIdx_767_, lean_object* v_t_768_, lean_object* v_h_769_, lean_object* v_k_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_IR_Arg_ctorElim(v_motive_766_, v_ctorIdx_767_, v_t_768_, v_h_769_, v_k_770_);
lean_dec(v_ctorIdx_767_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_var_elim___redArg(lean_object* v_t_772_, lean_object* v_var_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_772_, v_var_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_var_elim(lean_object* v_motive_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_var_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_776_, v_var_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_erased_elim___redArg(lean_object* v_t_780_, lean_object* v_erased_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_780_, v_erased_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_erased_elim(lean_object* v_motive_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_erased_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_784_, v_erased_786_);
return v___x_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqArg_beq(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v_id_794_; lean_object* v_id_795_; uint8_t v___x_796_; 
v_id_794_ = lean_ctor_get(v_x_792_, 0);
v_id_795_ = lean_ctor_get(v_x_793_, 0);
v___x_796_ = lean_nat_dec_eq(v_id_794_, v_id_795_);
return v___x_796_;
}
else
{
uint8_t v___x_797_; 
v___x_797_ = 0;
return v___x_797_;
}
}
else
{
if (lean_obj_tag(v_x_793_) == 1)
{
uint8_t v___x_798_; 
v___x_798_ = 1;
return v___x_798_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = 0;
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqArg_beq___boxed(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
uint8_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = l_Lean_IR_instBEqArg_beq(v_x_800_, v_x_801_);
lean_dec(v_x_801_);
lean_dec(v_x_800_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprArg_repr(lean_object* v_x_815_, lean_object* v_prec_816_){
_start:
{
lean_object* v___y_818_; 
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v_id_824_; lean_object* v___y_826_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_id_824_ = lean_ctor_get(v_x_815_, 0);
lean_inc(v_id_824_);
lean_dec_ref_known(v_x_815_, 1);
v___x_834_ = lean_unsigned_to_nat(1024u);
v___x_835_ = lean_nat_dec_le(v___x_834_, v_prec_816_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_826_ = v___x_836_;
goto v___jp_825_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_826_ = v___x_837_;
goto v___jp_825_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_827_ = ((lean_object*)(l_Lean_IR_instReprArg_repr___closed__4));
v___x_828_ = l_Lean_IR_instReprVarId_repr___redArg(v_id_824_);
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_inc(v___y_826_);
v___x_830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_826_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = 0;
v___x_832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*1, v___x_831_);
v___x_833_ = l_Repr_addAppParen(v___x_832_, v_prec_816_);
return v___x_833_;
}
}
else
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_unsigned_to_nat(1024u);
v___x_839_ = lean_nat_dec_le(v___x_838_, v_prec_816_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_818_ = v___x_840_;
goto v___jp_817_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_818_ = v___x_841_;
goto v___jp_817_;
}
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_819_ = ((lean_object*)(l_Lean_IR_instReprArg_repr___closed__1));
lean_inc(v___y_818_);
v___x_820_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_820_, 0, v___y_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = 0;
v___x_822_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v___x_821_);
v___x_823_ = l_Repr_addAppParen(v___x_822_, v_prec_816_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprArg_repr___boxed(lean_object* v_x_842_, lean_object* v_prec_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_IR_instReprArg_repr(v_x_842_, v_prec_843_);
lean_dec(v_prec_843_);
return v_res_844_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_beq(lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v_id_849_; lean_object* v_id_850_; uint8_t v___x_851_; 
v_id_849_ = lean_ctor_get(v_x_847_, 0);
v_id_850_ = lean_ctor_get(v_x_848_, 0);
v___x_851_ = lean_nat_dec_eq(v_id_849_, v_id_850_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
}
else
{
if (lean_obj_tag(v_x_848_) == 1)
{
uint8_t v___x_853_; 
v___x_853_ = 1;
return v___x_853_;
}
else
{
uint8_t v___x_854_; 
v___x_854_ = 0;
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_beq___boxed(lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
uint8_t v_res_857_; lean_object* v_r_858_; 
v_res_857_ = l_Lean_IR_Arg_beq(v_x_855_, v_x_856_);
lean_dec(v_x_856_);
lean_dec(v_x_855_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx(lean_object* v_x_859_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(0u);
return v___x_860_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_unsigned_to_nat(1u);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx___boxed(lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_IR_LitVal_ctorIdx(v_x_862_);
lean_dec_ref(v_x_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim___redArg(lean_object* v_t_864_, lean_object* v_k_865_){
_start:
{
if (lean_obj_tag(v_t_864_) == 0)
{
lean_object* v_v_866_; lean_object* v___x_867_; 
v_v_866_ = lean_ctor_get(v_t_864_, 0);
lean_inc(v_v_866_);
lean_dec_ref_known(v_t_864_, 1);
v___x_867_ = lean_apply_1(v_k_865_, v_v_866_);
return v___x_867_;
}
else
{
lean_object* v_v_868_; lean_object* v___x_869_; 
v_v_868_ = lean_ctor_get(v_t_864_, 0);
lean_inc_ref(v_v_868_);
lean_dec_ref_known(v_t_864_, 1);
v___x_869_ = lean_apply_1(v_k_865_, v_v_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim(lean_object* v_motive_870_, lean_object* v_ctorIdx_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_k_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_872_, v_k_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim___boxed(lean_object* v_motive_876_, lean_object* v_ctorIdx_877_, lean_object* v_t_878_, lean_object* v_h_879_, lean_object* v_k_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_IR_LitVal_ctorElim(v_motive_876_, v_ctorIdx_877_, v_t_878_, v_h_879_, v_k_880_);
lean_dec(v_ctorIdx_877_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_num_elim___redArg(lean_object* v_t_882_, lean_object* v_num_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_882_, v_num_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_num_elim(lean_object* v_motive_885_, lean_object* v_t_886_, lean_object* v_h_887_, lean_object* v_num_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_886_, v_num_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_str_elim___redArg(lean_object* v_t_890_, lean_object* v_str_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_890_, v_str_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_str_elim(lean_object* v_motive_893_, lean_object* v_t_894_, lean_object* v_h_895_, lean_object* v_str_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_894_, v_str_896_);
return v___x_897_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqLitVal_beq(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_object* v_v_904_; lean_object* v_v_905_; uint8_t v___x_906_; 
v_v_904_ = lean_ctor_get(v_x_902_, 0);
v_v_905_ = lean_ctor_get(v_x_903_, 0);
v___x_906_ = lean_nat_dec_eq(v_v_904_, v_v_905_);
return v___x_906_;
}
else
{
uint8_t v___x_907_; 
v___x_907_ = 0;
return v___x_907_;
}
}
else
{
if (lean_obj_tag(v_x_903_) == 1)
{
lean_object* v_v_908_; lean_object* v_v_909_; uint8_t v___x_910_; 
v_v_908_ = lean_ctor_get(v_x_902_, 0);
v_v_909_ = lean_ctor_get(v_x_903_, 0);
v___x_910_ = lean_string_dec_eq(v_v_908_, v_v_909_);
return v___x_910_;
}
else
{
uint8_t v___x_911_; 
v___x_911_ = 0;
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqLitVal_beq___boxed(lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Lean_IR_instBEqLitVal_beq(v_x_912_, v_x_913_);
lean_dec_ref(v_x_913_);
lean_dec_ref(v_x_912_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqCtorInfo_beq(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_name_925_; lean_object* v_cidx_926_; lean_object* v_size_927_; lean_object* v_usize_928_; lean_object* v_ssize_929_; lean_object* v_name_930_; lean_object* v_cidx_931_; lean_object* v_size_932_; lean_object* v_usize_933_; lean_object* v_ssize_934_; uint8_t v___x_935_; 
v_name_925_ = lean_ctor_get(v_x_923_, 0);
v_cidx_926_ = lean_ctor_get(v_x_923_, 1);
v_size_927_ = lean_ctor_get(v_x_923_, 2);
v_usize_928_ = lean_ctor_get(v_x_923_, 3);
v_ssize_929_ = lean_ctor_get(v_x_923_, 4);
v_name_930_ = lean_ctor_get(v_x_924_, 0);
v_cidx_931_ = lean_ctor_get(v_x_924_, 1);
v_size_932_ = lean_ctor_get(v_x_924_, 2);
v_usize_933_ = lean_ctor_get(v_x_924_, 3);
v_ssize_934_ = lean_ctor_get(v_x_924_, 4);
v___x_935_ = lean_name_eq(v_name_925_, v_name_930_);
if (v___x_935_ == 0)
{
return v___x_935_;
}
else
{
uint8_t v___x_936_; 
v___x_936_ = lean_nat_dec_eq(v_cidx_926_, v_cidx_931_);
if (v___x_936_ == 0)
{
return v___x_936_;
}
else
{
uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_eq(v_size_927_, v_size_932_);
if (v___x_937_ == 0)
{
return v___x_937_;
}
else
{
uint8_t v___x_938_; 
v___x_938_ = lean_nat_dec_eq(v_usize_928_, v_usize_933_);
if (v___x_938_ == 0)
{
return v___x_938_;
}
else
{
uint8_t v___x_939_; 
v___x_939_ = lean_nat_dec_eq(v_ssize_929_, v_ssize_934_);
return v___x_939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqCtorInfo_beq___boxed(lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Lean_IR_instBEqCtorInfo_beq(v_x_940_, v_x_941_);
lean_dec_ref(v_x_941_);
lean_dec_ref(v_x_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(8u);
v___x_956_ = lean_nat_to_int(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(9u);
v___x_967_ = lean_nat_to_int(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg(lean_object* v_x_971_){
_start:
{
lean_object* v_name_972_; lean_object* v_cidx_973_; lean_object* v_size_974_; lean_object* v_usize_975_; lean_object* v_ssize_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_name_972_ = lean_ctor_get(v_x_971_, 0);
lean_inc(v_name_972_);
v_cidx_973_ = lean_ctor_get(v_x_971_, 1);
lean_inc(v_cidx_973_);
v_size_974_ = lean_ctor_get(v_x_971_, 2);
lean_inc(v_size_974_);
v_usize_975_ = lean_ctor_get(v_x_971_, 3);
lean_inc(v_usize_975_);
v_ssize_976_ = lean_ctor_get(v_x_971_, 4);
lean_inc(v_ssize_976_);
lean_dec_ref(v_x_971_);
v___x_977_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__5));
v___x_978_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3));
v___x_979_ = lean_obj_once(&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4, &l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once, _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = l_Lean_Name_reprPrec(v_name_972_, v___x_980_);
v___x_982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_979_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = 0;
v___x_984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*1, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_978_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_box(1);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_977_);
v___x_993_ = l_Nat_reprFast(v_cidx_973_);
v___x_994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_979_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*1, v___x_983_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_992_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_986_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_988_);
v___x_1000_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_977_);
v___x_1003_ = l_Nat_reprFast(v_size_974_);
v___x_1004_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_979_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_983_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1002_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_986_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_988_);
v___x_1010_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_977_);
v___x_1013_ = lean_obj_once(&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11, &l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once, _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11);
v___x_1014_ = l_Nat_reprFast(v_usize_975_);
v___x_1015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v___x_983_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1012_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_986_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_988_);
v___x_1021_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13));
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_977_);
v___x_1024_ = l_Nat_reprFast(v_ssize_976_);
v___x_1025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1013_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*1, v___x_983_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1023_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_1030_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1028_);
v___x_1032_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1029_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_983_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr(lean_object* v_x_1036_, lean_object* v_prec_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_IR_instReprCtorInfo_repr___redArg(v_x_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr___boxed(lean_object* v_x_1039_, lean_object* v_prec_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_IR_instReprCtorInfo_repr(v_x_1039_, v_prec_1040_);
lean_dec(v_prec_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object* v_info_1044_){
_start:
{
lean_object* v_size_1045_; lean_object* v_usize_1046_; lean_object* v_ssize_1047_; uint8_t v___y_1049_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_size_1045_ = lean_ctor_get(v_info_1044_, 2);
v_usize_1046_ = lean_ctor_get(v_info_1044_, 3);
v_ssize_1047_ = lean_ctor_get(v_info_1044_, 4);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_nat_dec_lt(v___x_1052_, v_size_1045_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v_usize_1046_);
v___y_1049_ = v___x_1054_;
goto v___jp_1048_;
}
else
{
v___y_1049_ = v___x_1053_;
goto v___jp_1048_;
}
v___jp_1048_:
{
if (v___y_1049_ == 0)
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_nat_dec_lt(v___x_1050_, v_ssize_1047_);
return v___x_1051_;
}
else
{
return v___y_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object* v_info_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_IR_CtorInfo_isRef(v_info_1055_);
lean_dec_ref(v_info_1055_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object* v_info_1058_){
_start:
{
uint8_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = l_Lean_IR_CtorInfo_isRef(v_info_1058_);
v___x_1060_ = lean_bool_not(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object* v_info_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lean_IR_CtorInfo_isScalar(v_info_1061_);
lean_dec_ref(v_info_1061_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type(lean_object* v_info_1064_){
_start:
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Lean_IR_CtorInfo_isRef(v_info_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_box(12);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(7);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type___boxed(lean_object* v_info_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_IR_CtorInfo_type(v_info_1068_);
lean_dec_ref(v_info_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx(lean_object* v_x_1070_){
_start:
{
switch(lean_obj_tag(v_x_1070_))
{
case 0:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
return v___x_1071_;
}
case 1:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
return v___x_1072_;
}
case 2:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_unsigned_to_nat(2u);
return v___x_1073_;
}
case 3:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_unsigned_to_nat(3u);
return v___x_1074_;
}
case 4:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_unsigned_to_nat(4u);
return v___x_1075_;
}
case 5:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_unsigned_to_nat(5u);
return v___x_1076_;
}
case 6:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_unsigned_to_nat(6u);
return v___x_1077_;
}
case 7:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_unsigned_to_nat(7u);
return v___x_1078_;
}
case 8:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_unsigned_to_nat(8u);
return v___x_1079_;
}
case 9:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_unsigned_to_nat(9u);
return v___x_1080_;
}
case 10:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_unsigned_to_nat(10u);
return v___x_1081_;
}
case 11:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_unsigned_to_nat(11u);
return v___x_1082_;
}
default: 
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_unsigned_to_nat(12u);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___boxed(lean_object* v_x_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_IR_Expr_ctorIdx(v_x_1084_);
lean_dec_ref(v_x_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___redArg(lean_object* v_t_1086_, lean_object* v_k_1087_){
_start:
{
switch(lean_obj_tag(v_t_1086_))
{
case 0:
{
lean_object* v_i_1088_; lean_object* v_ys_1089_; lean_object* v___x_1090_; 
v_i_1088_ = lean_ctor_get(v_t_1086_, 0);
lean_inc_ref(v_i_1088_);
v_ys_1089_ = lean_ctor_get(v_t_1086_, 1);
lean_inc_ref(v_ys_1089_);
lean_dec_ref_known(v_t_1086_, 2);
v___x_1090_ = lean_apply_2(v_k_1087_, v_i_1088_, v_ys_1089_);
return v___x_1090_;
}
case 2:
{
lean_object* v_x_1091_; lean_object* v_i_1092_; uint8_t v_updtHeader_1093_; lean_object* v_ys_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_x_1091_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_x_1091_);
v_i_1092_ = lean_ctor_get(v_t_1086_, 1);
lean_inc_ref(v_i_1092_);
v_updtHeader_1093_ = lean_ctor_get_uint8(v_t_1086_, sizeof(void*)*3);
v_ys_1094_ = lean_ctor_get(v_t_1086_, 2);
lean_inc_ref(v_ys_1094_);
lean_dec_ref_known(v_t_1086_, 3);
v___x_1095_ = lean_box(v_updtHeader_1093_);
v___x_1096_ = lean_apply_4(v_k_1087_, v_x_1091_, v_i_1092_, v___x_1095_, v_ys_1094_);
return v___x_1096_;
}
case 5:
{
lean_object* v_n_1097_; lean_object* v_offset_1098_; lean_object* v_x_1099_; lean_object* v___x_1100_; 
v_n_1097_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_n_1097_);
v_offset_1098_ = lean_ctor_get(v_t_1086_, 1);
lean_inc(v_offset_1098_);
v_x_1099_ = lean_ctor_get(v_t_1086_, 2);
lean_inc(v_x_1099_);
lean_dec_ref_known(v_t_1086_, 3);
v___x_1100_ = lean_apply_3(v_k_1087_, v_n_1097_, v_offset_1098_, v_x_1099_);
return v___x_1100_;
}
case 6:
{
lean_object* v_c_1101_; lean_object* v_ys_1102_; lean_object* v___x_1103_; 
v_c_1101_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_c_1101_);
v_ys_1102_ = lean_ctor_get(v_t_1086_, 1);
lean_inc_ref(v_ys_1102_);
lean_dec_ref_known(v_t_1086_, 2);
v___x_1103_ = lean_apply_2(v_k_1087_, v_c_1101_, v_ys_1102_);
return v___x_1103_;
}
case 7:
{
lean_object* v_c_1104_; lean_object* v_ys_1105_; lean_object* v___x_1106_; 
v_c_1104_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_c_1104_);
v_ys_1105_ = lean_ctor_get(v_t_1086_, 1);
lean_inc_ref(v_ys_1105_);
lean_dec_ref_known(v_t_1086_, 2);
v___x_1106_ = lean_apply_2(v_k_1087_, v_c_1104_, v_ys_1105_);
return v___x_1106_;
}
case 8:
{
lean_object* v_x_1107_; lean_object* v_ys_1108_; lean_object* v___x_1109_; 
v_x_1107_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_x_1107_);
v_ys_1108_ = lean_ctor_get(v_t_1086_, 1);
lean_inc_ref(v_ys_1108_);
lean_dec_ref_known(v_t_1086_, 2);
v___x_1109_ = lean_apply_2(v_k_1087_, v_x_1107_, v_ys_1108_);
return v___x_1109_;
}
case 10:
{
lean_object* v_x_1110_; lean_object* v___x_1111_; 
v_x_1110_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_x_1110_);
lean_dec_ref_known(v_t_1086_, 1);
v___x_1111_ = lean_apply_1(v_k_1087_, v_x_1110_);
return v___x_1111_;
}
case 11:
{
lean_object* v_v_1112_; lean_object* v___x_1113_; 
v_v_1112_ = lean_ctor_get(v_t_1086_, 0);
lean_inc_ref(v_v_1112_);
lean_dec_ref_known(v_t_1086_, 1);
v___x_1113_ = lean_apply_1(v_k_1087_, v_v_1112_);
return v___x_1113_;
}
case 12:
{
lean_object* v_x_1114_; lean_object* v___x_1115_; 
v_x_1114_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_x_1114_);
lean_dec_ref_known(v_t_1086_, 1);
v___x_1115_ = lean_apply_1(v_k_1087_, v_x_1114_);
return v___x_1115_;
}
default: 
{
lean_object* v_n_1116_; lean_object* v_x_1117_; lean_object* v___x_1118_; 
v_n_1116_ = lean_ctor_get(v_t_1086_, 0);
lean_inc(v_n_1116_);
v_x_1117_ = lean_ctor_get(v_t_1086_, 1);
lean_inc(v_x_1117_);
lean_dec_ref(v_t_1086_);
v___x_1118_ = lean_apply_2(v_k_1087_, v_n_1116_, v_x_1117_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim(lean_object* v_motive_1119_, lean_object* v_ctorIdx_1120_, lean_object* v_t_1121_, lean_object* v_h_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1121_, v_k_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___boxed(lean_object* v_motive_1125_, lean_object* v_ctorIdx_1126_, lean_object* v_t_1127_, lean_object* v_h_1128_, lean_object* v_k_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_IR_Expr_ctorElim(v_motive_1125_, v_ctorIdx_1126_, v_t_1127_, v_h_1128_, v_k_1129_);
lean_dec(v_ctorIdx_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim___redArg(lean_object* v_t_1131_, lean_object* v_ctor_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1131_, v_ctor_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim(lean_object* v_motive_1134_, lean_object* v_t_1135_, lean_object* v_h_1136_, lean_object* v_ctor_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1135_, v_ctor_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim___redArg(lean_object* v_t_1139_, lean_object* v_reset_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1139_, v_reset_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim(lean_object* v_motive_1142_, lean_object* v_t_1143_, lean_object* v_h_1144_, lean_object* v_reset_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1143_, v_reset_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim___redArg(lean_object* v_t_1147_, lean_object* v_reuse_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1147_, v_reuse_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim(lean_object* v_motive_1150_, lean_object* v_t_1151_, lean_object* v_h_1152_, lean_object* v_reuse_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1151_, v_reuse_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim___redArg(lean_object* v_t_1155_, lean_object* v_proj_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1155_, v_proj_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim(lean_object* v_motive_1158_, lean_object* v_t_1159_, lean_object* v_h_1160_, lean_object* v_proj_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1159_, v_proj_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim___redArg(lean_object* v_t_1163_, lean_object* v_uproj_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1163_, v_uproj_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim(lean_object* v_motive_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_uproj_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1167_, v_uproj_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim___redArg(lean_object* v_t_1171_, lean_object* v_sproj_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1171_, v_sproj_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim(lean_object* v_motive_1174_, lean_object* v_t_1175_, lean_object* v_h_1176_, lean_object* v_sproj_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1175_, v_sproj_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim___redArg(lean_object* v_t_1179_, lean_object* v_fap_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1179_, v_fap_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim(lean_object* v_motive_1182_, lean_object* v_t_1183_, lean_object* v_h_1184_, lean_object* v_fap_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1183_, v_fap_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim___redArg(lean_object* v_t_1187_, lean_object* v_pap_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1187_, v_pap_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim(lean_object* v_motive_1190_, lean_object* v_t_1191_, lean_object* v_h_1192_, lean_object* v_pap_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1191_, v_pap_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim___redArg(lean_object* v_t_1195_, lean_object* v_ap_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1195_, v_ap_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim(lean_object* v_motive_1198_, lean_object* v_t_1199_, lean_object* v_h_1200_, lean_object* v_ap_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1199_, v_ap_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim___redArg(lean_object* v_t_1203_, lean_object* v_box_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1203_, v_box_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim(lean_object* v_motive_1206_, lean_object* v_t_1207_, lean_object* v_h_1208_, lean_object* v_box_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1207_, v_box_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim___redArg(lean_object* v_t_1211_, lean_object* v_unbox_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1211_, v_unbox_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim(lean_object* v_motive_1214_, lean_object* v_t_1215_, lean_object* v_h_1216_, lean_object* v_unbox_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1215_, v_unbox_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim___redArg(lean_object* v_t_1219_, lean_object* v_lit_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1219_, v_lit_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim(lean_object* v_motive_1222_, lean_object* v_t_1223_, lean_object* v_h_1224_, lean_object* v_lit_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1223_, v_lit_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim___redArg(lean_object* v_t_1227_, lean_object* v_isShared_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1227_, v_isShared_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim(lean_object* v_motive_1230_, lean_object* v_t_1231_, lean_object* v_h_1232_, lean_object* v_isShared_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1231_, v_isShared_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_unsigned_to_nat(5u);
v___x_1258_ = lean_nat_to_int(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_unsigned_to_nat(10u);
v___x_1263_ = lean_nat_to_int(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_unsigned_to_nat(6u);
v___x_1268_ = lean_nat_to_int(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___redArg(lean_object* v_x_1269_){
_start:
{
lean_object* v_x_1270_; uint8_t v_borrow_1271_; lean_object* v_ty_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_x_1270_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_x_1270_);
v_borrow_1271_ = lean_ctor_get_uint8(v_x_1269_, sizeof(void*)*2);
v_ty_1272_ = lean_ctor_get(v_x_1269_, 1);
lean_inc(v_ty_1272_);
lean_dec_ref(v_x_1269_);
v___x_1273_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__5));
v___x_1274_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__3));
v___x_1275_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__4, &l_Lean_IR_instReprParam_repr___redArg___closed__4_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__4);
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_1270_);
v___x_1278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1275_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = 0;
v___x_1280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1274_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2));
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_box(1);
v___x_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__6));
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1273_);
v___x_1289_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__7, &l_Lean_IR_instReprParam_repr___redArg___closed__7_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__7);
v___x_1290_ = l_Bool_repr___redArg(v_borrow_1271_);
v___x_1291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1, v___x_1279_);
v___x_1293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1288_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1282_);
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1284_);
v___x_1296_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__9));
v___x_1297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1273_);
v___x_1299_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__10, &l_Lean_IR_instReprParam_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__10);
v___x_1300_ = l_Lean_IR_instReprIRType_repr(v_ty_1272_, v___x_1276_);
v___x_1301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*1, v___x_1279_);
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1298_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_1305_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_1306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1303_);
v___x_1307_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_1308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1304_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*1, v___x_1279_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr(lean_object* v_x_1311_, lean_object* v_prec_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_IR_instReprParam_repr___redArg(v_x_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___boxed(lean_object* v_x_1314_, lean_object* v_prec_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_IR_instReprParam_repr(v_x_1314_, v_prec_1315_);
lean_dec(v_prec_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx(lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___boxed(lean_object* v_x_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_IR_Alt_ctorIdx(v_x_1322_);
lean_dec_ref(v_x_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___redArg(lean_object* v_t_1324_, lean_object* v_k_1325_){
_start:
{
if (lean_obj_tag(v_t_1324_) == 0)
{
lean_object* v_info_1326_; lean_object* v_b_1327_; lean_object* v___x_1328_; 
v_info_1326_ = lean_ctor_get(v_t_1324_, 0);
lean_inc_ref(v_info_1326_);
v_b_1327_ = lean_ctor_get(v_t_1324_, 1);
lean_inc(v_b_1327_);
lean_dec_ref_known(v_t_1324_, 2);
v___x_1328_ = lean_apply_2(v_k_1325_, v_info_1326_, v_b_1327_);
return v___x_1328_;
}
else
{
lean_object* v_b_1329_; lean_object* v___x_1330_; 
v_b_1329_ = lean_ctor_get(v_t_1324_, 0);
lean_inc(v_b_1329_);
lean_dec_ref_known(v_t_1324_, 1);
v___x_1330_ = lean_apply_1(v_k_1325_, v_b_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim(lean_object* v_motive__1_1331_, lean_object* v_ctorIdx_1332_, lean_object* v_t_1333_, lean_object* v_h_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1333_, v_k_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___boxed(lean_object* v_motive__1_1337_, lean_object* v_ctorIdx_1338_, lean_object* v_t_1339_, lean_object* v_h_1340_, lean_object* v_k_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_IR_Alt_ctorElim(v_motive__1_1337_, v_ctorIdx_1338_, v_t_1339_, v_h_1340_, v_k_1341_);
lean_dec(v_ctorIdx_1338_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim___redArg(lean_object* v_t_1343_, lean_object* v_ctor_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1343_, v_ctor_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim(lean_object* v_motive__1_1346_, lean_object* v_t_1347_, lean_object* v_h_1348_, lean_object* v_ctor_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1347_, v_ctor_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim___redArg(lean_object* v_t_1351_, lean_object* v_default_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1351_, v_default_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim(lean_object* v_motive__1_1354_, lean_object* v_t_1355_, lean_object* v_h_1356_, lean_object* v_default_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1355_, v_default_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx(lean_object* v_x_1359_){
_start:
{
switch(lean_obj_tag(v_x_1359_))
{
case 0:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
return v___x_1360_;
}
case 1:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_unsigned_to_nat(1u);
return v___x_1361_;
}
case 2:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_unsigned_to_nat(2u);
return v___x_1362_;
}
case 3:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_unsigned_to_nat(3u);
return v___x_1363_;
}
case 4:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_unsigned_to_nat(4u);
return v___x_1364_;
}
case 5:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_unsigned_to_nat(5u);
return v___x_1365_;
}
case 6:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_unsigned_to_nat(6u);
return v___x_1366_;
}
case 7:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_unsigned_to_nat(7u);
return v___x_1367_;
}
case 8:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_unsigned_to_nat(8u);
return v___x_1368_;
}
case 9:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(9u);
return v___x_1369_;
}
case 10:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(10u);
return v___x_1370_;
}
case 11:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_unsigned_to_nat(11u);
return v___x_1371_;
}
default: 
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_unsigned_to_nat(12u);
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___boxed(lean_object* v_x_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_IR_FnBody_ctorIdx(v_x_1373_);
lean_dec(v_x_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___redArg(lean_object* v_t_1375_, lean_object* v_k_1376_){
_start:
{
switch(lean_obj_tag(v_t_1375_))
{
case 0:
{
lean_object* v_x_1377_; lean_object* v_ty_1378_; lean_object* v_e_1379_; lean_object* v_b_1380_; lean_object* v___x_1381_; 
v_x_1377_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1377_);
v_ty_1378_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_ty_1378_);
v_e_1379_ = lean_ctor_get(v_t_1375_, 2);
lean_inc_ref(v_e_1379_);
v_b_1380_ = lean_ctor_get(v_t_1375_, 3);
lean_inc(v_b_1380_);
lean_dec_ref_known(v_t_1375_, 4);
v___x_1381_ = lean_apply_4(v_k_1376_, v_x_1377_, v_ty_1378_, v_e_1379_, v_b_1380_);
return v___x_1381_;
}
case 1:
{
lean_object* v_j_1382_; lean_object* v_xs_1383_; lean_object* v_v_1384_; lean_object* v_b_1385_; lean_object* v___x_1386_; 
v_j_1382_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_j_1382_);
v_xs_1383_ = lean_ctor_get(v_t_1375_, 1);
lean_inc_ref(v_xs_1383_);
v_v_1384_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_v_1384_);
v_b_1385_ = lean_ctor_get(v_t_1375_, 3);
lean_inc(v_b_1385_);
lean_dec_ref_known(v_t_1375_, 4);
v___x_1386_ = lean_apply_4(v_k_1376_, v_j_1382_, v_xs_1383_, v_v_1384_, v_b_1385_);
return v___x_1386_;
}
case 3:
{
lean_object* v_x_1387_; lean_object* v_cidx_1388_; lean_object* v_b_1389_; lean_object* v___x_1390_; 
v_x_1387_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1387_);
v_cidx_1388_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_cidx_1388_);
v_b_1389_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_b_1389_);
lean_dec_ref_known(v_t_1375_, 3);
v___x_1390_ = lean_apply_3(v_k_1376_, v_x_1387_, v_cidx_1388_, v_b_1389_);
return v___x_1390_;
}
case 5:
{
lean_object* v_x_1391_; lean_object* v_i_1392_; lean_object* v_offset_1393_; lean_object* v_y_1394_; lean_object* v_ty_1395_; lean_object* v_b_1396_; lean_object* v___x_1397_; 
v_x_1391_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1391_);
v_i_1392_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_i_1392_);
v_offset_1393_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_offset_1393_);
v_y_1394_ = lean_ctor_get(v_t_1375_, 3);
lean_inc(v_y_1394_);
v_ty_1395_ = lean_ctor_get(v_t_1375_, 4);
lean_inc(v_ty_1395_);
v_b_1396_ = lean_ctor_get(v_t_1375_, 5);
lean_inc(v_b_1396_);
lean_dec_ref_known(v_t_1375_, 6);
v___x_1397_ = lean_apply_6(v_k_1376_, v_x_1391_, v_i_1392_, v_offset_1393_, v_y_1394_, v_ty_1395_, v_b_1396_);
return v___x_1397_;
}
case 6:
{
lean_object* v_x_1398_; lean_object* v_n_1399_; uint8_t v_c_1400_; uint8_t v_persistent_1401_; lean_object* v_b_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_x_1398_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1398_);
v_n_1399_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_n_1399_);
v_c_1400_ = lean_ctor_get_uint8(v_t_1375_, sizeof(void*)*3);
v_persistent_1401_ = lean_ctor_get_uint8(v_t_1375_, sizeof(void*)*3 + 1);
v_b_1402_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_b_1402_);
lean_dec_ref_known(v_t_1375_, 3);
v___x_1403_ = lean_box(v_c_1400_);
v___x_1404_ = lean_box(v_persistent_1401_);
v___x_1405_ = lean_apply_5(v_k_1376_, v_x_1398_, v_n_1399_, v___x_1403_, v___x_1404_, v_b_1402_);
return v___x_1405_;
}
case 7:
{
lean_object* v_x_1406_; lean_object* v_n_1407_; uint8_t v_c_1408_; uint8_t v_persistent_1409_; lean_object* v_b_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_x_1406_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1406_);
v_n_1407_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_n_1407_);
v_c_1408_ = lean_ctor_get_uint8(v_t_1375_, sizeof(void*)*3);
v_persistent_1409_ = lean_ctor_get_uint8(v_t_1375_, sizeof(void*)*3 + 1);
v_b_1410_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_b_1410_);
lean_dec_ref_known(v_t_1375_, 3);
v___x_1411_ = lean_box(v_c_1408_);
v___x_1412_ = lean_box(v_persistent_1409_);
v___x_1413_ = lean_apply_5(v_k_1376_, v_x_1406_, v_n_1407_, v___x_1411_, v___x_1412_, v_b_1410_);
return v___x_1413_;
}
case 8:
{
lean_object* v_x_1414_; lean_object* v_b_1415_; lean_object* v___x_1416_; 
v_x_1414_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1414_);
v_b_1415_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_b_1415_);
lean_dec_ref_known(v_t_1375_, 2);
v___x_1416_ = lean_apply_2(v_k_1376_, v_x_1414_, v_b_1415_);
return v___x_1416_;
}
case 9:
{
lean_object* v_tid_1417_; lean_object* v_x_1418_; lean_object* v_xType_1419_; lean_object* v_cs_1420_; lean_object* v___x_1421_; 
v_tid_1417_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_tid_1417_);
v_x_1418_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_x_1418_);
v_xType_1419_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_xType_1419_);
v_cs_1420_ = lean_ctor_get(v_t_1375_, 3);
lean_inc_ref(v_cs_1420_);
lean_dec_ref_known(v_t_1375_, 4);
v___x_1421_ = lean_apply_4(v_k_1376_, v_tid_1417_, v_x_1418_, v_xType_1419_, v_cs_1420_);
return v___x_1421_;
}
case 10:
{
lean_object* v_x_1422_; lean_object* v___x_1423_; 
v_x_1422_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1422_);
lean_dec_ref_known(v_t_1375_, 1);
v___x_1423_ = lean_apply_1(v_k_1376_, v_x_1422_);
return v___x_1423_;
}
case 11:
{
lean_object* v_j_1424_; lean_object* v_ys_1425_; lean_object* v___x_1426_; 
v_j_1424_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_j_1424_);
v_ys_1425_ = lean_ctor_get(v_t_1375_, 1);
lean_inc_ref(v_ys_1425_);
lean_dec_ref_known(v_t_1375_, 2);
v___x_1426_ = lean_apply_2(v_k_1376_, v_j_1424_, v_ys_1425_);
return v___x_1426_;
}
case 12:
{
return v_k_1376_;
}
default: 
{
lean_object* v_x_1427_; lean_object* v_i_1428_; lean_object* v_y_1429_; lean_object* v_b_1430_; lean_object* v___x_1431_; 
v_x_1427_ = lean_ctor_get(v_t_1375_, 0);
lean_inc(v_x_1427_);
v_i_1428_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_i_1428_);
v_y_1429_ = lean_ctor_get(v_t_1375_, 2);
lean_inc(v_y_1429_);
v_b_1430_ = lean_ctor_get(v_t_1375_, 3);
lean_inc(v_b_1430_);
lean_dec(v_t_1375_);
v___x_1431_ = lean_apply_4(v_k_1376_, v_x_1427_, v_i_1428_, v_y_1429_, v_b_1430_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim(lean_object* v_motive__2_1432_, lean_object* v_ctorIdx_1433_, lean_object* v_t_1434_, lean_object* v_h_1435_, lean_object* v_k_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1434_, v_k_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___boxed(lean_object* v_motive__2_1438_, lean_object* v_ctorIdx_1439_, lean_object* v_t_1440_, lean_object* v_h_1441_, lean_object* v_k_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_IR_FnBody_ctorElim(v_motive__2_1438_, v_ctorIdx_1439_, v_t_1440_, v_h_1441_, v_k_1442_);
lean_dec(v_ctorIdx_1439_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim___redArg(lean_object* v_t_1444_, lean_object* v_vdecl_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1444_, v_vdecl_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim(lean_object* v_motive__2_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_vdecl_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1448_, v_vdecl_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim___redArg(lean_object* v_t_1452_, lean_object* v_jdecl_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1452_, v_jdecl_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim(lean_object* v_motive__2_1455_, lean_object* v_t_1456_, lean_object* v_h_1457_, lean_object* v_jdecl_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1456_, v_jdecl_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim___redArg(lean_object* v_t_1460_, lean_object* v_set_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1460_, v_set_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim(lean_object* v_motive__2_1463_, lean_object* v_t_1464_, lean_object* v_h_1465_, lean_object* v_set_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1464_, v_set_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim___redArg(lean_object* v_t_1468_, lean_object* v_setTag_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1468_, v_setTag_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim(lean_object* v_motive__2_1471_, lean_object* v_t_1472_, lean_object* v_h_1473_, lean_object* v_setTag_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1472_, v_setTag_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim___redArg(lean_object* v_t_1476_, lean_object* v_uset_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1476_, v_uset_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim(lean_object* v_motive__2_1479_, lean_object* v_t_1480_, lean_object* v_h_1481_, lean_object* v_uset_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1480_, v_uset_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim___redArg(lean_object* v_t_1484_, lean_object* v_sset_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1484_, v_sset_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim(lean_object* v_motive__2_1487_, lean_object* v_t_1488_, lean_object* v_h_1489_, lean_object* v_sset_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1488_, v_sset_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim___redArg(lean_object* v_t_1492_, lean_object* v_inc_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1492_, v_inc_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim(lean_object* v_motive__2_1495_, lean_object* v_t_1496_, lean_object* v_h_1497_, lean_object* v_inc_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1496_, v_inc_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim___redArg(lean_object* v_t_1500_, lean_object* v_dec_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1500_, v_dec_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim(lean_object* v_motive__2_1503_, lean_object* v_t_1504_, lean_object* v_h_1505_, lean_object* v_dec_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1504_, v_dec_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim___redArg(lean_object* v_t_1508_, lean_object* v_del_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1508_, v_del_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim(lean_object* v_motive__2_1511_, lean_object* v_t_1512_, lean_object* v_h_1513_, lean_object* v_del_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1512_, v_del_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim___redArg(lean_object* v_t_1516_, lean_object* v_case_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1516_, v_case_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim(lean_object* v_motive__2_1519_, lean_object* v_t_1520_, lean_object* v_h_1521_, lean_object* v_case_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1520_, v_case_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim___redArg(lean_object* v_t_1524_, lean_object* v_ret_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1524_, v_ret_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim(lean_object* v_motive__2_1527_, lean_object* v_t_1528_, lean_object* v_h_1529_, lean_object* v_ret_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1528_, v_ret_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim___redArg(lean_object* v_t_1532_, lean_object* v_jmp_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1532_, v_jmp_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim(lean_object* v_motive__2_1535_, lean_object* v_t_1536_, lean_object* v_h_1537_, lean_object* v_jmp_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1536_, v_jmp_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim___redArg(lean_object* v_t_1540_, lean_object* v_unreachable_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1540_, v_unreachable_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim(lean_object* v_motive__2_1543_, lean_object* v_t_1544_, lean_object* v_h_1545_, lean_object* v_unreachable_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1544_, v_unreachable_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_nil(void){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_box(12);
return v___x_1562_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* v_x_1563_){
_start:
{
switch(lean_obj_tag(v_x_1563_))
{
case 9:
{
uint8_t v___x_1564_; 
v___x_1564_ = 1;
return v___x_1564_;
}
case 10:
{
uint8_t v___x_1565_; 
v___x_1565_ = 1;
return v___x_1565_;
}
case 11:
{
uint8_t v___x_1566_; 
v___x_1566_ = 1;
return v___x_1566_;
}
case 12:
{
uint8_t v___x_1567_; 
v___x_1567_ = 1;
return v___x_1567_;
}
default: 
{
uint8_t v___x_1568_; 
v___x_1568_ = 0;
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object* v_x_1569_){
_start:
{
uint8_t v_res_1570_; lean_object* v_r_1571_; 
v_res_1570_ = l_Lean_IR_FnBody_isTerminal(v_x_1569_);
lean_dec(v_x_1569_);
v_r_1571_ = lean_box(v_res_1570_);
return v_r_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object* v_x_1572_){
_start:
{
switch(lean_obj_tag(v_x_1572_))
{
case 0:
{
lean_object* v_b_1573_; 
v_b_1573_ = lean_ctor_get(v_x_1572_, 3);
lean_inc(v_b_1573_);
return v_b_1573_;
}
case 1:
{
lean_object* v_b_1574_; 
v_b_1574_ = lean_ctor_get(v_x_1572_, 3);
lean_inc(v_b_1574_);
return v_b_1574_;
}
case 2:
{
lean_object* v_b_1575_; 
v_b_1575_ = lean_ctor_get(v_x_1572_, 3);
lean_inc(v_b_1575_);
return v_b_1575_;
}
case 4:
{
lean_object* v_b_1576_; 
v_b_1576_ = lean_ctor_get(v_x_1572_, 3);
lean_inc(v_b_1576_);
return v_b_1576_;
}
case 5:
{
lean_object* v_b_1577_; 
v_b_1577_ = lean_ctor_get(v_x_1572_, 5);
lean_inc(v_b_1577_);
return v_b_1577_;
}
case 3:
{
lean_object* v_b_1578_; 
v_b_1578_ = lean_ctor_get(v_x_1572_, 2);
lean_inc(v_b_1578_);
return v_b_1578_;
}
case 6:
{
lean_object* v_b_1579_; 
v_b_1579_ = lean_ctor_get(v_x_1572_, 2);
lean_inc(v_b_1579_);
return v_b_1579_;
}
case 7:
{
lean_object* v_b_1580_; 
v_b_1580_ = lean_ctor_get(v_x_1572_, 2);
lean_inc(v_b_1580_);
return v_b_1580_;
}
case 8:
{
lean_object* v_b_1581_; 
v_b_1581_ = lean_ctor_get(v_x_1572_, 1);
lean_inc(v_b_1581_);
return v_b_1581_;
}
default: 
{
lean_inc(v_x_1572_);
return v_x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* v_x_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_IR_FnBody_body(v_x_1582_);
lean_dec(v_x_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object* v_x_1584_, lean_object* v_x_1585_){
_start:
{
switch(lean_obj_tag(v_x_1584_))
{
case 0:
{
lean_object* v_x_1586_; lean_object* v_ty_1587_; lean_object* v_e_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_x_1586_ = lean_ctor_get(v_x_1584_, 0);
v_ty_1587_ = lean_ctor_get(v_x_1584_, 1);
v_e_1588_ = lean_ctor_get(v_x_1584_, 2);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v_x_1584_, 3);
lean_dec(v_unused_1596_);
v___x_1590_ = v_x_1584_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_e_1588_);
lean_inc(v_ty_1587_);
lean_inc(v_x_1586_);
lean_dec(v_x_1584_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 3, v_x_1585_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_x_1586_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_ty_1587_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_e_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_x_1585_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
case 1:
{
lean_object* v_j_1597_; lean_object* v_xs_1598_; lean_object* v_v_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_j_1597_ = lean_ctor_get(v_x_1584_, 0);
v_xs_1598_ = lean_ctor_get(v_x_1584_, 1);
v_v_1599_ = lean_ctor_get(v_x_1584_, 2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_x_1584_, 3);
lean_dec(v_unused_1607_);
v___x_1601_ = v_x_1584_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_v_1599_);
lean_inc(v_xs_1598_);
lean_inc(v_j_1597_);
lean_dec(v_x_1584_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 3, v_x_1585_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_j_1597_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_xs_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1599_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_x_1585_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
case 2:
{
lean_object* v_x_1608_; lean_object* v_i_1609_; lean_object* v_y_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_x_1608_ = lean_ctor_get(v_x_1584_, 0);
v_i_1609_ = lean_ctor_get(v_x_1584_, 1);
v_y_1610_ = lean_ctor_get(v_x_1584_, 2);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v_x_1584_, 3);
lean_dec(v_unused_1618_);
v___x_1612_ = v_x_1584_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_y_1610_);
lean_inc(v_i_1609_);
lean_inc(v_x_1608_);
lean_dec(v_x_1584_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 3, v_x_1585_);
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_x_1608_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_i_1609_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_y_1610_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_x_1585_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
case 4:
{
lean_object* v_x_1619_; lean_object* v_i_1620_; lean_object* v_y_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_x_1619_ = lean_ctor_get(v_x_1584_, 0);
v_i_1620_ = lean_ctor_get(v_x_1584_, 1);
v_y_1621_ = lean_ctor_get(v_x_1584_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_x_1584_, 3);
lean_dec(v_unused_1629_);
v___x_1623_ = v_x_1584_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_y_1621_);
lean_inc(v_i_1620_);
lean_inc(v_x_1619_);
lean_dec(v_x_1584_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 3, v_x_1585_);
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_x_1619_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_i_1620_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_y_1621_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_x_1585_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
case 5:
{
lean_object* v_x_1630_; lean_object* v_i_1631_; lean_object* v_offset_1632_; lean_object* v_y_1633_; lean_object* v_ty_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_x_1630_ = lean_ctor_get(v_x_1584_, 0);
v_i_1631_ = lean_ctor_get(v_x_1584_, 1);
v_offset_1632_ = lean_ctor_get(v_x_1584_, 2);
v_y_1633_ = lean_ctor_get(v_x_1584_, 3);
v_ty_1634_ = lean_ctor_get(v_x_1584_, 4);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_x_1584_, 5);
lean_dec(v_unused_1642_);
v___x_1636_ = v_x_1584_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_ty_1634_);
lean_inc(v_y_1633_);
lean_inc(v_offset_1632_);
lean_inc(v_i_1631_);
lean_inc(v_x_1630_);
lean_dec(v_x_1584_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 5, v_x_1585_);
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_x_1630_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_i_1631_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_offset_1632_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_y_1633_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_ty_1634_);
lean_ctor_set(v_reuseFailAlloc_1640_, 5, v_x_1585_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
case 3:
{
lean_object* v_x_1643_; lean_object* v_cidx_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_x_1643_ = lean_ctor_get(v_x_1584_, 0);
v_cidx_1644_ = lean_ctor_get(v_x_1584_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v_x_1584_, 2);
lean_dec(v_unused_1652_);
v___x_1646_ = v_x_1584_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_cidx_1644_);
lean_inc(v_x_1643_);
lean_dec(v_x_1584_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 2, v_x_1585_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_x_1643_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_cidx_1644_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_x_1585_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
case 6:
{
lean_object* v_x_1653_; lean_object* v_n_1654_; uint8_t v_c_1655_; uint8_t v_persistent_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_x_1653_ = lean_ctor_get(v_x_1584_, 0);
v_n_1654_ = lean_ctor_get(v_x_1584_, 1);
v_c_1655_ = lean_ctor_get_uint8(v_x_1584_, sizeof(void*)*3);
v_persistent_1656_ = lean_ctor_get_uint8(v_x_1584_, sizeof(void*)*3 + 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v_x_1584_, 2);
lean_dec(v_unused_1664_);
v___x_1658_ = v_x_1584_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_n_1654_);
lean_inc(v_x_1653_);
lean_dec(v_x_1584_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 2, v_x_1585_);
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_x_1653_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_n_1654_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_x_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*3, v_c_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1662_, sizeof(void*)*3 + 1, v_persistent_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
case 7:
{
lean_object* v_x_1665_; lean_object* v_n_1666_; uint8_t v_c_1667_; uint8_t v_persistent_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_x_1665_ = lean_ctor_get(v_x_1584_, 0);
v_n_1666_ = lean_ctor_get(v_x_1584_, 1);
v_c_1667_ = lean_ctor_get_uint8(v_x_1584_, sizeof(void*)*3);
v_persistent_1668_ = lean_ctor_get_uint8(v_x_1584_, sizeof(void*)*3 + 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v_x_1584_, 2);
lean_dec(v_unused_1676_);
v___x_1670_ = v_x_1584_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_n_1666_);
lean_inc(v_x_1665_);
lean_dec(v_x_1584_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 2, v_x_1585_);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_x_1665_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_n_1666_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_x_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*3, v_c_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*3 + 1, v_persistent_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
case 8:
{
lean_object* v_x_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_x_1677_ = lean_ctor_get(v_x_1584_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_x_1584_, 1);
lean_dec(v_unused_1685_);
v___x_1679_ = v_x_1584_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_x_1677_);
lean_dec(v_x_1584_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_x_1585_);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_x_1677_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_x_1585_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
default: 
{
lean_dec(v_x_1585_);
return v_x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object* v_b_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_box(12);
v___x_1688_ = l_Lean_IR_FnBody_setBody(v_b_1686_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object* v_b_1689_){
_start:
{
lean_object* v___y_1691_; 
switch(lean_obj_tag(v_b_1689_))
{
case 0:
{
lean_object* v_b_1695_; 
v_b_1695_ = lean_ctor_get(v_b_1689_, 3);
lean_inc(v_b_1695_);
v___y_1691_ = v_b_1695_;
goto v___jp_1690_;
}
case 1:
{
lean_object* v_b_1696_; 
v_b_1696_ = lean_ctor_get(v_b_1689_, 3);
lean_inc(v_b_1696_);
v___y_1691_ = v_b_1696_;
goto v___jp_1690_;
}
case 2:
{
lean_object* v_b_1697_; 
v_b_1697_ = lean_ctor_get(v_b_1689_, 3);
lean_inc(v_b_1697_);
v___y_1691_ = v_b_1697_;
goto v___jp_1690_;
}
case 4:
{
lean_object* v_b_1698_; 
v_b_1698_ = lean_ctor_get(v_b_1689_, 3);
lean_inc(v_b_1698_);
v___y_1691_ = v_b_1698_;
goto v___jp_1690_;
}
case 5:
{
lean_object* v_b_1699_; 
v_b_1699_ = lean_ctor_get(v_b_1689_, 5);
lean_inc(v_b_1699_);
v___y_1691_ = v_b_1699_;
goto v___jp_1690_;
}
case 3:
{
lean_object* v_b_1700_; 
v_b_1700_ = lean_ctor_get(v_b_1689_, 2);
lean_inc(v_b_1700_);
v___y_1691_ = v_b_1700_;
goto v___jp_1690_;
}
case 6:
{
lean_object* v_b_1701_; 
v_b_1701_ = lean_ctor_get(v_b_1689_, 2);
lean_inc(v_b_1701_);
v___y_1691_ = v_b_1701_;
goto v___jp_1690_;
}
case 7:
{
lean_object* v_b_1702_; 
v_b_1702_ = lean_ctor_get(v_b_1689_, 2);
lean_inc(v_b_1702_);
v___y_1691_ = v_b_1702_;
goto v___jp_1690_;
}
case 8:
{
lean_object* v_b_1703_; 
v_b_1703_ = lean_ctor_get(v_b_1689_, 1);
lean_inc(v_b_1703_);
v___y_1691_ = v_b_1703_;
goto v___jp_1690_;
}
default: 
{
lean_inc(v_b_1689_);
v___y_1691_ = v_b_1689_;
goto v___jp_1690_;
}
}
v___jp_1690_:
{
lean_object* v___x_1692_; lean_object* v_c_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_box(12);
v_c_1693_ = l_Lean_IR_FnBody_setBody(v_b_1689_, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_c_1693_);
lean_ctor_set(v___x_1694_, 1, v___y_1691_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object* v_x_1704_){
_start:
{
if (lean_obj_tag(v_x_1704_) == 0)
{
lean_object* v_b_1705_; 
v_b_1705_ = lean_ctor_get(v_x_1704_, 1);
lean_inc(v_b_1705_);
return v_b_1705_;
}
else
{
lean_object* v_b_1706_; 
v_b_1706_ = lean_ctor_get(v_x_1704_, 0);
lean_inc(v_b_1706_);
return v_b_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_IR_Alt_body(v_x_1707_);
lean_dec_ref(v_x_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object* v_x_1709_, lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v_info_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_info_1711_ = lean_ctor_get(v_x_1709_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v_x_1709_, 1);
lean_dec(v_unused_1719_);
v___x_1713_ = v_x_1709_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_info_1711_);
lean_dec(v_x_1709_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_x_1710_);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_info_1711_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_x_1710_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v_isSharedCheck_1726_ = !lean_is_exclusive(v_x_1709_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_x_1709_, 0);
lean_dec(v_unused_1727_);
v___x_1721_ = v_x_1709_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_dec(v_x_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v_x_1710_);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_x_1710_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object* v_f_1728_, lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
lean_object* v_info_1730_; lean_object* v_b_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
v_info_1730_ = lean_ctor_get(v_x_1729_, 0);
v_b_1731_ = lean_ctor_get(v_x_1729_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v_x_1729_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_b_1731_);
lean_inc(v_info_1730_);
lean_dec(v_x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_apply_1(v_f_1728_, v_b_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_info_1730_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_b_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_b_1740_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v_x_1729_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_b_1740_);
lean_dec(v_x_1729_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_apply_1(v_f_1728_, v_b_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(lean_object* v_info_1749_, lean_object* v_b_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_info_1749_);
lean_ctor_set(v___x_1751_, 1, v_b_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(lean_object* v_b_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg(lean_object* v_inst_1755_, lean_object* v_f_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v_toApplicative_1758_; 
v_toApplicative_1758_ = lean_ctor_get(v_inst_1755_, 0);
lean_inc_ref(v_toApplicative_1758_);
lean_dec_ref(v_inst_1755_);
if (lean_obj_tag(v_x_1757_) == 0)
{
lean_object* v_toFunctor_1759_; lean_object* v_info_1760_; lean_object* v_b_1761_; lean_object* v_map_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_toFunctor_1759_ = lean_ctor_get(v_toApplicative_1758_, 0);
lean_inc_ref(v_toFunctor_1759_);
lean_dec_ref(v_toApplicative_1758_);
v_info_1760_ = lean_ctor_get(v_x_1757_, 0);
lean_inc_ref(v_info_1760_);
v_b_1761_ = lean_ctor_get(v_x_1757_, 1);
lean_inc(v_b_1761_);
lean_dec_ref_known(v_x_1757_, 2);
v_map_1762_ = lean_ctor_get(v_toFunctor_1759_, 0);
lean_inc(v_map_1762_);
lean_dec_ref(v_toFunctor_1759_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1763_, 0, v_info_1760_);
v___x_1764_ = lean_apply_1(v_f_1756_, v_b_1761_);
v___x_1765_ = lean_apply_4(v_map_1762_, lean_box(0), lean_box(0), v___f_1763_, v___x_1764_);
return v___x_1765_;
}
else
{
lean_object* v_toFunctor_1766_; lean_object* v_b_1767_; lean_object* v_map_1768_; lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_toFunctor_1766_ = lean_ctor_get(v_toApplicative_1758_, 0);
lean_inc_ref(v_toFunctor_1766_);
lean_dec_ref(v_toApplicative_1758_);
v_b_1767_ = lean_ctor_get(v_x_1757_, 0);
lean_inc(v_b_1767_);
lean_dec_ref_known(v_x_1757_, 1);
v_map_1768_ = lean_ctor_get(v_toFunctor_1766_, 0);
lean_inc(v_map_1768_);
lean_dec_ref(v_toFunctor_1766_);
v___f_1769_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_1770_ = lean_apply_1(v_f_1756_, v_b_1767_);
v___x_1771_ = lean_apply_4(v_map_1768_, lean_box(0), lean_box(0), v___f_1769_, v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM(lean_object* v_m_1772_, lean_object* v_inst_1773_, lean_object* v_f_1774_, lean_object* v_x_1775_){
_start:
{
lean_object* v_toApplicative_1776_; 
v_toApplicative_1776_ = lean_ctor_get(v_inst_1773_, 0);
lean_inc_ref(v_toApplicative_1776_);
lean_dec_ref(v_inst_1773_);
if (lean_obj_tag(v_x_1775_) == 0)
{
lean_object* v_toFunctor_1777_; lean_object* v_info_1778_; lean_object* v_b_1779_; lean_object* v_map_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_toFunctor_1777_ = lean_ctor_get(v_toApplicative_1776_, 0);
lean_inc_ref(v_toFunctor_1777_);
lean_dec_ref(v_toApplicative_1776_);
v_info_1778_ = lean_ctor_get(v_x_1775_, 0);
lean_inc_ref(v_info_1778_);
v_b_1779_ = lean_ctor_get(v_x_1775_, 1);
lean_inc(v_b_1779_);
lean_dec_ref_known(v_x_1775_, 2);
v_map_1780_ = lean_ctor_get(v_toFunctor_1777_, 0);
lean_inc(v_map_1780_);
lean_dec_ref(v_toFunctor_1777_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1781_, 0, v_info_1778_);
v___x_1782_ = lean_apply_1(v_f_1774_, v_b_1779_);
v___x_1783_ = lean_apply_4(v_map_1780_, lean_box(0), lean_box(0), v___f_1781_, v___x_1782_);
return v___x_1783_;
}
else
{
lean_object* v_toFunctor_1784_; lean_object* v_b_1785_; lean_object* v_map_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_toFunctor_1784_ = lean_ctor_get(v_toApplicative_1776_, 0);
lean_inc_ref(v_toFunctor_1784_);
lean_dec_ref(v_toApplicative_1776_);
v_b_1785_ = lean_ctor_get(v_x_1775_, 0);
lean_inc(v_b_1785_);
lean_dec_ref_known(v_x_1775_, 1);
v_map_1786_ = lean_ctor_get(v_toFunctor_1784_, 0);
lean_inc(v_map_1786_);
lean_dec_ref(v_toFunctor_1784_);
v___f_1787_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_1788_ = lean_apply_1(v_f_1774_, v_b_1785_);
v___x_1789_ = lean_apply_4(v_map_1786_, lean_box(0), lean_box(0), v___f_1787_, v___x_1788_);
return v___x_1789_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = 1;
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* v_x_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_Lean_IR_Alt_isDefault(v_x_1793_);
lean_dec_ref(v_x_1793_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object* v_bs_1796_, lean_object* v_b_1797_){
_start:
{
lean_object* v___x_1798_; lean_object* v_b_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_box(12);
v_b_1799_ = l_Lean_IR_FnBody_setBody(v_b_1797_, v___x_1798_);
v___x_1800_ = lean_array_push(v_bs_1796_, v_b_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object* v_b_1801_, lean_object* v_r_1802_){
_start:
{
lean_object* v___y_1804_; uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_IR_FnBody_isTerminal(v_b_1801_);
if (v___x_1807_ == 0)
{
switch(lean_obj_tag(v_b_1801_))
{
case 0:
{
lean_object* v_b_1808_; 
v_b_1808_ = lean_ctor_get(v_b_1801_, 3);
lean_inc(v_b_1808_);
v___y_1804_ = v_b_1808_;
goto v___jp_1803_;
}
case 1:
{
lean_object* v_b_1809_; 
v_b_1809_ = lean_ctor_get(v_b_1801_, 3);
lean_inc(v_b_1809_);
v___y_1804_ = v_b_1809_;
goto v___jp_1803_;
}
case 2:
{
lean_object* v_b_1810_; 
v_b_1810_ = lean_ctor_get(v_b_1801_, 3);
lean_inc(v_b_1810_);
v___y_1804_ = v_b_1810_;
goto v___jp_1803_;
}
case 4:
{
lean_object* v_b_1811_; 
v_b_1811_ = lean_ctor_get(v_b_1801_, 3);
lean_inc(v_b_1811_);
v___y_1804_ = v_b_1811_;
goto v___jp_1803_;
}
case 5:
{
lean_object* v_b_1812_; 
v_b_1812_ = lean_ctor_get(v_b_1801_, 5);
lean_inc(v_b_1812_);
v___y_1804_ = v_b_1812_;
goto v___jp_1803_;
}
case 3:
{
lean_object* v_b_1813_; 
v_b_1813_ = lean_ctor_get(v_b_1801_, 2);
lean_inc(v_b_1813_);
v___y_1804_ = v_b_1813_;
goto v___jp_1803_;
}
case 6:
{
lean_object* v_b_1814_; 
v_b_1814_ = lean_ctor_get(v_b_1801_, 2);
lean_inc(v_b_1814_);
v___y_1804_ = v_b_1814_;
goto v___jp_1803_;
}
case 7:
{
lean_object* v_b_1815_; 
v_b_1815_ = lean_ctor_get(v_b_1801_, 2);
lean_inc(v_b_1815_);
v___y_1804_ = v_b_1815_;
goto v___jp_1803_;
}
case 8:
{
lean_object* v_b_1816_; 
v_b_1816_ = lean_ctor_get(v_b_1801_, 1);
lean_inc(v_b_1816_);
v___y_1804_ = v_b_1816_;
goto v___jp_1803_;
}
default: 
{
lean_inc(v_b_1801_);
v___y_1804_ = v_b_1801_;
goto v___jp_1803_;
}
}
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_r_1802_);
lean_ctor_set(v___x_1817_, 1, v_b_1801_);
return v___x_1817_;
}
v___jp_1803_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_IR_push(v_r_1802_, v_b_1801_);
v_b_1801_ = v___y_1804_;
v_r_1802_ = v___x_1805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object* v_b_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_IR_FnBody_flatten___closed__0));
v___x_1822_ = l_Lean_IR_flattenAux(v_b_1820_, v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0(lean_object* v___x_1823_, lean_object* v_msg_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_panic_fn_borrowed(v___x_1823_, v_msg_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(lean_object* v___x_1826_, lean_object* v_msg_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_1826_, v_msg_1827_);
lean_dec_ref(v___x_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object* v_a_1833_, lean_object* v_i_1834_, lean_object* v_b_1835_){
_start:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_nat_dec_eq(v_i_1834_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v_i_1839_; lean_object* v_fst_1841_; lean_object* v_snd_1842_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1838_ = lean_unsigned_to_nat(1u);
v_i_1839_ = lean_nat_sub(v_i_1834_, v___x_1838_);
lean_dec(v_i_1834_);
v___x_1845_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_1846_ = lean_array_get_size(v_a_1833_);
v___x_1847_ = lean_nat_dec_lt(v_i_1839_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; 
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1845_);
lean_ctor_set(v___x_1848_, 1, v_a_1833_);
v___x_1849_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__0));
v___x_1850_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__1));
v___x_1851_ = lean_unsigned_to_nat(438u);
v___x_1852_ = lean_unsigned_to_nat(4u);
v___x_1853_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__2));
lean_inc(v_i_1839_);
v___x_1854_ = l_Nat_reprFast(v_i_1839_);
v___x_1855_ = lean_string_append(v___x_1853_, v___x_1854_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__3));
v___x_1857_ = lean_string_append(v___x_1855_, v___x_1856_);
v___x_1858_ = l_mkPanicMessageWithDecl(v___x_1849_, v___x_1850_, v___x_1851_, v___x_1852_, v___x_1857_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = lean_panic_fn_borrowed(v___x_1848_, v___x_1858_);
lean_dec_ref_known(v___x_1848_, 2);
v_fst_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_fst_1860_);
v_snd_1861_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_snd_1861_);
lean_dec(v___x_1859_);
v_fst_1841_ = v_fst_1860_;
v_snd_1842_ = v_snd_1861_;
goto v___jp_1840_;
}
else
{
lean_object* v_e_1862_; lean_object* v_xs_x27_1863_; 
v_e_1862_ = lean_array_fget(v_a_1833_, v_i_1839_);
v_xs_x27_1863_ = lean_array_fset(v_a_1833_, v_i_1839_, v___x_1845_);
v_fst_1841_ = v_e_1862_;
v_snd_1842_ = v_xs_x27_1863_;
goto v___jp_1840_;
}
v___jp_1840_:
{
lean_object* v_b_1843_; 
v_b_1843_ = l_Lean_IR_FnBody_setBody(v_fst_1841_, v_b_1835_);
v_a_1833_ = v_snd_1842_;
v_i_1834_ = v_i_1839_;
v_b_1835_ = v_b_1843_;
goto _start;
}
}
else
{
lean_dec(v_i_1834_);
lean_dec_ref(v_a_1833_);
return v_b_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object* v_bs_1864_, lean_object* v_term_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_array_get_size(v_bs_1864_);
v___x_1867_ = l_Lean_IR_reshapeAux(v_bs_1864_, v___x_1866_, v_term_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object* v_f_1868_, lean_object* v_x_1869_){
_start:
{
if (lean_obj_tag(v_x_1869_) == 1)
{
lean_object* v_j_1870_; lean_object* v_xs_1871_; lean_object* v_v_1872_; lean_object* v_b_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1881_; 
v_j_1870_ = lean_ctor_get(v_x_1869_, 0);
v_xs_1871_ = lean_ctor_get(v_x_1869_, 1);
v_v_1872_ = lean_ctor_get(v_x_1869_, 2);
v_b_1873_ = lean_ctor_get(v_x_1869_, 3);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_x_1869_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1875_ = v_x_1869_;
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_b_1873_);
lean_inc(v_v_1872_);
lean_inc(v_xs_1871_);
lean_inc(v_j_1870_);
lean_dec(v_x_1869_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_apply_1(v_f_1868_, v_v_1872_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 2, v___x_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_j_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_xs_1871_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_b_1873_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_dec_ref(v_f_1868_);
return v_x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* v_bs_1901_, lean_object* v_f_1902_){
_start:
{
lean_object* v___f_1903_; lean_object* v___x_1904_; size_t v_sz_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPs___lam__0), 2, 1);
lean_closure_set(v___f_1903_, 0, v_f_1902_);
v___x_1904_ = ((lean_object*)(l_Lean_IR_modifyJPs___closed__9));
v_sz_1905_ = lean_array_size(v_bs_1901_);
v___x_1906_ = ((size_t)0ULL);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1904_, v___f_1903_, v_sz_1905_, v___x_1906_, v_bs_1901_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__0(lean_object* v_j_1908_, lean_object* v_xs_1909_, lean_object* v_b_1910_, lean_object* v_toPure_1911_, lean_object* v_____do__lift_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1913_, 0, v_j_1908_);
lean_ctor_set(v___x_1913_, 1, v_xs_1909_);
lean_ctor_set(v___x_1913_, 2, v_____do__lift_1912_);
lean_ctor_set(v___x_1913_, 3, v_b_1910_);
v___x_1914_ = lean_apply_2(v_toPure_1911_, lean_box(0), v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__1(lean_object* v_toPure_1915_, lean_object* v_f_1916_, lean_object* v_toBind_1917_, lean_object* v_b_1918_){
_start:
{
if (lean_obj_tag(v_b_1918_) == 1)
{
lean_object* v_j_1919_; lean_object* v_xs_1920_; lean_object* v_v_1921_; lean_object* v_b_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_j_1919_ = lean_ctor_get(v_b_1918_, 0);
lean_inc(v_j_1919_);
v_xs_1920_ = lean_ctor_get(v_b_1918_, 1);
lean_inc_ref(v_xs_1920_);
v_v_1921_ = lean_ctor_get(v_b_1918_, 2);
lean_inc(v_v_1921_);
v_b_1922_ = lean_ctor_get(v_b_1918_, 3);
lean_inc(v_b_1922_);
lean_dec_ref_known(v_b_1918_, 4);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1923_, 0, v_j_1919_);
lean_closure_set(v___f_1923_, 1, v_xs_1920_);
lean_closure_set(v___f_1923_, 2, v_b_1922_);
lean_closure_set(v___f_1923_, 3, v_toPure_1915_);
v___x_1924_ = lean_apply_1(v_f_1916_, v_v_1921_);
v___x_1925_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v___x_1924_, v___f_1923_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_toBind_1917_);
lean_dec(v_f_1916_);
v___x_1926_ = lean_apply_2(v_toPure_1915_, lean_box(0), v_b_1918_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg(lean_object* v_inst_1927_, lean_object* v_bs_1928_, lean_object* v_f_1929_){
_start:
{
lean_object* v_toApplicative_1930_; lean_object* v_toBind_1931_; lean_object* v_toPure_1932_; lean_object* v___f_1933_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_toApplicative_1930_ = lean_ctor_get(v_inst_1927_, 0);
v_toBind_1931_ = lean_ctor_get(v_inst_1927_, 1);
v_toPure_1932_ = lean_ctor_get(v_toApplicative_1930_, 1);
lean_inc(v_toBind_1931_);
lean_inc(v_toPure_1932_);
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1933_, 0, v_toPure_1932_);
lean_closure_set(v___f_1933_, 1, v_f_1929_);
lean_closure_set(v___f_1933_, 2, v_toBind_1931_);
v_sz_1934_ = lean_array_size(v_bs_1928_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1927_, v___f_1933_, v_sz_1934_, v___x_1935_, v_bs_1928_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM(lean_object* v_m_1937_, lean_object* v_inst_1938_, lean_object* v_bs_1939_, lean_object* v_f_1940_){
_start:
{
lean_object* v_toApplicative_1941_; lean_object* v_toBind_1942_; lean_object* v_toPure_1943_; lean_object* v___f_1944_; size_t v_sz_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v_toApplicative_1941_ = lean_ctor_get(v_inst_1938_, 0);
v_toBind_1942_ = lean_ctor_get(v_inst_1938_, 1);
v_toPure_1943_ = lean_ctor_get(v_toApplicative_1941_, 1);
lean_inc(v_toBind_1942_);
lean_inc(v_toPure_1943_);
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1944_, 0, v_toPure_1943_);
lean_closure_set(v___f_1944_, 1, v_f_1940_);
lean_closure_set(v___f_1944_, 2, v_toBind_1942_);
v_sz_1945_ = lean_array_size(v_bs_1939_);
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1938_, v___f_1944_, v_sz_1945_, v___x_1946_, v_bs_1939_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx(lean_object* v_x_1948_){
_start:
{
if (lean_obj_tag(v_x_1948_) == 0)
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_unsigned_to_nat(1u);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___boxed(lean_object* v_x_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_IR_Decl_ctorIdx(v_x_1951_);
lean_dec_ref(v_x_1951_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___redArg(lean_object* v_t_1953_, lean_object* v_k_1954_){
_start:
{
if (lean_obj_tag(v_t_1953_) == 0)
{
lean_object* v_f_1955_; lean_object* v_xs_1956_; lean_object* v_type_1957_; lean_object* v_body_1958_; lean_object* v_info_1959_; lean_object* v___x_1960_; 
v_f_1955_ = lean_ctor_get(v_t_1953_, 0);
lean_inc(v_f_1955_);
v_xs_1956_ = lean_ctor_get(v_t_1953_, 1);
lean_inc_ref(v_xs_1956_);
v_type_1957_ = lean_ctor_get(v_t_1953_, 2);
lean_inc(v_type_1957_);
v_body_1958_ = lean_ctor_get(v_t_1953_, 3);
lean_inc(v_body_1958_);
v_info_1959_ = lean_ctor_get(v_t_1953_, 4);
lean_inc(v_info_1959_);
lean_dec_ref_known(v_t_1953_, 5);
v___x_1960_ = lean_apply_5(v_k_1954_, v_f_1955_, v_xs_1956_, v_type_1957_, v_body_1958_, v_info_1959_);
return v___x_1960_;
}
else
{
lean_object* v_f_1961_; lean_object* v_xs_1962_; lean_object* v_type_1963_; lean_object* v_ext_1964_; lean_object* v___x_1965_; 
v_f_1961_ = lean_ctor_get(v_t_1953_, 0);
lean_inc(v_f_1961_);
v_xs_1962_ = lean_ctor_get(v_t_1953_, 1);
lean_inc_ref(v_xs_1962_);
v_type_1963_ = lean_ctor_get(v_t_1953_, 2);
lean_inc(v_type_1963_);
v_ext_1964_ = lean_ctor_get(v_t_1953_, 3);
lean_inc(v_ext_1964_);
lean_dec_ref_known(v_t_1953_, 4);
v___x_1965_ = lean_apply_4(v_k_1954_, v_f_1961_, v_xs_1962_, v_type_1963_, v_ext_1964_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim(lean_object* v_motive_1966_, lean_object* v_ctorIdx_1967_, lean_object* v_t_1968_, lean_object* v_h_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1968_, v_k_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___boxed(lean_object* v_motive_1972_, lean_object* v_ctorIdx_1973_, lean_object* v_t_1974_, lean_object* v_h_1975_, lean_object* v_k_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_IR_Decl_ctorElim(v_motive_1972_, v_ctorIdx_1973_, v_t_1974_, v_h_1975_, v_k_1976_);
lean_dec(v_ctorIdx_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim___redArg(lean_object* v_t_1978_, lean_object* v_fdecl_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1978_, v_fdecl_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim(lean_object* v_motive_1981_, lean_object* v_t_1982_, lean_object* v_h_1983_, lean_object* v_fdecl_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1982_, v_fdecl_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim___redArg(lean_object* v_t_1986_, lean_object* v_extern_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1986_, v_extern_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim(lean_object* v_motive_1989_, lean_object* v_t_1990_, lean_object* v_h_1991_, lean_object* v_extern_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1990_, v_extern_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object* v_x_2003_){
_start:
{
lean_object* v_f_2004_; 
v_f_2004_ = lean_ctor_get(v_x_2003_, 0);
lean_inc(v_f_2004_);
return v_f_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object* v_x_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_IR_Decl_name(v_x_2005_);
lean_dec_ref(v_x_2005_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object* v_x_2007_){
_start:
{
lean_object* v_xs_2008_; 
v_xs_2008_ = lean_ctor_get(v_x_2007_, 1);
lean_inc_ref(v_xs_2008_);
return v_xs_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object* v_x_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_IR_Decl_params(v_x_2009_);
lean_dec_ref(v_x_2009_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object* v_x_2011_){
_start:
{
lean_object* v_type_2012_; 
v_type_2012_ = lean_ctor_get(v_x_2011_, 2);
lean_inc(v_type_2012_);
return v_type_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* v_x_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_IR_Decl_resultType(v_x_2013_);
lean_dec_ref(v_x_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object* v_x_2015_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 1)
{
uint8_t v___x_2016_; 
v___x_2016_ = 1;
return v___x_2016_;
}
else
{
uint8_t v___x_2017_; 
v___x_2017_ = 0;
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* v_x_2018_){
_start:
{
uint8_t v_res_2019_; lean_object* v_r_2020_; 
v_res_2019_ = l_Lean_IR_Decl_isExtern(v_x_2018_);
lean_dec_ref(v_x_2018_);
v_r_2020_ = lean_box(v_res_2019_);
return v_r_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* v_x_2021_){
_start:
{
if (lean_obj_tag(v_x_2021_) == 0)
{
lean_object* v_info_2022_; 
v_info_2022_ = lean_ctor_get(v_x_2021_, 4);
lean_inc(v_info_2022_);
return v_info_2022_;
}
else
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_box(0);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* v_x_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_IR_Decl_getInfo(v_x_2024_);
lean_dec_ref(v_x_2024_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object* v_msg_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_IR_instInhabitedDecl_default));
v___x_2028_ = lean_panic_fn_borrowed(v___x_2027_, v_msg_2026_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__3(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2032_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__2));
v___x_2033_ = lean_unsigned_to_nat(9u);
v___x_2034_ = lean_unsigned_to_nat(382u);
v___x_2035_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__1));
v___x_2036_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__0));
v___x_2037_ = l_mkPanicMessageWithDecl(v___x_2036_, v___x_2035_, v___x_2034_, v___x_2033_, v___x_2032_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* v_d_2038_, lean_object* v_bNew_2039_){
_start:
{
if (lean_obj_tag(v_d_2038_) == 0)
{
lean_object* v_f_2040_; lean_object* v_xs_2041_; lean_object* v_type_2042_; lean_object* v_info_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_f_2040_ = lean_ctor_get(v_d_2038_, 0);
v_xs_2041_ = lean_ctor_get(v_d_2038_, 1);
v_type_2042_ = lean_ctor_get(v_d_2038_, 2);
v_info_2043_ = lean_ctor_get(v_d_2038_, 4);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_d_2038_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_d_2038_, 3);
lean_dec(v_unused_2051_);
v___x_2045_ = v_d_2038_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_info_2043_);
lean_inc(v_type_2042_);
lean_inc(v_xs_2041_);
lean_inc(v_f_2040_);
lean_dec(v_d_2038_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 3, v_bNew_2039_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_f_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_xs_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_type_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_bNew_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_info_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec(v_bNew_2039_);
lean_dec_ref(v_d_2038_);
v___x_2052_ = lean_obj_once(&l_Lean_IR_Decl_updateBody_x21___closed__3, &l_Lean_IR_Decl_updateBody_x21___closed__3_once, _init_l_Lean_IR_Decl_updateBody_x21___closed__3);
v___x_2053_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_2052_);
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object* v_f_2054_, lean_object* v_xs_2055_, lean_object* v_ty_2056_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_box(12);
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2059_, 0, v_f_2054_);
lean_ctor_set(v___x_2059_, 1, v_xs_2055_);
lean_ctor_set(v___x_2059_, 2, v_ty_2056_);
lean_ctor_set(v___x_2059_, 3, v___x_2057_);
lean_ctor_set(v___x_2059_, 4, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object* v_k_2060_, lean_object* v_v_2061_, lean_object* v_t_2062_){
_start:
{
if (lean_obj_tag(v_t_2062_) == 0)
{
lean_object* v_size_2063_; lean_object* v_k_2064_; lean_object* v_v_2065_; lean_object* v_l_2066_; lean_object* v_r_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2348_; 
v_size_2063_ = lean_ctor_get(v_t_2062_, 0);
v_k_2064_ = lean_ctor_get(v_t_2062_, 1);
v_v_2065_ = lean_ctor_get(v_t_2062_, 2);
v_l_2066_ = lean_ctor_get(v_t_2062_, 3);
v_r_2067_ = lean_ctor_get(v_t_2062_, 4);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_t_2062_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2069_ = v_t_2062_;
v_isShared_2070_ = v_isSharedCheck_2348_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_r_2067_);
lean_inc(v_l_2066_);
lean_inc(v_v_2065_);
lean_inc(v_k_2064_);
lean_inc(v_size_2063_);
lean_dec(v_t_2062_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2348_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_nat_dec_lt(v_k_2060_, v_k_2064_);
if (v___x_2071_ == 0)
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_nat_dec_eq(v_k_2060_, v_k_2064_);
if (v___x_2072_ == 0)
{
lean_object* v_impl_2073_; lean_object* v___x_2074_; 
lean_dec(v_size_2063_);
v_impl_2073_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2060_, v_v_2061_, v_r_2067_);
v___x_2074_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2066_) == 0)
{
lean_object* v_size_2075_; lean_object* v_size_2076_; lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v_l_2079_; lean_object* v_r_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_size_2075_ = lean_ctor_get(v_l_2066_, 0);
v_size_2076_ = lean_ctor_get(v_impl_2073_, 0);
lean_inc(v_size_2076_);
v_k_2077_ = lean_ctor_get(v_impl_2073_, 1);
lean_inc(v_k_2077_);
v_v_2078_ = lean_ctor_get(v_impl_2073_, 2);
lean_inc(v_v_2078_);
v_l_2079_ = lean_ctor_get(v_impl_2073_, 3);
lean_inc(v_l_2079_);
v_r_2080_ = lean_ctor_get(v_impl_2073_, 4);
lean_inc(v_r_2080_);
v___x_2081_ = lean_unsigned_to_nat(3u);
v___x_2082_ = lean_nat_mul(v___x_2081_, v_size_2075_);
v___x_2083_ = lean_nat_dec_lt(v___x_2082_, v_size_2076_);
lean_dec(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
lean_dec(v_r_2080_);
lean_dec(v_l_2079_);
lean_dec(v_v_2078_);
lean_dec(v_k_2077_);
v___x_2084_ = lean_nat_add(v___x_2074_, v_size_2075_);
v___x_2085_ = lean_nat_add(v___x_2084_, v_size_2076_);
lean_dec(v_size_2076_);
lean_dec(v___x_2084_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_impl_2073_);
lean_ctor_set(v___x_2069_, 0, v___x_2085_);
v___x_2087_ = v___x_2069_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_impl_2073_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
else
{
lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2152_; 
v_isSharedCheck_2152_ = !lean_is_exclusive(v_impl_2073_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; 
v_unused_2153_ = lean_ctor_get(v_impl_2073_, 4);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v_impl_2073_, 3);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_impl_2073_, 2);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_impl_2073_, 1);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_impl_2073_, 0);
lean_dec(v_unused_2157_);
v___x_2090_ = v_impl_2073_;
v_isShared_2091_ = v_isSharedCheck_2152_;
goto v_resetjp_2089_;
}
else
{
lean_dec(v_impl_2073_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2152_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_size_2092_; lean_object* v_k_2093_; lean_object* v_v_2094_; lean_object* v_l_2095_; lean_object* v_r_2096_; lean_object* v_size_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_size_2092_ = lean_ctor_get(v_l_2079_, 0);
v_k_2093_ = lean_ctor_get(v_l_2079_, 1);
v_v_2094_ = lean_ctor_get(v_l_2079_, 2);
v_l_2095_ = lean_ctor_get(v_l_2079_, 3);
v_r_2096_ = lean_ctor_get(v_l_2079_, 4);
v_size_2097_ = lean_ctor_get(v_r_2080_, 0);
v___x_2098_ = lean_unsigned_to_nat(2u);
v___x_2099_ = lean_nat_mul(v___x_2098_, v_size_2097_);
v___x_2100_ = lean_nat_dec_lt(v_size_2092_, v___x_2099_);
lean_dec(v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2128_; 
lean_inc(v_r_2096_);
lean_inc(v_l_2095_);
lean_inc(v_v_2094_);
lean_inc(v_k_2093_);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_l_2079_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; 
v_unused_2129_ = lean_ctor_get(v_l_2079_, 4);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_l_2079_, 3);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_2079_, 2);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_2079_, 1);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_l_2079_, 0);
lean_dec(v_unused_2133_);
v___x_2102_ = v_l_2079_;
v_isShared_2103_ = v_isSharedCheck_2128_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_l_2079_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2128_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2118_; 
v___x_2104_ = lean_nat_add(v___x_2074_, v_size_2075_);
v___x_2105_ = lean_nat_add(v___x_2104_, v_size_2076_);
lean_dec(v_size_2076_);
if (lean_obj_tag(v_l_2095_) == 0)
{
lean_object* v_size_2126_; 
v_size_2126_ = lean_ctor_get(v_l_2095_, 0);
lean_inc(v_size_2126_);
v___y_2118_ = v_size_2126_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___y_2118_ = v___x_2127_;
goto v___jp_2117_;
}
v___jp_2106_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_nat_add(v___y_2107_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec(v___y_2107_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v_r_2080_);
lean_ctor_set(v___x_2102_, 3, v_r_2096_);
lean_ctor_set(v___x_2102_, 2, v_v_2078_);
lean_ctor_set(v___x_2102_, 1, v_k_2077_);
lean_ctor_set(v___x_2102_, 0, v___x_2110_);
v___x_2112_ = v___x_2102_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_r_2096_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_r_2080_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 4, v___x_2112_);
lean_ctor_set(v___x_2090_, 3, v___y_2108_);
lean_ctor_set(v___x_2090_, 2, v_v_2094_);
lean_ctor_set(v___x_2090_, 1, v_k_2093_);
lean_ctor_set(v___x_2090_, 0, v___x_2105_);
v___x_2114_ = v___x_2090_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_k_2093_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_v_2094_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v___y_2108_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_nat_add(v___x_2104_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec(v___x_2104_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_l_2095_);
lean_ctor_set(v___x_2069_, 0, v___x_2119_);
v___x_2121_ = v___x_2069_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_l_2095_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_nat_add(v___x_2074_, v_size_2097_);
if (lean_obj_tag(v_r_2096_) == 0)
{
lean_object* v_size_2123_; 
v_size_2123_ = lean_ctor_get(v_r_2096_, 0);
lean_inc(v_size_2123_);
v___y_2107_ = v___x_2122_;
v___y_2108_ = v___x_2121_;
v___y_2109_ = v_size_2123_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___y_2107_ = v___x_2122_;
v___y_2108_ = v___x_2121_;
v___y_2109_ = v___x_2124_;
goto v___jp_2106_;
}
}
}
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_del_object(v___x_2069_);
v___x_2134_ = lean_nat_add(v___x_2074_, v_size_2075_);
v___x_2135_ = lean_nat_add(v___x_2134_, v_size_2076_);
lean_dec(v_size_2076_);
v___x_2136_ = lean_nat_add(v___x_2134_, v_size_2092_);
lean_dec(v___x_2134_);
lean_inc_ref(v_l_2066_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 4, v_l_2079_);
lean_ctor_set(v___x_2090_, 3, v_l_2066_);
lean_ctor_set(v___x_2090_, 2, v_v_2065_);
lean_ctor_set(v___x_2090_, 1, v_k_2064_);
lean_ctor_set(v___x_2090_, 0, v___x_2136_);
v___x_2138_ = v___x_2090_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v_l_2079_);
v___x_2138_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_isSharedCheck_2145_ = !lean_is_exclusive(v_l_2066_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; 
v_unused_2146_ = lean_ctor_get(v_l_2066_, 4);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_2066_, 3);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2066_, 2);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2066_, 1);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2066_, 0);
lean_dec(v_unused_2150_);
v___x_2140_ = v_l_2066_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v_l_2066_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 4, v_r_2080_);
lean_ctor_set(v___x_2140_, 3, v___x_2138_);
lean_ctor_set(v___x_2140_, 2, v_v_2078_);
lean_ctor_set(v___x_2140_, 1, v_k_2077_);
lean_ctor_set(v___x_2140_, 0, v___x_2135_);
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_r_2080_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2158_; 
v_l_2158_ = lean_ctor_get(v_impl_2073_, 3);
lean_inc(v_l_2158_);
if (lean_obj_tag(v_l_2158_) == 0)
{
lean_object* v_r_2159_; lean_object* v_k_2160_; lean_object* v_v_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2184_; 
v_r_2159_ = lean_ctor_get(v_impl_2073_, 4);
v_k_2160_ = lean_ctor_get(v_impl_2073_, 1);
v_v_2161_ = lean_ctor_get(v_impl_2073_, 2);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_impl_2073_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2185_ = lean_ctor_get(v_impl_2073_, 3);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_impl_2073_, 0);
lean_dec(v_unused_2186_);
v___x_2163_ = v_impl_2073_;
v_isShared_2164_ = v_isSharedCheck_2184_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_r_2159_);
lean_inc(v_v_2161_);
lean_inc(v_k_2160_);
lean_dec(v_impl_2073_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2184_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_k_2165_; lean_object* v_v_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2180_; 
v_k_2165_ = lean_ctor_get(v_l_2158_, 1);
v_v_2166_ = lean_ctor_get(v_l_2158_, 2);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_l_2158_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2181_ = lean_ctor_get(v_l_2158_, 4);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_l_2158_, 3);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_2158_, 0);
lean_dec(v_unused_2183_);
v___x_2168_ = v_l_2158_;
v_isShared_2169_ = v_isSharedCheck_2180_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_v_2166_);
lean_inc(v_k_2165_);
lean_dec(v_l_2158_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2180_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2159_, 2);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 4, v_r_2159_);
lean_ctor_set(v___x_2168_, 3, v_r_2159_);
lean_ctor_set(v___x_2168_, 2, v_v_2065_);
lean_ctor_set(v___x_2168_, 1, v_k_2064_);
lean_ctor_set(v___x_2168_, 0, v___x_2074_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_r_2159_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_r_2159_);
v___x_2172_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; 
lean_inc(v_r_2159_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 3, v_r_2159_);
lean_ctor_set(v___x_2163_, 0, v___x_2074_);
v___x_2174_ = v___x_2163_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2160_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2161_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_r_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_r_2159_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v___x_2174_);
lean_ctor_set(v___x_2069_, 3, v___x_2172_);
lean_ctor_set(v___x_2069_, 2, v_v_2166_);
lean_ctor_set(v___x_2069_, 1, v_k_2165_);
lean_ctor_set(v___x_2069_, 0, v___x_2170_);
v___x_2176_ = v___x_2069_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2165_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2166_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
else
{
lean_object* v_r_2187_; 
v_r_2187_ = lean_ctor_get(v_impl_2073_, 4);
lean_inc(v_r_2187_);
if (lean_obj_tag(v_r_2187_) == 0)
{
lean_object* v_k_2188_; lean_object* v_v_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2200_; 
v_k_2188_ = lean_ctor_get(v_impl_2073_, 1);
v_v_2189_ = lean_ctor_get(v_impl_2073_, 2);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_impl_2073_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2201_ = lean_ctor_get(v_impl_2073_, 4);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_impl_2073_, 3);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_impl_2073_, 0);
lean_dec(v_unused_2203_);
v___x_2191_ = v_impl_2073_;
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_v_2189_);
lean_inc(v_k_2188_);
lean_dec(v_impl_2073_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2200_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = lean_unsigned_to_nat(3u);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 4, v_l_2158_);
lean_ctor_set(v___x_2191_, 2, v_v_2065_);
lean_ctor_set(v___x_2191_, 1, v_k_2064_);
lean_ctor_set(v___x_2191_, 0, v___x_2074_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_l_2158_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_l_2158_);
v___x_2195_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_r_2187_);
lean_ctor_set(v___x_2069_, 3, v___x_2195_);
lean_ctor_set(v___x_2069_, 2, v_v_2189_);
lean_ctor_set(v___x_2069_, 1, v_k_2188_);
lean_ctor_set(v___x_2069_, 0, v___x_2193_);
v___x_2197_ = v___x_2069_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_k_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_v_2189_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_r_2187_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_unsigned_to_nat(2u);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_impl_2073_);
lean_ctor_set(v___x_2069_, 3, v_r_2187_);
lean_ctor_set(v___x_2069_, 0, v___x_2204_);
v___x_2206_ = v___x_2069_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_r_2187_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v_impl_2073_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v___x_2209_; 
lean_dec(v_v_2065_);
lean_dec(v_k_2064_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 2, v_v_2061_);
lean_ctor_set(v___x_2069_, 1, v_k_2060_);
v___x_2209_ = v___x_2069_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_size_2063_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2060_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2061_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_r_2067_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
lean_object* v_impl_2211_; lean_object* v___x_2212_; 
lean_dec(v_size_2063_);
v_impl_2211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2060_, v_v_2061_, v_l_2066_);
v___x_2212_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2067_) == 0)
{
lean_object* v_size_2213_; lean_object* v_size_2214_; lean_object* v_k_2215_; lean_object* v_v_2216_; lean_object* v_l_2217_; lean_object* v_r_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v_size_2213_ = lean_ctor_get(v_r_2067_, 0);
v_size_2214_ = lean_ctor_get(v_impl_2211_, 0);
lean_inc(v_size_2214_);
v_k_2215_ = lean_ctor_get(v_impl_2211_, 1);
lean_inc(v_k_2215_);
v_v_2216_ = lean_ctor_get(v_impl_2211_, 2);
lean_inc(v_v_2216_);
v_l_2217_ = lean_ctor_get(v_impl_2211_, 3);
lean_inc(v_l_2217_);
v_r_2218_ = lean_ctor_get(v_impl_2211_, 4);
lean_inc(v_r_2218_);
v___x_2219_ = lean_unsigned_to_nat(3u);
v___x_2220_ = lean_nat_mul(v___x_2219_, v_size_2213_);
v___x_2221_ = lean_nat_dec_lt(v___x_2220_, v_size_2214_);
lean_dec(v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
lean_dec(v_r_2218_);
lean_dec(v_l_2217_);
lean_dec(v_v_2216_);
lean_dec(v_k_2215_);
v___x_2222_ = lean_nat_add(v___x_2212_, v_size_2214_);
lean_dec(v_size_2214_);
v___x_2223_ = lean_nat_add(v___x_2222_, v_size_2213_);
lean_dec(v___x_2222_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 3, v_impl_2211_);
lean_ctor_set(v___x_2069_, 0, v___x_2223_);
v___x_2225_ = v___x_2069_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_impl_2211_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_r_2067_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2292_; 
v_isSharedCheck_2292_ = !lean_is_exclusive(v_impl_2211_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; lean_object* v_unused_2297_; 
v_unused_2293_ = lean_ctor_get(v_impl_2211_, 4);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_impl_2211_, 3);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_impl_2211_, 2);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_impl_2211_, 1);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_impl_2211_, 0);
lean_dec(v_unused_2297_);
v___x_2228_ = v_impl_2211_;
v_isShared_2229_ = v_isSharedCheck_2292_;
goto v_resetjp_2227_;
}
else
{
lean_dec(v_impl_2211_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2292_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_size_2230_; lean_object* v_size_2231_; lean_object* v_k_2232_; lean_object* v_v_2233_; lean_object* v_l_2234_; lean_object* v_r_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_size_2230_ = lean_ctor_get(v_l_2217_, 0);
v_size_2231_ = lean_ctor_get(v_r_2218_, 0);
v_k_2232_ = lean_ctor_get(v_r_2218_, 1);
v_v_2233_ = lean_ctor_get(v_r_2218_, 2);
v_l_2234_ = lean_ctor_get(v_r_2218_, 3);
v_r_2235_ = lean_ctor_get(v_r_2218_, 4);
v___x_2236_ = lean_unsigned_to_nat(2u);
v___x_2237_ = lean_nat_mul(v___x_2236_, v_size_2230_);
v___x_2238_ = lean_nat_dec_lt(v_size_2231_, v___x_2237_);
lean_dec(v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2267_; 
lean_inc(v_r_2235_);
lean_inc(v_l_2234_);
lean_inc(v_v_2233_);
lean_inc(v_k_2232_);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_r_2218_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; lean_object* v_unused_2272_; 
v_unused_2268_ = lean_ctor_get(v_r_2218_, 4);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_r_2218_, 3);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_r_2218_, 2);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_r_2218_, 1);
lean_dec(v_unused_2271_);
v_unused_2272_ = lean_ctor_get(v_r_2218_, 0);
lean_dec(v_unused_2272_);
v___x_2240_ = v_r_2218_;
v_isShared_2241_ = v_isSharedCheck_2267_;
goto v_resetjp_2239_;
}
else
{
lean_dec(v_r_2218_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2267_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___x_2255_; lean_object* v___y_2257_; 
v___x_2242_ = lean_nat_add(v___x_2212_, v_size_2214_);
lean_dec(v_size_2214_);
v___x_2243_ = lean_nat_add(v___x_2242_, v_size_2213_);
lean_dec(v___x_2242_);
v___x_2255_ = lean_nat_add(v___x_2212_, v_size_2230_);
if (lean_obj_tag(v_l_2234_) == 0)
{
lean_object* v_size_2265_; 
v_size_2265_ = lean_ctor_get(v_l_2234_, 0);
lean_inc(v_size_2265_);
v___y_2257_ = v_size_2265_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_unsigned_to_nat(0u);
v___y_2257_ = v___x_2266_;
goto v___jp_2256_;
}
v___jp_2244_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_nat_add(v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec(v___y_2246_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v_r_2067_);
lean_ctor_set(v___x_2240_, 3, v_r_2235_);
lean_ctor_set(v___x_2240_, 2, v_v_2065_);
lean_ctor_set(v___x_2240_, 1, v_k_2064_);
lean_ctor_set(v___x_2240_, 0, v___x_2248_);
v___x_2250_ = v___x_2240_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_r_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_r_2067_);
v___x_2250_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 4, v___x_2250_);
lean_ctor_set(v___x_2228_, 3, v___y_2245_);
lean_ctor_set(v___x_2228_, 2, v_v_2233_);
lean_ctor_set(v___x_2228_, 1, v_k_2232_);
lean_ctor_set(v___x_2228_, 0, v___x_2243_);
v___x_2252_ = v___x_2228_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_2232_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_2233_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v___y_2245_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
v___jp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = lean_nat_add(v___x_2255_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec(v___x_2255_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_l_2234_);
lean_ctor_set(v___x_2069_, 3, v_l_2217_);
lean_ctor_set(v___x_2069_, 2, v_v_2216_);
lean_ctor_set(v___x_2069_, 1, v_k_2215_);
lean_ctor_set(v___x_2069_, 0, v___x_2258_);
v___x_2260_ = v___x_2069_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_k_2215_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_v_2216_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_l_2217_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v_l_2234_);
v___x_2260_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_nat_add(v___x_2212_, v_size_2213_);
if (lean_obj_tag(v_r_2235_) == 0)
{
lean_object* v_size_2262_; 
v_size_2262_ = lean_ctor_get(v_r_2235_, 0);
lean_inc(v_size_2262_);
v___y_2245_ = v___x_2260_;
v___y_2246_ = v___x_2261_;
v___y_2247_ = v_size_2262_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_unsigned_to_nat(0u);
v___y_2245_ = v___x_2260_;
v___y_2246_ = v___x_2261_;
v___y_2247_ = v___x_2263_;
goto v___jp_2244_;
}
}
}
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_del_object(v___x_2069_);
v___x_2273_ = lean_nat_add(v___x_2212_, v_size_2214_);
lean_dec(v_size_2214_);
v___x_2274_ = lean_nat_add(v___x_2273_, v_size_2213_);
lean_dec(v___x_2273_);
v___x_2275_ = lean_nat_add(v___x_2212_, v_size_2213_);
v___x_2276_ = lean_nat_add(v___x_2275_, v_size_2231_);
lean_dec(v___x_2275_);
lean_inc_ref(v_r_2067_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 4, v_r_2067_);
lean_ctor_set(v___x_2228_, 3, v_r_2218_);
lean_ctor_set(v___x_2228_, 2, v_v_2065_);
lean_ctor_set(v___x_2228_, 1, v_k_2064_);
lean_ctor_set(v___x_2228_, 0, v___x_2276_);
v___x_2278_ = v___x_2228_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_r_2218_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_r_2067_);
v___x_2278_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_isSharedCheck_2285_ = !lean_is_exclusive(v_r_2067_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; lean_object* v_unused_2287_; lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2286_ = lean_ctor_get(v_r_2067_, 4);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_r_2067_, 3);
lean_dec(v_unused_2287_);
v_unused_2288_ = lean_ctor_get(v_r_2067_, 2);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_r_2067_, 1);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_r_2067_, 0);
lean_dec(v_unused_2290_);
v___x_2280_ = v_r_2067_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v_r_2067_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 4, v___x_2278_);
lean_ctor_set(v___x_2280_, 3, v_l_2217_);
lean_ctor_set(v___x_2280_, 2, v_v_2216_);
lean_ctor_set(v___x_2280_, 1, v_k_2215_);
lean_ctor_set(v___x_2280_, 0, v___x_2274_);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_2215_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_2216_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_l_2217_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v___x_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2298_; 
v_l_2298_ = lean_ctor_get(v_impl_2211_, 3);
lean_inc(v_l_2298_);
if (lean_obj_tag(v_l_2298_) == 0)
{
lean_object* v_r_2299_; lean_object* v_k_2300_; lean_object* v_v_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2312_; 
v_r_2299_ = lean_ctor_get(v_impl_2211_, 4);
v_k_2300_ = lean_ctor_get(v_impl_2211_, 1);
v_v_2301_ = lean_ctor_get(v_impl_2211_, 2);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_impl_2211_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2313_ = lean_ctor_get(v_impl_2211_, 3);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_impl_2211_, 0);
lean_dec(v_unused_2314_);
v___x_2303_ = v_impl_2211_;
v_isShared_2304_ = v_isSharedCheck_2312_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_r_2299_);
lean_inc(v_v_2301_);
lean_inc(v_k_2300_);
lean_dec(v_impl_2211_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2312_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2299_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 3, v_r_2299_);
lean_ctor_set(v___x_2303_, 2, v_v_2065_);
lean_ctor_set(v___x_2303_, 1, v_k_2064_);
lean_ctor_set(v___x_2303_, 0, v___x_2212_);
v___x_2307_ = v___x_2303_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_r_2299_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_r_2299_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v___x_2307_);
lean_ctor_set(v___x_2069_, 3, v_l_2298_);
lean_ctor_set(v___x_2069_, 2, v_v_2301_);
lean_ctor_set(v___x_2069_, 1, v_k_2300_);
lean_ctor_set(v___x_2069_, 0, v___x_2305_);
v___x_2309_ = v___x_2069_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_k_2300_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_v_2301_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_r_2315_; 
v_r_2315_ = lean_ctor_get(v_impl_2211_, 4);
lean_inc(v_r_2315_);
if (lean_obj_tag(v_r_2315_) == 0)
{
lean_object* v_k_2316_; lean_object* v_v_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2340_; 
v_k_2316_ = lean_ctor_get(v_impl_2211_, 1);
v_v_2317_ = lean_ctor_get(v_impl_2211_, 2);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_impl_2211_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; lean_object* v_unused_2342_; lean_object* v_unused_2343_; 
v_unused_2341_ = lean_ctor_get(v_impl_2211_, 4);
lean_dec(v_unused_2341_);
v_unused_2342_ = lean_ctor_get(v_impl_2211_, 3);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_impl_2211_, 0);
lean_dec(v_unused_2343_);
v___x_2319_ = v_impl_2211_;
v_isShared_2320_ = v_isSharedCheck_2340_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_v_2317_);
lean_inc(v_k_2316_);
lean_dec(v_impl_2211_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2340_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_k_2321_; lean_object* v_v_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2336_; 
v_k_2321_ = lean_ctor_get(v_r_2315_, 1);
v_v_2322_ = lean_ctor_get(v_r_2315_, 2);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_r_2315_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; lean_object* v_unused_2338_; lean_object* v_unused_2339_; 
v_unused_2337_ = lean_ctor_get(v_r_2315_, 4);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_r_2315_, 3);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_2315_, 0);
lean_dec(v_unused_2339_);
v___x_2324_ = v_r_2315_;
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_v_2322_);
lean_inc(v_k_2321_);
lean_dec(v_r_2315_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = lean_unsigned_to_nat(3u);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 4, v_l_2298_);
lean_ctor_set(v___x_2324_, 3, v_l_2298_);
lean_ctor_set(v___x_2324_, 2, v_v_2317_);
lean_ctor_set(v___x_2324_, 1, v_k_2316_);
lean_ctor_set(v___x_2324_, 0, v___x_2212_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2316_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2317_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_l_2298_);
v___x_2328_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_l_2298_);
lean_ctor_set(v___x_2319_, 2, v_v_2065_);
lean_ctor_set(v___x_2319_, 1, v_k_2064_);
lean_ctor_set(v___x_2319_, 0, v___x_2212_);
v___x_2330_ = v___x_2319_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_l_2298_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v___x_2330_);
lean_ctor_set(v___x_2069_, 3, v___x_2328_);
lean_ctor_set(v___x_2069_, 2, v_v_2322_);
lean_ctor_set(v___x_2069_, 1, v_k_2321_);
lean_ctor_set(v___x_2069_, 0, v___x_2326_);
v___x_2332_ = v___x_2069_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2322_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = lean_unsigned_to_nat(2u);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_r_2315_);
lean_ctor_set(v___x_2069_, 3, v_impl_2211_);
lean_ctor_set(v___x_2069_, 0, v___x_2344_);
v___x_2346_ = v___x_2069_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_impl_2211_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_r_2315_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_k_2060_);
lean_ctor_set(v___x_2350_, 2, v_v_2061_);
lean_ctor_set(v___x_2350_, 3, v_t_2062_);
lean_ctor_set(v___x_2350_, 4, v_t_2062_);
return v___x_2350_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object* v_k_2351_, lean_object* v_t_2352_){
_start:
{
if (lean_obj_tag(v_t_2352_) == 0)
{
lean_object* v_k_2353_; lean_object* v_l_2354_; lean_object* v_r_2355_; uint8_t v___x_2356_; 
v_k_2353_ = lean_ctor_get(v_t_2352_, 1);
v_l_2354_ = lean_ctor_get(v_t_2352_, 3);
v_r_2355_ = lean_ctor_get(v_t_2352_, 4);
v___x_2356_ = lean_nat_dec_lt(v_k_2351_, v_k_2353_);
if (v___x_2356_ == 0)
{
uint8_t v___x_2357_; 
v___x_2357_ = lean_nat_dec_eq(v_k_2351_, v_k_2353_);
if (v___x_2357_ == 0)
{
v_t_2352_ = v_r_2355_;
goto _start;
}
else
{
return v___x_2357_;
}
}
else
{
v_t_2352_ = v_l_2354_;
goto _start;
}
}
else
{
uint8_t v___x_2360_; 
v___x_2360_ = 0;
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object* v_k_2361_, lean_object* v_t_2362_){
_start:
{
uint8_t v_res_2363_; lean_object* v_r_2364_; 
v_res_2363_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2361_, v_t_2362_);
lean_dec(v_t_2362_);
lean_dec(v_k_2361_);
v_r_2364_ = lean_box(v_res_2363_);
return v_r_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* v_idx_2365_){
_start:
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = lean_box(1);
v___x_2367_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_idx_2365_, v___x_2368_, v___x_2366_);
return v___x_2369_;
}
else
{
lean_dec(v_idx_2365_);
return v___x_2366_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object* v_00_u03b2_2370_, lean_object* v_k_2371_, lean_object* v_t_2372_){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2371_, v_t_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object* v_00_u03b2_2374_, lean_object* v_k_2375_, lean_object* v_t_2376_){
_start:
{
uint8_t v_res_2377_; lean_object* v_r_2378_; 
v_res_2377_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(v_00_u03b2_2374_, v_k_2375_, v_t_2376_);
lean_dec(v_t_2376_);
lean_dec(v_k_2375_);
v_r_2378_ = lean_box(v_res_2377_);
return v_r_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object* v_00_u03b2_2379_, lean_object* v_k_2380_, lean_object* v_v_2381_, lean_object* v_t_2382_, lean_object* v_hl_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2380_, v_v_2381_, v_t_2382_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx(lean_object* v_x_2385_){
_start:
{
switch(lean_obj_tag(v_x_2385_))
{
case 0:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_unsigned_to_nat(0u);
return v___x_2386_;
}
case 1:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_unsigned_to_nat(1u);
return v___x_2387_;
}
default: 
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_unsigned_to_nat(2u);
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___boxed(lean_object* v_x_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_IR_LocalContextEntry_ctorIdx(v_x_2389_);
lean_dec_ref(v_x_2389_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object* v_t_2391_, lean_object* v_k_2392_){
_start:
{
switch(lean_obj_tag(v_t_2391_))
{
case 0:
{
lean_object* v_a_2393_; lean_object* v___x_2394_; 
v_a_2393_ = lean_ctor_get(v_t_2391_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v_t_2391_, 1);
v___x_2394_ = lean_apply_1(v_k_2392_, v_a_2393_);
return v___x_2394_;
}
case 1:
{
lean_object* v_a_2395_; lean_object* v_a_2396_; lean_object* v___x_2397_; 
v_a_2395_ = lean_ctor_get(v_t_2391_, 0);
lean_inc(v_a_2395_);
v_a_2396_ = lean_ctor_get(v_t_2391_, 1);
lean_inc_ref(v_a_2396_);
lean_dec_ref_known(v_t_2391_, 2);
v___x_2397_ = lean_apply_2(v_k_2392_, v_a_2395_, v_a_2396_);
return v___x_2397_;
}
default: 
{
lean_object* v_a_2398_; lean_object* v_a_2399_; lean_object* v___x_2400_; 
v_a_2398_ = lean_ctor_get(v_t_2391_, 0);
lean_inc_ref(v_a_2398_);
v_a_2399_ = lean_ctor_get(v_t_2391_, 1);
lean_inc(v_a_2399_);
lean_dec_ref_known(v_t_2391_, 2);
v___x_2400_ = lean_apply_2(v_k_2392_, v_a_2398_, v_a_2399_);
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object* v_motive_2401_, lean_object* v_ctorIdx_2402_, lean_object* v_t_2403_, lean_object* v_h_2404_, lean_object* v_k_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2403_, v_k_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object* v_motive_2407_, lean_object* v_ctorIdx_2408_, lean_object* v_t_2409_, lean_object* v_h_2410_, lean_object* v_k_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_IR_LocalContextEntry_ctorElim(v_motive_2407_, v_ctorIdx_2408_, v_t_2409_, v_h_2410_, v_k_2411_);
lean_dec(v_ctorIdx_2408_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object* v_t_2413_, lean_object* v_param_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2413_, v_param_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object* v_motive_2416_, lean_object* v_t_2417_, lean_object* v_h_2418_, lean_object* v_param_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2417_, v_param_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object* v_t_2421_, lean_object* v_localVar_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2421_, v_localVar_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object* v_motive_2424_, lean_object* v_t_2425_, lean_object* v_h_2426_, lean_object* v_localVar_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2425_, v_localVar_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim___redArg(lean_object* v_t_2429_, lean_object* v_joinPoint_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2429_, v_joinPoint_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim(lean_object* v_motive_2432_, lean_object* v_t_2433_, lean_object* v_h_2434_, lean_object* v_joinPoint_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2433_, v_joinPoint_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* v_ctx_2437_, lean_object* v_x_2438_, lean_object* v_t_2439_, lean_object* v_v_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_t_2439_);
lean_ctor_set(v___x_2441_, 1, v_v_2440_);
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2438_, v___x_2441_, v_ctx_2437_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* v_ctx_2443_, lean_object* v_j_2444_, lean_object* v_xs_2445_, lean_object* v_b_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_xs_2445_);
lean_ctor_set(v___x_2447_, 1, v_b_2446_);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_j_2444_, v___x_2447_, v_ctx_2443_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* v_ctx_2449_, lean_object* v_p_2450_){
_start:
{
lean_object* v_x_2451_; lean_object* v_ty_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_x_2451_ = lean_ctor_get(v_p_2450_, 0);
lean_inc(v_x_2451_);
v_ty_2452_ = lean_ctor_get(v_p_2450_, 1);
lean_inc(v_ty_2452_);
lean_dec_ref(v_p_2450_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_ty_2452_);
v___x_2454_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2451_, v___x_2453_, v_ctx_2449_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object* v_as_2455_, size_t v_i_2456_, size_t v_stop_2457_, lean_object* v_b_2458_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_usize_dec_eq(v_i_2456_, v_stop_2457_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; 
v___x_2460_ = lean_array_uget_borrowed(v_as_2455_, v_i_2456_);
lean_inc(v___x_2460_);
v___x_2461_ = l_Lean_IR_LocalContext_addParam(v_b_2458_, v___x_2460_);
v___x_2462_ = ((size_t)1ULL);
v___x_2463_ = lean_usize_add(v_i_2456_, v___x_2462_);
v_i_2456_ = v___x_2463_;
v_b_2458_ = v___x_2461_;
goto _start;
}
else
{
return v_b_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* v_as_2465_, lean_object* v_i_2466_, lean_object* v_stop_2467_, lean_object* v_b_2468_){
_start:
{
size_t v_i_boxed_2469_; size_t v_stop_boxed_2470_; lean_object* v_res_2471_; 
v_i_boxed_2469_ = lean_unbox_usize(v_i_2466_);
lean_dec(v_i_2466_);
v_stop_boxed_2470_ = lean_unbox_usize(v_stop_2467_);
lean_dec(v_stop_2467_);
v_res_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_2465_, v_i_boxed_2469_, v_stop_boxed_2470_, v_b_2468_);
lean_dec_ref(v_as_2465_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* v_ctx_2472_, lean_object* v_ps_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = lean_array_get_size(v_ps_2473_);
v___x_2476_ = lean_nat_dec_lt(v___x_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
return v_ctx_2472_;
}
else
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_nat_dec_le(v___x_2475_, v___x_2475_);
if (v___x_2477_ == 0)
{
if (v___x_2476_ == 0)
{
return v_ctx_2472_;
}
else
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = lean_usize_of_nat(v___x_2475_);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2473_, v___x_2478_, v___x_2479_, v_ctx_2472_);
return v___x_2480_;
}
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2475_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2473_, v___x_2481_, v___x_2482_, v_ctx_2472_);
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_2484_, lean_object* v_ps_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_IR_LocalContext_addParams(v_ctx_2484_, v_ps_2485_);
lean_dec_ref(v_ps_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(lean_object* v_t_2487_, lean_object* v_k_2488_){
_start:
{
if (lean_obj_tag(v_t_2487_) == 0)
{
lean_object* v_k_2489_; lean_object* v_v_2490_; lean_object* v_l_2491_; lean_object* v_r_2492_; uint8_t v___x_2493_; 
v_k_2489_ = lean_ctor_get(v_t_2487_, 1);
v_v_2490_ = lean_ctor_get(v_t_2487_, 2);
v_l_2491_ = lean_ctor_get(v_t_2487_, 3);
v_r_2492_ = lean_ctor_get(v_t_2487_, 4);
v___x_2493_ = lean_nat_dec_lt(v_k_2488_, v_k_2489_);
if (v___x_2493_ == 0)
{
uint8_t v___x_2494_; 
v___x_2494_ = lean_nat_dec_eq(v_k_2488_, v_k_2489_);
if (v___x_2494_ == 0)
{
v_t_2487_ = v_r_2492_;
goto _start;
}
else
{
lean_object* v___x_2496_; 
lean_inc(v_v_2490_);
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_v_2490_);
return v___x_2496_;
}
}
else
{
v_t_2487_ = v_l_2491_;
goto _start;
}
}
else
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_box(0);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(lean_object* v_t_2499_, lean_object* v_k_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_2499_, v_k_2500_);
lean_dec(v_k_2500_);
lean_dec(v_t_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_2502_, lean_object* v_idx_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2502_, v_idx_2503_);
if (lean_obj_tag(v___x_2504_) == 1)
{
lean_object* v_val_2505_; 
v_val_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_val_2505_);
lean_dec_ref_known(v___x_2504_, 1);
if (lean_obj_tag(v_val_2505_) == 2)
{
uint8_t v___x_2506_; 
lean_dec_ref_known(v_val_2505_, 2);
v___x_2506_ = 1;
return v___x_2506_;
}
else
{
uint8_t v___x_2507_; 
lean_dec(v_val_2505_);
v___x_2507_ = 0;
return v___x_2507_;
}
}
else
{
uint8_t v___x_2508_; 
lean_dec(v___x_2504_);
v___x_2508_ = 0;
return v___x_2508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_2509_, lean_object* v_idx_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Lean_IR_LocalContext_isJP(v_ctx_2509_, v_idx_2510_);
lean_dec(v_idx_2510_);
lean_dec(v_ctx_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(lean_object* v_00_u03b4_2513_, lean_object* v_t_2514_, lean_object* v_k_2515_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_2514_, v_k_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___boxed(lean_object* v_00_u03b4_2517_, lean_object* v_t_2518_, lean_object* v_k_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(v_00_u03b4_2517_, v_t_2518_, v_k_2519_);
lean_dec(v_k_2519_);
lean_dec(v_t_2518_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_2521_, lean_object* v_j_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2521_, v_j_2522_);
if (lean_obj_tag(v___x_2523_) == 1)
{
lean_object* v_val_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2533_; 
v_val_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_val_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
if (lean_obj_tag(v_val_2524_) == 2)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; 
v_a_2528_ = lean_ctor_get(v_val_2524_, 1);
lean_inc(v_a_2528_);
lean_dec_ref_known(v_val_2524_, 2);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v_a_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2532_; 
lean_del_object(v___x_2526_);
lean_dec(v_val_2524_);
v___x_2532_ = lean_box(0);
return v___x_2532_;
}
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v___x_2523_);
v___x_2534_ = lean_box(0);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_2535_, lean_object* v_j_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_2535_, v_j_2536_);
lean_dec(v_j_2536_);
lean_dec(v_ctx_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_2538_, lean_object* v_j_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2538_, v_j_2539_);
if (lean_obj_tag(v___x_2540_) == 1)
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2550_; 
v_val_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
if (lean_obj_tag(v_val_2541_) == 2)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; 
v_a_2545_ = lean_ctor_get(v_val_2541_, 0);
lean_inc_ref(v_a_2545_);
lean_dec_ref_known(v_val_2541_, 2);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v_a_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
else
{
lean_object* v___x_2549_; 
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
v___x_2549_ = lean_box(0);
return v___x_2549_;
}
}
}
else
{
lean_object* v___x_2551_; 
lean_dec(v___x_2540_);
v___x_2551_ = lean_box(0);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_2552_, lean_object* v_j_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_2552_, v_j_2553_);
lean_dec(v_j_2553_);
lean_dec(v_ctx_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_2555_, lean_object* v_idx_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2555_, v_idx_2556_);
if (lean_obj_tag(v___x_2557_) == 1)
{
lean_object* v_val_2558_; 
v_val_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v___x_2557_, 1);
if (lean_obj_tag(v_val_2558_) == 0)
{
uint8_t v___x_2559_; 
lean_dec_ref_known(v_val_2558_, 1);
v___x_2559_ = 1;
return v___x_2559_;
}
else
{
uint8_t v___x_2560_; 
lean_dec(v_val_2558_);
v___x_2560_ = 0;
return v___x_2560_;
}
}
else
{
uint8_t v___x_2561_; 
lean_dec(v___x_2557_);
v___x_2561_ = 0;
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_2562_, lean_object* v_idx_2563_){
_start:
{
uint8_t v_res_2564_; lean_object* v_r_2565_; 
v_res_2564_ = l_Lean_IR_LocalContext_isParam(v_ctx_2562_, v_idx_2563_);
lean_dec(v_idx_2563_);
lean_dec(v_ctx_2562_);
v_r_2565_ = lean_box(v_res_2564_);
return v_r_2565_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_2566_, lean_object* v_idx_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2566_, v_idx_2567_);
if (lean_obj_tag(v___x_2568_) == 1)
{
lean_object* v_val_2569_; 
v_val_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v___x_2568_, 1);
if (lean_obj_tag(v_val_2569_) == 1)
{
uint8_t v___x_2570_; 
lean_dec_ref_known(v_val_2569_, 2);
v___x_2570_ = 1;
return v___x_2570_;
}
else
{
uint8_t v___x_2571_; 
lean_dec(v_val_2569_);
v___x_2571_ = 0;
return v___x_2571_;
}
}
else
{
uint8_t v___x_2572_; 
lean_dec(v___x_2568_);
v___x_2572_ = 0;
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_2573_, lean_object* v_idx_2574_){
_start:
{
uint8_t v_res_2575_; lean_object* v_r_2576_; 
v_res_2575_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_2573_, v_idx_2574_);
lean_dec(v_idx_2574_);
lean_dec(v_ctx_2573_);
v_r_2576_ = lean_box(v_res_2575_);
return v_r_2576_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object* v_ctx_2577_, lean_object* v_idx_2578_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2578_, v_ctx_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object* v_ctx_2580_, lean_object* v_idx_2581_){
_start:
{
uint8_t v_res_2582_; lean_object* v_r_2583_; 
v_res_2582_ = l_Lean_IR_LocalContext_contains(v_ctx_2580_, v_idx_2581_);
lean_dec(v_idx_2581_);
lean_dec(v_ctx_2580_);
v_r_2583_ = lean_box(v_res_2582_);
return v_r_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_2584_, lean_object* v_t_2585_){
_start:
{
if (lean_obj_tag(v_t_2585_) == 0)
{
lean_object* v_k_2586_; lean_object* v_v_2587_; lean_object* v_l_2588_; lean_object* v_r_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_3244_; 
v_k_2586_ = lean_ctor_get(v_t_2585_, 1);
v_v_2587_ = lean_ctor_get(v_t_2585_, 2);
v_l_2588_ = lean_ctor_get(v_t_2585_, 3);
v_r_2589_ = lean_ctor_get(v_t_2585_, 4);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_t_2585_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_t_2585_, 0);
lean_dec(v_unused_3245_);
v___x_2591_ = v_t_2585_;
v_isShared_2592_ = v_isSharedCheck_3244_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_r_2589_);
lean_inc(v_l_2588_);
lean_inc(v_v_2587_);
lean_inc(v_k_2586_);
lean_dec(v_t_2585_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_3244_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_nat_dec_lt(v_k_2584_, v_k_2586_);
if (v___x_2593_ == 0)
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_nat_dec_eq(v_k_2584_, v_k_2586_);
if (v___x_2594_ == 0)
{
lean_object* v_impl_2595_; lean_object* v___x_2596_; 
v_impl_2595_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2584_, v_r_2589_);
v___x_2596_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2595_) == 0)
{
if (lean_obj_tag(v_l_2588_) == 0)
{
lean_object* v_size_2597_; lean_object* v_size_2598_; lean_object* v_k_2599_; lean_object* v_v_2600_; lean_object* v_l_2601_; lean_object* v_r_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v_size_2597_ = lean_ctor_get(v_impl_2595_, 0);
lean_inc(v_size_2597_);
v_size_2598_ = lean_ctor_get(v_l_2588_, 0);
v_k_2599_ = lean_ctor_get(v_l_2588_, 1);
v_v_2600_ = lean_ctor_get(v_l_2588_, 2);
v_l_2601_ = lean_ctor_get(v_l_2588_, 3);
v_r_2602_ = lean_ctor_get(v_l_2588_, 4);
lean_inc(v_r_2602_);
v___x_2603_ = lean_unsigned_to_nat(3u);
v___x_2604_ = lean_nat_mul(v___x_2603_, v_size_2597_);
v___x_2605_ = lean_nat_dec_lt(v___x_2604_, v_size_2598_);
lean_dec(v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec(v_r_2602_);
v___x_2606_ = lean_nat_add(v___x_2596_, v_size_2598_);
v___x_2607_ = lean_nat_add(v___x_2606_, v_size_2597_);
lean_dec(v_size_2597_);
lean_dec(v___x_2606_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_impl_2595_);
lean_ctor_set(v___x_2591_, 0, v___x_2607_);
v___x_2609_ = v___x_2591_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_l_2588_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_impl_2595_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
else
{
lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2676_; 
lean_inc(v_l_2601_);
lean_inc(v_v_2600_);
lean_inc(v_k_2599_);
lean_inc(v_size_2598_);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2677_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2588_, 2);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2588_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_2681_);
v___x_2612_ = v_l_2588_;
v_isShared_2613_ = v_isSharedCheck_2676_;
goto v_resetjp_2611_;
}
else
{
lean_dec(v_l_2588_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2676_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v_size_2614_; lean_object* v_size_2615_; lean_object* v_k_2616_; lean_object* v_v_2617_; lean_object* v_l_2618_; lean_object* v_r_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v_size_2614_ = lean_ctor_get(v_l_2601_, 0);
v_size_2615_ = lean_ctor_get(v_r_2602_, 0);
v_k_2616_ = lean_ctor_get(v_r_2602_, 1);
v_v_2617_ = lean_ctor_get(v_r_2602_, 2);
v_l_2618_ = lean_ctor_get(v_r_2602_, 3);
v_r_2619_ = lean_ctor_get(v_r_2602_, 4);
v___x_2620_ = lean_unsigned_to_nat(2u);
v___x_2621_ = lean_nat_mul(v___x_2620_, v_size_2614_);
v___x_2622_ = lean_nat_dec_lt(v_size_2615_, v___x_2621_);
lean_dec(v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2651_; 
lean_inc(v_r_2619_);
lean_inc(v_l_2618_);
lean_inc(v_v_2617_);
lean_inc(v_k_2616_);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_r_2602_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; lean_object* v_unused_2653_; lean_object* v_unused_2654_; lean_object* v_unused_2655_; lean_object* v_unused_2656_; 
v_unused_2652_ = lean_ctor_get(v_r_2602_, 4);
lean_dec(v_unused_2652_);
v_unused_2653_ = lean_ctor_get(v_r_2602_, 3);
lean_dec(v_unused_2653_);
v_unused_2654_ = lean_ctor_get(v_r_2602_, 2);
lean_dec(v_unused_2654_);
v_unused_2655_ = lean_ctor_get(v_r_2602_, 1);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v_r_2602_, 0);
lean_dec(v_unused_2656_);
v___x_2624_ = v_r_2602_;
v_isShared_2625_ = v_isSharedCheck_2651_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v_r_2602_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2651_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___x_2639_; lean_object* v___y_2641_; 
v___x_2626_ = lean_nat_add(v___x_2596_, v_size_2598_);
lean_dec(v_size_2598_);
v___x_2627_ = lean_nat_add(v___x_2626_, v_size_2597_);
lean_dec(v___x_2626_);
v___x_2639_ = lean_nat_add(v___x_2596_, v_size_2614_);
if (lean_obj_tag(v_l_2618_) == 0)
{
lean_object* v_size_2649_; 
v_size_2649_ = lean_ctor_get(v_l_2618_, 0);
lean_inc(v_size_2649_);
v___y_2641_ = v_size_2649_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v___y_2641_ = v___x_2650_;
goto v___jp_2640_;
}
v___jp_2628_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_nat_add(v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec(v___y_2630_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 4, v_impl_2595_);
lean_ctor_set(v___x_2624_, 3, v_r_2619_);
lean_ctor_set(v___x_2624_, 2, v_v_2587_);
lean_ctor_set(v___x_2624_, 1, v_k_2586_);
lean_ctor_set(v___x_2624_, 0, v___x_2632_);
v___x_2634_ = v___x_2624_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2638_, 3, v_r_2619_);
lean_ctor_set(v_reuseFailAlloc_2638_, 4, v_impl_2595_);
v___x_2634_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v___x_2634_);
lean_ctor_set(v___x_2612_, 3, v___y_2629_);
lean_ctor_set(v___x_2612_, 2, v_v_2617_);
lean_ctor_set(v___x_2612_, 1, v_k_2616_);
lean_ctor_set(v___x_2612_, 0, v___x_2627_);
v___x_2636_ = v___x_2612_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_k_2616_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_v_2617_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v___y_2629_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
v___jp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_nat_add(v___x_2639_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec(v___x_2639_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_l_2618_);
lean_ctor_set(v___x_2591_, 3, v_l_2601_);
lean_ctor_set(v___x_2591_, 2, v_v_2600_);
lean_ctor_set(v___x_2591_, 1, v_k_2599_);
lean_ctor_set(v___x_2591_, 0, v___x_2642_);
v___x_2644_ = v___x_2591_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2599_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2600_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_l_2601_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_l_2618_);
v___x_2644_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; 
v___x_2645_ = lean_nat_add(v___x_2596_, v_size_2597_);
lean_dec(v_size_2597_);
if (lean_obj_tag(v_r_2619_) == 0)
{
lean_object* v_size_2646_; 
v_size_2646_ = lean_ctor_get(v_r_2619_, 0);
lean_inc(v_size_2646_);
v___y_2629_ = v___x_2644_;
v___y_2630_ = v___x_2645_;
v___y_2631_ = v_size_2646_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_unsigned_to_nat(0u);
v___y_2629_ = v___x_2644_;
v___y_2630_ = v___x_2645_;
v___y_2631_ = v___x_2647_;
goto v___jp_2628_;
}
}
}
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_del_object(v___x_2591_);
v___x_2657_ = lean_nat_add(v___x_2596_, v_size_2598_);
lean_dec(v_size_2598_);
v___x_2658_ = lean_nat_add(v___x_2657_, v_size_2597_);
lean_dec(v___x_2657_);
v___x_2659_ = lean_nat_add(v___x_2596_, v_size_2597_);
lean_dec(v_size_2597_);
v___x_2660_ = lean_nat_add(v___x_2659_, v_size_2615_);
lean_dec(v___x_2659_);
lean_inc_ref(v_impl_2595_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v_impl_2595_);
lean_ctor_set(v___x_2612_, 3, v_r_2602_);
lean_ctor_set(v___x_2612_, 2, v_v_2587_);
lean_ctor_set(v___x_2612_, 1, v_k_2586_);
lean_ctor_set(v___x_2612_, 0, v___x_2660_);
v___x_2662_ = v___x_2612_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_r_2602_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v_impl_2595_);
v___x_2662_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
v_isSharedCheck_2669_ = !lean_is_exclusive(v_impl_2595_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; lean_object* v_unused_2671_; lean_object* v_unused_2672_; lean_object* v_unused_2673_; lean_object* v_unused_2674_; 
v_unused_2670_ = lean_ctor_get(v_impl_2595_, 4);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_impl_2595_, 3);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_impl_2595_, 2);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_impl_2595_, 1);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_impl_2595_, 0);
lean_dec(v_unused_2674_);
v___x_2664_ = v_impl_2595_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v_impl_2595_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 4, v___x_2662_);
lean_ctor_set(v___x_2664_, 3, v_l_2601_);
lean_ctor_set(v___x_2664_, 2, v_v_2600_);
lean_ctor_set(v___x_2664_, 1, v_k_2599_);
lean_ctor_set(v___x_2664_, 0, v___x_2658_);
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_k_2599_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_v_2600_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_l_2601_);
lean_ctor_set(v_reuseFailAlloc_2668_, 4, v___x_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v_size_2682_ = lean_ctor_get(v_impl_2595_, 0);
lean_inc(v_size_2682_);
v___x_2683_ = lean_nat_add(v___x_2596_, v_size_2682_);
lean_dec(v_size_2682_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_impl_2595_);
lean_ctor_set(v___x_2591_, 0, v___x_2683_);
v___x_2685_ = v___x_2591_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2686_, 3, v_l_2588_);
lean_ctor_set(v_reuseFailAlloc_2686_, 4, v_impl_2595_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
if (lean_obj_tag(v_l_2588_) == 0)
{
lean_object* v_l_2687_; 
v_l_2687_ = lean_ctor_get(v_l_2588_, 3);
if (lean_obj_tag(v_l_2687_) == 0)
{
lean_object* v_r_2688_; 
lean_inc_ref(v_l_2687_);
v_r_2688_ = lean_ctor_get(v_l_2588_, 4);
lean_inc(v_r_2688_);
if (lean_obj_tag(v_r_2688_) == 0)
{
lean_object* v_size_2689_; lean_object* v_k_2690_; lean_object* v_v_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2704_; 
v_size_2689_ = lean_ctor_get(v_l_2588_, 0);
v_k_2690_ = lean_ctor_get(v_l_2588_, 1);
v_v_2691_ = lean_ctor_get(v_l_2588_, 2);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2705_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_2706_);
v___x_2693_ = v_l_2588_;
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_v_2691_);
lean_inc(v_k_2690_);
lean_inc(v_size_2689_);
lean_dec(v_l_2588_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_size_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v_size_2695_ = lean_ctor_get(v_r_2688_, 0);
v___x_2696_ = lean_nat_add(v___x_2596_, v_size_2689_);
lean_dec(v_size_2689_);
v___x_2697_ = lean_nat_add(v___x_2596_, v_size_2695_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 4, v_impl_2595_);
lean_ctor_set(v___x_2693_, 3, v_r_2688_);
lean_ctor_set(v___x_2693_, 2, v_v_2587_);
lean_ctor_set(v___x_2693_, 1, v_k_2586_);
lean_ctor_set(v___x_2693_, 0, v___x_2697_);
v___x_2699_ = v___x_2693_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_r_2688_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_impl_2595_);
v___x_2699_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_2699_);
lean_ctor_set(v___x_2591_, 3, v_l_2687_);
lean_ctor_set(v___x_2591_, 2, v_v_2691_);
lean_ctor_set(v___x_2591_, 1, v_k_2690_);
lean_ctor_set(v___x_2591_, 0, v___x_2696_);
v___x_2701_ = v___x_2591_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_k_2690_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_v_2691_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_l_2687_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_k_2707_; lean_object* v_v_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2719_; 
v_k_2707_ = lean_ctor_get(v_l_2588_, 1);
v_v_2708_ = lean_ctor_get(v_l_2588_, 2);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; lean_object* v_unused_2721_; lean_object* v_unused_2722_; 
v_unused_2720_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_2722_);
v___x_2710_ = v_l_2588_;
v_isShared_2711_ = v_isSharedCheck_2719_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_v_2708_);
lean_inc(v_k_2707_);
lean_dec(v_l_2588_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2719_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_unsigned_to_nat(3u);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 3, v_r_2688_);
lean_ctor_set(v___x_2710_, 2, v_v_2587_);
lean_ctor_set(v___x_2710_, 1, v_k_2586_);
lean_ctor_set(v___x_2710_, 0, v___x_2596_);
v___x_2714_ = v___x_2710_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v_r_2688_);
lean_ctor_set(v_reuseFailAlloc_2718_, 4, v_r_2688_);
v___x_2714_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2716_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_2714_);
lean_ctor_set(v___x_2591_, 3, v_l_2687_);
lean_ctor_set(v___x_2591_, 2, v_v_2708_);
lean_ctor_set(v___x_2591_, 1, v_k_2707_);
lean_ctor_set(v___x_2591_, 0, v___x_2712_);
v___x_2716_ = v___x_2591_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_k_2707_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_v_2708_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_l_2687_);
lean_ctor_set(v_reuseFailAlloc_2717_, 4, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
lean_object* v_r_2723_; 
v_r_2723_ = lean_ctor_get(v_l_2588_, 4);
lean_inc(v_r_2723_);
if (lean_obj_tag(v_r_2723_) == 0)
{
lean_object* v_k_2724_; lean_object* v_v_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2748_; 
lean_inc(v_l_2687_);
v_k_2724_ = lean_ctor_get(v_l_2588_, 1);
v_v_2725_ = lean_ctor_get(v_l_2588_, 2);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; 
v_unused_2749_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_2751_);
v___x_2727_ = v_l_2588_;
v_isShared_2728_ = v_isSharedCheck_2748_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_v_2725_);
lean_inc(v_k_2724_);
lean_dec(v_l_2588_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2748_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_k_2729_; lean_object* v_v_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2744_; 
v_k_2729_ = lean_ctor_get(v_r_2723_, 1);
v_v_2730_ = lean_ctor_get(v_r_2723_, 2);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_r_2723_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; 
v_unused_2745_ = lean_ctor_get(v_r_2723_, 4);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_r_2723_, 3);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_r_2723_, 0);
lean_dec(v_unused_2747_);
v___x_2732_ = v_r_2723_;
v_isShared_2733_ = v_isSharedCheck_2744_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_v_2730_);
lean_inc(v_k_2729_);
lean_dec(v_r_2723_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2744_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_unsigned_to_nat(3u);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 4, v_l_2687_);
lean_ctor_set(v___x_2732_, 3, v_l_2687_);
lean_ctor_set(v___x_2732_, 2, v_v_2725_);
lean_ctor_set(v___x_2732_, 1, v_k_2724_);
lean_ctor_set(v___x_2732_, 0, v___x_2596_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_k_2724_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_v_2725_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_l_2687_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_l_2687_);
v___x_2736_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2738_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v_l_2687_);
lean_ctor_set(v___x_2727_, 2, v_v_2587_);
lean_ctor_set(v___x_2727_, 1, v_k_2586_);
lean_ctor_set(v___x_2727_, 0, v___x_2596_);
v___x_2738_ = v___x_2727_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_l_2687_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_l_2687_);
v___x_2738_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2740_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_2738_);
lean_ctor_set(v___x_2591_, 3, v___x_2736_);
lean_ctor_set(v___x_2591_, 2, v_v_2730_);
lean_ctor_set(v___x_2591_, 1, v_k_2729_);
lean_ctor_set(v___x_2591_, 0, v___x_2734_);
v___x_2740_ = v___x_2591_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2752_ = lean_unsigned_to_nat(2u);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_r_2723_);
lean_ctor_set(v___x_2591_, 0, v___x_2752_);
v___x_2754_ = v___x_2591_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_l_2588_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_r_2723_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v___x_2757_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_l_2588_);
lean_ctor_set(v___x_2591_, 0, v___x_2596_);
v___x_2757_ = v___x_2591_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2758_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2758_, 3, v_l_2588_);
lean_ctor_set(v_reuseFailAlloc_2758_, 4, v_l_2588_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_del_object(v___x_2591_);
lean_dec(v_v_2587_);
lean_dec(v_k_2586_);
if (lean_obj_tag(v_l_2588_) == 0)
{
if (lean_obj_tag(v_r_2589_) == 0)
{
lean_object* v_size_2759_; lean_object* v_k_2760_; lean_object* v_v_2761_; lean_object* v_l_2762_; lean_object* v_r_2763_; lean_object* v_size_2764_; lean_object* v_k_2765_; lean_object* v_v_2766_; lean_object* v_l_2767_; lean_object* v_r_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_size_2759_ = lean_ctor_get(v_l_2588_, 0);
v_k_2760_ = lean_ctor_get(v_l_2588_, 1);
v_v_2761_ = lean_ctor_get(v_l_2588_, 2);
v_l_2762_ = lean_ctor_get(v_l_2588_, 3);
v_r_2763_ = lean_ctor_get(v_l_2588_, 4);
lean_inc(v_r_2763_);
v_size_2764_ = lean_ctor_get(v_r_2589_, 0);
v_k_2765_ = lean_ctor_get(v_r_2589_, 1);
v_v_2766_ = lean_ctor_get(v_r_2589_, 2);
v_l_2767_ = lean_ctor_get(v_r_2589_, 3);
lean_inc(v_l_2767_);
v_r_2768_ = lean_ctor_get(v_r_2589_, 4);
v___x_2769_ = lean_unsigned_to_nat(1u);
v___x_2770_ = lean_nat_dec_lt(v_size_2759_, v_size_2764_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2906_; 
lean_inc(v_l_2762_);
lean_inc(v_v_2761_);
lean_inc(v_k_2760_);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; lean_object* v_unused_2908_; lean_object* v_unused_2909_; lean_object* v_unused_2910_; lean_object* v_unused_2911_; 
v_unused_2907_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_2907_);
v_unused_2908_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_l_2588_, 2);
lean_dec(v_unused_2909_);
v_unused_2910_ = lean_ctor_get(v_l_2588_, 1);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_2911_);
v___x_2772_ = v_l_2588_;
v_isShared_2773_ = v_isSharedCheck_2906_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v_l_2588_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2906_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v_tree_2775_; 
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2760_, v_v_2761_, v_l_2762_, v_r_2763_);
v_tree_2775_ = lean_ctor_get(v___x_2774_, 2);
lean_inc(v_tree_2775_);
if (lean_obj_tag(v_tree_2775_) == 0)
{
lean_object* v_k_2776_; lean_object* v_v_2777_; lean_object* v_size_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v_k_2776_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_k_2776_);
v_v_2777_ = lean_ctor_get(v___x_2774_, 1);
lean_inc(v_v_2777_);
lean_dec_ref(v___x_2774_);
v_size_2778_ = lean_ctor_get(v_tree_2775_, 0);
v___x_2779_ = lean_unsigned_to_nat(3u);
v___x_2780_ = lean_nat_mul(v___x_2779_, v_size_2778_);
v___x_2781_ = lean_nat_dec_lt(v___x_2780_, v_size_2764_);
lean_dec(v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_dec(v_l_2767_);
v___x_2782_ = lean_nat_add(v___x_2769_, v_size_2778_);
v___x_2783_ = lean_nat_add(v___x_2782_, v_size_2764_);
lean_dec(v___x_2782_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v_r_2589_);
lean_ctor_set(v___x_2772_, 3, v_tree_2775_);
lean_ctor_set(v___x_2772_, 2, v_v_2777_);
lean_ctor_set(v___x_2772_, 1, v_k_2776_);
lean_ctor_set(v___x_2772_, 0, v___x_2783_);
v___x_2785_ = v___x_2772_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_k_2776_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_v_2777_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_tree_2775_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v_r_2589_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2841_; 
lean_inc(v_r_2768_);
lean_inc(v_v_2766_);
lean_inc(v_k_2765_);
lean_inc(v_size_2764_);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; lean_object* v_unused_2843_; lean_object* v_unused_2844_; lean_object* v_unused_2845_; lean_object* v_unused_2846_; 
v_unused_2842_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_2842_);
v_unused_2843_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_2843_);
v_unused_2844_ = lean_ctor_get(v_r_2589_, 2);
lean_dec(v_unused_2844_);
v_unused_2845_ = lean_ctor_get(v_r_2589_, 1);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_r_2589_, 0);
lean_dec(v_unused_2846_);
v___x_2788_ = v_r_2589_;
v_isShared_2789_ = v_isSharedCheck_2841_;
goto v_resetjp_2787_;
}
else
{
lean_dec(v_r_2589_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2841_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_size_2790_; lean_object* v_k_2791_; lean_object* v_v_2792_; lean_object* v_l_2793_; lean_object* v_r_2794_; lean_object* v_size_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_size_2790_ = lean_ctor_get(v_l_2767_, 0);
v_k_2791_ = lean_ctor_get(v_l_2767_, 1);
v_v_2792_ = lean_ctor_get(v_l_2767_, 2);
v_l_2793_ = lean_ctor_get(v_l_2767_, 3);
v_r_2794_ = lean_ctor_get(v_l_2767_, 4);
v_size_2795_ = lean_ctor_get(v_r_2768_, 0);
v___x_2796_ = lean_unsigned_to_nat(2u);
v___x_2797_ = lean_nat_mul(v___x_2796_, v_size_2795_);
v___x_2798_ = lean_nat_dec_lt(v_size_2790_, v___x_2797_);
lean_dec(v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2826_; 
lean_inc(v_r_2794_);
lean_inc(v_l_2793_);
lean_inc(v_v_2792_);
lean_inc(v_k_2791_);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_l_2767_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; lean_object* v_unused_2831_; 
v_unused_2827_ = lean_ctor_get(v_l_2767_, 4);
lean_dec(v_unused_2827_);
v_unused_2828_ = lean_ctor_get(v_l_2767_, 3);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_l_2767_, 2);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_l_2767_, 1);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_l_2767_, 0);
lean_dec(v_unused_2831_);
v___x_2800_ = v_l_2767_;
v_isShared_2801_ = v_isSharedCheck_2826_;
goto v_resetjp_2799_;
}
else
{
lean_dec(v_l_2767_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2826_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2816_; 
v___x_2802_ = lean_nat_add(v___x_2769_, v_size_2778_);
v___x_2803_ = lean_nat_add(v___x_2802_, v_size_2764_);
lean_dec(v_size_2764_);
if (lean_obj_tag(v_l_2793_) == 0)
{
lean_object* v_size_2824_; 
v_size_2824_ = lean_ctor_get(v_l_2793_, 0);
lean_inc(v_size_2824_);
v___y_2816_ = v_size_2824_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_unsigned_to_nat(0u);
v___y_2816_ = v___x_2825_;
goto v___jp_2815_;
}
v___jp_2804_:
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = lean_nat_add(v___y_2805_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec(v___y_2805_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 4, v_r_2768_);
lean_ctor_set(v___x_2800_, 3, v_r_2794_);
lean_ctor_set(v___x_2800_, 2, v_v_2766_);
lean_ctor_set(v___x_2800_, 1, v_k_2765_);
lean_ctor_set(v___x_2800_, 0, v___x_2808_);
v___x_2810_ = v___x_2800_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_k_2765_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_v_2766_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_r_2794_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_r_2768_);
v___x_2810_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2812_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 4, v___x_2810_);
lean_ctor_set(v___x_2788_, 3, v___y_2806_);
lean_ctor_set(v___x_2788_, 2, v_v_2792_);
lean_ctor_set(v___x_2788_, 1, v_k_2791_);
lean_ctor_set(v___x_2788_, 0, v___x_2803_);
v___x_2812_ = v___x_2788_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_k_2791_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_v_2792_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v___y_2806_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
v___jp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2817_ = lean_nat_add(v___x_2802_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec(v___x_2802_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v_l_2793_);
lean_ctor_set(v___x_2772_, 3, v_tree_2775_);
lean_ctor_set(v___x_2772_, 2, v_v_2777_);
lean_ctor_set(v___x_2772_, 1, v_k_2776_);
lean_ctor_set(v___x_2772_, 0, v___x_2817_);
v___x_2819_ = v___x_2772_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_k_2776_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_v_2777_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v_tree_2775_);
lean_ctor_set(v_reuseFailAlloc_2823_, 4, v_l_2793_);
v___x_2819_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; 
v___x_2820_ = lean_nat_add(v___x_2769_, v_size_2795_);
if (lean_obj_tag(v_r_2794_) == 0)
{
lean_object* v_size_2821_; 
v_size_2821_ = lean_ctor_get(v_r_2794_, 0);
lean_inc(v_size_2821_);
v___y_2805_ = v___x_2820_;
v___y_2806_ = v___x_2819_;
v___y_2807_ = v_size_2821_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_unsigned_to_nat(0u);
v___y_2805_ = v___x_2820_;
v___y_2806_ = v___x_2819_;
v___y_2807_ = v___x_2822_;
goto v___jp_2804_;
}
}
}
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2832_ = lean_nat_add(v___x_2769_, v_size_2778_);
v___x_2833_ = lean_nat_add(v___x_2832_, v_size_2764_);
lean_dec(v_size_2764_);
v___x_2834_ = lean_nat_add(v___x_2832_, v_size_2790_);
lean_dec(v___x_2832_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 4, v_l_2767_);
lean_ctor_set(v___x_2788_, 3, v_tree_2775_);
lean_ctor_set(v___x_2788_, 2, v_v_2777_);
lean_ctor_set(v___x_2788_, 1, v_k_2776_);
lean_ctor_set(v___x_2788_, 0, v___x_2834_);
v___x_2836_ = v___x_2788_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2776_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2777_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_tree_2775_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_l_2767_);
v___x_2836_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2838_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v_r_2768_);
lean_ctor_set(v___x_2772_, 3, v___x_2836_);
lean_ctor_set(v___x_2772_, 2, v_v_2766_);
lean_ctor_set(v___x_2772_, 1, v_k_2765_);
lean_ctor_set(v___x_2772_, 0, v___x_2833_);
v___x_2838_ = v___x_2772_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_k_2765_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_v_2766_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_r_2768_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
else
{
lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2900_; 
lean_inc(v_r_2768_);
lean_inc(v_v_2766_);
lean_inc(v_k_2765_);
lean_inc(v_size_2764_);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; lean_object* v_unused_2902_; lean_object* v_unused_2903_; lean_object* v_unused_2904_; lean_object* v_unused_2905_; 
v_unused_2901_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_2901_);
v_unused_2902_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_2902_);
v_unused_2903_ = lean_ctor_get(v_r_2589_, 2);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_r_2589_, 1);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_r_2589_, 0);
lean_dec(v_unused_2905_);
v___x_2848_ = v_r_2589_;
v_isShared_2849_ = v_isSharedCheck_2900_;
goto v_resetjp_2847_;
}
else
{
lean_dec(v_r_2589_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2900_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
if (lean_obj_tag(v_l_2767_) == 0)
{
if (lean_obj_tag(v_r_2768_) == 0)
{
lean_object* v_k_2850_; lean_object* v_v_2851_; lean_object* v_size_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v_k_2850_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_k_2850_);
v_v_2851_ = lean_ctor_get(v___x_2774_, 1);
lean_inc(v_v_2851_);
lean_dec_ref(v___x_2774_);
v_size_2852_ = lean_ctor_get(v_l_2767_, 0);
v___x_2853_ = lean_nat_add(v___x_2769_, v_size_2764_);
lean_dec(v_size_2764_);
v___x_2854_ = lean_nat_add(v___x_2769_, v_size_2852_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 4, v_l_2767_);
lean_ctor_set(v___x_2848_, 3, v_tree_2775_);
lean_ctor_set(v___x_2848_, 2, v_v_2851_);
lean_ctor_set(v___x_2848_, 1, v_k_2850_);
lean_ctor_set(v___x_2848_, 0, v___x_2854_);
v___x_2856_ = v___x_2848_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_k_2850_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_v_2851_);
lean_ctor_set(v_reuseFailAlloc_2860_, 3, v_tree_2775_);
lean_ctor_set(v_reuseFailAlloc_2860_, 4, v_l_2767_);
v___x_2856_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v_r_2768_);
lean_ctor_set(v___x_2772_, 3, v___x_2856_);
lean_ctor_set(v___x_2772_, 2, v_v_2766_);
lean_ctor_set(v___x_2772_, 1, v_k_2765_);
lean_ctor_set(v___x_2772_, 0, v___x_2853_);
v___x_2858_ = v___x_2772_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_k_2765_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_v_2766_);
lean_ctor_set(v_reuseFailAlloc_2859_, 3, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2859_, 4, v_r_2768_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_k_2861_; lean_object* v_v_2862_; lean_object* v_k_2863_; lean_object* v_v_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_size_2764_);
v_k_2861_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_k_2861_);
v_v_2862_ = lean_ctor_get(v___x_2774_, 1);
lean_inc(v_v_2862_);
lean_dec_ref(v___x_2774_);
v_k_2863_ = lean_ctor_get(v_l_2767_, 1);
v_v_2864_ = lean_ctor_get(v_l_2767_, 2);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_l_2767_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; lean_object* v_unused_2880_; lean_object* v_unused_2881_; 
v_unused_2879_ = lean_ctor_get(v_l_2767_, 4);
lean_dec(v_unused_2879_);
v_unused_2880_ = lean_ctor_get(v_l_2767_, 3);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_l_2767_, 0);
lean_dec(v_unused_2881_);
v___x_2866_ = v_l_2767_;
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_v_2864_);
lean_inc(v_k_2863_);
lean_dec(v_l_2767_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = lean_unsigned_to_nat(3u);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 4, v_r_2768_);
lean_ctor_set(v___x_2866_, 3, v_r_2768_);
lean_ctor_set(v___x_2866_, 2, v_v_2862_);
lean_ctor_set(v___x_2866_, 1, v_k_2861_);
lean_ctor_set(v___x_2866_, 0, v___x_2769_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2861_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2862_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_r_2768_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_r_2768_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 3, v_r_2768_);
lean_ctor_set(v___x_2848_, 0, v___x_2769_);
v___x_2872_ = v___x_2848_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_k_2765_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_v_2766_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_r_2768_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_r_2768_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___x_2872_);
lean_ctor_set(v___x_2772_, 3, v___x_2870_);
lean_ctor_set(v___x_2772_, 2, v_v_2864_);
lean_ctor_set(v___x_2772_, 1, v_k_2863_);
lean_ctor_set(v___x_2772_, 0, v___x_2868_);
v___x_2874_ = v___x_2772_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_k_2863_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_v_2864_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2768_) == 0)
{
lean_object* v_k_2882_; lean_object* v_v_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_dec(v_size_2764_);
v_k_2882_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_k_2882_);
v_v_2883_ = lean_ctor_get(v___x_2774_, 1);
lean_inc(v_v_2883_);
lean_dec_ref(v___x_2774_);
v___x_2884_ = lean_unsigned_to_nat(3u);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 4, v_l_2767_);
lean_ctor_set(v___x_2848_, 2, v_v_2883_);
lean_ctor_set(v___x_2848_, 1, v_k_2882_);
lean_ctor_set(v___x_2848_, 0, v___x_2769_);
v___x_2886_ = v___x_2848_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_k_2882_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_v_2883_);
lean_ctor_set(v_reuseFailAlloc_2890_, 3, v_l_2767_);
lean_ctor_set(v_reuseFailAlloc_2890_, 4, v_l_2767_);
v___x_2886_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v_r_2768_);
lean_ctor_set(v___x_2772_, 3, v___x_2886_);
lean_ctor_set(v___x_2772_, 2, v_v_2766_);
lean_ctor_set(v___x_2772_, 1, v_k_2765_);
lean_ctor_set(v___x_2772_, 0, v___x_2884_);
v___x_2888_ = v___x_2772_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_k_2765_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_v_2766_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2889_, 4, v_r_2768_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
else
{
lean_object* v_k_2891_; lean_object* v_v_2892_; lean_object* v___x_2894_; 
v_k_2891_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_k_2891_);
v_v_2892_ = lean_ctor_get(v___x_2774_, 1);
lean_inc(v_v_2892_);
lean_dec_ref(v___x_2774_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 3, v_r_2768_);
v___x_2894_ = v___x_2848_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_size_2764_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_k_2765_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_v_2766_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_r_2768_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_r_2768_);
v___x_2894_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = lean_unsigned_to_nat(2u);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___x_2894_);
lean_ctor_set(v___x_2772_, 3, v_r_2768_);
lean_ctor_set(v___x_2772_, 2, v_v_2892_);
lean_ctor_set(v___x_2772_, 1, v_k_2891_);
lean_ctor_set(v___x_2772_, 0, v___x_2895_);
v___x_2897_ = v___x_2772_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_k_2891_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_v_2892_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_r_2768_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v___x_2894_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3064_; 
lean_inc(v_r_2768_);
lean_inc(v_v_2766_);
lean_inc(v_k_2765_);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; lean_object* v_unused_3066_; lean_object* v_unused_3067_; lean_object* v_unused_3068_; lean_object* v_unused_3069_; 
v_unused_3065_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_3065_);
v_unused_3066_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_3066_);
v_unused_3067_ = lean_ctor_get(v_r_2589_, 2);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v_r_2589_, 1);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v_r_2589_, 0);
lean_dec(v_unused_3069_);
v___x_2913_ = v_r_2589_;
v_isShared_2914_ = v_isSharedCheck_3064_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v_r_2589_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3064_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v_tree_2916_; 
v___x_2915_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2765_, v_v_2766_, v_l_2767_, v_r_2768_);
v_tree_2916_ = lean_ctor_get(v___x_2915_, 2);
lean_inc(v_tree_2916_);
if (lean_obj_tag(v_tree_2916_) == 0)
{
lean_object* v_k_2917_; lean_object* v_v_2918_; lean_object* v_size_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v_k_2917_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_k_2917_);
v_v_2918_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_v_2918_);
lean_dec_ref(v___x_2915_);
v_size_2919_ = lean_ctor_get(v_tree_2916_, 0);
v___x_2920_ = lean_unsigned_to_nat(3u);
v___x_2921_ = lean_nat_mul(v___x_2920_, v_size_2919_);
v___x_2922_ = lean_nat_dec_lt(v___x_2921_, v_size_2759_);
lean_dec(v___x_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
lean_dec(v_r_2763_);
v___x_2923_ = lean_nat_add(v___x_2769_, v_size_2759_);
v___x_2924_ = lean_nat_add(v___x_2923_, v_size_2919_);
lean_dec(v___x_2923_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_tree_2916_);
lean_ctor_set(v___x_2913_, 3, v_l_2588_);
lean_ctor_set(v___x_2913_, 2, v_v_2918_);
lean_ctor_set(v___x_2913_, 1, v_k_2917_);
lean_ctor_set(v___x_2913_, 0, v___x_2924_);
v___x_2926_ = v___x_2913_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_l_2588_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_tree_2916_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
else
{
lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2993_; 
lean_inc(v_l_2762_);
lean_inc(v_v_2761_);
lean_inc(v_k_2760_);
lean_inc(v_size_2759_);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; lean_object* v_unused_2995_; lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; 
v_unused_2994_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_l_2588_, 2);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_l_2588_, 1);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_2998_);
v___x_2929_ = v_l_2588_;
v_isShared_2930_ = v_isSharedCheck_2993_;
goto v_resetjp_2928_;
}
else
{
lean_dec(v_l_2588_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2993_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_size_2931_; lean_object* v_size_2932_; lean_object* v_k_2933_; lean_object* v_v_2934_; lean_object* v_l_2935_; lean_object* v_r_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_size_2931_ = lean_ctor_get(v_l_2762_, 0);
v_size_2932_ = lean_ctor_get(v_r_2763_, 0);
v_k_2933_ = lean_ctor_get(v_r_2763_, 1);
v_v_2934_ = lean_ctor_get(v_r_2763_, 2);
v_l_2935_ = lean_ctor_get(v_r_2763_, 3);
v_r_2936_ = lean_ctor_get(v_r_2763_, 4);
v___x_2937_ = lean_unsigned_to_nat(2u);
v___x_2938_ = lean_nat_mul(v___x_2937_, v_size_2931_);
v___x_2939_ = lean_nat_dec_lt(v_size_2932_, v___x_2938_);
lean_dec(v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2977_; 
lean_inc(v_r_2936_);
lean_inc(v_l_2935_);
lean_inc(v_v_2934_);
lean_inc(v_k_2933_);
lean_del_object(v___x_2929_);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_r_2763_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; lean_object* v_unused_2979_; lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; 
v_unused_2978_ = lean_ctor_get(v_r_2763_, 4);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v_r_2763_, 3);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_r_2763_, 2);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_r_2763_, 1);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_r_2763_, 0);
lean_dec(v_unused_2982_);
v___x_2941_ = v_r_2763_;
v_isShared_2942_ = v_isSharedCheck_2977_;
goto v_resetjp_2940_;
}
else
{
lean_dec(v_r_2763_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2977_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___x_2965_; lean_object* v___y_2967_; 
v___x_2943_ = lean_nat_add(v___x_2769_, v_size_2759_);
lean_dec(v_size_2759_);
v___x_2944_ = lean_nat_add(v___x_2943_, v_size_2919_);
lean_dec(v___x_2943_);
v___x_2965_ = lean_nat_add(v___x_2769_, v_size_2931_);
if (lean_obj_tag(v_l_2935_) == 0)
{
lean_object* v_size_2975_; 
v_size_2975_ = lean_ctor_get(v_l_2935_, 0);
lean_inc(v_size_2975_);
v___y_2967_ = v_size_2975_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_unsigned_to_nat(0u);
v___y_2967_ = v___x_2976_;
goto v___jp_2966_;
}
v___jp_2945_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = lean_nat_add(v___y_2946_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec(v___y_2946_);
lean_inc_ref(v_tree_2916_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 4, v_tree_2916_);
lean_ctor_set(v___x_2941_, 3, v_r_2936_);
lean_ctor_set(v___x_2941_, 2, v_v_2918_);
lean_ctor_set(v___x_2941_, 1, v_k_2917_);
lean_ctor_set(v___x_2941_, 0, v___x_2949_);
v___x_2951_ = v___x_2941_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_r_2936_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_tree_2916_);
v___x_2951_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_isSharedCheck_2958_ = !lean_is_exclusive(v_tree_2916_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; lean_object* v_unused_2960_; lean_object* v_unused_2961_; lean_object* v_unused_2962_; lean_object* v_unused_2963_; 
v_unused_2959_ = lean_ctor_get(v_tree_2916_, 4);
lean_dec(v_unused_2959_);
v_unused_2960_ = lean_ctor_get(v_tree_2916_, 3);
lean_dec(v_unused_2960_);
v_unused_2961_ = lean_ctor_get(v_tree_2916_, 2);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v_tree_2916_, 1);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_tree_2916_, 0);
lean_dec(v_unused_2963_);
v___x_2953_ = v_tree_2916_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_dec(v_tree_2916_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 4, v___x_2951_);
lean_ctor_set(v___x_2953_, 3, v___y_2947_);
lean_ctor_set(v___x_2953_, 2, v_v_2934_);
lean_ctor_set(v___x_2953_, 1, v_k_2933_);
lean_ctor_set(v___x_2953_, 0, v___x_2944_);
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_k_2933_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_v_2934_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v___y_2947_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v___x_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
v___jp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2968_ = lean_nat_add(v___x_2965_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec(v___x_2965_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_l_2935_);
lean_ctor_set(v___x_2913_, 3, v_l_2762_);
lean_ctor_set(v___x_2913_, 2, v_v_2761_);
lean_ctor_set(v___x_2913_, 1, v_k_2760_);
lean_ctor_set(v___x_2913_, 0, v___x_2968_);
v___x_2970_ = v___x_2913_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_k_2760_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_v_2761_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_l_2762_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_l_2935_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_nat_add(v___x_2769_, v_size_2919_);
if (lean_obj_tag(v_r_2936_) == 0)
{
lean_object* v_size_2972_; 
v_size_2972_ = lean_ctor_get(v_r_2936_, 0);
lean_inc(v_size_2972_);
v___y_2946_ = v___x_2971_;
v___y_2947_ = v___x_2970_;
v___y_2948_ = v_size_2972_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_unsigned_to_nat(0u);
v___y_2946_ = v___x_2971_;
v___y_2947_ = v___x_2970_;
v___y_2948_ = v___x_2973_;
goto v___jp_2945_;
}
}
}
}
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2983_ = lean_nat_add(v___x_2769_, v_size_2759_);
lean_dec(v_size_2759_);
v___x_2984_ = lean_nat_add(v___x_2983_, v_size_2919_);
lean_dec(v___x_2983_);
v___x_2985_ = lean_nat_add(v___x_2769_, v_size_2919_);
v___x_2986_ = lean_nat_add(v___x_2985_, v_size_2932_);
lean_dec(v___x_2985_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_tree_2916_);
lean_ctor_set(v___x_2913_, 3, v_r_2763_);
lean_ctor_set(v___x_2913_, 2, v_v_2918_);
lean_ctor_set(v___x_2913_, 1, v_k_2917_);
lean_ctor_set(v___x_2913_, 0, v___x_2986_);
v___x_2988_ = v___x_2913_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_r_2763_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v_tree_2916_);
v___x_2988_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2990_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 4, v___x_2988_);
lean_ctor_set(v___x_2929_, 0, v___x_2984_);
v___x_2990_ = v___x_2929_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_k_2760_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_v_2761_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_l_2762_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2762_) == 0)
{
lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3022_; 
lean_inc_ref(v_l_2762_);
lean_inc(v_v_2761_);
lean_inc(v_k_2760_);
lean_inc(v_size_2759_);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; lean_object* v_unused_3024_; lean_object* v_unused_3025_; lean_object* v_unused_3026_; lean_object* v_unused_3027_; 
v_unused_3023_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_3023_);
v_unused_3024_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_l_2588_, 2);
lean_dec(v_unused_3025_);
v_unused_3026_ = lean_ctor_get(v_l_2588_, 1);
lean_dec(v_unused_3026_);
v_unused_3027_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_3027_);
v___x_3000_ = v_l_2588_;
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
else
{
lean_dec(v_l_2588_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
if (lean_obj_tag(v_r_2763_) == 0)
{
lean_object* v_k_3002_; lean_object* v_v_3003_; lean_object* v_size_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v_k_3002_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_k_3002_);
v_v_3003_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_v_3003_);
lean_dec_ref(v___x_2915_);
v_size_3004_ = lean_ctor_get(v_r_2763_, 0);
v___x_3005_ = lean_nat_add(v___x_2769_, v_size_2759_);
lean_dec(v_size_2759_);
v___x_3006_ = lean_nat_add(v___x_2769_, v_size_3004_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_tree_2916_);
lean_ctor_set(v___x_2913_, 3, v_r_2763_);
lean_ctor_set(v___x_2913_, 2, v_v_3003_);
lean_ctor_set(v___x_2913_, 1, v_k_3002_);
lean_ctor_set(v___x_2913_, 0, v___x_3006_);
v___x_3008_ = v___x_2913_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_3002_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_3003_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_r_2763_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_tree_2916_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 4, v___x_3008_);
lean_ctor_set(v___x_3000_, 0, v___x_3005_);
v___x_3010_ = v___x_3000_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_2760_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_2761_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_l_2762_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
lean_object* v_k_3013_; lean_object* v_v_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
lean_dec(v_size_2759_);
v_k_3013_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_k_3013_);
v_v_3014_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_v_3014_);
lean_dec_ref(v___x_2915_);
v___x_3015_ = lean_unsigned_to_nat(3u);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_r_2763_);
lean_ctor_set(v___x_2913_, 3, v_r_2763_);
lean_ctor_set(v___x_2913_, 2, v_v_3014_);
lean_ctor_set(v___x_2913_, 1, v_k_3013_);
lean_ctor_set(v___x_2913_, 0, v___x_2769_);
v___x_3017_ = v___x_2913_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_k_3013_);
lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_v_3014_);
lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_r_2763_);
lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_r_2763_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 4, v___x_3017_);
lean_ctor_set(v___x_3000_, 0, v___x_3015_);
v___x_3019_ = v___x_3000_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_k_2760_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_v_2761_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_l_2762_);
lean_ctor_set(v_reuseFailAlloc_3020_, 4, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2763_) == 0)
{
lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3052_; 
lean_inc(v_l_2762_);
lean_inc(v_v_2761_);
lean_inc(v_k_2760_);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_l_2588_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; lean_object* v_unused_3054_; lean_object* v_unused_3055_; lean_object* v_unused_3056_; lean_object* v_unused_3057_; 
v_unused_3053_ = lean_ctor_get(v_l_2588_, 4);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v_l_2588_, 3);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v_l_2588_, 2);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_l_2588_, 1);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v_l_2588_, 0);
lean_dec(v_unused_3057_);
v___x_3029_ = v_l_2588_;
v_isShared_3030_ = v_isSharedCheck_3052_;
goto v_resetjp_3028_;
}
else
{
lean_dec(v_l_2588_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3052_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v_k_3031_; lean_object* v_v_3032_; lean_object* v_k_3033_; lean_object* v_v_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3048_; 
v_k_3031_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_k_3031_);
v_v_3032_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_v_3032_);
lean_dec_ref(v___x_2915_);
v_k_3033_ = lean_ctor_get(v_r_2763_, 1);
v_v_3034_ = lean_ctor_get(v_r_2763_, 2);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_r_2763_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; lean_object* v_unused_3050_; lean_object* v_unused_3051_; 
v_unused_3049_ = lean_ctor_get(v_r_2763_, 4);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v_r_2763_, 3);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v_r_2763_, 0);
lean_dec(v_unused_3051_);
v___x_3036_ = v_r_2763_;
v_isShared_3037_ = v_isSharedCheck_3048_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_v_3034_);
lean_inc(v_k_3033_);
lean_dec(v_r_2763_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3048_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3038_ = lean_unsigned_to_nat(3u);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 4, v_l_2762_);
lean_ctor_set(v___x_3036_, 3, v_l_2762_);
lean_ctor_set(v___x_3036_, 2, v_v_2761_);
lean_ctor_set(v___x_3036_, 1, v_k_2760_);
lean_ctor_set(v___x_3036_, 0, v___x_2769_);
v___x_3040_ = v___x_3036_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_k_2760_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_v_2761_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_l_2762_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_l_2762_);
v___x_3040_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_l_2762_);
lean_ctor_set(v___x_2913_, 3, v_l_2762_);
lean_ctor_set(v___x_2913_, 2, v_v_3032_);
lean_ctor_set(v___x_2913_, 1, v_k_3031_);
lean_ctor_set(v___x_2913_, 0, v___x_2769_);
v___x_3042_ = v___x_2913_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_k_3031_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_v_3032_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_l_2762_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v_l_2762_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3044_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 4, v___x_3042_);
lean_ctor_set(v___x_3029_, 3, v___x_3040_);
lean_ctor_set(v___x_3029_, 2, v_v_3034_);
lean_ctor_set(v___x_3029_, 1, v_k_3033_);
lean_ctor_set(v___x_3029_, 0, v___x_3038_);
v___x_3044_ = v___x_3029_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_k_3033_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_v_3034_);
lean_ctor_set(v_reuseFailAlloc_3045_, 3, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3045_, 4, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
}
}
else
{
lean_object* v_k_3058_; lean_object* v_v_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v_k_3058_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_k_3058_);
v_v_3059_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_v_3059_);
lean_dec_ref(v___x_2915_);
v___x_3060_ = lean_unsigned_to_nat(2u);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_r_2763_);
lean_ctor_set(v___x_2913_, 3, v_l_2588_);
lean_ctor_set(v___x_2913_, 2, v_v_3059_);
lean_ctor_set(v___x_2913_, 1, v_k_3058_);
lean_ctor_set(v___x_2913_, 0, v___x_3060_);
v___x_3062_ = v___x_2913_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_k_3058_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_v_3059_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v_l_2588_);
lean_ctor_set(v_reuseFailAlloc_3063_, 4, v_r_2763_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
}
else
{
return v_l_2588_;
}
}
else
{
return v_r_2589_;
}
}
}
else
{
lean_object* v_impl_3070_; lean_object* v___x_3071_; 
v_impl_3070_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2584_, v_l_2588_);
v___x_3071_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3070_) == 0)
{
if (lean_obj_tag(v_r_2589_) == 0)
{
lean_object* v_size_3072_; lean_object* v_size_3073_; lean_object* v_k_3074_; lean_object* v_v_3075_; lean_object* v_l_3076_; lean_object* v_r_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_size_3072_ = lean_ctor_get(v_impl_3070_, 0);
lean_inc(v_size_3072_);
v_size_3073_ = lean_ctor_get(v_r_2589_, 0);
v_k_3074_ = lean_ctor_get(v_r_2589_, 1);
v_v_3075_ = lean_ctor_get(v_r_2589_, 2);
v_l_3076_ = lean_ctor_get(v_r_2589_, 3);
lean_inc(v_l_3076_);
v_r_3077_ = lean_ctor_get(v_r_2589_, 4);
v___x_3078_ = lean_unsigned_to_nat(3u);
v___x_3079_ = lean_nat_mul(v___x_3078_, v_size_3072_);
v___x_3080_ = lean_nat_dec_lt(v___x_3079_, v_size_3073_);
lean_dec(v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_dec(v_l_3076_);
v___x_3081_ = lean_nat_add(v___x_3071_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3082_ = lean_nat_add(v___x_3081_, v_size_3073_);
lean_dec(v___x_3081_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 3, v_impl_3070_);
lean_ctor_set(v___x_2591_, 0, v___x_3082_);
v___x_3084_ = v___x_2591_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3085_, 3, v_impl_3070_);
lean_ctor_set(v_reuseFailAlloc_3085_, 4, v_r_2589_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
else
{
lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3149_; 
lean_inc(v_r_3077_);
lean_inc(v_v_3075_);
lean_inc(v_k_3074_);
lean_inc(v_size_3073_);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; 
v_unused_3150_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_r_2589_, 2);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_r_2589_, 1);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_r_2589_, 0);
lean_dec(v_unused_3154_);
v___x_3087_ = v_r_2589_;
v_isShared_3088_ = v_isSharedCheck_3149_;
goto v_resetjp_3086_;
}
else
{
lean_dec(v_r_2589_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3149_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_size_3089_; lean_object* v_k_3090_; lean_object* v_v_3091_; lean_object* v_l_3092_; lean_object* v_r_3093_; lean_object* v_size_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v_size_3089_ = lean_ctor_get(v_l_3076_, 0);
v_k_3090_ = lean_ctor_get(v_l_3076_, 1);
v_v_3091_ = lean_ctor_get(v_l_3076_, 2);
v_l_3092_ = lean_ctor_get(v_l_3076_, 3);
v_r_3093_ = lean_ctor_get(v_l_3076_, 4);
v_size_3094_ = lean_ctor_get(v_r_3077_, 0);
v___x_3095_ = lean_unsigned_to_nat(2u);
v___x_3096_ = lean_nat_mul(v___x_3095_, v_size_3094_);
v___x_3097_ = lean_nat_dec_lt(v_size_3089_, v___x_3096_);
lean_dec(v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_r_3093_);
lean_inc(v_l_3092_);
lean_inc(v_v_3091_);
lean_inc(v_k_3090_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_l_3076_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; 
v_unused_3126_ = lean_ctor_get(v_l_3076_, 4);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_l_3076_, 3);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_l_3076_, 2);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_l_3076_, 1);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_l_3076_, 0);
lean_dec(v_unused_3130_);
v___x_3099_ = v_l_3076_;
v_isShared_3100_ = v_isSharedCheck_3125_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v_l_3076_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3125_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3115_; 
v___x_3101_ = lean_nat_add(v___x_3071_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3102_ = lean_nat_add(v___x_3101_, v_size_3073_);
lean_dec(v_size_3073_);
if (lean_obj_tag(v_l_3092_) == 0)
{
lean_object* v_size_3123_; 
v_size_3123_ = lean_ctor_get(v_l_3092_, 0);
lean_inc(v_size_3123_);
v___y_3115_ = v_size_3123_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_unsigned_to_nat(0u);
v___y_3115_ = v___x_3124_;
goto v___jp_3114_;
}
v___jp_3103_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_nat_add(v___y_3104_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec(v___y_3104_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 4, v_r_3077_);
lean_ctor_set(v___x_3099_, 3, v_r_3093_);
lean_ctor_set(v___x_3099_, 2, v_v_3075_);
lean_ctor_set(v___x_3099_, 1, v_k_3074_);
lean_ctor_set(v___x_3099_, 0, v___x_3107_);
v___x_3109_ = v___x_3099_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_k_3074_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_v_3075_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_r_3093_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_r_3077_);
v___x_3109_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3111_; 
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 4, v___x_3109_);
lean_ctor_set(v___x_3087_, 3, v___y_3105_);
lean_ctor_set(v___x_3087_, 2, v_v_3091_);
lean_ctor_set(v___x_3087_, 1, v_k_3090_);
lean_ctor_set(v___x_3087_, 0, v___x_3102_);
v___x_3111_ = v___x_3087_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_k_3090_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_v_3091_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v___y_3105_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_nat_add(v___x_3101_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec(v___x_3101_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_l_3092_);
lean_ctor_set(v___x_2591_, 3, v_impl_3070_);
lean_ctor_set(v___x_2591_, 0, v___x_3116_);
v___x_3118_ = v___x_2591_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_impl_3070_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_l_3092_);
v___x_3118_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_nat_add(v___x_3071_, v_size_3094_);
if (lean_obj_tag(v_r_3093_) == 0)
{
lean_object* v_size_3120_; 
v_size_3120_ = lean_ctor_get(v_r_3093_, 0);
lean_inc(v_size_3120_);
v___y_3104_ = v___x_3119_;
v___y_3105_ = v___x_3118_;
v___y_3106_ = v_size_3120_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_unsigned_to_nat(0u);
v___y_3104_ = v___x_3119_;
v___y_3105_ = v___x_3118_;
v___y_3106_ = v___x_3121_;
goto v___jp_3103_;
}
}
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
lean_del_object(v___x_2591_);
v___x_3131_ = lean_nat_add(v___x_3071_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3132_ = lean_nat_add(v___x_3131_, v_size_3073_);
lean_dec(v_size_3073_);
v___x_3133_ = lean_nat_add(v___x_3131_, v_size_3089_);
lean_dec(v___x_3131_);
lean_inc_ref(v_impl_3070_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 4, v_l_3076_);
lean_ctor_set(v___x_3087_, 3, v_impl_3070_);
lean_ctor_set(v___x_3087_, 2, v_v_2587_);
lean_ctor_set(v___x_3087_, 1, v_k_2586_);
lean_ctor_set(v___x_3087_, 0, v___x_3133_);
v___x_3135_ = v___x_3087_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_impl_3070_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_l_3076_);
v___x_3135_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_isSharedCheck_3142_ = !lean_is_exclusive(v_impl_3070_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; lean_object* v_unused_3147_; 
v_unused_3143_ = lean_ctor_get(v_impl_3070_, 4);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_impl_3070_, 3);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_impl_3070_, 2);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v_impl_3070_, 1);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_impl_3070_, 0);
lean_dec(v_unused_3147_);
v___x_3137_ = v_impl_3070_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_dec(v_impl_3070_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 4, v_r_3077_);
lean_ctor_set(v___x_3137_, 3, v___x_3135_);
lean_ctor_set(v___x_3137_, 2, v_v_3075_);
lean_ctor_set(v___x_3137_, 1, v_k_3074_);
lean_ctor_set(v___x_3137_, 0, v___x_3132_);
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_k_3074_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_v_3075_);
lean_ctor_set(v_reuseFailAlloc_3141_, 3, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3141_, 4, v_r_3077_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
v_size_3155_ = lean_ctor_get(v_impl_3070_, 0);
lean_inc(v_size_3155_);
v___x_3156_ = lean_nat_add(v___x_3071_, v_size_3155_);
lean_dec(v_size_3155_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 3, v_impl_3070_);
lean_ctor_set(v___x_2591_, 0, v___x_3156_);
v___x_3158_ = v___x_2591_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_impl_3070_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_r_2589_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
if (lean_obj_tag(v_r_2589_) == 0)
{
lean_object* v_l_3160_; 
v_l_3160_ = lean_ctor_get(v_r_2589_, 3);
lean_inc(v_l_3160_);
if (lean_obj_tag(v_l_3160_) == 0)
{
lean_object* v_r_3161_; 
v_r_3161_ = lean_ctor_get(v_r_2589_, 4);
lean_inc(v_r_3161_);
if (lean_obj_tag(v_r_3161_) == 0)
{
lean_object* v_size_3162_; lean_object* v_k_3163_; lean_object* v_v_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3177_; 
v_size_3162_ = lean_ctor_get(v_r_2589_, 0);
v_k_3163_ = lean_ctor_get(v_r_2589_, 1);
v_v_3164_ = lean_ctor_get(v_r_2589_, 2);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; lean_object* v_unused_3179_; 
v_unused_3178_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_3179_);
v___x_3166_ = v_r_2589_;
v_isShared_3167_ = v_isSharedCheck_3177_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_v_3164_);
lean_inc(v_k_3163_);
lean_inc(v_size_3162_);
lean_dec(v_r_2589_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3177_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v_size_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v_size_3168_ = lean_ctor_get(v_l_3160_, 0);
v___x_3169_ = lean_nat_add(v___x_3071_, v_size_3162_);
lean_dec(v_size_3162_);
v___x_3170_ = lean_nat_add(v___x_3071_, v_size_3168_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_l_3160_);
lean_ctor_set(v___x_3166_, 3, v_impl_3070_);
lean_ctor_set(v___x_3166_, 2, v_v_2587_);
lean_ctor_set(v___x_3166_, 1, v_k_2586_);
lean_ctor_set(v___x_3166_, 0, v___x_3170_);
v___x_3172_ = v___x_3166_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3176_, 3, v_impl_3070_);
lean_ctor_set(v_reuseFailAlloc_3176_, 4, v_l_3160_);
v___x_3172_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3174_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_r_3161_);
lean_ctor_set(v___x_2591_, 3, v___x_3172_);
lean_ctor_set(v___x_2591_, 2, v_v_3164_);
lean_ctor_set(v___x_2591_, 1, v_k_3163_);
lean_ctor_set(v___x_2591_, 0, v___x_3169_);
v___x_3174_ = v___x_2591_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_k_3163_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_v_3164_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_r_3161_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_k_3180_; lean_object* v_v_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3204_; 
v_k_3180_ = lean_ctor_get(v_r_2589_, 1);
v_v_3181_ = lean_ctor_get(v_r_2589_, 2);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; lean_object* v_unused_3207_; 
v_unused_3205_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_r_2589_, 0);
lean_dec(v_unused_3207_);
v___x_3183_ = v_r_2589_;
v_isShared_3184_ = v_isSharedCheck_3204_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_v_3181_);
lean_inc(v_k_3180_);
lean_dec(v_r_2589_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3204_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_k_3185_; lean_object* v_v_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3200_; 
v_k_3185_ = lean_ctor_get(v_l_3160_, 1);
v_v_3186_ = lean_ctor_get(v_l_3160_, 2);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_l_3160_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; lean_object* v_unused_3202_; lean_object* v_unused_3203_; 
v_unused_3201_ = lean_ctor_get(v_l_3160_, 4);
lean_dec(v_unused_3201_);
v_unused_3202_ = lean_ctor_get(v_l_3160_, 3);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_l_3160_, 0);
lean_dec(v_unused_3203_);
v___x_3188_ = v_l_3160_;
v_isShared_3189_ = v_isSharedCheck_3200_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_v_3186_);
lean_inc(v_k_3185_);
lean_dec(v_l_3160_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3200_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_unsigned_to_nat(3u);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 4, v_r_3161_);
lean_ctor_set(v___x_3188_, 3, v_r_3161_);
lean_ctor_set(v___x_3188_, 2, v_v_2587_);
lean_ctor_set(v___x_3188_, 1, v_k_2586_);
lean_ctor_set(v___x_3188_, 0, v___x_3071_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_r_3161_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_r_3161_);
v___x_3192_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3194_; 
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 3, v_r_3161_);
lean_ctor_set(v___x_3183_, 0, v___x_3071_);
v___x_3194_ = v___x_3183_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_3180_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_3181_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_r_3161_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_r_3161_);
v___x_3194_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_3194_);
lean_ctor_set(v___x_2591_, 3, v___x_3192_);
lean_ctor_set(v___x_2591_, 2, v_v_3186_);
lean_ctor_set(v___x_2591_, 1, v_k_3185_);
lean_ctor_set(v___x_2591_, 0, v___x_3190_);
v___x_3196_ = v___x_2591_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_k_3185_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_v_3186_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3197_, 4, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3208_; 
v_r_3208_ = lean_ctor_get(v_r_2589_, 4);
lean_inc(v_r_3208_);
if (lean_obj_tag(v_r_3208_) == 0)
{
lean_object* v_k_3209_; lean_object* v_v_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3221_; 
v_k_3209_ = lean_ctor_get(v_r_2589_, 1);
v_v_3210_ = lean_ctor_get(v_r_2589_, 2);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; lean_object* v_unused_3223_; lean_object* v_unused_3224_; 
v_unused_3222_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_3222_);
v_unused_3223_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_r_2589_, 0);
lean_dec(v_unused_3224_);
v___x_3212_ = v_r_2589_;
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_v_3210_);
lean_inc(v_k_3209_);
lean_dec(v_r_2589_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3214_ = lean_unsigned_to_nat(3u);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 4, v_l_3160_);
lean_ctor_set(v___x_3212_, 2, v_v_2587_);
lean_ctor_set(v___x_3212_, 1, v_k_2586_);
lean_ctor_set(v___x_3212_, 0, v___x_3071_);
v___x_3216_ = v___x_3212_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_l_3160_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_l_3160_);
v___x_3216_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3218_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v_r_3208_);
lean_ctor_set(v___x_2591_, 3, v___x_3216_);
lean_ctor_set(v___x_2591_, 2, v_v_3210_);
lean_ctor_set(v___x_2591_, 1, v_k_3209_);
lean_ctor_set(v___x_2591_, 0, v___x_3214_);
v___x_3218_ = v___x_2591_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_k_3209_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_v_3210_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v___x_3216_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v_r_3208_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_size_3225_; lean_object* v_k_3226_; lean_object* v_v_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3238_; 
v_size_3225_ = lean_ctor_get(v_r_2589_, 0);
v_k_3226_ = lean_ctor_get(v_r_2589_, 1);
v_v_3227_ = lean_ctor_get(v_r_2589_, 2);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_r_2589_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; lean_object* v_unused_3240_; 
v_unused_3239_ = lean_ctor_get(v_r_2589_, 4);
lean_dec(v_unused_3239_);
v_unused_3240_ = lean_ctor_get(v_r_2589_, 3);
lean_dec(v_unused_3240_);
v___x_3229_ = v_r_2589_;
v_isShared_3230_ = v_isSharedCheck_3238_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_v_3227_);
lean_inc(v_k_3226_);
lean_inc(v_size_3225_);
lean_dec(v_r_2589_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3238_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 3, v_r_3208_);
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_size_3225_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_k_3226_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_v_3227_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_r_3208_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v_r_3208_);
v___x_3232_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = lean_unsigned_to_nat(2u);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_3232_);
lean_ctor_set(v___x_2591_, 3, v_r_3208_);
lean_ctor_set(v___x_2591_, 0, v___x_3233_);
v___x_3235_ = v___x_2591_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_r_3208_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v___x_3232_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
else
{
lean_object* v___x_3242_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 3, v_r_2589_);
lean_ctor_set(v___x_2591_, 0, v___x_3071_);
v___x_3242_ = v___x_2591_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_r_2589_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v_r_2589_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
}
else
{
return v_t_2585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3246_, lean_object* v_t_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3246_, v_t_3247_);
lean_dec(v_k_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3249_, lean_object* v_j_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3250_, v_ctx_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3252_, lean_object* v_j_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3252_, v_j_3253_);
lean_dec(v_j_3253_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3255_, lean_object* v_k_3256_, lean_object* v_t_3257_, lean_object* v_h_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3256_, v_t_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_k_3261_, lean_object* v_t_3262_, lean_object* v_h_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3260_, v_k_3261_, v_t_3262_, v_h_3263_);
lean_dec(v_k_3261_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3265_, lean_object* v_x_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_3265_, v_x_3266_);
if (lean_obj_tag(v___x_3267_) == 1)
{
lean_object* v_val_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3281_; 
v_val_3268_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3270_ = v___x_3267_;
v_isShared_3271_ = v_isSharedCheck_3281_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_val_3268_);
lean_dec(v___x_3267_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3281_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
switch(lean_obj_tag(v_val_3268_))
{
case 0:
{
lean_object* v_a_3272_; lean_object* v___x_3274_; 
v_a_3272_ = lean_ctor_get(v_val_3268_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v_val_3268_, 1);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v_a_3272_);
v___x_3274_ = v___x_3270_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
case 1:
{
lean_object* v_a_3276_; lean_object* v___x_3278_; 
v_a_3276_ = lean_ctor_get(v_val_3268_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v_val_3268_, 2);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v_a_3276_);
v___x_3278_ = v___x_3270_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
default: 
{
lean_object* v___x_3280_; 
lean_del_object(v___x_3270_);
lean_dec(v_val_3268_);
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
}
}
}
else
{
lean_object* v___x_3282_; 
lean_dec(v___x_3267_);
v___x_3282_ = lean_box(0);
return v___x_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_IR_LocalContext_getType(v_ctx_3283_, v_x_3284_);
lean_dec(v_x_3284_);
lean_dec(v_ctx_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_3286_, v_x_3287_);
if (lean_obj_tag(v___x_3288_) == 1)
{
lean_object* v_val_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3298_; 
v_val_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_val_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3298_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
if (lean_obj_tag(v_val_3289_) == 1)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; 
v_a_3293_ = lean_ctor_get(v_val_3289_, 1);
lean_inc_ref(v_a_3293_);
lean_dec_ref_known(v_val_3289_, 2);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v_a_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
else
{
lean_object* v___x_3297_; 
lean_del_object(v___x_3291_);
lean_dec(v_val_3289_);
v___x_3297_ = lean_box(0);
return v___x_3297_;
}
}
}
else
{
lean_object* v___x_3299_; 
lean_dec(v___x_3288_);
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_IR_LocalContext_getValue(v_ctx_3300_, v_x_3301_);
lean_dec(v_x_3301_);
lean_dec(v_ctx_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3303_, lean_object* v_v_u2081_3304_, lean_object* v_v_u2082_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_00_u03c1_3303_, v_v_u2081_3304_);
if (lean_obj_tag(v___x_3306_) == 0)
{
uint8_t v___x_3307_; 
v___x_3307_ = lean_nat_dec_eq(v_v_u2081_3304_, v_v_u2082_3305_);
return v___x_3307_;
}
else
{
lean_object* v_val_3308_; uint8_t v___x_3309_; 
v_val_3308_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3308_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3309_ = lean_nat_dec_eq(v_val_3308_, v_v_u2082_3305_);
lean_dec(v_val_3308_);
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3310_, lean_object* v_v_u2081_3311_, lean_object* v_v_u2082_3312_){
_start:
{
uint8_t v_res_3313_; lean_object* v_r_3314_; 
v_res_3313_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3310_, v_v_u2081_3311_, v_v_u2082_3312_);
lean_dec(v_v_u2082_3312_);
lean_dec(v_v_u2081_3311_);
lean_dec(v_00_u03c1_3310_);
v_r_3314_ = lean_box(v_res_3313_);
return v_r_3314_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_){
_start:
{
if (lean_obj_tag(v_x_3318_) == 0)
{
if (lean_obj_tag(v_x_3319_) == 0)
{
lean_object* v_id_3320_; lean_object* v_id_3321_; uint8_t v___x_3322_; 
v_id_3320_ = lean_ctor_get(v_x_3318_, 0);
v_id_3321_ = lean_ctor_get(v_x_3319_, 0);
v___x_3322_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3317_, v_id_3320_, v_id_3321_);
return v___x_3322_;
}
else
{
uint8_t v___x_3323_; 
v___x_3323_ = 0;
return v___x_3323_;
}
}
else
{
if (lean_obj_tag(v_x_3319_) == 1)
{
uint8_t v___x_3324_; 
v___x_3324_ = 1;
return v___x_3324_;
}
else
{
uint8_t v___x_3325_; 
v___x_3325_ = 0;
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3326_, v_x_3327_, v_x_3328_);
lean_dec(v_x_3328_);
lean_dec(v_x_3327_);
lean_dec(v_00_u03c1_3326_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3333_, lean_object* v_xs_3334_, lean_object* v_ys_3335_, lean_object* v_x_3336_){
_start:
{
lean_object* v_zero_3337_; uint8_t v_isZero_3338_; 
v_zero_3337_ = lean_unsigned_to_nat(0u);
v_isZero_3338_ = lean_nat_dec_eq(v_x_3336_, v_zero_3337_);
if (v_isZero_3338_ == 1)
{
lean_dec(v_x_3336_);
return v_isZero_3338_;
}
else
{
lean_object* v_one_3339_; lean_object* v_n_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v_one_3339_ = lean_unsigned_to_nat(1u);
v_n_3340_ = lean_nat_sub(v_x_3336_, v_one_3339_);
lean_dec(v_x_3336_);
v___x_3341_ = lean_array_fget_borrowed(v_xs_3334_, v_n_3340_);
v___x_3342_ = lean_array_fget_borrowed(v_ys_3335_, v_n_3340_);
v___x_3343_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3333_, v___x_3341_, v___x_3342_);
if (v___x_3343_ == 0)
{
lean_dec(v_n_3340_);
return v___x_3343_;
}
else
{
v_x_3336_ = v_n_3340_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3345_, lean_object* v_xs_3346_, lean_object* v_ys_3347_, lean_object* v_x_3348_){
_start:
{
uint8_t v_res_3349_; lean_object* v_r_3350_; 
v_res_3349_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3345_, v_xs_3346_, v_ys_3347_, v_x_3348_);
lean_dec_ref(v_ys_3347_);
lean_dec_ref(v_xs_3346_);
lean_dec(v_00_u03c1_3345_);
v_r_3350_ = lean_box(v_res_3349_);
return v_r_3350_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3351_, lean_object* v_args_u2081_3352_, lean_object* v_args_u2082_3353_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3354_ = lean_array_get_size(v_args_u2081_3352_);
v___x_3355_ = lean_array_get_size(v_args_u2082_3353_);
v___x_3356_ = lean_nat_dec_eq(v___x_3354_, v___x_3355_);
if (v___x_3356_ == 0)
{
return v___x_3356_;
}
else
{
uint8_t v___x_3357_; 
v___x_3357_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3351_, v_args_u2081_3352_, v_args_u2082_3353_, v___x_3354_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3358_, lean_object* v_args_u2081_3359_, lean_object* v_args_u2082_3360_){
_start:
{
uint8_t v_res_3361_; lean_object* v_r_3362_; 
v_res_3361_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3358_, v_args_u2081_3359_, v_args_u2082_3360_);
lean_dec_ref(v_args_u2082_3360_);
lean_dec_ref(v_args_u2081_3359_);
lean_dec(v_00_u03c1_3358_);
v_r_3362_ = lean_box(v_res_3361_);
return v_r_3362_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3363_, lean_object* v_xs_3364_, lean_object* v_ys_3365_, lean_object* v_hsz_3366_, lean_object* v_x_3367_, lean_object* v_x_3368_){
_start:
{
uint8_t v___x_3369_; 
v___x_3369_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3363_, v_xs_3364_, v_ys_3365_, v_x_3367_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3370_, lean_object* v_xs_3371_, lean_object* v_ys_3372_, lean_object* v_hsz_3373_, lean_object* v_x_3374_, lean_object* v_x_3375_){
_start:
{
uint8_t v_res_3376_; lean_object* v_r_3377_; 
v_res_3376_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3370_, v_xs_3371_, v_ys_3372_, v_hsz_3373_, v_x_3374_, v_x_3375_);
lean_dec_ref(v_ys_3372_);
lean_dec_ref(v_xs_3371_);
lean_dec(v_00_u03c1_3370_);
v_r_3377_ = lean_box(v_res_3376_);
return v_r_3377_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* v_00_u03c1_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_){
_start:
{
lean_object* v_n_u2081_3384_; lean_object* v_x_u2081_3385_; lean_object* v_n_u2082_3386_; lean_object* v_x_u2082_3387_; lean_object* v_c_u2081_3391_; lean_object* v_ys_u2081_3392_; lean_object* v_c_u2082_3393_; lean_object* v_ys_u2082_3394_; 
switch(lean_obj_tag(v_x_3381_))
{
case 0:
{
if (lean_obj_tag(v_x_3382_) == 0)
{
lean_object* v_i_3397_; lean_object* v_ys_3398_; lean_object* v_i_3399_; lean_object* v_ys_3400_; uint8_t v___x_3401_; 
v_i_3397_ = lean_ctor_get(v_x_3381_, 0);
v_ys_3398_ = lean_ctor_get(v_x_3381_, 1);
v_i_3399_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3400_ = lean_ctor_get(v_x_3382_, 1);
v___x_3401_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3397_, v_i_3399_);
if (v___x_3401_ == 0)
{
return v___x_3401_;
}
else
{
uint8_t v___x_3402_; 
v___x_3402_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3380_, v_ys_3398_, v_ys_3400_);
return v___x_3402_;
}
}
else
{
uint8_t v___x_3403_; 
v___x_3403_ = 0;
return v___x_3403_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3382_) == 1)
{
lean_object* v_n_3404_; lean_object* v_x_3405_; lean_object* v_n_3406_; lean_object* v_x_3407_; 
v_n_3404_ = lean_ctor_get(v_x_3381_, 0);
v_x_3405_ = lean_ctor_get(v_x_3381_, 1);
v_n_3406_ = lean_ctor_get(v_x_3382_, 0);
v_x_3407_ = lean_ctor_get(v_x_3382_, 1);
v_n_u2081_3384_ = v_n_3404_;
v_x_u2081_3385_ = v_x_3405_;
v_n_u2082_3386_ = v_n_3406_;
v_x_u2082_3387_ = v_x_3407_;
goto v___jp_3383_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = 0;
return v___x_3408_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3382_) == 2)
{
lean_object* v_x_3409_; lean_object* v_i_3410_; uint8_t v_updtHeader_3411_; lean_object* v_ys_3412_; lean_object* v_x_3413_; lean_object* v_i_3414_; uint8_t v_updtHeader_3415_; lean_object* v_ys_3416_; uint8_t v___y_3418_; uint8_t v___x_3421_; 
v_x_3409_ = lean_ctor_get(v_x_3381_, 0);
v_i_3410_ = lean_ctor_get(v_x_3381_, 1);
v_updtHeader_3411_ = lean_ctor_get_uint8(v_x_3381_, sizeof(void*)*3);
v_ys_3412_ = lean_ctor_get(v_x_3381_, 2);
v_x_3413_ = lean_ctor_get(v_x_3382_, 0);
v_i_3414_ = lean_ctor_get(v_x_3382_, 1);
v_updtHeader_3415_ = lean_ctor_get_uint8(v_x_3382_, sizeof(void*)*3);
v_ys_3416_ = lean_ctor_get(v_x_3382_, 2);
v___x_3421_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_3409_, v_x_3413_);
if (v___x_3421_ == 0)
{
v___y_3418_ = v___x_3421_;
goto v___jp_3417_;
}
else
{
uint8_t v___x_3422_; 
v___x_3422_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3410_, v_i_3414_);
v___y_3418_ = v___x_3422_;
goto v___jp_3417_;
}
v___jp_3417_:
{
if (v___y_3418_ == 0)
{
return v___y_3418_;
}
else
{
if (v_updtHeader_3411_ == 0)
{
if (v_updtHeader_3415_ == 0)
{
uint8_t v___x_3419_; 
v___x_3419_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3380_, v_ys_3412_, v_ys_3416_);
return v___x_3419_;
}
else
{
return v_updtHeader_3411_;
}
}
else
{
if (v_updtHeader_3415_ == 0)
{
return v_updtHeader_3415_;
}
else
{
uint8_t v___x_3420_; 
v___x_3420_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3380_, v_ys_3412_, v_ys_3416_);
return v___x_3420_;
}
}
}
}
}
else
{
uint8_t v___x_3423_; 
v___x_3423_ = 0;
return v___x_3423_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3382_) == 3)
{
lean_object* v_i_3424_; lean_object* v_x_3425_; lean_object* v_i_3426_; lean_object* v_x_3427_; 
v_i_3424_ = lean_ctor_get(v_x_3381_, 0);
v_x_3425_ = lean_ctor_get(v_x_3381_, 1);
v_i_3426_ = lean_ctor_get(v_x_3382_, 0);
v_x_3427_ = lean_ctor_get(v_x_3382_, 1);
v_n_u2081_3384_ = v_i_3424_;
v_x_u2081_3385_ = v_x_3425_;
v_n_u2082_3386_ = v_i_3426_;
v_x_u2082_3387_ = v_x_3427_;
goto v___jp_3383_;
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = 0;
return v___x_3428_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3382_) == 4)
{
lean_object* v_i_3429_; lean_object* v_x_3430_; lean_object* v_i_3431_; lean_object* v_x_3432_; 
v_i_3429_ = lean_ctor_get(v_x_3381_, 0);
v_x_3430_ = lean_ctor_get(v_x_3381_, 1);
v_i_3431_ = lean_ctor_get(v_x_3382_, 0);
v_x_3432_ = lean_ctor_get(v_x_3382_, 1);
v_n_u2081_3384_ = v_i_3429_;
v_x_u2081_3385_ = v_x_3430_;
v_n_u2082_3386_ = v_i_3431_;
v_x_u2082_3387_ = v_x_3432_;
goto v___jp_3383_;
}
else
{
uint8_t v___x_3433_; 
v___x_3433_ = 0;
return v___x_3433_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3382_) == 5)
{
lean_object* v_n_3434_; lean_object* v_offset_3435_; lean_object* v_x_3436_; lean_object* v_n_3437_; lean_object* v_offset_3438_; lean_object* v_x_3439_; uint8_t v___y_3441_; uint8_t v___x_3443_; 
v_n_3434_ = lean_ctor_get(v_x_3381_, 0);
v_offset_3435_ = lean_ctor_get(v_x_3381_, 1);
v_x_3436_ = lean_ctor_get(v_x_3381_, 2);
v_n_3437_ = lean_ctor_get(v_x_3382_, 0);
v_offset_3438_ = lean_ctor_get(v_x_3382_, 1);
v_x_3439_ = lean_ctor_get(v_x_3382_, 2);
v___x_3443_ = lean_nat_dec_eq(v_n_3434_, v_n_3437_);
if (v___x_3443_ == 0)
{
v___y_3441_ = v___x_3443_;
goto v___jp_3440_;
}
else
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_nat_dec_eq(v_offset_3435_, v_offset_3438_);
v___y_3441_ = v___x_3444_;
goto v___jp_3440_;
}
v___jp_3440_:
{
if (v___y_3441_ == 0)
{
return v___y_3441_;
}
else
{
uint8_t v___x_3442_; 
v___x_3442_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_3436_, v_x_3439_);
return v___x_3442_;
}
}
}
else
{
uint8_t v___x_3445_; 
v___x_3445_ = 0;
return v___x_3445_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3382_) == 6)
{
lean_object* v_c_3446_; lean_object* v_ys_3447_; lean_object* v_c_3448_; lean_object* v_ys_3449_; 
v_c_3446_ = lean_ctor_get(v_x_3381_, 0);
v_ys_3447_ = lean_ctor_get(v_x_3381_, 1);
v_c_3448_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3449_ = lean_ctor_get(v_x_3382_, 1);
v_c_u2081_3391_ = v_c_3446_;
v_ys_u2081_3392_ = v_ys_3447_;
v_c_u2082_3393_ = v_c_3448_;
v_ys_u2082_3394_ = v_ys_3449_;
goto v___jp_3390_;
}
else
{
uint8_t v___x_3450_; 
v___x_3450_ = 0;
return v___x_3450_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3382_) == 7)
{
lean_object* v_c_3451_; lean_object* v_ys_3452_; lean_object* v_c_3453_; lean_object* v_ys_3454_; 
v_c_3451_ = lean_ctor_get(v_x_3381_, 0);
v_ys_3452_ = lean_ctor_get(v_x_3381_, 1);
v_c_3453_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3454_ = lean_ctor_get(v_x_3382_, 1);
v_c_u2081_3391_ = v_c_3451_;
v_ys_u2081_3392_ = v_ys_3452_;
v_c_u2082_3393_ = v_c_3453_;
v_ys_u2082_3394_ = v_ys_3454_;
goto v___jp_3390_;
}
else
{
uint8_t v___x_3455_; 
v___x_3455_ = 0;
return v___x_3455_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3382_) == 8)
{
lean_object* v_x_3456_; lean_object* v_ys_3457_; lean_object* v_x_3458_; lean_object* v_ys_3459_; uint8_t v___x_3460_; 
v_x_3456_ = lean_ctor_get(v_x_3381_, 0);
v_ys_3457_ = lean_ctor_get(v_x_3381_, 1);
v_x_3458_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3459_ = lean_ctor_get(v_x_3382_, 1);
v___x_3460_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_3456_, v_x_3458_);
if (v___x_3460_ == 0)
{
return v___x_3460_;
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3380_, v_ys_3457_, v_ys_3459_);
return v___x_3461_;
}
}
else
{
uint8_t v___x_3462_; 
v___x_3462_ = 0;
return v___x_3462_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3382_) == 9)
{
lean_object* v_ty_3463_; lean_object* v_x_3464_; lean_object* v_ty_3465_; lean_object* v_x_3466_; uint8_t v___x_3467_; 
v_ty_3463_ = lean_ctor_get(v_x_3381_, 0);
v_x_3464_ = lean_ctor_get(v_x_3381_, 1);
v_ty_3465_ = lean_ctor_get(v_x_3382_, 0);
v_x_3466_ = lean_ctor_get(v_x_3382_, 1);
v___x_3467_ = l_Lean_IR_instBEqIRType_beq(v_ty_3463_, v_ty_3465_);
if (v___x_3467_ == 0)
{
return v___x_3467_;
}
else
{
uint8_t v___x_3468_; 
v___x_3468_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_3464_, v_x_3466_);
return v___x_3468_;
}
}
else
{
uint8_t v___x_3469_; 
v___x_3469_ = 0;
return v___x_3469_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3382_) == 10)
{
lean_object* v_x_3470_; lean_object* v_x_3471_; uint8_t v___x_3472_; 
v_x_3470_ = lean_ctor_get(v_x_3381_, 0);
v_x_3471_ = lean_ctor_get(v_x_3382_, 0);
v___x_3472_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_3470_, v_x_3471_);
return v___x_3472_;
}
else
{
uint8_t v___x_3473_; 
v___x_3473_ = 0;
return v___x_3473_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3382_) == 11)
{
lean_object* v_v_3474_; lean_object* v_v_3475_; uint8_t v___x_3476_; 
v_v_3474_ = lean_ctor_get(v_x_3381_, 0);
v_v_3475_ = lean_ctor_get(v_x_3382_, 0);
v___x_3476_ = l_Lean_IR_instBEqLitVal_beq(v_v_3474_, v_v_3475_);
return v___x_3476_;
}
else
{
uint8_t v___x_3477_; 
v___x_3477_ = 0;
return v___x_3477_;
}
}
default: 
{
if (lean_obj_tag(v_x_3382_) == 12)
{
lean_object* v_x_3478_; lean_object* v_x_3479_; uint8_t v___x_3480_; 
v_x_3478_ = lean_ctor_get(v_x_3381_, 0);
v_x_3479_ = lean_ctor_get(v_x_3382_, 0);
v___x_3480_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_3478_, v_x_3479_);
return v___x_3480_;
}
else
{
uint8_t v___x_3481_; 
v___x_3481_ = 0;
return v___x_3481_;
}
}
}
v___jp_3383_:
{
uint8_t v___x_3388_; 
v___x_3388_ = lean_nat_dec_eq(v_n_u2081_3384_, v_n_u2082_3386_);
if (v___x_3388_ == 0)
{
return v___x_3388_;
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3380_, v_x_u2081_3385_, v_x_u2082_3387_);
return v___x_3389_;
}
}
v___jp_3390_:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_name_eq(v_c_u2081_3391_, v_c_u2082_3393_);
if (v___x_3395_ == 0)
{
return v___x_3395_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3380_, v_ys_u2081_3392_, v_ys_u2082_3394_);
return v___x_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* v_00_u03c1_3482_, lean_object* v_x_3483_, lean_object* v_x_3484_){
_start:
{
uint8_t v_res_3485_; lean_object* v_r_3486_; 
v_res_3485_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_3482_, v_x_3483_, v_x_3484_);
lean_dec_ref(v_x_3484_);
lean_dec_ref(v_x_3483_);
lean_dec(v_00_u03c1_3482_);
v_r_3486_ = lean_box(v_res_3485_);
return v_r_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3489_, lean_object* v_x_u2081_3490_, lean_object* v_x_u2082_3491_){
_start:
{
uint8_t v___x_3492_; 
v___x_3492_ = lean_nat_dec_eq(v_x_u2081_3490_, v_x_u2082_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3490_, v_x_u2082_3491_, v_00_u03c1_3489_);
return v___x_3493_;
}
else
{
lean_dec(v_x_u2082_3491_);
lean_dec(v_x_u2081_3490_);
return v_00_u03c1_3489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3494_, lean_object* v_p_u2081_3495_, lean_object* v_p_u2082_3496_){
_start:
{
lean_object* v_x_3497_; uint8_t v_borrow_3498_; lean_object* v_ty_3499_; lean_object* v_x_3500_; uint8_t v_borrow_3501_; lean_object* v_ty_3502_; uint8_t v___y_3504_; uint8_t v___x_3508_; 
v_x_3497_ = lean_ctor_get(v_p_u2081_3495_, 0);
lean_inc(v_x_3497_);
v_borrow_3498_ = lean_ctor_get_uint8(v_p_u2081_3495_, sizeof(void*)*2);
v_ty_3499_ = lean_ctor_get(v_p_u2081_3495_, 1);
lean_inc(v_ty_3499_);
lean_dec_ref(v_p_u2081_3495_);
v_x_3500_ = lean_ctor_get(v_p_u2082_3496_, 0);
lean_inc(v_x_3500_);
v_borrow_3501_ = lean_ctor_get_uint8(v_p_u2082_3496_, sizeof(void*)*2);
v_ty_3502_ = lean_ctor_get(v_p_u2082_3496_, 1);
lean_inc(v_ty_3502_);
lean_dec_ref(v_p_u2082_3496_);
v___x_3508_ = l_Lean_IR_instBEqIRType_beq(v_ty_3499_, v_ty_3502_);
lean_dec(v_ty_3502_);
lean_dec(v_ty_3499_);
if (v___x_3508_ == 0)
{
v___y_3504_ = v___x_3508_;
goto v___jp_3503_;
}
else
{
if (v_borrow_3498_ == 0)
{
if (v_borrow_3501_ == 0)
{
v___y_3504_ = v___x_3508_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3509_; 
lean_dec(v_x_3500_);
lean_dec(v_x_3497_);
lean_dec(v_00_u03c1_3494_);
v___x_3509_ = lean_box(0);
return v___x_3509_;
}
}
else
{
v___y_3504_ = v_borrow_3501_;
goto v___jp_3503_;
}
}
v___jp_3503_:
{
if (v___y_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v_x_3500_);
lean_dec(v_x_3497_);
lean_dec(v_00_u03c1_3494_);
v___x_3505_ = lean_box(0);
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = l_Lean_IR_addVarRename(v_00_u03c1_3494_, v_x_3497_, v_x_3500_);
v___x_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
return v___x_3507_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3510_, lean_object* v_ps_u2081_3511_, lean_object* v_ps_u2082_3512_, lean_object* v_a_3513_, lean_object* v_b_3514_){
_start:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_nat_dec_lt(v_a_3513_, v_upperBound_3510_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v_a_3513_);
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_b_3514_);
return v___x_3516_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3517_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_3518_ = lean_array_get_borrowed(v___x_3517_, v_ps_u2081_3511_, v_a_3513_);
v___x_3519_ = lean_array_get_borrowed(v___x_3517_, v_ps_u2082_3512_, v_a_3513_);
lean_inc(v___x_3519_);
lean_inc(v___x_3518_);
v___x_3520_ = l_Lean_IR_addParamRename(v_b_3514_, v___x_3518_, v___x_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_dec(v_a_3513_);
return v___x_3520_;
}
else
{
lean_object* v_val_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_val_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = lean_nat_add(v_a_3513_, v___x_3522_);
lean_dec(v_a_3513_);
v_a_3513_ = v___x_3523_;
v_b_3514_ = v_val_3521_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_3525_, lean_object* v_ps_u2081_3526_, lean_object* v_ps_u2082_3527_, lean_object* v_a_3528_, lean_object* v_b_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3525_, v_ps_u2081_3526_, v_ps_u2082_3527_, v_a_3528_, v_b_3529_);
lean_dec_ref(v_ps_u2082_3527_);
lean_dec_ref(v_ps_u2081_3526_);
lean_dec(v_upperBound_3525_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_3531_, lean_object* v_ps_u2081_3532_, lean_object* v_ps_u2082_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; uint8_t v___x_3537_; 
v___x_3534_ = lean_array_get_size(v_ps_u2081_3532_);
v___x_3535_ = lean_array_get_size(v_ps_u2082_3533_);
v___x_3536_ = lean_nat_dec_eq(v___x_3534_, v___x_3535_);
v___x_3537_ = lean_bool_not(v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_3534_, v_ps_u2081_3532_, v_ps_u2082_3533_, v___x_3538_, v_00_u03c1_3531_);
return v___x_3539_;
}
else
{
lean_object* v___x_3540_; 
lean_dec(v_00_u03c1_3531_);
v___x_3540_ = lean_box(0);
return v___x_3540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* v_00_u03c1_3541_, lean_object* v_ps_u2081_3542_, lean_object* v_ps_u2082_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_IR_addParamsRename(v_00_u03c1_3541_, v_ps_u2081_3542_, v_ps_u2082_3543_);
lean_dec_ref(v_ps_u2082_3543_);
lean_dec_ref(v_ps_u2081_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object* v_upperBound_3545_, lean_object* v_ps_u2081_3546_, lean_object* v_ps_u2082_3547_, lean_object* v_inst_3548_, lean_object* v_R_3549_, lean_object* v_a_3550_, lean_object* v_b_3551_, lean_object* v_c_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3545_, v_ps_u2081_3546_, v_ps_u2082_3547_, v_a_3550_, v_b_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object* v_upperBound_3554_, lean_object* v_ps_u2081_3555_, lean_object* v_ps_u2082_3556_, lean_object* v_inst_3557_, lean_object* v_R_3558_, lean_object* v_a_3559_, lean_object* v_b_3560_, lean_object* v_c_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(v_upperBound_3554_, v_ps_u2081_3555_, v_ps_u2082_3556_, v_inst_3557_, v_R_3558_, v_a_3559_, v_b_3560_, v_c_3561_);
lean_dec_ref(v_ps_u2082_3556_);
lean_dec_ref(v_ps_u2081_3555_);
lean_dec(v_upperBound_3554_);
return v_res_3562_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
uint8_t v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; uint8_t v___y_3570_; lean_object* v___y_3571_; uint8_t v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; uint8_t v___y_3579_; uint8_t v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3582_; lean_object* v_00_u03c1_3584_; lean_object* v_x_u2081_3585_; lean_object* v_n_u2081_3586_; uint8_t v_c_u2081_3587_; uint8_t v_p_u2081_3588_; lean_object* v_b_u2081_3589_; lean_object* v_x_u2082_3590_; lean_object* v_n_u2082_3591_; uint8_t v_c_u2082_3592_; uint8_t v_p_u2082_3593_; lean_object* v_b_u2082_3594_; 
switch(lean_obj_tag(v_x_3564_))
{
case 0:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_object* v_x_3597_; lean_object* v_ty_3598_; lean_object* v_e_3599_; lean_object* v_b_3600_; lean_object* v_x_3601_; lean_object* v_ty_3602_; lean_object* v_e_3603_; lean_object* v_b_3604_; uint8_t v___y_3606_; uint8_t v___x_3609_; 
v_x_3597_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3597_);
v_ty_3598_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_ty_3598_);
v_e_3599_ = lean_ctor_get(v_x_3564_, 2);
lean_inc_ref(v_e_3599_);
v_b_3600_ = lean_ctor_get(v_x_3564_, 3);
lean_inc(v_b_3600_);
lean_dec_ref_known(v_x_3564_, 4);
v_x_3601_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3601_);
v_ty_3602_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_ty_3602_);
v_e_3603_ = lean_ctor_get(v_x_3565_, 2);
lean_inc_ref(v_e_3603_);
v_b_3604_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3604_);
lean_dec_ref_known(v_x_3565_, 4);
v___x_3609_ = l_Lean_IR_instBEqIRType_beq(v_ty_3598_, v_ty_3602_);
lean_dec(v_ty_3602_);
lean_dec(v_ty_3598_);
if (v___x_3609_ == 0)
{
lean_dec_ref(v_e_3603_);
lean_dec_ref(v_e_3599_);
v___y_3606_ = v___x_3609_;
goto v___jp_3605_;
}
else
{
uint8_t v___x_3610_; 
v___x_3610_ = l_Lean_IR_Expr_alphaEqv(v_x_3563_, v_e_3599_, v_e_3603_);
lean_dec_ref(v_e_3603_);
lean_dec_ref(v_e_3599_);
v___y_3606_ = v___x_3610_;
goto v___jp_3605_;
}
v___jp_3605_:
{
if (v___y_3606_ == 0)
{
lean_dec(v_b_3604_);
lean_dec(v_x_3601_);
lean_dec(v_b_3600_);
lean_dec(v_x_3597_);
lean_dec(v_x_3563_);
return v___y_3606_;
}
else
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_IR_addVarRename(v_x_3563_, v_x_3597_, v_x_3601_);
v_x_3563_ = v___x_3607_;
v_x_3564_ = v_b_3600_;
v_x_3565_ = v_b_3604_;
goto _start;
}
}
}
else
{
uint8_t v___x_3611_; 
lean_dec_ref_known(v_x_3564_, 4);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3611_ = 0;
return v___x_3611_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3565_) == 1)
{
lean_object* v_j_3612_; lean_object* v_xs_3613_; lean_object* v_v_3614_; lean_object* v_b_3615_; lean_object* v_j_3616_; lean_object* v_xs_3617_; lean_object* v_v_3618_; lean_object* v_b_3619_; lean_object* v___x_3620_; 
v_j_3612_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_j_3612_);
v_xs_3613_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_xs_3613_);
v_v_3614_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_v_3614_);
v_b_3615_ = lean_ctor_get(v_x_3564_, 3);
lean_inc(v_b_3615_);
lean_dec_ref_known(v_x_3564_, 4);
v_j_3616_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_j_3616_);
v_xs_3617_ = lean_ctor_get(v_x_3565_, 1);
lean_inc_ref(v_xs_3617_);
v_v_3618_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_v_3618_);
v_b_3619_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3619_);
lean_dec_ref_known(v_x_3565_, 4);
lean_inc(v_x_3563_);
v___x_3620_ = l_Lean_IR_addParamsRename(v_x_3563_, v_xs_3613_, v_xs_3617_);
lean_dec_ref(v_xs_3617_);
lean_dec_ref(v_xs_3613_);
if (lean_obj_tag(v___x_3620_) == 0)
{
uint8_t v___x_3621_; 
lean_dec(v_b_3619_);
lean_dec(v_v_3618_);
lean_dec(v_j_3616_);
lean_dec(v_b_3615_);
lean_dec(v_v_3614_);
lean_dec(v_j_3612_);
lean_dec(v_x_3563_);
v___x_3621_ = 0;
return v___x_3621_;
}
else
{
lean_object* v_val_3622_; uint8_t v___x_3623_; 
v_val_3622_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3623_ = l_Lean_IR_FnBody_alphaEqv(v_val_3622_, v_v_3614_, v_v_3618_);
if (v___x_3623_ == 0)
{
lean_dec(v_b_3619_);
lean_dec(v_j_3616_);
lean_dec(v_b_3615_);
lean_dec(v_j_3612_);
lean_dec(v_x_3563_);
return v___x_3623_;
}
else
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_IR_addVarRename(v_x_3563_, v_j_3612_, v_j_3616_);
v_x_3563_ = v___x_3624_;
v_x_3564_ = v_b_3615_;
v_x_3565_ = v_b_3619_;
goto _start;
}
}
}
else
{
uint8_t v___x_3626_; 
lean_dec_ref_known(v_x_3564_, 4);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3626_ = 0;
return v___x_3626_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3565_) == 2)
{
lean_object* v_x_3627_; lean_object* v_i_3628_; lean_object* v_y_3629_; lean_object* v_b_3630_; lean_object* v_x_3631_; lean_object* v_i_3632_; lean_object* v_y_3633_; lean_object* v_b_3634_; uint8_t v___y_3636_; uint8_t v___x_3639_; 
v_x_3627_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3627_);
v_i_3628_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_i_3628_);
v_y_3629_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_y_3629_);
v_b_3630_ = lean_ctor_get(v_x_3564_, 3);
lean_inc(v_b_3630_);
lean_dec_ref_known(v_x_3564_, 4);
v_x_3631_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3631_);
v_i_3632_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_i_3632_);
v_y_3633_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_y_3633_);
v_b_3634_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3634_);
lean_dec_ref_known(v_x_3565_, 4);
v___x_3639_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_x_3627_, v_x_3631_);
lean_dec(v_x_3631_);
lean_dec(v_x_3627_);
if (v___x_3639_ == 0)
{
lean_dec(v_i_3632_);
lean_dec(v_i_3628_);
v___y_3636_ = v___x_3639_;
goto v___jp_3635_;
}
else
{
uint8_t v___x_3640_; 
v___x_3640_ = lean_nat_dec_eq(v_i_3628_, v_i_3632_);
lean_dec(v_i_3632_);
lean_dec(v_i_3628_);
v___y_3636_ = v___x_3640_;
goto v___jp_3635_;
}
v___jp_3635_:
{
if (v___y_3636_ == 0)
{
lean_dec(v_b_3634_);
lean_dec(v_y_3633_);
lean_dec(v_b_3630_);
lean_dec(v_y_3629_);
lean_dec(v_x_3563_);
return v___y_3636_;
}
else
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_IR_Arg_alphaEqv(v_x_3563_, v_y_3629_, v_y_3633_);
lean_dec(v_y_3633_);
lean_dec(v_y_3629_);
if (v___x_3637_ == 0)
{
lean_dec(v_b_3634_);
lean_dec(v_b_3630_);
lean_dec(v_x_3563_);
return v___x_3637_;
}
else
{
v_x_3564_ = v_b_3630_;
v_x_3565_ = v_b_3634_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3641_; 
lean_dec_ref_known(v_x_3564_, 4);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3641_ = 0;
return v___x_3641_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3565_) == 3)
{
lean_object* v_x_3642_; lean_object* v_cidx_3643_; lean_object* v_b_3644_; lean_object* v_x_3645_; lean_object* v_cidx_3646_; lean_object* v_b_3647_; uint8_t v___y_3649_; uint8_t v___x_3651_; 
v_x_3642_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3642_);
v_cidx_3643_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_cidx_3643_);
v_b_3644_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_b_3644_);
lean_dec_ref_known(v_x_3564_, 3);
v_x_3645_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3645_);
v_cidx_3646_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_cidx_3646_);
v_b_3647_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_b_3647_);
lean_dec_ref_known(v_x_3565_, 3);
v___x_3651_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_x_3642_, v_x_3645_);
lean_dec(v_x_3645_);
lean_dec(v_x_3642_);
if (v___x_3651_ == 0)
{
lean_dec(v_cidx_3646_);
lean_dec(v_cidx_3643_);
v___y_3649_ = v___x_3651_;
goto v___jp_3648_;
}
else
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_nat_dec_eq(v_cidx_3643_, v_cidx_3646_);
lean_dec(v_cidx_3646_);
lean_dec(v_cidx_3643_);
v___y_3649_ = v___x_3652_;
goto v___jp_3648_;
}
v___jp_3648_:
{
if (v___y_3649_ == 0)
{
lean_dec(v_b_3647_);
lean_dec(v_b_3644_);
lean_dec(v_x_3563_);
return v___y_3649_;
}
else
{
v_x_3564_ = v_b_3644_;
v_x_3565_ = v_b_3647_;
goto _start;
}
}
}
else
{
uint8_t v___x_3653_; 
lean_dec_ref_known(v_x_3564_, 3);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3653_ = 0;
return v___x_3653_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3565_) == 4)
{
lean_object* v_x_3654_; lean_object* v_i_3655_; lean_object* v_y_3656_; lean_object* v_b_3657_; lean_object* v_x_3658_; lean_object* v_i_3659_; lean_object* v_y_3660_; lean_object* v_b_3661_; uint8_t v___y_3663_; uint8_t v___x_3666_; 
v_x_3654_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3654_);
v_i_3655_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_i_3655_);
v_y_3656_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_y_3656_);
v_b_3657_ = lean_ctor_get(v_x_3564_, 3);
lean_inc(v_b_3657_);
lean_dec_ref_known(v_x_3564_, 4);
v_x_3658_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3658_);
v_i_3659_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_i_3659_);
v_y_3660_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_y_3660_);
v_b_3661_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3661_);
lean_dec_ref_known(v_x_3565_, 4);
v___x_3666_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_x_3654_, v_x_3658_);
lean_dec(v_x_3658_);
lean_dec(v_x_3654_);
if (v___x_3666_ == 0)
{
lean_dec(v_i_3659_);
lean_dec(v_i_3655_);
v___y_3663_ = v___x_3666_;
goto v___jp_3662_;
}
else
{
uint8_t v___x_3667_; 
v___x_3667_ = lean_nat_dec_eq(v_i_3655_, v_i_3659_);
lean_dec(v_i_3659_);
lean_dec(v_i_3655_);
v___y_3663_ = v___x_3667_;
goto v___jp_3662_;
}
v___jp_3662_:
{
if (v___y_3663_ == 0)
{
lean_dec(v_b_3661_);
lean_dec(v_y_3660_);
lean_dec(v_b_3657_);
lean_dec(v_y_3656_);
lean_dec(v_x_3563_);
return v___y_3663_;
}
else
{
uint8_t v___x_3664_; 
v___x_3664_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_y_3656_, v_y_3660_);
lean_dec(v_y_3660_);
lean_dec(v_y_3656_);
if (v___x_3664_ == 0)
{
lean_dec(v_b_3661_);
lean_dec(v_b_3657_);
lean_dec(v_x_3563_);
return v___x_3664_;
}
else
{
v_x_3564_ = v_b_3657_;
v_x_3565_ = v_b_3661_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3668_; 
lean_dec_ref_known(v_x_3564_, 4);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3668_ = 0;
return v___x_3668_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3565_) == 5)
{
lean_object* v_x_3669_; lean_object* v_i_3670_; lean_object* v_offset_3671_; lean_object* v_y_3672_; lean_object* v_ty_3673_; lean_object* v_b_3674_; lean_object* v_x_3675_; lean_object* v_i_3676_; lean_object* v_offset_3677_; lean_object* v_y_3678_; lean_object* v_ty_3679_; lean_object* v_b_3680_; uint8_t v___x_3681_; uint8_t v___y_3683_; uint8_t v___x_3687_; 
v_x_3669_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3669_);
v_i_3670_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_i_3670_);
v_offset_3671_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_offset_3671_);
v_y_3672_ = lean_ctor_get(v_x_3564_, 3);
lean_inc(v_y_3672_);
v_ty_3673_ = lean_ctor_get(v_x_3564_, 4);
lean_inc(v_ty_3673_);
v_b_3674_ = lean_ctor_get(v_x_3564_, 5);
lean_inc(v_b_3674_);
lean_dec_ref_known(v_x_3564_, 6);
v_x_3675_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3675_);
v_i_3676_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_i_3676_);
v_offset_3677_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_offset_3677_);
v_y_3678_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_y_3678_);
v_ty_3679_ = lean_ctor_get(v_x_3565_, 4);
lean_inc(v_ty_3679_);
v_b_3680_ = lean_ctor_get(v_x_3565_, 5);
lean_inc(v_b_3680_);
lean_dec_ref_known(v_x_3565_, 6);
v___x_3681_ = lean_nat_dec_eq(v_offset_3671_, v_offset_3677_);
lean_dec(v_offset_3677_);
lean_dec(v_offset_3671_);
v___x_3687_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_x_3669_, v_x_3675_);
lean_dec(v_x_3675_);
lean_dec(v_x_3669_);
if (v___x_3687_ == 0)
{
lean_dec(v_i_3676_);
lean_dec(v_i_3670_);
v___y_3683_ = v___x_3687_;
goto v___jp_3682_;
}
else
{
uint8_t v___x_3688_; 
v___x_3688_ = lean_nat_dec_eq(v_i_3670_, v_i_3676_);
lean_dec(v_i_3676_);
lean_dec(v_i_3670_);
v___y_3683_ = v___x_3688_;
goto v___jp_3682_;
}
v___jp_3682_:
{
if (v___y_3683_ == 0)
{
lean_dec(v_b_3680_);
lean_dec(v_ty_3679_);
lean_dec(v_y_3678_);
lean_dec(v_b_3674_);
lean_dec(v_ty_3673_);
lean_dec(v_y_3672_);
lean_dec(v_x_3563_);
return v___y_3683_;
}
else
{
if (v___x_3681_ == 0)
{
lean_dec(v_b_3680_);
lean_dec(v_ty_3679_);
lean_dec(v_y_3678_);
lean_dec(v_b_3674_);
lean_dec(v_ty_3673_);
lean_dec(v_y_3672_);
lean_dec(v_x_3563_);
return v___x_3681_;
}
else
{
uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_y_3672_, v_y_3678_);
lean_dec(v_y_3678_);
lean_dec(v_y_3672_);
if (v___x_3684_ == 0)
{
lean_dec(v_b_3680_);
lean_dec(v_ty_3679_);
lean_dec(v_b_3674_);
lean_dec(v_ty_3673_);
lean_dec(v_x_3563_);
return v___x_3684_;
}
else
{
uint8_t v___x_3685_; 
v___x_3685_ = l_Lean_IR_instBEqIRType_beq(v_ty_3673_, v_ty_3679_);
lean_dec(v_ty_3679_);
lean_dec(v_ty_3673_);
if (v___x_3685_ == 0)
{
lean_dec(v_b_3680_);
lean_dec(v_b_3674_);
lean_dec(v_x_3563_);
return v___x_3685_;
}
else
{
v_x_3564_ = v_b_3674_;
v_x_3565_ = v_b_3680_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_3689_; 
lean_dec_ref_known(v_x_3564_, 6);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3689_ = 0;
return v___x_3689_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3565_) == 6)
{
lean_object* v_x_3690_; lean_object* v_n_3691_; uint8_t v_c_3692_; uint8_t v_persistent_3693_; lean_object* v_b_3694_; lean_object* v_x_3695_; lean_object* v_n_3696_; uint8_t v_c_3697_; uint8_t v_persistent_3698_; lean_object* v_b_3699_; 
v_x_3690_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3690_);
v_n_3691_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_n_3691_);
v_c_3692_ = lean_ctor_get_uint8(v_x_3564_, sizeof(void*)*3);
v_persistent_3693_ = lean_ctor_get_uint8(v_x_3564_, sizeof(void*)*3 + 1);
v_b_3694_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_b_3694_);
lean_dec_ref_known(v_x_3564_, 3);
v_x_3695_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3695_);
v_n_3696_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_n_3696_);
v_c_3697_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3);
v_persistent_3698_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3 + 1);
v_b_3699_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_b_3699_);
lean_dec_ref_known(v_x_3565_, 3);
v_00_u03c1_3584_ = v_x_3563_;
v_x_u2081_3585_ = v_x_3690_;
v_n_u2081_3586_ = v_n_3691_;
v_c_u2081_3587_ = v_c_3692_;
v_p_u2081_3588_ = v_persistent_3693_;
v_b_u2081_3589_ = v_b_3694_;
v_x_u2082_3590_ = v_x_3695_;
v_n_u2082_3591_ = v_n_3696_;
v_c_u2082_3592_ = v_c_3697_;
v_p_u2082_3593_ = v_persistent_3698_;
v_b_u2082_3594_ = v_b_3699_;
goto v___jp_3583_;
}
else
{
uint8_t v___x_3700_; 
lean_dec_ref_known(v_x_3564_, 3);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3700_ = 0;
return v___x_3700_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3565_) == 7)
{
lean_object* v_x_3701_; lean_object* v_n_3702_; uint8_t v_c_3703_; uint8_t v_persistent_3704_; lean_object* v_b_3705_; lean_object* v_x_3706_; lean_object* v_n_3707_; uint8_t v_c_3708_; uint8_t v_persistent_3709_; lean_object* v_b_3710_; 
v_x_3701_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3701_);
v_n_3702_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_n_3702_);
v_c_3703_ = lean_ctor_get_uint8(v_x_3564_, sizeof(void*)*3);
v_persistent_3704_ = lean_ctor_get_uint8(v_x_3564_, sizeof(void*)*3 + 1);
v_b_3705_ = lean_ctor_get(v_x_3564_, 2);
lean_inc(v_b_3705_);
lean_dec_ref_known(v_x_3564_, 3);
v_x_3706_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3706_);
v_n_3707_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_n_3707_);
v_c_3708_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3);
v_persistent_3709_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3 + 1);
v_b_3710_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_b_3710_);
lean_dec_ref_known(v_x_3565_, 3);
v_00_u03c1_3584_ = v_x_3563_;
v_x_u2081_3585_ = v_x_3701_;
v_n_u2081_3586_ = v_n_3702_;
v_c_u2081_3587_ = v_c_3703_;
v_p_u2081_3588_ = v_persistent_3704_;
v_b_u2081_3589_ = v_b_3705_;
v_x_u2082_3590_ = v_x_3706_;
v_n_u2082_3591_ = v_n_3707_;
v_c_u2082_3592_ = v_c_3708_;
v_p_u2082_3593_ = v_persistent_3709_;
v_b_u2082_3594_ = v_b_3710_;
goto v___jp_3583_;
}
else
{
uint8_t v___x_3711_; 
lean_dec_ref_known(v_x_3564_, 3);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3711_ = 0;
return v___x_3711_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3565_) == 8)
{
lean_object* v_x_3712_; lean_object* v_b_3713_; lean_object* v_x_3714_; lean_object* v_b_3715_; uint8_t v___x_3716_; 
v_x_3712_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3712_);
v_b_3713_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_b_3713_);
lean_dec_ref_known(v_x_3564_, 2);
v_x_3714_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3714_);
v_b_3715_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_b_3715_);
lean_dec_ref_known(v_x_3565_, 2);
v___x_3716_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_x_3712_, v_x_3714_);
lean_dec(v_x_3714_);
lean_dec(v_x_3712_);
if (v___x_3716_ == 0)
{
lean_dec(v_b_3715_);
lean_dec(v_b_3713_);
lean_dec(v_x_3563_);
return v___x_3716_;
}
else
{
v_x_3564_ = v_b_3713_;
v_x_3565_ = v_b_3715_;
goto _start;
}
}
else
{
uint8_t v___x_3718_; 
lean_dec_ref_known(v_x_3564_, 2);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3718_ = 0;
return v___x_3718_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3565_) == 9)
{
lean_object* v_tid_3719_; lean_object* v_x_3720_; lean_object* v_cs_3721_; lean_object* v_tid_3722_; lean_object* v_x_3723_; lean_object* v_cs_3724_; uint8_t v___y_3726_; uint8_t v___x_3731_; 
v_tid_3719_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_tid_3719_);
v_x_3720_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_x_3720_);
v_cs_3721_ = lean_ctor_get(v_x_3564_, 3);
lean_inc_ref(v_cs_3721_);
lean_dec_ref_known(v_x_3564_, 4);
v_tid_3722_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_tid_3722_);
v_x_3723_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_x_3723_);
v_cs_3724_ = lean_ctor_get(v_x_3565_, 3);
lean_inc_ref(v_cs_3724_);
lean_dec_ref_known(v_x_3565_, 4);
v___x_3731_ = lean_name_eq(v_tid_3719_, v_tid_3722_);
lean_dec(v_tid_3722_);
lean_dec(v_tid_3719_);
if (v___x_3731_ == 0)
{
lean_dec(v_x_3723_);
lean_dec(v_x_3720_);
v___y_3726_ = v___x_3731_;
goto v___jp_3725_;
}
else
{
uint8_t v___x_3732_; 
v___x_3732_ = l_Lean_IR_VarId_alphaEqv(v_x_3563_, v_x_3720_, v_x_3723_);
lean_dec(v_x_3723_);
lean_dec(v_x_3720_);
v___y_3726_ = v___x_3732_;
goto v___jp_3725_;
}
v___jp_3725_:
{
if (v___y_3726_ == 0)
{
lean_dec_ref(v_cs_3724_);
lean_dec_ref(v_cs_3721_);
lean_dec(v_x_3563_);
return v___y_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = lean_array_get_size(v_cs_3721_);
v___x_3728_ = lean_array_get_size(v_cs_3724_);
v___x_3729_ = lean_nat_dec_eq(v___x_3727_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_dec_ref(v_cs_3724_);
lean_dec_ref(v_cs_3721_);
lean_dec(v_x_3563_);
return v___x_3729_;
}
else
{
uint8_t v___x_3730_; 
v___x_3730_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3563_, v_cs_3721_, v_cs_3724_, v___x_3727_);
lean_dec_ref(v_cs_3724_);
lean_dec_ref(v_cs_3721_);
return v___x_3730_;
}
}
}
}
else
{
uint8_t v___x_3733_; 
lean_dec_ref_known(v_x_3564_, 4);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3733_ = 0;
return v___x_3733_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3565_) == 10)
{
lean_object* v_x_3734_; lean_object* v_x_3735_; uint8_t v___x_3736_; 
v_x_3734_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_x_3734_);
lean_dec_ref_known(v_x_3564_, 1);
v_x_3735_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3735_);
lean_dec_ref_known(v_x_3565_, 1);
v___x_3736_ = l_Lean_IR_Arg_alphaEqv(v_x_3563_, v_x_3734_, v_x_3735_);
lean_dec(v_x_3735_);
lean_dec(v_x_3734_);
lean_dec(v_x_3563_);
return v___x_3736_;
}
else
{
uint8_t v___x_3737_; 
lean_dec_ref_known(v_x_3564_, 1);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3737_ = 0;
return v___x_3737_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3565_) == 11)
{
lean_object* v_j_3738_; lean_object* v_ys_3739_; lean_object* v_j_3740_; lean_object* v_ys_3741_; uint8_t v___x_3742_; 
v_j_3738_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_j_3738_);
v_ys_3739_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_ys_3739_);
lean_dec_ref_known(v_x_3564_, 2);
v_j_3740_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_j_3740_);
v_ys_3741_ = lean_ctor_get(v_x_3565_, 1);
lean_inc_ref(v_ys_3741_);
lean_dec_ref_known(v_x_3565_, 2);
v___x_3742_ = lean_nat_dec_eq(v_j_3738_, v_j_3740_);
lean_dec(v_j_3740_);
lean_dec(v_j_3738_);
if (v___x_3742_ == 0)
{
lean_dec_ref(v_ys_3741_);
lean_dec_ref(v_ys_3739_);
lean_dec(v_x_3563_);
return v___x_3742_;
}
else
{
uint8_t v___x_3743_; 
v___x_3743_ = l_Lean_IR_args_alphaEqv(v_x_3563_, v_ys_3739_, v_ys_3741_);
lean_dec_ref(v_ys_3741_);
lean_dec_ref(v_ys_3739_);
lean_dec(v_x_3563_);
return v___x_3743_;
}
}
else
{
uint8_t v___x_3744_; 
lean_dec_ref_known(v_x_3564_, 2);
lean_dec(v_x_3565_);
lean_dec(v_x_3563_);
v___x_3744_ = 0;
return v___x_3744_;
}
}
default: 
{
lean_dec(v_x_3563_);
if (lean_obj_tag(v_x_3565_) == 12)
{
uint8_t v___x_3745_; 
v___x_3745_ = 1;
return v___x_3745_;
}
else
{
uint8_t v___x_3746_; 
lean_dec(v_x_3565_);
v___x_3746_ = 0;
return v___x_3746_;
}
}
}
v___jp_3566_:
{
if (v___y_3570_ == 0)
{
if (v___y_3567_ == 0)
{
v_x_3563_ = v___y_3569_;
v_x_3564_ = v___y_3571_;
v_x_3565_ = v___y_3568_;
goto _start;
}
else
{
lean_dec(v___y_3571_);
lean_dec(v___y_3569_);
lean_dec(v___y_3568_);
return v___y_3570_;
}
}
else
{
if (v___y_3567_ == 0)
{
lean_dec(v___y_3571_);
lean_dec(v___y_3569_);
lean_dec(v___y_3568_);
return v___y_3567_;
}
else
{
v_x_3563_ = v___y_3569_;
v_x_3564_ = v___y_3571_;
v_x_3565_ = v___y_3568_;
goto _start;
}
}
}
v___jp_3574_:
{
if (v___y_3582_ == 0)
{
lean_dec(v___y_3581_);
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
return v___y_3582_;
}
else
{
if (v___y_3580_ == 0)
{
if (v___y_3579_ == 0)
{
v___y_3567_ = v___y_3575_;
v___y_3568_ = v___y_3576_;
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___y_3578_;
v___y_3571_ = v___y_3581_;
goto v___jp_3566_;
}
else
{
lean_dec(v___y_3581_);
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
return v___y_3580_;
}
}
else
{
if (v___y_3579_ == 0)
{
lean_dec(v___y_3581_);
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
return v___y_3579_;
}
else
{
v___y_3567_ = v___y_3575_;
v___y_3568_ = v___y_3576_;
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___y_3578_;
v___y_3571_ = v___y_3581_;
goto v___jp_3566_;
}
}
}
}
v___jp_3583_:
{
uint8_t v___x_3595_; 
v___x_3595_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3584_, v_x_u2081_3585_, v_x_u2082_3590_);
lean_dec(v_x_u2082_3590_);
lean_dec(v_x_u2081_3585_);
if (v___x_3595_ == 0)
{
lean_dec(v_n_u2082_3591_);
lean_dec(v_n_u2081_3586_);
v___y_3575_ = v_p_u2082_3593_;
v___y_3576_ = v_b_u2082_3594_;
v___y_3577_ = v_00_u03c1_3584_;
v___y_3578_ = v_p_u2081_3588_;
v___y_3579_ = v_c_u2082_3592_;
v___y_3580_ = v_c_u2081_3587_;
v___y_3581_ = v_b_u2081_3589_;
v___y_3582_ = v___x_3595_;
goto v___jp_3574_;
}
else
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_nat_dec_eq(v_n_u2081_3586_, v_n_u2082_3591_);
lean_dec(v_n_u2082_3591_);
lean_dec(v_n_u2081_3586_);
v___y_3575_ = v_p_u2082_3593_;
v___y_3576_ = v_b_u2082_3594_;
v___y_3577_ = v_00_u03c1_3584_;
v___y_3578_ = v_p_u2081_3588_;
v___y_3579_ = v_c_u2082_3592_;
v___y_3580_ = v_c_u2081_3587_;
v___y_3581_ = v_b_u2081_3589_;
v___y_3582_ = v___x_3596_;
goto v___jp_3574_;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* v_x_3747_, lean_object* v_xs_3748_, lean_object* v_ys_3749_, lean_object* v_x_3750_){
_start:
{
lean_object* v_zero_3751_; uint8_t v_isZero_3752_; 
v_zero_3751_ = lean_unsigned_to_nat(0u);
v_isZero_3752_ = lean_nat_dec_eq(v_x_3750_, v_zero_3751_);
if (v_isZero_3752_ == 1)
{
lean_dec(v_x_3750_);
lean_dec(v_x_3747_);
return v_isZero_3752_;
}
else
{
lean_object* v_one_3753_; lean_object* v_n_3754_; uint8_t v___y_3756_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v_one_3753_ = lean_unsigned_to_nat(1u);
v_n_3754_ = lean_nat_sub(v_x_3750_, v_one_3753_);
lean_dec(v_x_3750_);
v___x_3758_ = lean_array_fget_borrowed(v_xs_3748_, v_n_3754_);
v___x_3759_ = lean_array_fget_borrowed(v_ys_3749_, v_n_3754_);
if (lean_obj_tag(v___x_3758_) == 0)
{
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_info_3760_; lean_object* v_b_3761_; lean_object* v_info_3762_; lean_object* v_b_3763_; uint8_t v___x_3764_; 
v_info_3760_ = lean_ctor_get(v___x_3758_, 0);
v_b_3761_ = lean_ctor_get(v___x_3758_, 1);
v_info_3762_ = lean_ctor_get(v___x_3759_, 0);
v_b_3763_ = lean_ctor_get(v___x_3759_, 1);
v___x_3764_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_3760_, v_info_3762_);
if (v___x_3764_ == 0)
{
v___y_3756_ = v___x_3764_;
goto v___jp_3755_;
}
else
{
uint8_t v___x_3765_; 
lean_inc(v_b_3763_);
lean_inc(v_b_3761_);
lean_inc(v_x_3747_);
v___x_3765_ = l_Lean_IR_FnBody_alphaEqv(v_x_3747_, v_b_3761_, v_b_3763_);
v___y_3756_ = v___x_3765_;
goto v___jp_3755_;
}
}
else
{
lean_dec(v_n_3754_);
lean_dec(v_x_3747_);
return v_isZero_3752_;
}
}
else
{
if (lean_obj_tag(v___x_3759_) == 1)
{
lean_object* v_b_3766_; lean_object* v_b_3767_; uint8_t v___x_3768_; 
v_b_3766_ = lean_ctor_get(v___x_3758_, 0);
v_b_3767_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_b_3767_);
lean_inc(v_b_3766_);
lean_inc(v_x_3747_);
v___x_3768_ = l_Lean_IR_FnBody_alphaEqv(v_x_3747_, v_b_3766_, v_b_3767_);
v___y_3756_ = v___x_3768_;
goto v___jp_3755_;
}
else
{
lean_dec(v_n_3754_);
lean_dec(v_x_3747_);
return v_isZero_3752_;
}
}
v___jp_3755_:
{
if (v___y_3756_ == 0)
{
lean_dec(v_n_3754_);
lean_dec(v_x_3747_);
return v___y_3756_;
}
else
{
v_x_3750_ = v_n_3754_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* v_x_3769_, lean_object* v_xs_3770_, lean_object* v_ys_3771_, lean_object* v_x_3772_){
_start:
{
uint8_t v_res_3773_; lean_object* v_r_3774_; 
v_res_3773_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3769_, v_xs_3770_, v_ys_3771_, v_x_3772_);
lean_dec_ref(v_ys_3771_);
lean_dec_ref(v_xs_3770_);
v_r_3774_ = lean_box(v_res_3773_);
return v_r_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
uint8_t v_res_3778_; lean_object* v_r_3779_; 
v_res_3778_ = l_Lean_IR_FnBody_alphaEqv(v_x_3775_, v_x_3776_, v_x_3777_);
v_r_3779_ = lean_box(v_res_3778_);
return v_r_3779_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object* v_x_3780_, lean_object* v_xs_3781_, lean_object* v_ys_3782_, lean_object* v_hsz_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_){
_start:
{
uint8_t v___x_3786_; 
v___x_3786_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3780_, v_xs_3781_, v_ys_3782_, v_x_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* v_x_3787_, lean_object* v_xs_3788_, lean_object* v_ys_3789_, lean_object* v_hsz_3790_, lean_object* v_x_3791_, lean_object* v_x_3792_){
_start:
{
uint8_t v_res_3793_; lean_object* v_r_3794_; 
v_res_3793_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(v_x_3787_, v_xs_3788_, v_ys_3789_, v_hsz_3790_, v_x_3791_, v_x_3792_);
lean_dec_ref(v_ys_3789_);
lean_dec_ref(v_xs_3788_);
v_r_3794_ = lean_box(v_res_3793_);
return v_r_3794_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* v_b_u2081_3795_, lean_object* v_b_u2082_3796_){
_start:
{
lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = lean_box(1);
v___x_3798_ = l_Lean_IR_FnBody_alphaEqv(v___x_3797_, v_b_u2081_3795_, v_b_u2082_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* v_b_u2081_3799_, lean_object* v_b_u2082_3800_){
_start:
{
uint8_t v_res_3801_; lean_object* v_r_3802_; 
v_res_3801_ = l_Lean_IR_FnBody_beq(v_b_u2081_3799_, v_b_u2082_3800_);
v_r_3802_ = lean_box(v_res_3801_);
return v_r_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* v_x_3823_, lean_object* v_t_3824_, lean_object* v_e_3825_){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3826_ = ((lean_object*)(l_Lean_IR_mkIf___closed__1));
v___x_3827_ = lean_box(1);
v___x_3828_ = ((lean_object*)(l_Lean_IR_mkIf___closed__4));
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
lean_ctor_set(v___x_3829_, 1, v_e_3825_);
v___x_3830_ = ((lean_object*)(l_Lean_IR_mkIf___closed__7));
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
lean_ctor_set(v___x_3831_, 1, v_t_3824_);
v___x_3832_ = lean_unsigned_to_nat(2u);
v___x_3833_ = lean_mk_empty_array_with_capacity(v___x_3832_);
v___x_3834_ = lean_array_push(v___x_3833_, v___x_3829_);
v___x_3835_ = lean_array_push(v___x_3834_, v___x_3831_);
v___x_3836_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3826_);
lean_ctor_set(v___x_3836_, 1, v_x_3823_);
lean_ctor_set(v___x_3836_, 2, v___x_3827_);
lean_ctor_set(v___x_3836_, 3, v___x_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* v_t_3843_){
_start:
{
switch(lean_obj_tag(v_t_3843_))
{
case 5:
{
lean_object* v___x_3844_; 
v___x_3844_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__0));
return v___x_3844_;
}
case 3:
{
lean_object* v___x_3845_; 
v___x_3845_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__1));
return v___x_3845_;
}
case 4:
{
lean_object* v___x_3846_; 
v___x_3846_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__2));
return v___x_3846_;
}
case 0:
{
lean_object* v___x_3847_; 
v___x_3847_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__3));
return v___x_3847_;
}
case 9:
{
lean_object* v___x_3848_; 
v___x_3848_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__4));
return v___x_3848_;
}
default: 
{
lean_object* v___x_3849_; 
v___x_3849_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__5));
return v___x_3849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* v_t_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_IR_getUnboxOpName(v_t_3850_);
lean_dec(v_t_3850_);
return v_res_3851_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_instInhabitedVarId_default = _init_l_Lean_IR_instInhabitedVarId_default();
lean_mark_persistent(l_Lean_IR_instInhabitedVarId_default);
l_Lean_IR_instInhabitedVarId = _init_l_Lean_IR_instInhabitedVarId();
lean_mark_persistent(l_Lean_IR_instInhabitedVarId);
l_Lean_IR_instInhabitedJoinPointId_default = _init_l_Lean_IR_instInhabitedJoinPointId_default();
lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId_default);
l_Lean_IR_instInhabitedJoinPointId = _init_l_Lean_IR_instInhabitedJoinPointId();
lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId);
l_Lean_IR_instInhabitedIRType_default = _init_l_Lean_IR_instInhabitedIRType_default();
lean_mark_persistent(l_Lean_IR_instInhabitedIRType_default);
l_Lean_IR_instInhabitedIRType = _init_l_Lean_IR_instInhabitedIRType();
lean_mark_persistent(l_Lean_IR_instInhabitedIRType);
l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
lean_mark_persistent(l_Lean_IR_FnBody_nil);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
