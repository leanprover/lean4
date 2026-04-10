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
lean_dec_ref(v_t_153_);
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
lean_dec_ref(v_t_153_);
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
lean_dec_ref(v_x_363_);
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
lean_dec_ref(v_x_459_);
v___x_464_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_463_);
return v___x_464_;
}
else
{
lean_object* v_head_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_inc(v_tail_462_);
v_head_465_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_head_465_);
lean_dec_ref(v_x_459_);
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
lean_dec_ref(v_t_756_);
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
lean_dec_ref(v_x_815_);
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
lean_dec_ref(v_t_864_);
v___x_867_ = lean_apply_1(v_k_865_, v_v_866_);
return v___x_867_;
}
else
{
lean_object* v_v_868_; lean_object* v___x_869_; 
v_v_868_ = lean_ctor_get(v_t_864_, 0);
lean_inc_ref(v_v_868_);
lean_dec_ref(v_t_864_);
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
uint8_t v___x_1059_; 
v___x_1059_ = l_Lean_IR_CtorInfo_isRef(v_info_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; 
v___x_1060_ = 1;
return v___x_1060_;
}
else
{
uint8_t v___x_1061_; 
v___x_1061_ = 0;
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object* v_info_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_IR_CtorInfo_isScalar(v_info_1062_);
lean_dec_ref(v_info_1062_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type(lean_object* v_info_1065_){
_start:
{
uint8_t v___x_1066_; 
v___x_1066_ = l_Lean_IR_CtorInfo_isRef(v_info_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(12);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_box(7);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type___boxed(lean_object* v_info_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_IR_CtorInfo_type(v_info_1069_);
lean_dec_ref(v_info_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx(lean_object* v_x_1071_){
_start:
{
switch(lean_obj_tag(v_x_1071_))
{
case 0:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
return v___x_1072_;
}
case 1:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_unsigned_to_nat(1u);
return v___x_1073_;
}
case 2:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_unsigned_to_nat(2u);
return v___x_1074_;
}
case 3:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_unsigned_to_nat(3u);
return v___x_1075_;
}
case 4:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_unsigned_to_nat(4u);
return v___x_1076_;
}
case 5:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_unsigned_to_nat(5u);
return v___x_1077_;
}
case 6:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_unsigned_to_nat(6u);
return v___x_1078_;
}
case 7:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_unsigned_to_nat(7u);
return v___x_1079_;
}
case 8:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_unsigned_to_nat(8u);
return v___x_1080_;
}
case 9:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_unsigned_to_nat(9u);
return v___x_1081_;
}
case 10:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_unsigned_to_nat(10u);
return v___x_1082_;
}
case 11:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_unsigned_to_nat(11u);
return v___x_1083_;
}
default: 
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_unsigned_to_nat(12u);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___boxed(lean_object* v_x_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_IR_Expr_ctorIdx(v_x_1085_);
lean_dec_ref(v_x_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___redArg(lean_object* v_t_1087_, lean_object* v_k_1088_){
_start:
{
switch(lean_obj_tag(v_t_1087_))
{
case 0:
{
lean_object* v_i_1089_; lean_object* v_ys_1090_; lean_object* v___x_1091_; 
v_i_1089_ = lean_ctor_get(v_t_1087_, 0);
lean_inc_ref(v_i_1089_);
v_ys_1090_ = lean_ctor_get(v_t_1087_, 1);
lean_inc_ref(v_ys_1090_);
lean_dec_ref(v_t_1087_);
v___x_1091_ = lean_apply_2(v_k_1088_, v_i_1089_, v_ys_1090_);
return v___x_1091_;
}
case 2:
{
lean_object* v_x_1092_; lean_object* v_i_1093_; uint8_t v_updtHeader_1094_; lean_object* v_ys_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_x_1092_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_x_1092_);
v_i_1093_ = lean_ctor_get(v_t_1087_, 1);
lean_inc_ref(v_i_1093_);
v_updtHeader_1094_ = lean_ctor_get_uint8(v_t_1087_, sizeof(void*)*3);
v_ys_1095_ = lean_ctor_get(v_t_1087_, 2);
lean_inc_ref(v_ys_1095_);
lean_dec_ref(v_t_1087_);
v___x_1096_ = lean_box(v_updtHeader_1094_);
v___x_1097_ = lean_apply_4(v_k_1088_, v_x_1092_, v_i_1093_, v___x_1096_, v_ys_1095_);
return v___x_1097_;
}
case 5:
{
lean_object* v_n_1098_; lean_object* v_offset_1099_; lean_object* v_x_1100_; lean_object* v___x_1101_; 
v_n_1098_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_n_1098_);
v_offset_1099_ = lean_ctor_get(v_t_1087_, 1);
lean_inc(v_offset_1099_);
v_x_1100_ = lean_ctor_get(v_t_1087_, 2);
lean_inc(v_x_1100_);
lean_dec_ref(v_t_1087_);
v___x_1101_ = lean_apply_3(v_k_1088_, v_n_1098_, v_offset_1099_, v_x_1100_);
return v___x_1101_;
}
case 6:
{
lean_object* v_c_1102_; lean_object* v_ys_1103_; lean_object* v___x_1104_; 
v_c_1102_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_c_1102_);
v_ys_1103_ = lean_ctor_get(v_t_1087_, 1);
lean_inc_ref(v_ys_1103_);
lean_dec_ref(v_t_1087_);
v___x_1104_ = lean_apply_2(v_k_1088_, v_c_1102_, v_ys_1103_);
return v___x_1104_;
}
case 7:
{
lean_object* v_c_1105_; lean_object* v_ys_1106_; lean_object* v___x_1107_; 
v_c_1105_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_c_1105_);
v_ys_1106_ = lean_ctor_get(v_t_1087_, 1);
lean_inc_ref(v_ys_1106_);
lean_dec_ref(v_t_1087_);
v___x_1107_ = lean_apply_2(v_k_1088_, v_c_1105_, v_ys_1106_);
return v___x_1107_;
}
case 8:
{
lean_object* v_x_1108_; lean_object* v_ys_1109_; lean_object* v___x_1110_; 
v_x_1108_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_x_1108_);
v_ys_1109_ = lean_ctor_get(v_t_1087_, 1);
lean_inc_ref(v_ys_1109_);
lean_dec_ref(v_t_1087_);
v___x_1110_ = lean_apply_2(v_k_1088_, v_x_1108_, v_ys_1109_);
return v___x_1110_;
}
case 10:
{
lean_object* v_x_1111_; lean_object* v___x_1112_; 
v_x_1111_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_x_1111_);
lean_dec_ref(v_t_1087_);
v___x_1112_ = lean_apply_1(v_k_1088_, v_x_1111_);
return v___x_1112_;
}
case 11:
{
lean_object* v_v_1113_; lean_object* v___x_1114_; 
v_v_1113_ = lean_ctor_get(v_t_1087_, 0);
lean_inc_ref(v_v_1113_);
lean_dec_ref(v_t_1087_);
v___x_1114_ = lean_apply_1(v_k_1088_, v_v_1113_);
return v___x_1114_;
}
case 12:
{
lean_object* v_x_1115_; lean_object* v___x_1116_; 
v_x_1115_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_x_1115_);
lean_dec_ref(v_t_1087_);
v___x_1116_ = lean_apply_1(v_k_1088_, v_x_1115_);
return v___x_1116_;
}
default: 
{
lean_object* v_n_1117_; lean_object* v_x_1118_; lean_object* v___x_1119_; 
v_n_1117_ = lean_ctor_get(v_t_1087_, 0);
lean_inc(v_n_1117_);
v_x_1118_ = lean_ctor_get(v_t_1087_, 1);
lean_inc(v_x_1118_);
lean_dec_ref(v_t_1087_);
v___x_1119_ = lean_apply_2(v_k_1088_, v_n_1117_, v_x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim(lean_object* v_motive_1120_, lean_object* v_ctorIdx_1121_, lean_object* v_t_1122_, lean_object* v_h_1123_, lean_object* v_k_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1122_, v_k_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___boxed(lean_object* v_motive_1126_, lean_object* v_ctorIdx_1127_, lean_object* v_t_1128_, lean_object* v_h_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_IR_Expr_ctorElim(v_motive_1126_, v_ctorIdx_1127_, v_t_1128_, v_h_1129_, v_k_1130_);
lean_dec(v_ctorIdx_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim___redArg(lean_object* v_t_1132_, lean_object* v_ctor_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1132_, v_ctor_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim(lean_object* v_motive_1135_, lean_object* v_t_1136_, lean_object* v_h_1137_, lean_object* v_ctor_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1136_, v_ctor_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim___redArg(lean_object* v_t_1140_, lean_object* v_reset_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1140_, v_reset_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim(lean_object* v_motive_1143_, lean_object* v_t_1144_, lean_object* v_h_1145_, lean_object* v_reset_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1144_, v_reset_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim___redArg(lean_object* v_t_1148_, lean_object* v_reuse_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1148_, v_reuse_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim(lean_object* v_motive_1151_, lean_object* v_t_1152_, lean_object* v_h_1153_, lean_object* v_reuse_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1152_, v_reuse_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim___redArg(lean_object* v_t_1156_, lean_object* v_proj_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1156_, v_proj_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim(lean_object* v_motive_1159_, lean_object* v_t_1160_, lean_object* v_h_1161_, lean_object* v_proj_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1160_, v_proj_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim___redArg(lean_object* v_t_1164_, lean_object* v_uproj_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1164_, v_uproj_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim(lean_object* v_motive_1167_, lean_object* v_t_1168_, lean_object* v_h_1169_, lean_object* v_uproj_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1168_, v_uproj_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim___redArg(lean_object* v_t_1172_, lean_object* v_sproj_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1172_, v_sproj_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim(lean_object* v_motive_1175_, lean_object* v_t_1176_, lean_object* v_h_1177_, lean_object* v_sproj_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1176_, v_sproj_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim___redArg(lean_object* v_t_1180_, lean_object* v_fap_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1180_, v_fap_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim(lean_object* v_motive_1183_, lean_object* v_t_1184_, lean_object* v_h_1185_, lean_object* v_fap_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1184_, v_fap_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim___redArg(lean_object* v_t_1188_, lean_object* v_pap_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1188_, v_pap_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim(lean_object* v_motive_1191_, lean_object* v_t_1192_, lean_object* v_h_1193_, lean_object* v_pap_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1192_, v_pap_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim___redArg(lean_object* v_t_1196_, lean_object* v_ap_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1196_, v_ap_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim(lean_object* v_motive_1199_, lean_object* v_t_1200_, lean_object* v_h_1201_, lean_object* v_ap_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1200_, v_ap_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim___redArg(lean_object* v_t_1204_, lean_object* v_box_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1204_, v_box_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim(lean_object* v_motive_1207_, lean_object* v_t_1208_, lean_object* v_h_1209_, lean_object* v_box_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1208_, v_box_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim___redArg(lean_object* v_t_1212_, lean_object* v_unbox_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1212_, v_unbox_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim(lean_object* v_motive_1215_, lean_object* v_t_1216_, lean_object* v_h_1217_, lean_object* v_unbox_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1216_, v_unbox_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim___redArg(lean_object* v_t_1220_, lean_object* v_lit_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1220_, v_lit_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim(lean_object* v_motive_1223_, lean_object* v_t_1224_, lean_object* v_h_1225_, lean_object* v_lit_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1224_, v_lit_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim___redArg(lean_object* v_t_1228_, lean_object* v_isShared_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1228_, v_isShared_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim(lean_object* v_motive_1231_, lean_object* v_t_1232_, lean_object* v_h_1233_, lean_object* v_isShared_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1232_, v_isShared_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_unsigned_to_nat(5u);
v___x_1259_ = lean_nat_to_int(v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(10u);
v___x_1264_ = lean_nat_to_int(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_unsigned_to_nat(6u);
v___x_1269_ = lean_nat_to_int(v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___redArg(lean_object* v_x_1270_){
_start:
{
lean_object* v_x_1271_; uint8_t v_borrow_1272_; lean_object* v_ty_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_x_1271_ = lean_ctor_get(v_x_1270_, 0);
lean_inc(v_x_1271_);
v_borrow_1272_ = lean_ctor_get_uint8(v_x_1270_, sizeof(void*)*2);
v_ty_1273_ = lean_ctor_get(v_x_1270_, 1);
lean_inc(v_ty_1273_);
lean_dec_ref(v_x_1270_);
v___x_1274_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__5));
v___x_1275_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__3));
v___x_1276_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__4, &l_Lean_IR_instReprParam_repr___redArg___closed__4_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__4);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_1271_);
v___x_1279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1276_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = 0;
v___x_1281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*1, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1275_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2));
v___x_1284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_box(1);
v___x_1286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__6));
v___x_1288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1274_);
v___x_1290_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__7, &l_Lean_IR_instReprParam_repr___redArg___closed__7_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__7);
v___x_1291_ = l_Bool_repr___redArg(v_borrow_1272_);
v___x_1292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*1, v___x_1280_);
v___x_1294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1289_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1283_);
v___x_1296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1285_);
v___x_1297_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__9));
v___x_1298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1274_);
v___x_1300_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__10, &l_Lean_IR_instReprParam_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__10);
v___x_1301_ = l_Lean_IR_instReprIRType_repr(v_ty_1273_, v___x_1277_);
v___x_1302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*1, v___x_1280_);
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1299_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_1306_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_1307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1304_);
v___x_1308_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_1309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1305_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*1, v___x_1280_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr(lean_object* v_x_1312_, lean_object* v_prec_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_IR_instReprParam_repr___redArg(v_x_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___boxed(lean_object* v_x_1315_, lean_object* v_prec_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_IR_instReprParam_repr(v_x_1315_, v_prec_1316_);
lean_dec(v_prec_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx(lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1320_) == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_unsigned_to_nat(1u);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___boxed(lean_object* v_x_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_IR_Alt_ctorIdx(v_x_1323_);
lean_dec_ref(v_x_1323_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___redArg(lean_object* v_t_1325_, lean_object* v_k_1326_){
_start:
{
if (lean_obj_tag(v_t_1325_) == 0)
{
lean_object* v_info_1327_; lean_object* v_b_1328_; lean_object* v___x_1329_; 
v_info_1327_ = lean_ctor_get(v_t_1325_, 0);
lean_inc_ref(v_info_1327_);
v_b_1328_ = lean_ctor_get(v_t_1325_, 1);
lean_inc(v_b_1328_);
lean_dec_ref(v_t_1325_);
v___x_1329_ = lean_apply_2(v_k_1326_, v_info_1327_, v_b_1328_);
return v___x_1329_;
}
else
{
lean_object* v_b_1330_; lean_object* v___x_1331_; 
v_b_1330_ = lean_ctor_get(v_t_1325_, 0);
lean_inc(v_b_1330_);
lean_dec_ref(v_t_1325_);
v___x_1331_ = lean_apply_1(v_k_1326_, v_b_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim(lean_object* v_motive__1_1332_, lean_object* v_ctorIdx_1333_, lean_object* v_t_1334_, lean_object* v_h_1335_, lean_object* v_k_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1334_, v_k_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___boxed(lean_object* v_motive__1_1338_, lean_object* v_ctorIdx_1339_, lean_object* v_t_1340_, lean_object* v_h_1341_, lean_object* v_k_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_IR_Alt_ctorElim(v_motive__1_1338_, v_ctorIdx_1339_, v_t_1340_, v_h_1341_, v_k_1342_);
lean_dec(v_ctorIdx_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim___redArg(lean_object* v_t_1344_, lean_object* v_ctor_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1344_, v_ctor_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim(lean_object* v_motive__1_1347_, lean_object* v_t_1348_, lean_object* v_h_1349_, lean_object* v_ctor_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1348_, v_ctor_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim___redArg(lean_object* v_t_1352_, lean_object* v_default_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1352_, v_default_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim(lean_object* v_motive__1_1355_, lean_object* v_t_1356_, lean_object* v_h_1357_, lean_object* v_default_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1356_, v_default_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx(lean_object* v_x_1360_){
_start:
{
switch(lean_obj_tag(v_x_1360_))
{
case 0:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
return v___x_1361_;
}
case 1:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
return v___x_1362_;
}
case 2:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_unsigned_to_nat(2u);
return v___x_1363_;
}
case 3:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_unsigned_to_nat(3u);
return v___x_1364_;
}
case 4:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_unsigned_to_nat(4u);
return v___x_1365_;
}
case 5:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_unsigned_to_nat(5u);
return v___x_1366_;
}
case 6:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_unsigned_to_nat(6u);
return v___x_1367_;
}
case 7:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_unsigned_to_nat(7u);
return v___x_1368_;
}
case 8:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(8u);
return v___x_1369_;
}
case 9:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(9u);
return v___x_1370_;
}
case 10:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_unsigned_to_nat(10u);
return v___x_1371_;
}
case 11:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_unsigned_to_nat(11u);
return v___x_1372_;
}
default: 
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_unsigned_to_nat(12u);
return v___x_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___boxed(lean_object* v_x_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_IR_FnBody_ctorIdx(v_x_1374_);
lean_dec(v_x_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___redArg(lean_object* v_t_1376_, lean_object* v_k_1377_){
_start:
{
switch(lean_obj_tag(v_t_1376_))
{
case 0:
{
lean_object* v_x_1378_; lean_object* v_ty_1379_; lean_object* v_e_1380_; lean_object* v_b_1381_; lean_object* v___x_1382_; 
v_x_1378_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1378_);
v_ty_1379_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_ty_1379_);
v_e_1380_ = lean_ctor_get(v_t_1376_, 2);
lean_inc_ref(v_e_1380_);
v_b_1381_ = lean_ctor_get(v_t_1376_, 3);
lean_inc(v_b_1381_);
lean_dec_ref(v_t_1376_);
v___x_1382_ = lean_apply_4(v_k_1377_, v_x_1378_, v_ty_1379_, v_e_1380_, v_b_1381_);
return v___x_1382_;
}
case 1:
{
lean_object* v_j_1383_; lean_object* v_xs_1384_; lean_object* v_v_1385_; lean_object* v_b_1386_; lean_object* v___x_1387_; 
v_j_1383_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_j_1383_);
v_xs_1384_ = lean_ctor_get(v_t_1376_, 1);
lean_inc_ref(v_xs_1384_);
v_v_1385_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_v_1385_);
v_b_1386_ = lean_ctor_get(v_t_1376_, 3);
lean_inc(v_b_1386_);
lean_dec_ref(v_t_1376_);
v___x_1387_ = lean_apply_4(v_k_1377_, v_j_1383_, v_xs_1384_, v_v_1385_, v_b_1386_);
return v___x_1387_;
}
case 3:
{
lean_object* v_x_1388_; lean_object* v_cidx_1389_; lean_object* v_b_1390_; lean_object* v___x_1391_; 
v_x_1388_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1388_);
v_cidx_1389_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_cidx_1389_);
v_b_1390_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_b_1390_);
lean_dec_ref(v_t_1376_);
v___x_1391_ = lean_apply_3(v_k_1377_, v_x_1388_, v_cidx_1389_, v_b_1390_);
return v___x_1391_;
}
case 5:
{
lean_object* v_x_1392_; lean_object* v_i_1393_; lean_object* v_offset_1394_; lean_object* v_y_1395_; lean_object* v_ty_1396_; lean_object* v_b_1397_; lean_object* v___x_1398_; 
v_x_1392_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1392_);
v_i_1393_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_i_1393_);
v_offset_1394_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_offset_1394_);
v_y_1395_ = lean_ctor_get(v_t_1376_, 3);
lean_inc(v_y_1395_);
v_ty_1396_ = lean_ctor_get(v_t_1376_, 4);
lean_inc(v_ty_1396_);
v_b_1397_ = lean_ctor_get(v_t_1376_, 5);
lean_inc(v_b_1397_);
lean_dec_ref(v_t_1376_);
v___x_1398_ = lean_apply_6(v_k_1377_, v_x_1392_, v_i_1393_, v_offset_1394_, v_y_1395_, v_ty_1396_, v_b_1397_);
return v___x_1398_;
}
case 6:
{
lean_object* v_x_1399_; lean_object* v_n_1400_; uint8_t v_c_1401_; uint8_t v_persistent_1402_; lean_object* v_b_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_x_1399_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1399_);
v_n_1400_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_n_1400_);
v_c_1401_ = lean_ctor_get_uint8(v_t_1376_, sizeof(void*)*3);
v_persistent_1402_ = lean_ctor_get_uint8(v_t_1376_, sizeof(void*)*3 + 1);
v_b_1403_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_b_1403_);
lean_dec_ref(v_t_1376_);
v___x_1404_ = lean_box(v_c_1401_);
v___x_1405_ = lean_box(v_persistent_1402_);
v___x_1406_ = lean_apply_5(v_k_1377_, v_x_1399_, v_n_1400_, v___x_1404_, v___x_1405_, v_b_1403_);
return v___x_1406_;
}
case 7:
{
lean_object* v_x_1407_; lean_object* v_n_1408_; uint8_t v_c_1409_; uint8_t v_persistent_1410_; lean_object* v_b_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_x_1407_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1407_);
v_n_1408_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_n_1408_);
v_c_1409_ = lean_ctor_get_uint8(v_t_1376_, sizeof(void*)*3);
v_persistent_1410_ = lean_ctor_get_uint8(v_t_1376_, sizeof(void*)*3 + 1);
v_b_1411_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_b_1411_);
lean_dec_ref(v_t_1376_);
v___x_1412_ = lean_box(v_c_1409_);
v___x_1413_ = lean_box(v_persistent_1410_);
v___x_1414_ = lean_apply_5(v_k_1377_, v_x_1407_, v_n_1408_, v___x_1412_, v___x_1413_, v_b_1411_);
return v___x_1414_;
}
case 8:
{
lean_object* v_x_1415_; lean_object* v_b_1416_; lean_object* v___x_1417_; 
v_x_1415_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1415_);
v_b_1416_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_b_1416_);
lean_dec_ref(v_t_1376_);
v___x_1417_ = lean_apply_2(v_k_1377_, v_x_1415_, v_b_1416_);
return v___x_1417_;
}
case 9:
{
lean_object* v_tid_1418_; lean_object* v_x_1419_; lean_object* v_xType_1420_; lean_object* v_cs_1421_; lean_object* v___x_1422_; 
v_tid_1418_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_tid_1418_);
v_x_1419_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_x_1419_);
v_xType_1420_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_xType_1420_);
v_cs_1421_ = lean_ctor_get(v_t_1376_, 3);
lean_inc_ref(v_cs_1421_);
lean_dec_ref(v_t_1376_);
v___x_1422_ = lean_apply_4(v_k_1377_, v_tid_1418_, v_x_1419_, v_xType_1420_, v_cs_1421_);
return v___x_1422_;
}
case 10:
{
lean_object* v_x_1423_; lean_object* v___x_1424_; 
v_x_1423_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1423_);
lean_dec_ref(v_t_1376_);
v___x_1424_ = lean_apply_1(v_k_1377_, v_x_1423_);
return v___x_1424_;
}
case 11:
{
lean_object* v_j_1425_; lean_object* v_ys_1426_; lean_object* v___x_1427_; 
v_j_1425_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_j_1425_);
v_ys_1426_ = lean_ctor_get(v_t_1376_, 1);
lean_inc_ref(v_ys_1426_);
lean_dec_ref(v_t_1376_);
v___x_1427_ = lean_apply_2(v_k_1377_, v_j_1425_, v_ys_1426_);
return v___x_1427_;
}
case 12:
{
return v_k_1377_;
}
default: 
{
lean_object* v_x_1428_; lean_object* v_i_1429_; lean_object* v_y_1430_; lean_object* v_b_1431_; lean_object* v___x_1432_; 
v_x_1428_ = lean_ctor_get(v_t_1376_, 0);
lean_inc(v_x_1428_);
v_i_1429_ = lean_ctor_get(v_t_1376_, 1);
lean_inc(v_i_1429_);
v_y_1430_ = lean_ctor_get(v_t_1376_, 2);
lean_inc(v_y_1430_);
v_b_1431_ = lean_ctor_get(v_t_1376_, 3);
lean_inc(v_b_1431_);
lean_dec(v_t_1376_);
v___x_1432_ = lean_apply_4(v_k_1377_, v_x_1428_, v_i_1429_, v_y_1430_, v_b_1431_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim(lean_object* v_motive__2_1433_, lean_object* v_ctorIdx_1434_, lean_object* v_t_1435_, lean_object* v_h_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1435_, v_k_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___boxed(lean_object* v_motive__2_1439_, lean_object* v_ctorIdx_1440_, lean_object* v_t_1441_, lean_object* v_h_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_IR_FnBody_ctorElim(v_motive__2_1439_, v_ctorIdx_1440_, v_t_1441_, v_h_1442_, v_k_1443_);
lean_dec(v_ctorIdx_1440_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim___redArg(lean_object* v_t_1445_, lean_object* v_vdecl_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1445_, v_vdecl_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim(lean_object* v_motive__2_1448_, lean_object* v_t_1449_, lean_object* v_h_1450_, lean_object* v_vdecl_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1449_, v_vdecl_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim___redArg(lean_object* v_t_1453_, lean_object* v_jdecl_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1453_, v_jdecl_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim(lean_object* v_motive__2_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_jdecl_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1457_, v_jdecl_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim___redArg(lean_object* v_t_1461_, lean_object* v_set_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1461_, v_set_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim(lean_object* v_motive__2_1464_, lean_object* v_t_1465_, lean_object* v_h_1466_, lean_object* v_set_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1465_, v_set_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim___redArg(lean_object* v_t_1469_, lean_object* v_setTag_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1469_, v_setTag_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim(lean_object* v_motive__2_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_setTag_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1473_, v_setTag_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim___redArg(lean_object* v_t_1477_, lean_object* v_uset_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1477_, v_uset_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim(lean_object* v_motive__2_1480_, lean_object* v_t_1481_, lean_object* v_h_1482_, lean_object* v_uset_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1481_, v_uset_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim___redArg(lean_object* v_t_1485_, lean_object* v_sset_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1485_, v_sset_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim(lean_object* v_motive__2_1488_, lean_object* v_t_1489_, lean_object* v_h_1490_, lean_object* v_sset_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1489_, v_sset_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim___redArg(lean_object* v_t_1493_, lean_object* v_inc_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1493_, v_inc_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim(lean_object* v_motive__2_1496_, lean_object* v_t_1497_, lean_object* v_h_1498_, lean_object* v_inc_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1497_, v_inc_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim___redArg(lean_object* v_t_1501_, lean_object* v_dec_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1501_, v_dec_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim(lean_object* v_motive__2_1504_, lean_object* v_t_1505_, lean_object* v_h_1506_, lean_object* v_dec_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1505_, v_dec_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim___redArg(lean_object* v_t_1509_, lean_object* v_del_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1509_, v_del_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim(lean_object* v_motive__2_1512_, lean_object* v_t_1513_, lean_object* v_h_1514_, lean_object* v_del_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1513_, v_del_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim___redArg(lean_object* v_t_1517_, lean_object* v_case_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1517_, v_case_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim(lean_object* v_motive__2_1520_, lean_object* v_t_1521_, lean_object* v_h_1522_, lean_object* v_case_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1521_, v_case_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim___redArg(lean_object* v_t_1525_, lean_object* v_ret_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1525_, v_ret_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim(lean_object* v_motive__2_1528_, lean_object* v_t_1529_, lean_object* v_h_1530_, lean_object* v_ret_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1529_, v_ret_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim___redArg(lean_object* v_t_1533_, lean_object* v_jmp_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1533_, v_jmp_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim(lean_object* v_motive__2_1536_, lean_object* v_t_1537_, lean_object* v_h_1538_, lean_object* v_jmp_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1537_, v_jmp_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim___redArg(lean_object* v_t_1541_, lean_object* v_unreachable_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1541_, v_unreachable_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim(lean_object* v_motive__2_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_unreachable_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1545_, v_unreachable_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_nil(void){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_box(12);
return v___x_1563_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* v_x_1564_){
_start:
{
switch(lean_obj_tag(v_x_1564_))
{
case 9:
{
uint8_t v___x_1565_; 
v___x_1565_ = 1;
return v___x_1565_;
}
case 10:
{
uint8_t v___x_1566_; 
v___x_1566_ = 1;
return v___x_1566_;
}
case 11:
{
uint8_t v___x_1567_; 
v___x_1567_ = 1;
return v___x_1567_;
}
case 12:
{
uint8_t v___x_1568_; 
v___x_1568_ = 1;
return v___x_1568_;
}
default: 
{
uint8_t v___x_1569_; 
v___x_1569_ = 0;
return v___x_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object* v_x_1570_){
_start:
{
uint8_t v_res_1571_; lean_object* v_r_1572_; 
v_res_1571_ = l_Lean_IR_FnBody_isTerminal(v_x_1570_);
lean_dec(v_x_1570_);
v_r_1572_ = lean_box(v_res_1571_);
return v_r_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object* v_x_1573_){
_start:
{
switch(lean_obj_tag(v_x_1573_))
{
case 0:
{
lean_object* v_b_1574_; 
v_b_1574_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_b_1574_);
return v_b_1574_;
}
case 1:
{
lean_object* v_b_1575_; 
v_b_1575_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_b_1575_);
return v_b_1575_;
}
case 2:
{
lean_object* v_b_1576_; 
v_b_1576_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_b_1576_);
return v_b_1576_;
}
case 4:
{
lean_object* v_b_1577_; 
v_b_1577_ = lean_ctor_get(v_x_1573_, 3);
lean_inc(v_b_1577_);
return v_b_1577_;
}
case 5:
{
lean_object* v_b_1578_; 
v_b_1578_ = lean_ctor_get(v_x_1573_, 5);
lean_inc(v_b_1578_);
return v_b_1578_;
}
case 3:
{
lean_object* v_b_1579_; 
v_b_1579_ = lean_ctor_get(v_x_1573_, 2);
lean_inc(v_b_1579_);
return v_b_1579_;
}
case 6:
{
lean_object* v_b_1580_; 
v_b_1580_ = lean_ctor_get(v_x_1573_, 2);
lean_inc(v_b_1580_);
return v_b_1580_;
}
case 7:
{
lean_object* v_b_1581_; 
v_b_1581_ = lean_ctor_get(v_x_1573_, 2);
lean_inc(v_b_1581_);
return v_b_1581_;
}
case 8:
{
lean_object* v_b_1582_; 
v_b_1582_ = lean_ctor_get(v_x_1573_, 1);
lean_inc(v_b_1582_);
return v_b_1582_;
}
default: 
{
lean_inc(v_x_1573_);
return v_x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* v_x_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_IR_FnBody_body(v_x_1583_);
lean_dec(v_x_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
switch(lean_obj_tag(v_x_1585_))
{
case 0:
{
lean_object* v_x_1587_; lean_object* v_ty_1588_; lean_object* v_e_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_x_1587_ = lean_ctor_get(v_x_1585_, 0);
v_ty_1588_ = lean_ctor_get(v_x_1585_, 1);
v_e_1589_ = lean_ctor_get(v_x_1585_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_x_1585_, 3);
lean_dec(v_unused_1597_);
v___x_1591_ = v_x_1585_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_e_1589_);
lean_inc(v_ty_1588_);
lean_inc(v_x_1587_);
lean_dec(v_x_1585_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 3, v_x_1586_);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_x_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_ty_1588_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_e_1589_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_x_1586_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
case 1:
{
lean_object* v_j_1598_; lean_object* v_xs_1599_; lean_object* v_v_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_j_1598_ = lean_ctor_get(v_x_1585_, 0);
v_xs_1599_ = lean_ctor_get(v_x_1585_, 1);
v_v_1600_ = lean_ctor_get(v_x_1585_, 2);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_x_1585_, 3);
lean_dec(v_unused_1608_);
v___x_1602_ = v_x_1585_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_v_1600_);
lean_inc(v_xs_1599_);
lean_inc(v_j_1598_);
lean_dec(v_x_1585_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v_x_1586_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_j_1598_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_xs_1599_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1600_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_x_1586_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
case 2:
{
lean_object* v_x_1609_; lean_object* v_i_1610_; lean_object* v_y_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_x_1609_ = lean_ctor_get(v_x_1585_, 0);
v_i_1610_ = lean_ctor_get(v_x_1585_, 1);
v_y_1611_ = lean_ctor_get(v_x_1585_, 2);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_x_1585_, 3);
lean_dec(v_unused_1619_);
v___x_1613_ = v_x_1585_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_y_1611_);
lean_inc(v_i_1610_);
lean_inc(v_x_1609_);
lean_dec(v_x_1585_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 3, v_x_1586_);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_x_1609_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_i_1610_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_y_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_x_1586_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
case 4:
{
lean_object* v_x_1620_; lean_object* v_i_1621_; lean_object* v_y_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_x_1620_ = lean_ctor_get(v_x_1585_, 0);
v_i_1621_ = lean_ctor_get(v_x_1585_, 1);
v_y_1622_ = lean_ctor_get(v_x_1585_, 2);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v_x_1585_, 3);
lean_dec(v_unused_1630_);
v___x_1624_ = v_x_1585_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_y_1622_);
lean_inc(v_i_1621_);
lean_inc(v_x_1620_);
lean_dec(v_x_1585_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 3, v_x_1586_);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_x_1620_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_i_1621_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_y_1622_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_x_1586_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
case 5:
{
lean_object* v_x_1631_; lean_object* v_i_1632_; lean_object* v_offset_1633_; lean_object* v_y_1634_; lean_object* v_ty_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_x_1631_ = lean_ctor_get(v_x_1585_, 0);
v_i_1632_ = lean_ctor_get(v_x_1585_, 1);
v_offset_1633_ = lean_ctor_get(v_x_1585_, 2);
v_y_1634_ = lean_ctor_get(v_x_1585_, 3);
v_ty_1635_ = lean_ctor_get(v_x_1585_, 4);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v_x_1585_, 5);
lean_dec(v_unused_1643_);
v___x_1637_ = v_x_1585_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_ty_1635_);
lean_inc(v_y_1634_);
lean_inc(v_offset_1633_);
lean_inc(v_i_1632_);
lean_inc(v_x_1631_);
lean_dec(v_x_1585_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 5, v_x_1586_);
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_x_1631_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_i_1632_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_offset_1633_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_y_1634_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_ty_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 5, v_x_1586_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
case 3:
{
lean_object* v_x_1644_; lean_object* v_cidx_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_x_1644_ = lean_ctor_get(v_x_1585_, 0);
v_cidx_1645_ = lean_ctor_get(v_x_1585_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v_x_1585_, 2);
lean_dec(v_unused_1653_);
v___x_1647_ = v_x_1585_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_cidx_1645_);
lean_inc(v_x_1644_);
lean_dec(v_x_1585_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 2, v_x_1586_);
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_x_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_cidx_1645_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_x_1586_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
case 6:
{
lean_object* v_x_1654_; lean_object* v_n_1655_; uint8_t v_c_1656_; uint8_t v_persistent_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_x_1654_ = lean_ctor_get(v_x_1585_, 0);
v_n_1655_ = lean_ctor_get(v_x_1585_, 1);
v_c_1656_ = lean_ctor_get_uint8(v_x_1585_, sizeof(void*)*3);
v_persistent_1657_ = lean_ctor_get_uint8(v_x_1585_, sizeof(void*)*3 + 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_x_1585_, 2);
lean_dec(v_unused_1665_);
v___x_1659_ = v_x_1585_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_n_1655_);
lean_inc(v_x_1654_);
lean_dec(v_x_1585_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 2, v_x_1586_);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_x_1654_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_n_1655_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_x_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1663_, sizeof(void*)*3, v_c_1656_);
lean_ctor_set_uint8(v_reuseFailAlloc_1663_, sizeof(void*)*3 + 1, v_persistent_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
case 7:
{
lean_object* v_x_1666_; lean_object* v_n_1667_; uint8_t v_c_1668_; uint8_t v_persistent_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_x_1666_ = lean_ctor_get(v_x_1585_, 0);
v_n_1667_ = lean_ctor_get(v_x_1585_, 1);
v_c_1668_ = lean_ctor_get_uint8(v_x_1585_, sizeof(void*)*3);
v_persistent_1669_ = lean_ctor_get_uint8(v_x_1585_, sizeof(void*)*3 + 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_x_1585_, 2);
lean_dec(v_unused_1677_);
v___x_1671_ = v_x_1585_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_n_1667_);
lean_inc(v_x_1666_);
lean_dec(v_x_1585_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 2, v_x_1586_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_x_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_n_1667_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_x_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1675_, sizeof(void*)*3, v_c_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1675_, sizeof(void*)*3 + 1, v_persistent_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
case 8:
{
lean_object* v_x_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_x_1678_ = lean_ctor_get(v_x_1585_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v_x_1585_, 1);
lean_dec(v_unused_1686_);
v___x_1680_ = v_x_1585_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_x_1678_);
lean_dec(v_x_1585_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_x_1586_);
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_x_1678_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_x_1586_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
default: 
{
lean_dec(v_x_1586_);
return v_x_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object* v_b_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_box(12);
v___x_1689_ = l_Lean_IR_FnBody_setBody(v_b_1687_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object* v_b_1690_){
_start:
{
lean_object* v___y_1692_; 
switch(lean_obj_tag(v_b_1690_))
{
case 0:
{
lean_object* v_b_1696_; 
v_b_1696_ = lean_ctor_get(v_b_1690_, 3);
lean_inc(v_b_1696_);
v___y_1692_ = v_b_1696_;
goto v___jp_1691_;
}
case 1:
{
lean_object* v_b_1697_; 
v_b_1697_ = lean_ctor_get(v_b_1690_, 3);
lean_inc(v_b_1697_);
v___y_1692_ = v_b_1697_;
goto v___jp_1691_;
}
case 2:
{
lean_object* v_b_1698_; 
v_b_1698_ = lean_ctor_get(v_b_1690_, 3);
lean_inc(v_b_1698_);
v___y_1692_ = v_b_1698_;
goto v___jp_1691_;
}
case 4:
{
lean_object* v_b_1699_; 
v_b_1699_ = lean_ctor_get(v_b_1690_, 3);
lean_inc(v_b_1699_);
v___y_1692_ = v_b_1699_;
goto v___jp_1691_;
}
case 5:
{
lean_object* v_b_1700_; 
v_b_1700_ = lean_ctor_get(v_b_1690_, 5);
lean_inc(v_b_1700_);
v___y_1692_ = v_b_1700_;
goto v___jp_1691_;
}
case 3:
{
lean_object* v_b_1701_; 
v_b_1701_ = lean_ctor_get(v_b_1690_, 2);
lean_inc(v_b_1701_);
v___y_1692_ = v_b_1701_;
goto v___jp_1691_;
}
case 6:
{
lean_object* v_b_1702_; 
v_b_1702_ = lean_ctor_get(v_b_1690_, 2);
lean_inc(v_b_1702_);
v___y_1692_ = v_b_1702_;
goto v___jp_1691_;
}
case 7:
{
lean_object* v_b_1703_; 
v_b_1703_ = lean_ctor_get(v_b_1690_, 2);
lean_inc(v_b_1703_);
v___y_1692_ = v_b_1703_;
goto v___jp_1691_;
}
case 8:
{
lean_object* v_b_1704_; 
v_b_1704_ = lean_ctor_get(v_b_1690_, 1);
lean_inc(v_b_1704_);
v___y_1692_ = v_b_1704_;
goto v___jp_1691_;
}
default: 
{
lean_inc(v_b_1690_);
v___y_1692_ = v_b_1690_;
goto v___jp_1691_;
}
}
v___jp_1691_:
{
lean_object* v___x_1693_; lean_object* v_c_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_box(12);
v_c_1694_ = l_Lean_IR_FnBody_setBody(v_b_1690_, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_c_1694_);
lean_ctor_set(v___x_1695_, 1, v___y_1692_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
lean_object* v_b_1706_; 
v_b_1706_ = lean_ctor_get(v_x_1705_, 1);
lean_inc(v_b_1706_);
return v_b_1706_;
}
else
{
lean_object* v_b_1707_; 
v_b_1707_ = lean_ctor_get(v_x_1705_, 0);
lean_inc(v_b_1707_);
return v_b_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_IR_Alt_body(v_x_1708_);
lean_dec_ref(v_x_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v_info_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_info_1712_ = lean_ctor_get(v_x_1710_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_x_1710_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v_x_1710_, 1);
lean_dec(v_unused_1720_);
v___x_1714_ = v_x_1710_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_info_1712_);
lean_dec(v_x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_x_1711_);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_info_1712_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_x_1711_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1710_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_x_1710_, 0);
lean_dec(v_unused_1728_);
v___x_1722_ = v_x_1710_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_dec(v_x_1710_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v_x_1711_);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_x_1711_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object* v_f_1729_, lean_object* v_x_1730_){
_start:
{
if (lean_obj_tag(v_x_1730_) == 0)
{
lean_object* v_info_1731_; lean_object* v_b_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_info_1731_ = lean_ctor_get(v_x_1730_, 0);
v_b_1732_ = lean_ctor_get(v_x_1730_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1730_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v_x_1730_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_b_1732_);
lean_inc(v_info_1731_);
lean_dec(v_x_1730_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = lean_apply_1(v_f_1729_, v_b_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_info_1731_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_b_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1749_; 
v_b_1741_ = lean_ctor_get(v_x_1730_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_x_1730_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1743_ = v_x_1730_;
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_b_1741_);
lean_dec(v_x_1730_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_apply_1(v_f_1729_, v_b_1741_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(lean_object* v_info_1750_, lean_object* v_b_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_info_1750_);
lean_ctor_set(v___x_1752_, 1, v_b_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(lean_object* v_b_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_b_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg(lean_object* v_inst_1756_, lean_object* v_f_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v_toApplicative_1759_; 
v_toApplicative_1759_ = lean_ctor_get(v_inst_1756_, 0);
lean_inc_ref(v_toApplicative_1759_);
lean_dec_ref(v_inst_1756_);
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_object* v_toFunctor_1760_; lean_object* v_info_1761_; lean_object* v_b_1762_; lean_object* v_map_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_toFunctor_1760_ = lean_ctor_get(v_toApplicative_1759_, 0);
lean_inc_ref(v_toFunctor_1760_);
lean_dec_ref(v_toApplicative_1759_);
v_info_1761_ = lean_ctor_get(v_x_1758_, 0);
lean_inc_ref(v_info_1761_);
v_b_1762_ = lean_ctor_get(v_x_1758_, 1);
lean_inc(v_b_1762_);
lean_dec_ref(v_x_1758_);
v_map_1763_ = lean_ctor_get(v_toFunctor_1760_, 0);
lean_inc(v_map_1763_);
lean_dec_ref(v_toFunctor_1760_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1764_, 0, v_info_1761_);
v___x_1765_ = lean_apply_1(v_f_1757_, v_b_1762_);
v___x_1766_ = lean_apply_4(v_map_1763_, lean_box(0), lean_box(0), v___f_1764_, v___x_1765_);
return v___x_1766_;
}
else
{
lean_object* v_toFunctor_1767_; lean_object* v_b_1768_; lean_object* v_map_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_toFunctor_1767_ = lean_ctor_get(v_toApplicative_1759_, 0);
lean_inc_ref(v_toFunctor_1767_);
lean_dec_ref(v_toApplicative_1759_);
v_b_1768_ = lean_ctor_get(v_x_1758_, 0);
lean_inc(v_b_1768_);
lean_dec_ref(v_x_1758_);
v_map_1769_ = lean_ctor_get(v_toFunctor_1767_, 0);
lean_inc(v_map_1769_);
lean_dec_ref(v_toFunctor_1767_);
v___f_1770_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_1771_ = lean_apply_1(v_f_1757_, v_b_1768_);
v___x_1772_ = lean_apply_4(v_map_1769_, lean_box(0), lean_box(0), v___f_1770_, v___x_1771_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM(lean_object* v_m_1773_, lean_object* v_inst_1774_, lean_object* v_f_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v_toApplicative_1777_; 
v_toApplicative_1777_ = lean_ctor_get(v_inst_1774_, 0);
lean_inc_ref(v_toApplicative_1777_);
lean_dec_ref(v_inst_1774_);
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v_toFunctor_1778_; lean_object* v_info_1779_; lean_object* v_b_1780_; lean_object* v_map_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_toFunctor_1778_ = lean_ctor_get(v_toApplicative_1777_, 0);
lean_inc_ref(v_toFunctor_1778_);
lean_dec_ref(v_toApplicative_1777_);
v_info_1779_ = lean_ctor_get(v_x_1776_, 0);
lean_inc_ref(v_info_1779_);
v_b_1780_ = lean_ctor_get(v_x_1776_, 1);
lean_inc(v_b_1780_);
lean_dec_ref(v_x_1776_);
v_map_1781_ = lean_ctor_get(v_toFunctor_1778_, 0);
lean_inc(v_map_1781_);
lean_dec_ref(v_toFunctor_1778_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1782_, 0, v_info_1779_);
v___x_1783_ = lean_apply_1(v_f_1775_, v_b_1780_);
v___x_1784_ = lean_apply_4(v_map_1781_, lean_box(0), lean_box(0), v___f_1782_, v___x_1783_);
return v___x_1784_;
}
else
{
lean_object* v_toFunctor_1785_; lean_object* v_b_1786_; lean_object* v_map_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_toFunctor_1785_ = lean_ctor_get(v_toApplicative_1777_, 0);
lean_inc_ref(v_toFunctor_1785_);
lean_dec_ref(v_toApplicative_1777_);
v_b_1786_ = lean_ctor_get(v_x_1776_, 0);
lean_inc(v_b_1786_);
lean_dec_ref(v_x_1776_);
v_map_1787_ = lean_ctor_get(v_toFunctor_1785_, 0);
lean_inc(v_map_1787_);
lean_dec_ref(v_toFunctor_1785_);
v___f_1788_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_1789_ = lean_apply_1(v_f_1775_, v_b_1786_);
v___x_1790_ = lean_apply_4(v_map_1787_, lean_box(0), lean_box(0), v___f_1788_, v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* v_x_1791_){
_start:
{
if (lean_obj_tag(v_x_1791_) == 0)
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
else
{
uint8_t v___x_1793_; 
v___x_1793_ = 1;
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* v_x_1794_){
_start:
{
uint8_t v_res_1795_; lean_object* v_r_1796_; 
v_res_1795_ = l_Lean_IR_Alt_isDefault(v_x_1794_);
lean_dec_ref(v_x_1794_);
v_r_1796_ = lean_box(v_res_1795_);
return v_r_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object* v_bs_1797_, lean_object* v_b_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v_b_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_box(12);
v_b_1800_ = l_Lean_IR_FnBody_setBody(v_b_1798_, v___x_1799_);
v___x_1801_ = lean_array_push(v_bs_1797_, v_b_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object* v_b_1802_, lean_object* v_r_1803_){
_start:
{
lean_object* v___y_1805_; uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_IR_FnBody_isTerminal(v_b_1802_);
if (v___x_1808_ == 0)
{
switch(lean_obj_tag(v_b_1802_))
{
case 0:
{
lean_object* v_b_1809_; 
v_b_1809_ = lean_ctor_get(v_b_1802_, 3);
lean_inc(v_b_1809_);
v___y_1805_ = v_b_1809_;
goto v___jp_1804_;
}
case 1:
{
lean_object* v_b_1810_; 
v_b_1810_ = lean_ctor_get(v_b_1802_, 3);
lean_inc(v_b_1810_);
v___y_1805_ = v_b_1810_;
goto v___jp_1804_;
}
case 2:
{
lean_object* v_b_1811_; 
v_b_1811_ = lean_ctor_get(v_b_1802_, 3);
lean_inc(v_b_1811_);
v___y_1805_ = v_b_1811_;
goto v___jp_1804_;
}
case 4:
{
lean_object* v_b_1812_; 
v_b_1812_ = lean_ctor_get(v_b_1802_, 3);
lean_inc(v_b_1812_);
v___y_1805_ = v_b_1812_;
goto v___jp_1804_;
}
case 5:
{
lean_object* v_b_1813_; 
v_b_1813_ = lean_ctor_get(v_b_1802_, 5);
lean_inc(v_b_1813_);
v___y_1805_ = v_b_1813_;
goto v___jp_1804_;
}
case 3:
{
lean_object* v_b_1814_; 
v_b_1814_ = lean_ctor_get(v_b_1802_, 2);
lean_inc(v_b_1814_);
v___y_1805_ = v_b_1814_;
goto v___jp_1804_;
}
case 6:
{
lean_object* v_b_1815_; 
v_b_1815_ = lean_ctor_get(v_b_1802_, 2);
lean_inc(v_b_1815_);
v___y_1805_ = v_b_1815_;
goto v___jp_1804_;
}
case 7:
{
lean_object* v_b_1816_; 
v_b_1816_ = lean_ctor_get(v_b_1802_, 2);
lean_inc(v_b_1816_);
v___y_1805_ = v_b_1816_;
goto v___jp_1804_;
}
case 8:
{
lean_object* v_b_1817_; 
v_b_1817_ = lean_ctor_get(v_b_1802_, 1);
lean_inc(v_b_1817_);
v___y_1805_ = v_b_1817_;
goto v___jp_1804_;
}
default: 
{
lean_inc(v_b_1802_);
v___y_1805_ = v_b_1802_;
goto v___jp_1804_;
}
}
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_r_1803_);
lean_ctor_set(v___x_1818_, 1, v_b_1802_);
return v___x_1818_;
}
v___jp_1804_:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_IR_push(v_r_1803_, v_b_1802_);
v_b_1802_ = v___y_1805_;
v_r_1803_ = v___x_1806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object* v_b_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_IR_FnBody_flatten___closed__0));
v___x_1823_ = l_Lean_IR_flattenAux(v_b_1821_, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0(lean_object* v___x_1824_, lean_object* v_msg_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_panic_fn_borrowed(v___x_1824_, v_msg_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(lean_object* v___x_1827_, lean_object* v_msg_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_1827_, v_msg_1828_);
lean_dec_ref(v___x_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object* v_a_1834_, lean_object* v_i_1835_, lean_object* v_b_1836_){
_start:
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_nat_dec_eq(v_i_1835_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v_i_1840_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1839_ = lean_unsigned_to_nat(1u);
v_i_1840_ = lean_nat_sub(v_i_1835_, v___x_1839_);
lean_dec(v_i_1835_);
v___x_1846_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_1847_ = lean_array_get_size(v_a_1834_);
v___x_1848_ = lean_nat_dec_lt(v_i_1840_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_fst_1861_; lean_object* v_snd_1862_; 
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1846_);
lean_ctor_set(v___x_1849_, 1, v_a_1834_);
v___x_1850_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__0));
v___x_1851_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__1));
v___x_1852_ = lean_unsigned_to_nat(438u);
v___x_1853_ = lean_unsigned_to_nat(4u);
v___x_1854_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__2));
lean_inc(v_i_1840_);
v___x_1855_ = l_Nat_reprFast(v_i_1840_);
v___x_1856_ = lean_string_append(v___x_1854_, v___x_1855_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__3));
v___x_1858_ = lean_string_append(v___x_1856_, v___x_1857_);
v___x_1859_ = l_mkPanicMessageWithDecl(v___x_1850_, v___x_1851_, v___x_1852_, v___x_1853_, v___x_1858_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = lean_panic_fn_borrowed(v___x_1849_, v___x_1859_);
lean_dec_ref(v___x_1849_);
v_fst_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_fst_1861_);
v_snd_1862_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1862_);
lean_dec(v___x_1860_);
v_fst_1842_ = v_fst_1861_;
v_snd_1843_ = v_snd_1862_;
goto v___jp_1841_;
}
else
{
lean_object* v_e_1863_; lean_object* v_xs_x27_1864_; 
v_e_1863_ = lean_array_fget(v_a_1834_, v_i_1840_);
v_xs_x27_1864_ = lean_array_fset(v_a_1834_, v_i_1840_, v___x_1846_);
v_fst_1842_ = v_e_1863_;
v_snd_1843_ = v_xs_x27_1864_;
goto v___jp_1841_;
}
v___jp_1841_:
{
lean_object* v_b_1844_; 
v_b_1844_ = l_Lean_IR_FnBody_setBody(v_fst_1842_, v_b_1836_);
v_a_1834_ = v_snd_1843_;
v_i_1835_ = v_i_1840_;
v_b_1836_ = v_b_1844_;
goto _start;
}
}
else
{
lean_dec(v_i_1835_);
lean_dec_ref(v_a_1834_);
return v_b_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object* v_bs_1865_, lean_object* v_term_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_array_get_size(v_bs_1865_);
v___x_1868_ = l_Lean_IR_reshapeAux(v_bs_1865_, v___x_1867_, v_term_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object* v_f_1869_, lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 1)
{
lean_object* v_j_1871_; lean_object* v_xs_1872_; lean_object* v_v_1873_; lean_object* v_b_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_j_1871_ = lean_ctor_get(v_x_1870_, 0);
v_xs_1872_ = lean_ctor_get(v_x_1870_, 1);
v_v_1873_ = lean_ctor_get(v_x_1870_, 2);
v_b_1874_ = lean_ctor_get(v_x_1870_, 3);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1876_ = v_x_1870_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_b_1874_);
lean_inc(v_v_1873_);
lean_inc(v_xs_1872_);
lean_inc(v_j_1871_);
lean_dec(v_x_1870_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = lean_apply_1(v_f_1869_, v_v_1873_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 2, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_j_1871_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_xs_1872_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_b_1874_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_dec_ref(v_f_1869_);
return v_x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* v_bs_1902_, lean_object* v_f_1903_){
_start:
{
lean_object* v___f_1904_; lean_object* v___x_1905_; size_t v_sz_1906_; size_t v___x_1907_; lean_object* v___x_1908_; 
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPs___lam__0), 2, 1);
lean_closure_set(v___f_1904_, 0, v_f_1903_);
v___x_1905_ = ((lean_object*)(l_Lean_IR_modifyJPs___closed__9));
v_sz_1906_ = lean_array_size(v_bs_1902_);
v___x_1907_ = ((size_t)0ULL);
v___x_1908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1905_, v___f_1904_, v_sz_1906_, v___x_1907_, v_bs_1902_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__0(lean_object* v_j_1909_, lean_object* v_xs_1910_, lean_object* v_b_1911_, lean_object* v_toPure_1912_, lean_object* v_____do__lift_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1914_, 0, v_j_1909_);
lean_ctor_set(v___x_1914_, 1, v_xs_1910_);
lean_ctor_set(v___x_1914_, 2, v_____do__lift_1913_);
lean_ctor_set(v___x_1914_, 3, v_b_1911_);
v___x_1915_ = lean_apply_2(v_toPure_1912_, lean_box(0), v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__1(lean_object* v_toPure_1916_, lean_object* v_f_1917_, lean_object* v_toBind_1918_, lean_object* v_b_1919_){
_start:
{
if (lean_obj_tag(v_b_1919_) == 1)
{
lean_object* v_j_1920_; lean_object* v_xs_1921_; lean_object* v_v_1922_; lean_object* v_b_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_j_1920_ = lean_ctor_get(v_b_1919_, 0);
lean_inc(v_j_1920_);
v_xs_1921_ = lean_ctor_get(v_b_1919_, 1);
lean_inc_ref(v_xs_1921_);
v_v_1922_ = lean_ctor_get(v_b_1919_, 2);
lean_inc(v_v_1922_);
v_b_1923_ = lean_ctor_get(v_b_1919_, 3);
lean_inc(v_b_1923_);
lean_dec_ref(v_b_1919_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1924_, 0, v_j_1920_);
lean_closure_set(v___f_1924_, 1, v_xs_1921_);
lean_closure_set(v___f_1924_, 2, v_b_1923_);
lean_closure_set(v___f_1924_, 3, v_toPure_1916_);
v___x_1925_ = lean_apply_1(v_f_1917_, v_v_1922_);
v___x_1926_ = lean_apply_4(v_toBind_1918_, lean_box(0), lean_box(0), v___x_1925_, v___f_1924_);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; 
lean_dec(v_toBind_1918_);
lean_dec(v_f_1917_);
v___x_1927_ = lean_apply_2(v_toPure_1916_, lean_box(0), v_b_1919_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg(lean_object* v_inst_1928_, lean_object* v_bs_1929_, lean_object* v_f_1930_){
_start:
{
lean_object* v_toApplicative_1931_; lean_object* v_toBind_1932_; lean_object* v_toPure_1933_; lean_object* v___f_1934_; size_t v_sz_1935_; size_t v___x_1936_; lean_object* v___x_1937_; 
v_toApplicative_1931_ = lean_ctor_get(v_inst_1928_, 0);
v_toBind_1932_ = lean_ctor_get(v_inst_1928_, 1);
v_toPure_1933_ = lean_ctor_get(v_toApplicative_1931_, 1);
lean_inc(v_toBind_1932_);
lean_inc(v_toPure_1933_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1934_, 0, v_toPure_1933_);
lean_closure_set(v___f_1934_, 1, v_f_1930_);
lean_closure_set(v___f_1934_, 2, v_toBind_1932_);
v_sz_1935_ = lean_array_size(v_bs_1929_);
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1928_, v___f_1934_, v_sz_1935_, v___x_1936_, v_bs_1929_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM(lean_object* v_m_1938_, lean_object* v_inst_1939_, lean_object* v_bs_1940_, lean_object* v_f_1941_){
_start:
{
lean_object* v_toApplicative_1942_; lean_object* v_toBind_1943_; lean_object* v_toPure_1944_; lean_object* v___f_1945_; size_t v_sz_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v_toApplicative_1942_ = lean_ctor_get(v_inst_1939_, 0);
v_toBind_1943_ = lean_ctor_get(v_inst_1939_, 1);
v_toPure_1944_ = lean_ctor_get(v_toApplicative_1942_, 1);
lean_inc(v_toBind_1943_);
lean_inc(v_toPure_1944_);
v___f_1945_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1945_, 0, v_toPure_1944_);
lean_closure_set(v___f_1945_, 1, v_f_1941_);
lean_closure_set(v___f_1945_, 2, v_toBind_1943_);
v_sz_1946_ = lean_array_size(v_bs_1940_);
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1939_, v___f_1945_, v_sz_1946_, v___x_1947_, v_bs_1940_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx(lean_object* v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_unsigned_to_nat(0u);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_unsigned_to_nat(1u);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___boxed(lean_object* v_x_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_IR_Decl_ctorIdx(v_x_1952_);
lean_dec_ref(v_x_1952_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___redArg(lean_object* v_t_1954_, lean_object* v_k_1955_){
_start:
{
if (lean_obj_tag(v_t_1954_) == 0)
{
lean_object* v_f_1956_; lean_object* v_xs_1957_; lean_object* v_type_1958_; lean_object* v_body_1959_; lean_object* v_info_1960_; lean_object* v___x_1961_; 
v_f_1956_ = lean_ctor_get(v_t_1954_, 0);
lean_inc(v_f_1956_);
v_xs_1957_ = lean_ctor_get(v_t_1954_, 1);
lean_inc_ref(v_xs_1957_);
v_type_1958_ = lean_ctor_get(v_t_1954_, 2);
lean_inc(v_type_1958_);
v_body_1959_ = lean_ctor_get(v_t_1954_, 3);
lean_inc(v_body_1959_);
v_info_1960_ = lean_ctor_get(v_t_1954_, 4);
lean_inc(v_info_1960_);
lean_dec_ref(v_t_1954_);
v___x_1961_ = lean_apply_5(v_k_1955_, v_f_1956_, v_xs_1957_, v_type_1958_, v_body_1959_, v_info_1960_);
return v___x_1961_;
}
else
{
lean_object* v_f_1962_; lean_object* v_xs_1963_; lean_object* v_type_1964_; lean_object* v_ext_1965_; lean_object* v___x_1966_; 
v_f_1962_ = lean_ctor_get(v_t_1954_, 0);
lean_inc(v_f_1962_);
v_xs_1963_ = lean_ctor_get(v_t_1954_, 1);
lean_inc_ref(v_xs_1963_);
v_type_1964_ = lean_ctor_get(v_t_1954_, 2);
lean_inc(v_type_1964_);
v_ext_1965_ = lean_ctor_get(v_t_1954_, 3);
lean_inc(v_ext_1965_);
lean_dec_ref(v_t_1954_);
v___x_1966_ = lean_apply_4(v_k_1955_, v_f_1962_, v_xs_1963_, v_type_1964_, v_ext_1965_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim(lean_object* v_motive_1967_, lean_object* v_ctorIdx_1968_, lean_object* v_t_1969_, lean_object* v_h_1970_, lean_object* v_k_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1969_, v_k_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___boxed(lean_object* v_motive_1973_, lean_object* v_ctorIdx_1974_, lean_object* v_t_1975_, lean_object* v_h_1976_, lean_object* v_k_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_IR_Decl_ctorElim(v_motive_1973_, v_ctorIdx_1974_, v_t_1975_, v_h_1976_, v_k_1977_);
lean_dec(v_ctorIdx_1974_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim___redArg(lean_object* v_t_1979_, lean_object* v_fdecl_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1979_, v_fdecl_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim(lean_object* v_motive_1982_, lean_object* v_t_1983_, lean_object* v_h_1984_, lean_object* v_fdecl_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1983_, v_fdecl_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim___redArg(lean_object* v_t_1987_, lean_object* v_extern_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1987_, v_extern_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim(lean_object* v_motive_1990_, lean_object* v_t_1991_, lean_object* v_h_1992_, lean_object* v_extern_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1991_, v_extern_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object* v_x_2004_){
_start:
{
lean_object* v_f_2005_; 
v_f_2005_ = lean_ctor_get(v_x_2004_, 0);
lean_inc(v_f_2005_);
return v_f_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object* v_x_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_IR_Decl_name(v_x_2006_);
lean_dec_ref(v_x_2006_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object* v_x_2008_){
_start:
{
lean_object* v_xs_2009_; 
v_xs_2009_ = lean_ctor_get(v_x_2008_, 1);
lean_inc_ref(v_xs_2009_);
return v_xs_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object* v_x_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_IR_Decl_params(v_x_2010_);
lean_dec_ref(v_x_2010_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object* v_x_2012_){
_start:
{
lean_object* v_type_2013_; 
v_type_2013_ = lean_ctor_get(v_x_2012_, 2);
lean_inc(v_type_2013_);
return v_type_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_IR_Decl_resultType(v_x_2014_);
lean_dec_ref(v_x_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object* v_x_2016_){
_start:
{
if (lean_obj_tag(v_x_2016_) == 1)
{
uint8_t v___x_2017_; 
v___x_2017_ = 1;
return v___x_2017_;
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = 0;
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* v_x_2019_){
_start:
{
uint8_t v_res_2020_; lean_object* v_r_2021_; 
v_res_2020_ = l_Lean_IR_Decl_isExtern(v_x_2019_);
lean_dec_ref(v_x_2019_);
v_r_2021_ = lean_box(v_res_2020_);
return v_r_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* v_x_2022_){
_start:
{
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v_info_2023_; 
v_info_2023_ = lean_ctor_get(v_x_2022_, 4);
lean_inc(v_info_2023_);
return v_info_2023_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_box(0);
return v___x_2024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* v_x_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_IR_Decl_getInfo(v_x_2025_);
lean_dec_ref(v_x_2025_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object* v_msg_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_IR_instInhabitedDecl_default));
v___x_2029_ = lean_panic_fn_borrowed(v___x_2028_, v_msg_2027_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__3(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2033_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__2));
v___x_2034_ = lean_unsigned_to_nat(9u);
v___x_2035_ = lean_unsigned_to_nat(382u);
v___x_2036_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__1));
v___x_2037_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__0));
v___x_2038_ = l_mkPanicMessageWithDecl(v___x_2037_, v___x_2036_, v___x_2035_, v___x_2034_, v___x_2033_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* v_d_2039_, lean_object* v_bNew_2040_){
_start:
{
if (lean_obj_tag(v_d_2039_) == 0)
{
lean_object* v_f_2041_; lean_object* v_xs_2042_; lean_object* v_type_2043_; lean_object* v_info_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_f_2041_ = lean_ctor_get(v_d_2039_, 0);
v_xs_2042_ = lean_ctor_get(v_d_2039_, 1);
v_type_2043_ = lean_ctor_get(v_d_2039_, 2);
v_info_2044_ = lean_ctor_get(v_d_2039_, 4);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_d_2039_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v_d_2039_, 3);
lean_dec(v_unused_2052_);
v___x_2046_ = v_d_2039_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_info_2044_);
lean_inc(v_type_2043_);
lean_inc(v_xs_2042_);
lean_inc(v_f_2041_);
lean_dec(v_d_2039_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 3, v_bNew_2040_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_f_2041_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_xs_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_type_2043_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_bNew_2040_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_info_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec(v_bNew_2040_);
lean_dec_ref(v_d_2039_);
v___x_2053_ = lean_obj_once(&l_Lean_IR_Decl_updateBody_x21___closed__3, &l_Lean_IR_Decl_updateBody_x21___closed__3_once, _init_l_Lean_IR_Decl_updateBody_x21___closed__3);
v___x_2054_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_2053_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object* v_f_2055_, lean_object* v_xs_2056_, lean_object* v_ty_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_box(12);
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2060_, 0, v_f_2055_);
lean_ctor_set(v___x_2060_, 1, v_xs_2056_);
lean_ctor_set(v___x_2060_, 2, v_ty_2057_);
lean_ctor_set(v___x_2060_, 3, v___x_2058_);
lean_ctor_set(v___x_2060_, 4, v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object* v_k_2061_, lean_object* v_v_2062_, lean_object* v_t_2063_){
_start:
{
if (lean_obj_tag(v_t_2063_) == 0)
{
lean_object* v_size_2064_; lean_object* v_k_2065_; lean_object* v_v_2066_; lean_object* v_l_2067_; lean_object* v_r_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2349_; 
v_size_2064_ = lean_ctor_get(v_t_2063_, 0);
v_k_2065_ = lean_ctor_get(v_t_2063_, 1);
v_v_2066_ = lean_ctor_get(v_t_2063_, 2);
v_l_2067_ = lean_ctor_get(v_t_2063_, 3);
v_r_2068_ = lean_ctor_get(v_t_2063_, 4);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_t_2063_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2070_ = v_t_2063_;
v_isShared_2071_ = v_isSharedCheck_2349_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_r_2068_);
lean_inc(v_l_2067_);
lean_inc(v_v_2066_);
lean_inc(v_k_2065_);
lean_inc(v_size_2064_);
lean_dec(v_t_2063_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2349_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_nat_dec_lt(v_k_2061_, v_k_2065_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_nat_dec_eq(v_k_2061_, v_k_2065_);
if (v___x_2073_ == 0)
{
lean_object* v_impl_2074_; lean_object* v___x_2075_; 
lean_dec(v_size_2064_);
v_impl_2074_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2061_, v_v_2062_, v_r_2068_);
v___x_2075_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2067_) == 0)
{
lean_object* v_size_2076_; lean_object* v_size_2077_; lean_object* v_k_2078_; lean_object* v_v_2079_; lean_object* v_l_2080_; lean_object* v_r_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_size_2076_ = lean_ctor_get(v_l_2067_, 0);
v_size_2077_ = lean_ctor_get(v_impl_2074_, 0);
lean_inc(v_size_2077_);
v_k_2078_ = lean_ctor_get(v_impl_2074_, 1);
lean_inc(v_k_2078_);
v_v_2079_ = lean_ctor_get(v_impl_2074_, 2);
lean_inc(v_v_2079_);
v_l_2080_ = lean_ctor_get(v_impl_2074_, 3);
lean_inc(v_l_2080_);
v_r_2081_ = lean_ctor_get(v_impl_2074_, 4);
lean_inc(v_r_2081_);
v___x_2082_ = lean_unsigned_to_nat(3u);
v___x_2083_ = lean_nat_mul(v___x_2082_, v_size_2076_);
v___x_2084_ = lean_nat_dec_lt(v___x_2083_, v_size_2077_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec(v_r_2081_);
lean_dec(v_l_2080_);
lean_dec(v_v_2079_);
lean_dec(v_k_2078_);
v___x_2085_ = lean_nat_add(v___x_2075_, v_size_2076_);
v___x_2086_ = lean_nat_add(v___x_2085_, v_size_2077_);
lean_dec(v_size_2077_);
lean_dec(v___x_2085_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_impl_2074_);
lean_ctor_set(v___x_2070_, 0, v___x_2086_);
v___x_2088_ = v___x_2070_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_impl_2074_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
else
{
lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2153_; 
v_isSharedCheck_2153_ = !lean_is_exclusive(v_impl_2074_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2154_ = lean_ctor_get(v_impl_2074_, 4);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_impl_2074_, 3);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_impl_2074_, 2);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_impl_2074_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_impl_2074_, 0);
lean_dec(v_unused_2158_);
v___x_2091_ = v_impl_2074_;
v_isShared_2092_ = v_isSharedCheck_2153_;
goto v_resetjp_2090_;
}
else
{
lean_dec(v_impl_2074_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2153_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_size_2093_; lean_object* v_k_2094_; lean_object* v_v_2095_; lean_object* v_l_2096_; lean_object* v_r_2097_; lean_object* v_size_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_size_2093_ = lean_ctor_get(v_l_2080_, 0);
v_k_2094_ = lean_ctor_get(v_l_2080_, 1);
v_v_2095_ = lean_ctor_get(v_l_2080_, 2);
v_l_2096_ = lean_ctor_get(v_l_2080_, 3);
v_r_2097_ = lean_ctor_get(v_l_2080_, 4);
v_size_2098_ = lean_ctor_get(v_r_2081_, 0);
v___x_2099_ = lean_unsigned_to_nat(2u);
v___x_2100_ = lean_nat_mul(v___x_2099_, v_size_2098_);
v___x_2101_ = lean_nat_dec_lt(v_size_2093_, v___x_2100_);
lean_dec(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2129_; 
lean_inc(v_r_2097_);
lean_inc(v_l_2096_);
lean_inc(v_v_2095_);
lean_inc(v_k_2094_);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_l_2080_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; lean_object* v_unused_2134_; 
v_unused_2130_ = lean_ctor_get(v_l_2080_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_2080_, 3);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_2080_, 2);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_l_2080_, 1);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_l_2080_, 0);
lean_dec(v_unused_2134_);
v___x_2103_ = v_l_2080_;
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_l_2080_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2119_; 
v___x_2105_ = lean_nat_add(v___x_2075_, v_size_2076_);
v___x_2106_ = lean_nat_add(v___x_2105_, v_size_2077_);
lean_dec(v_size_2077_);
if (lean_obj_tag(v_l_2096_) == 0)
{
lean_object* v_size_2127_; 
v_size_2127_ = lean_ctor_get(v_l_2096_, 0);
lean_inc(v_size_2127_);
v___y_2119_ = v_size_2127_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_unsigned_to_nat(0u);
v___y_2119_ = v___x_2128_;
goto v___jp_2118_;
}
v___jp_2107_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_nat_add(v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec(v___y_2109_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v_r_2081_);
lean_ctor_set(v___x_2103_, 3, v_r_2097_);
lean_ctor_set(v___x_2103_, 2, v_v_2079_);
lean_ctor_set(v___x_2103_, 1, v_k_2078_);
lean_ctor_set(v___x_2103_, 0, v___x_2111_);
v___x_2113_ = v___x_2103_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_r_2097_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_r_2081_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v___x_2113_);
lean_ctor_set(v___x_2091_, 3, v___y_2108_);
lean_ctor_set(v___x_2091_, 2, v_v_2095_);
lean_ctor_set(v___x_2091_, 1, v_k_2094_);
lean_ctor_set(v___x_2091_, 0, v___x_2106_);
v___x_2115_ = v___x_2091_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2094_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2095_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v___y_2108_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
v___jp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_nat_add(v___x_2105_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec(v___x_2105_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_l_2096_);
lean_ctor_set(v___x_2070_, 0, v___x_2120_);
v___x_2122_ = v___x_2070_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_l_2096_);
v___x_2122_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_nat_add(v___x_2075_, v_size_2098_);
if (lean_obj_tag(v_r_2097_) == 0)
{
lean_object* v_size_2124_; 
v_size_2124_ = lean_ctor_get(v_r_2097_, 0);
lean_inc(v_size_2124_);
v___y_2108_ = v___x_2122_;
v___y_2109_ = v___x_2123_;
v___y_2110_ = v_size_2124_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___y_2108_ = v___x_2122_;
v___y_2109_ = v___x_2123_;
v___y_2110_ = v___x_2125_;
goto v___jp_2107_;
}
}
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_del_object(v___x_2070_);
v___x_2135_ = lean_nat_add(v___x_2075_, v_size_2076_);
v___x_2136_ = lean_nat_add(v___x_2135_, v_size_2077_);
lean_dec(v_size_2077_);
v___x_2137_ = lean_nat_add(v___x_2135_, v_size_2093_);
lean_dec(v___x_2135_);
lean_inc_ref(v_l_2067_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v_l_2080_);
lean_ctor_set(v___x_2091_, 3, v_l_2067_);
lean_ctor_set(v___x_2091_, 2, v_v_2066_);
lean_ctor_set(v___x_2091_, 1, v_k_2065_);
lean_ctor_set(v___x_2091_, 0, v___x_2137_);
v___x_2139_ = v___x_2091_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_l_2080_);
v___x_2139_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v_l_2067_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2147_ = lean_ctor_get(v_l_2067_, 4);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2067_, 3);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2067_, 2);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2067_, 1);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_l_2067_, 0);
lean_dec(v_unused_2151_);
v___x_2141_ = v_l_2067_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_l_2067_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_r_2081_);
lean_ctor_set(v___x_2141_, 3, v___x_2139_);
lean_ctor_set(v___x_2141_, 2, v_v_2079_);
lean_ctor_set(v___x_2141_, 1, v_k_2078_);
lean_ctor_set(v___x_2141_, 0, v___x_2136_);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_r_2081_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2159_; 
v_l_2159_ = lean_ctor_get(v_impl_2074_, 3);
lean_inc(v_l_2159_);
if (lean_obj_tag(v_l_2159_) == 0)
{
lean_object* v_r_2160_; lean_object* v_k_2161_; lean_object* v_v_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2185_; 
v_r_2160_ = lean_ctor_get(v_impl_2074_, 4);
v_k_2161_ = lean_ctor_get(v_impl_2074_, 1);
v_v_2162_ = lean_ctor_get(v_impl_2074_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_impl_2074_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; lean_object* v_unused_2187_; 
v_unused_2186_ = lean_ctor_get(v_impl_2074_, 3);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_impl_2074_, 0);
lean_dec(v_unused_2187_);
v___x_2164_ = v_impl_2074_;
v_isShared_2165_ = v_isSharedCheck_2185_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_r_2160_);
lean_inc(v_v_2162_);
lean_inc(v_k_2161_);
lean_dec(v_impl_2074_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2185_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_k_2166_; lean_object* v_v_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2181_; 
v_k_2166_ = lean_ctor_get(v_l_2159_, 1);
v_v_2167_ = lean_ctor_get(v_l_2159_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_l_2159_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2182_ = lean_ctor_get(v_l_2159_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_2159_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_2159_, 0);
lean_dec(v_unused_2184_);
v___x_2169_ = v_l_2159_;
v_isShared_2170_ = v_isSharedCheck_2181_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_v_2167_);
lean_inc(v_k_2166_);
lean_dec(v_l_2159_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2181_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2160_, 2);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 4, v_r_2160_);
lean_ctor_set(v___x_2169_, 3, v_r_2160_);
lean_ctor_set(v___x_2169_, 2, v_v_2066_);
lean_ctor_set(v___x_2169_, 1, v_k_2065_);
lean_ctor_set(v___x_2169_, 0, v___x_2075_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_r_2160_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_r_2160_);
v___x_2173_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
lean_inc(v_r_2160_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 3, v_r_2160_);
lean_ctor_set(v___x_2164_, 0, v___x_2075_);
v___x_2175_ = v___x_2164_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_k_2161_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2162_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_r_2160_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_r_2160_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2175_);
lean_ctor_set(v___x_2070_, 3, v___x_2173_);
lean_ctor_set(v___x_2070_, 2, v_v_2167_);
lean_ctor_set(v___x_2070_, 1, v_k_2166_);
lean_ctor_set(v___x_2070_, 0, v___x_2171_);
v___x_2177_ = v___x_2070_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
else
{
lean_object* v_r_2188_; 
v_r_2188_ = lean_ctor_get(v_impl_2074_, 4);
lean_inc(v_r_2188_);
if (lean_obj_tag(v_r_2188_) == 0)
{
lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2201_; 
v_k_2189_ = lean_ctor_get(v_impl_2074_, 1);
v_v_2190_ = lean_ctor_get(v_impl_2074_, 2);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_impl_2074_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; lean_object* v_unused_2203_; lean_object* v_unused_2204_; 
v_unused_2202_ = lean_ctor_get(v_impl_2074_, 4);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_impl_2074_, 3);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_impl_2074_, 0);
lean_dec(v_unused_2204_);
v___x_2192_ = v_impl_2074_;
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_v_2190_);
lean_inc(v_k_2189_);
lean_dec(v_impl_2074_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 4, v_l_2159_);
lean_ctor_set(v___x_2192_, 2, v_v_2066_);
lean_ctor_set(v___x_2192_, 1, v_k_2065_);
lean_ctor_set(v___x_2192_, 0, v___x_2075_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_2159_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_l_2159_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_r_2188_);
lean_ctor_set(v___x_2070_, 3, v___x_2196_);
lean_ctor_set(v___x_2070_, 2, v_v_2190_);
lean_ctor_set(v___x_2070_, 1, v_k_2189_);
lean_ctor_set(v___x_2070_, 0, v___x_2194_);
v___x_2198_ = v___x_2070_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2189_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2190_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_r_2188_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(2u);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_impl_2074_);
lean_ctor_set(v___x_2070_, 3, v_r_2188_);
lean_ctor_set(v___x_2070_, 0, v___x_2205_);
v___x_2207_ = v___x_2070_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_r_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_impl_2074_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v___x_2210_; 
lean_dec(v_v_2066_);
lean_dec(v_k_2065_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 2, v_v_2062_);
lean_ctor_set(v___x_2070_, 1, v_k_2061_);
v___x_2210_ = v___x_2070_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_size_2064_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_2061_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_2062_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_l_2067_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_r_2068_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_impl_2212_; lean_object* v___x_2213_; 
lean_dec(v_size_2064_);
v_impl_2212_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2061_, v_v_2062_, v_l_2067_);
v___x_2213_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2068_) == 0)
{
lean_object* v_size_2214_; lean_object* v_size_2215_; lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v_l_2218_; lean_object* v_r_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_size_2214_ = lean_ctor_get(v_r_2068_, 0);
v_size_2215_ = lean_ctor_get(v_impl_2212_, 0);
lean_inc(v_size_2215_);
v_k_2216_ = lean_ctor_get(v_impl_2212_, 1);
lean_inc(v_k_2216_);
v_v_2217_ = lean_ctor_get(v_impl_2212_, 2);
lean_inc(v_v_2217_);
v_l_2218_ = lean_ctor_get(v_impl_2212_, 3);
lean_inc(v_l_2218_);
v_r_2219_ = lean_ctor_get(v_impl_2212_, 4);
lean_inc(v_r_2219_);
v___x_2220_ = lean_unsigned_to_nat(3u);
v___x_2221_ = lean_nat_mul(v___x_2220_, v_size_2214_);
v___x_2222_ = lean_nat_dec_lt(v___x_2221_, v_size_2215_);
lean_dec(v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_dec(v_r_2219_);
lean_dec(v_l_2218_);
lean_dec(v_v_2217_);
lean_dec(v_k_2216_);
v___x_2223_ = lean_nat_add(v___x_2213_, v_size_2215_);
lean_dec(v_size_2215_);
v___x_2224_ = lean_nat_add(v___x_2223_, v_size_2214_);
lean_dec(v___x_2223_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 3, v_impl_2212_);
lean_ctor_set(v___x_2070_, 0, v___x_2224_);
v___x_2226_ = v___x_2070_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_impl_2212_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_r_2068_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2293_; 
v_isSharedCheck_2293_ = !lean_is_exclusive(v_impl_2212_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; lean_object* v_unused_2297_; lean_object* v_unused_2298_; 
v_unused_2294_ = lean_ctor_get(v_impl_2212_, 4);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_impl_2212_, 3);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_impl_2212_, 2);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_impl_2212_, 1);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_impl_2212_, 0);
lean_dec(v_unused_2298_);
v___x_2229_ = v_impl_2212_;
v_isShared_2230_ = v_isSharedCheck_2293_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v_impl_2212_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2293_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_size_2231_; lean_object* v_size_2232_; lean_object* v_k_2233_; lean_object* v_v_2234_; lean_object* v_l_2235_; lean_object* v_r_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_size_2231_ = lean_ctor_get(v_l_2218_, 0);
v_size_2232_ = lean_ctor_get(v_r_2219_, 0);
v_k_2233_ = lean_ctor_get(v_r_2219_, 1);
v_v_2234_ = lean_ctor_get(v_r_2219_, 2);
v_l_2235_ = lean_ctor_get(v_r_2219_, 3);
v_r_2236_ = lean_ctor_get(v_r_2219_, 4);
v___x_2237_ = lean_unsigned_to_nat(2u);
v___x_2238_ = lean_nat_mul(v___x_2237_, v_size_2231_);
v___x_2239_ = lean_nat_dec_lt(v_size_2232_, v___x_2238_);
lean_dec(v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2268_; 
lean_inc(v_r_2236_);
lean_inc(v_l_2235_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_r_2219_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; lean_object* v_unused_2272_; lean_object* v_unused_2273_; 
v_unused_2269_ = lean_ctor_get(v_r_2219_, 4);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_r_2219_, 3);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_r_2219_, 2);
lean_dec(v_unused_2271_);
v_unused_2272_ = lean_ctor_get(v_r_2219_, 1);
lean_dec(v_unused_2272_);
v_unused_2273_ = lean_ctor_get(v_r_2219_, 0);
lean_dec(v_unused_2273_);
v___x_2241_ = v_r_2219_;
v_isShared_2242_ = v_isSharedCheck_2268_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v_r_2219_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2268_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___x_2256_; lean_object* v___y_2258_; 
v___x_2243_ = lean_nat_add(v___x_2213_, v_size_2215_);
lean_dec(v_size_2215_);
v___x_2244_ = lean_nat_add(v___x_2243_, v_size_2214_);
lean_dec(v___x_2243_);
v___x_2256_ = lean_nat_add(v___x_2213_, v_size_2231_);
if (lean_obj_tag(v_l_2235_) == 0)
{
lean_object* v_size_2266_; 
v_size_2266_ = lean_ctor_get(v_l_2235_, 0);
lean_inc(v_size_2266_);
v___y_2258_ = v_size_2266_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___y_2258_ = v___x_2267_;
goto v___jp_2257_;
}
v___jp_2245_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_nat_add(v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec(v___y_2247_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v_r_2068_);
lean_ctor_set(v___x_2241_, 3, v_r_2236_);
lean_ctor_set(v___x_2241_, 2, v_v_2066_);
lean_ctor_set(v___x_2241_, 1, v_k_2065_);
lean_ctor_set(v___x_2241_, 0, v___x_2249_);
v___x_2251_ = v___x_2241_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2255_, 4, v_r_2068_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 4, v___x_2251_);
lean_ctor_set(v___x_2229_, 3, v___y_2246_);
lean_ctor_set(v___x_2229_, 2, v_v_2234_);
lean_ctor_set(v___x_2229_, 1, v_k_2233_);
lean_ctor_set(v___x_2229_, 0, v___x_2244_);
v___x_2253_ = v___x_2229_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v___y_2246_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
v___jp_2257_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = lean_nat_add(v___x_2256_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec(v___x_2256_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_l_2235_);
lean_ctor_set(v___x_2070_, 3, v_l_2218_);
lean_ctor_set(v___x_2070_, 2, v_v_2217_);
lean_ctor_set(v___x_2070_, 1, v_k_2216_);
lean_ctor_set(v___x_2070_, 0, v___x_2259_);
v___x_2261_ = v___x_2070_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_l_2218_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_l_2235_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_nat_add(v___x_2213_, v_size_2214_);
if (lean_obj_tag(v_r_2236_) == 0)
{
lean_object* v_size_2263_; 
v_size_2263_ = lean_ctor_get(v_r_2236_, 0);
lean_inc(v_size_2263_);
v___y_2246_ = v___x_2261_;
v___y_2247_ = v___x_2262_;
v___y_2248_ = v_size_2263_;
goto v___jp_2245_;
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___y_2246_ = v___x_2261_;
v___y_2247_ = v___x_2262_;
v___y_2248_ = v___x_2264_;
goto v___jp_2245_;
}
}
}
}
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
lean_del_object(v___x_2070_);
v___x_2274_ = lean_nat_add(v___x_2213_, v_size_2215_);
lean_dec(v_size_2215_);
v___x_2275_ = lean_nat_add(v___x_2274_, v_size_2214_);
lean_dec(v___x_2274_);
v___x_2276_ = lean_nat_add(v___x_2213_, v_size_2214_);
v___x_2277_ = lean_nat_add(v___x_2276_, v_size_2232_);
lean_dec(v___x_2276_);
lean_inc_ref(v_r_2068_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 4, v_r_2068_);
lean_ctor_set(v___x_2229_, 3, v_r_2219_);
lean_ctor_set(v___x_2229_, 2, v_v_2066_);
lean_ctor_set(v___x_2229_, 1, v_k_2065_);
lean_ctor_set(v___x_2229_, 0, v___x_2277_);
v___x_2279_ = v___x_2229_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_r_2219_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_r_2068_);
v___x_2279_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
v_isSharedCheck_2286_ = !lean_is_exclusive(v_r_2068_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; lean_object* v_unused_2291_; 
v_unused_2287_ = lean_ctor_get(v_r_2068_, 4);
lean_dec(v_unused_2287_);
v_unused_2288_ = lean_ctor_get(v_r_2068_, 3);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_r_2068_, 2);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_r_2068_, 1);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_r_2068_, 0);
lean_dec(v_unused_2291_);
v___x_2281_ = v_r_2068_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_r_2068_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v___x_2279_);
lean_ctor_set(v___x_2281_, 3, v_l_2218_);
lean_ctor_set(v___x_2281_, 2, v_v_2217_);
lean_ctor_set(v___x_2281_, 1, v_k_2216_);
lean_ctor_set(v___x_2281_, 0, v___x_2275_);
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_l_2218_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v___x_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2299_; 
v_l_2299_ = lean_ctor_get(v_impl_2212_, 3);
lean_inc(v_l_2299_);
if (lean_obj_tag(v_l_2299_) == 0)
{
lean_object* v_r_2300_; lean_object* v_k_2301_; lean_object* v_v_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2313_; 
v_r_2300_ = lean_ctor_get(v_impl_2212_, 4);
v_k_2301_ = lean_ctor_get(v_impl_2212_, 1);
v_v_2302_ = lean_ctor_get(v_impl_2212_, 2);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_impl_2212_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2314_ = lean_ctor_get(v_impl_2212_, 3);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_impl_2212_, 0);
lean_dec(v_unused_2315_);
v___x_2304_ = v_impl_2212_;
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_r_2300_);
lean_inc(v_v_2302_);
lean_inc(v_k_2301_);
lean_dec(v_impl_2212_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2313_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2300_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 3, v_r_2300_);
lean_ctor_set(v___x_2304_, 2, v_v_2066_);
lean_ctor_set(v___x_2304_, 1, v_k_2065_);
lean_ctor_set(v___x_2304_, 0, v___x_2213_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_r_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_r_2300_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2308_);
lean_ctor_set(v___x_2070_, 3, v_l_2299_);
lean_ctor_set(v___x_2070_, 2, v_v_2302_);
lean_ctor_set(v___x_2070_, 1, v_k_2301_);
lean_ctor_set(v___x_2070_, 0, v___x_2306_);
v___x_2310_ = v___x_2070_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_2301_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_2302_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_l_2299_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_r_2316_; 
v_r_2316_ = lean_ctor_get(v_impl_2212_, 4);
lean_inc(v_r_2316_);
if (lean_obj_tag(v_r_2316_) == 0)
{
lean_object* v_k_2317_; lean_object* v_v_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2341_; 
v_k_2317_ = lean_ctor_get(v_impl_2212_, 1);
v_v_2318_ = lean_ctor_get(v_impl_2212_, 2);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_impl_2212_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; lean_object* v_unused_2343_; lean_object* v_unused_2344_; 
v_unused_2342_ = lean_ctor_get(v_impl_2212_, 4);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_impl_2212_, 3);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_impl_2212_, 0);
lean_dec(v_unused_2344_);
v___x_2320_ = v_impl_2212_;
v_isShared_2321_ = v_isSharedCheck_2341_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_v_2318_);
lean_inc(v_k_2317_);
lean_dec(v_impl_2212_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2341_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_k_2322_; lean_object* v_v_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_k_2322_ = lean_ctor_get(v_r_2316_, 1);
v_v_2323_ = lean_ctor_get(v_r_2316_, 2);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_r_2316_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; lean_object* v_unused_2339_; lean_object* v_unused_2340_; 
v_unused_2338_ = lean_ctor_get(v_r_2316_, 4);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_2316_, 3);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_r_2316_, 0);
lean_dec(v_unused_2340_);
v___x_2325_ = v_r_2316_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_v_2323_);
lean_inc(v_k_2322_);
lean_dec(v_r_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(3u);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v_l_2299_);
lean_ctor_set(v___x_2325_, 3, v_l_2299_);
lean_ctor_set(v___x_2325_, 2, v_v_2318_);
lean_ctor_set(v___x_2325_, 1, v_k_2317_);
lean_ctor_set(v___x_2325_, 0, v___x_2213_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2317_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2318_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_l_2299_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_l_2299_);
v___x_2329_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 4, v_l_2299_);
lean_ctor_set(v___x_2320_, 2, v_v_2066_);
lean_ctor_set(v___x_2320_, 1, v_k_2065_);
lean_ctor_set(v___x_2320_, 0, v___x_2213_);
v___x_2331_ = v___x_2320_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2299_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_l_2299_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2331_);
lean_ctor_set(v___x_2070_, 3, v___x_2329_);
lean_ctor_set(v___x_2070_, 2, v_v_2323_);
lean_ctor_set(v___x_2070_, 1, v_k_2322_);
lean_ctor_set(v___x_2070_, 0, v___x_2327_);
v___x_2333_ = v___x_2070_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_unsigned_to_nat(2u);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_r_2316_);
lean_ctor_set(v___x_2070_, 3, v_impl_2212_);
lean_ctor_set(v___x_2070_, 0, v___x_2345_);
v___x_2347_ = v___x_2070_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_impl_2212_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_r_2316_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v_k_2061_);
lean_ctor_set(v___x_2351_, 2, v_v_2062_);
lean_ctor_set(v___x_2351_, 3, v_t_2063_);
lean_ctor_set(v___x_2351_, 4, v_t_2063_);
return v___x_2351_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object* v_k_2352_, lean_object* v_t_2353_){
_start:
{
if (lean_obj_tag(v_t_2353_) == 0)
{
lean_object* v_k_2354_; lean_object* v_l_2355_; lean_object* v_r_2356_; uint8_t v___x_2357_; 
v_k_2354_ = lean_ctor_get(v_t_2353_, 1);
v_l_2355_ = lean_ctor_get(v_t_2353_, 3);
v_r_2356_ = lean_ctor_get(v_t_2353_, 4);
v___x_2357_ = lean_nat_dec_lt(v_k_2352_, v_k_2354_);
if (v___x_2357_ == 0)
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_nat_dec_eq(v_k_2352_, v_k_2354_);
if (v___x_2358_ == 0)
{
v_t_2353_ = v_r_2356_;
goto _start;
}
else
{
return v___x_2358_;
}
}
else
{
v_t_2353_ = v_l_2355_;
goto _start;
}
}
else
{
uint8_t v___x_2361_; 
v___x_2361_ = 0;
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object* v_k_2362_, lean_object* v_t_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2362_, v_t_2363_);
lean_dec(v_t_2363_);
lean_dec(v_k_2362_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* v_idx_2366_){
_start:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_box(1);
v___x_2368_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2366_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_idx_2366_, v___x_2369_, v___x_2367_);
return v___x_2370_;
}
else
{
lean_dec(v_idx_2366_);
return v___x_2367_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object* v_00_u03b2_2371_, lean_object* v_k_2372_, lean_object* v_t_2373_){
_start:
{
uint8_t v___x_2374_; 
v___x_2374_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2372_, v_t_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object* v_00_u03b2_2375_, lean_object* v_k_2376_, lean_object* v_t_2377_){
_start:
{
uint8_t v_res_2378_; lean_object* v_r_2379_; 
v_res_2378_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(v_00_u03b2_2375_, v_k_2376_, v_t_2377_);
lean_dec(v_t_2377_);
lean_dec(v_k_2376_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object* v_00_u03b2_2380_, lean_object* v_k_2381_, lean_object* v_v_2382_, lean_object* v_t_2383_, lean_object* v_hl_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2381_, v_v_2382_, v_t_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx(lean_object* v_x_2386_){
_start:
{
switch(lean_obj_tag(v_x_2386_))
{
case 0:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_unsigned_to_nat(0u);
return v___x_2387_;
}
case 1:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_unsigned_to_nat(1u);
return v___x_2388_;
}
default: 
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_unsigned_to_nat(2u);
return v___x_2389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___boxed(lean_object* v_x_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_IR_LocalContextEntry_ctorIdx(v_x_2390_);
lean_dec_ref(v_x_2390_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object* v_t_2392_, lean_object* v_k_2393_){
_start:
{
switch(lean_obj_tag(v_t_2392_))
{
case 0:
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_ctor_get(v_t_2392_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v_t_2392_);
v___x_2395_ = lean_apply_1(v_k_2393_, v_a_2394_);
return v___x_2395_;
}
case 1:
{
lean_object* v_a_2396_; lean_object* v_a_2397_; lean_object* v___x_2398_; 
v_a_2396_ = lean_ctor_get(v_t_2392_, 0);
lean_inc(v_a_2396_);
v_a_2397_ = lean_ctor_get(v_t_2392_, 1);
lean_inc_ref(v_a_2397_);
lean_dec_ref(v_t_2392_);
v___x_2398_ = lean_apply_2(v_k_2393_, v_a_2396_, v_a_2397_);
return v___x_2398_;
}
default: 
{
lean_object* v_a_2399_; lean_object* v_a_2400_; lean_object* v___x_2401_; 
v_a_2399_ = lean_ctor_get(v_t_2392_, 0);
lean_inc_ref(v_a_2399_);
v_a_2400_ = lean_ctor_get(v_t_2392_, 1);
lean_inc(v_a_2400_);
lean_dec_ref(v_t_2392_);
v___x_2401_ = lean_apply_2(v_k_2393_, v_a_2399_, v_a_2400_);
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object* v_motive_2402_, lean_object* v_ctorIdx_2403_, lean_object* v_t_2404_, lean_object* v_h_2405_, lean_object* v_k_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2404_, v_k_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object* v_motive_2408_, lean_object* v_ctorIdx_2409_, lean_object* v_t_2410_, lean_object* v_h_2411_, lean_object* v_k_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_IR_LocalContextEntry_ctorElim(v_motive_2408_, v_ctorIdx_2409_, v_t_2410_, v_h_2411_, v_k_2412_);
lean_dec(v_ctorIdx_2409_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object* v_t_2414_, lean_object* v_param_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2414_, v_param_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object* v_motive_2417_, lean_object* v_t_2418_, lean_object* v_h_2419_, lean_object* v_param_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2418_, v_param_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object* v_t_2422_, lean_object* v_localVar_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2422_, v_localVar_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object* v_motive_2425_, lean_object* v_t_2426_, lean_object* v_h_2427_, lean_object* v_localVar_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2426_, v_localVar_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim___redArg(lean_object* v_t_2430_, lean_object* v_joinPoint_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2430_, v_joinPoint_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim(lean_object* v_motive_2433_, lean_object* v_t_2434_, lean_object* v_h_2435_, lean_object* v_joinPoint_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2434_, v_joinPoint_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* v_ctx_2438_, lean_object* v_x_2439_, lean_object* v_t_2440_, lean_object* v_v_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_t_2440_);
lean_ctor_set(v___x_2442_, 1, v_v_2441_);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2439_, v___x_2442_, v_ctx_2438_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* v_ctx_2444_, lean_object* v_j_2445_, lean_object* v_xs_2446_, lean_object* v_b_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_xs_2446_);
lean_ctor_set(v___x_2448_, 1, v_b_2447_);
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_j_2445_, v___x_2448_, v_ctx_2444_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* v_ctx_2450_, lean_object* v_p_2451_){
_start:
{
lean_object* v_x_2452_; lean_object* v_ty_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_x_2452_ = lean_ctor_get(v_p_2451_, 0);
lean_inc(v_x_2452_);
v_ty_2453_ = lean_ctor_get(v_p_2451_, 1);
lean_inc(v_ty_2453_);
lean_dec_ref(v_p_2451_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_ty_2453_);
v___x_2455_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2452_, v___x_2454_, v_ctx_2450_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object* v_as_2456_, size_t v_i_2457_, size_t v_stop_2458_, lean_object* v_b_2459_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; size_t v___x_2463_; size_t v___x_2464_; 
v___x_2461_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
lean_inc(v___x_2461_);
v___x_2462_ = l_Lean_IR_LocalContext_addParam(v_b_2459_, v___x_2461_);
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_add(v_i_2457_, v___x_2463_);
v_i_2457_ = v___x_2464_;
v_b_2459_ = v___x_2462_;
goto _start;
}
else
{
return v_b_2459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* v_as_2466_, lean_object* v_i_2467_, lean_object* v_stop_2468_, lean_object* v_b_2469_){
_start:
{
size_t v_i_boxed_2470_; size_t v_stop_boxed_2471_; lean_object* v_res_2472_; 
v_i_boxed_2470_ = lean_unbox_usize(v_i_2467_);
lean_dec(v_i_2467_);
v_stop_boxed_2471_ = lean_unbox_usize(v_stop_2468_);
lean_dec(v_stop_2468_);
v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_2466_, v_i_boxed_2470_, v_stop_boxed_2471_, v_b_2469_);
lean_dec_ref(v_as_2466_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* v_ctx_2473_, lean_object* v_ps_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = lean_array_get_size(v_ps_2474_);
v___x_2477_ = lean_nat_dec_lt(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
return v_ctx_2473_;
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_le(v___x_2476_, v___x_2476_);
if (v___x_2478_ == 0)
{
if (v___x_2477_ == 0)
{
return v_ctx_2473_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = lean_usize_of_nat(v___x_2476_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2474_, v___x_2479_, v___x_2480_, v_ctx_2473_);
return v___x_2481_;
}
}
else
{
size_t v___x_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = lean_usize_of_nat(v___x_2476_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2474_, v___x_2482_, v___x_2483_, v_ctx_2473_);
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_2485_, lean_object* v_ps_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_IR_LocalContext_addParams(v_ctx_2485_, v_ps_2486_);
lean_dec_ref(v_ps_2486_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(lean_object* v_t_2488_, lean_object* v_k_2489_){
_start:
{
if (lean_obj_tag(v_t_2488_) == 0)
{
lean_object* v_k_2490_; lean_object* v_v_2491_; lean_object* v_l_2492_; lean_object* v_r_2493_; uint8_t v___x_2494_; 
v_k_2490_ = lean_ctor_get(v_t_2488_, 1);
v_v_2491_ = lean_ctor_get(v_t_2488_, 2);
v_l_2492_ = lean_ctor_get(v_t_2488_, 3);
v_r_2493_ = lean_ctor_get(v_t_2488_, 4);
v___x_2494_ = lean_nat_dec_lt(v_k_2489_, v_k_2490_);
if (v___x_2494_ == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_nat_dec_eq(v_k_2489_, v_k_2490_);
if (v___x_2495_ == 0)
{
v_t_2488_ = v_r_2493_;
goto _start;
}
else
{
lean_object* v___x_2497_; 
lean_inc(v_v_2491_);
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_v_2491_);
return v___x_2497_;
}
}
else
{
v_t_2488_ = v_l_2492_;
goto _start;
}
}
else
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_box(0);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(lean_object* v_t_2500_, lean_object* v_k_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_2500_, v_k_2501_);
lean_dec(v_k_2501_);
lean_dec(v_t_2500_);
return v_res_2502_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_2503_, lean_object* v_idx_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2503_, v_idx_2504_);
if (lean_obj_tag(v___x_2505_) == 1)
{
lean_object* v_val_2506_; 
v_val_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_val_2506_);
lean_dec_ref(v___x_2505_);
if (lean_obj_tag(v_val_2506_) == 2)
{
uint8_t v___x_2507_; 
lean_dec_ref(v_val_2506_);
v___x_2507_ = 1;
return v___x_2507_;
}
else
{
uint8_t v___x_2508_; 
lean_dec(v_val_2506_);
v___x_2508_ = 0;
return v___x_2508_;
}
}
else
{
uint8_t v___x_2509_; 
lean_dec(v___x_2505_);
v___x_2509_ = 0;
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_2510_, lean_object* v_idx_2511_){
_start:
{
uint8_t v_res_2512_; lean_object* v_r_2513_; 
v_res_2512_ = l_Lean_IR_LocalContext_isJP(v_ctx_2510_, v_idx_2511_);
lean_dec(v_idx_2511_);
lean_dec(v_ctx_2510_);
v_r_2513_ = lean_box(v_res_2512_);
return v_r_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(lean_object* v_00_u03b4_2514_, lean_object* v_t_2515_, lean_object* v_k_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_2515_, v_k_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___boxed(lean_object* v_00_u03b4_2518_, lean_object* v_t_2519_, lean_object* v_k_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(v_00_u03b4_2518_, v_t_2519_, v_k_2520_);
lean_dec(v_k_2520_);
lean_dec(v_t_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_2522_, lean_object* v_j_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2522_, v_j_2523_);
if (lean_obj_tag(v___x_2524_) == 1)
{
lean_object* v_val_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_val_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
if (lean_obj_tag(v_val_2525_) == 2)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; 
v_a_2529_ = lean_ctor_get(v_val_2525_, 1);
lean_inc(v_a_2529_);
lean_dec_ref(v_val_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_a_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
else
{
lean_object* v___x_2533_; 
lean_del_object(v___x_2527_);
lean_dec(v_val_2525_);
v___x_2533_ = lean_box(0);
return v___x_2533_;
}
}
}
else
{
lean_object* v___x_2535_; 
lean_dec(v___x_2524_);
v___x_2535_ = lean_box(0);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_2536_, lean_object* v_j_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_2536_, v_j_2537_);
lean_dec(v_j_2537_);
lean_dec(v_ctx_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_2539_, lean_object* v_j_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2539_, v_j_2540_);
if (lean_obj_tag(v___x_2541_) == 1)
{
lean_object* v_val_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2551_; 
v_val_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2551_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_val_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2551_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
if (lean_obj_tag(v_val_2542_) == 2)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; 
v_a_2546_ = lean_ctor_get(v_val_2542_, 0);
lean_inc_ref(v_a_2546_);
lean_dec_ref(v_val_2542_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v_a_2546_);
v___x_2548_ = v___x_2544_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
else
{
lean_object* v___x_2550_; 
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
v___x_2550_ = lean_box(0);
return v___x_2550_;
}
}
}
else
{
lean_object* v___x_2552_; 
lean_dec(v___x_2541_);
v___x_2552_ = lean_box(0);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_2553_, lean_object* v_j_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_2553_, v_j_2554_);
lean_dec(v_j_2554_);
lean_dec(v_ctx_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_2556_, lean_object* v_idx_2557_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2556_, v_idx_2557_);
if (lean_obj_tag(v___x_2558_) == 1)
{
lean_object* v_val_2559_; 
v_val_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_val_2559_);
lean_dec_ref(v___x_2558_);
if (lean_obj_tag(v_val_2559_) == 0)
{
uint8_t v___x_2560_; 
lean_dec_ref(v_val_2559_);
v___x_2560_ = 1;
return v___x_2560_;
}
else
{
uint8_t v___x_2561_; 
lean_dec(v_val_2559_);
v___x_2561_ = 0;
return v___x_2561_;
}
}
else
{
uint8_t v___x_2562_; 
lean_dec(v___x_2558_);
v___x_2562_ = 0;
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_2563_, lean_object* v_idx_2564_){
_start:
{
uint8_t v_res_2565_; lean_object* v_r_2566_; 
v_res_2565_ = l_Lean_IR_LocalContext_isParam(v_ctx_2563_, v_idx_2564_);
lean_dec(v_idx_2564_);
lean_dec(v_ctx_2563_);
v_r_2566_ = lean_box(v_res_2565_);
return v_r_2566_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_2567_, lean_object* v_idx_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2567_, v_idx_2568_);
if (lean_obj_tag(v___x_2569_) == 1)
{
lean_object* v_val_2570_; 
v_val_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_val_2570_);
lean_dec_ref(v___x_2569_);
if (lean_obj_tag(v_val_2570_) == 1)
{
uint8_t v___x_2571_; 
lean_dec_ref(v_val_2570_);
v___x_2571_ = 1;
return v___x_2571_;
}
else
{
uint8_t v___x_2572_; 
lean_dec(v_val_2570_);
v___x_2572_ = 0;
return v___x_2572_;
}
}
else
{
uint8_t v___x_2573_; 
lean_dec(v___x_2569_);
v___x_2573_ = 0;
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_2574_, lean_object* v_idx_2575_){
_start:
{
uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_res_2576_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_2574_, v_idx_2575_);
lean_dec(v_idx_2575_);
lean_dec(v_ctx_2574_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object* v_ctx_2578_, lean_object* v_idx_2579_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2579_, v_ctx_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object* v_ctx_2581_, lean_object* v_idx_2582_){
_start:
{
uint8_t v_res_2583_; lean_object* v_r_2584_; 
v_res_2583_ = l_Lean_IR_LocalContext_contains(v_ctx_2581_, v_idx_2582_);
lean_dec(v_idx_2582_);
lean_dec(v_ctx_2581_);
v_r_2584_ = lean_box(v_res_2583_);
return v_r_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_2585_, lean_object* v_t_2586_){
_start:
{
if (lean_obj_tag(v_t_2586_) == 0)
{
lean_object* v_k_2587_; lean_object* v_v_2588_; lean_object* v_l_2589_; lean_object* v_r_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_3245_; 
v_k_2587_ = lean_ctor_get(v_t_2586_, 1);
v_v_2588_ = lean_ctor_get(v_t_2586_, 2);
v_l_2589_ = lean_ctor_get(v_t_2586_, 3);
v_r_2590_ = lean_ctor_get(v_t_2586_, 4);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_t_2586_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_t_2586_, 0);
lean_dec(v_unused_3246_);
v___x_2592_ = v_t_2586_;
v_isShared_2593_ = v_isSharedCheck_3245_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_r_2590_);
lean_inc(v_l_2589_);
lean_inc(v_v_2588_);
lean_inc(v_k_2587_);
lean_dec(v_t_2586_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_3245_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
uint8_t v___x_2594_; 
v___x_2594_ = lean_nat_dec_lt(v_k_2585_, v_k_2587_);
if (v___x_2594_ == 0)
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_nat_dec_eq(v_k_2585_, v_k_2587_);
if (v___x_2595_ == 0)
{
lean_object* v_impl_2596_; lean_object* v___x_2597_; 
v_impl_2596_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2585_, v_r_2590_);
v___x_2597_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2596_) == 0)
{
if (lean_obj_tag(v_l_2589_) == 0)
{
lean_object* v_size_2598_; lean_object* v_size_2599_; lean_object* v_k_2600_; lean_object* v_v_2601_; lean_object* v_l_2602_; lean_object* v_r_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v_size_2598_ = lean_ctor_get(v_impl_2596_, 0);
lean_inc(v_size_2598_);
v_size_2599_ = lean_ctor_get(v_l_2589_, 0);
v_k_2600_ = lean_ctor_get(v_l_2589_, 1);
v_v_2601_ = lean_ctor_get(v_l_2589_, 2);
v_l_2602_ = lean_ctor_get(v_l_2589_, 3);
v_r_2603_ = lean_ctor_get(v_l_2589_, 4);
lean_inc(v_r_2603_);
v___x_2604_ = lean_unsigned_to_nat(3u);
v___x_2605_ = lean_nat_mul(v___x_2604_, v_size_2598_);
v___x_2606_ = lean_nat_dec_lt(v___x_2605_, v_size_2599_);
lean_dec(v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec(v_r_2603_);
v___x_2607_ = lean_nat_add(v___x_2597_, v_size_2599_);
v___x_2608_ = lean_nat_add(v___x_2607_, v_size_2598_);
lean_dec(v_size_2598_);
lean_dec(v___x_2607_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_impl_2596_);
lean_ctor_set(v___x_2592_, 0, v___x_2608_);
v___x_2610_ = v___x_2592_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_impl_2596_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
else
{
lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2677_; 
lean_inc(v_l_2602_);
lean_inc(v_v_2601_);
lean_inc(v_k_2600_);
lean_inc(v_size_2599_);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2678_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2589_, 2);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2589_, 1);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_2682_);
v___x_2613_ = v_l_2589_;
v_isShared_2614_ = v_isSharedCheck_2677_;
goto v_resetjp_2612_;
}
else
{
lean_dec(v_l_2589_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2677_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v_size_2615_; lean_object* v_size_2616_; lean_object* v_k_2617_; lean_object* v_v_2618_; lean_object* v_l_2619_; lean_object* v_r_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_size_2615_ = lean_ctor_get(v_l_2602_, 0);
v_size_2616_ = lean_ctor_get(v_r_2603_, 0);
v_k_2617_ = lean_ctor_get(v_r_2603_, 1);
v_v_2618_ = lean_ctor_get(v_r_2603_, 2);
v_l_2619_ = lean_ctor_get(v_r_2603_, 3);
v_r_2620_ = lean_ctor_get(v_r_2603_, 4);
v___x_2621_ = lean_unsigned_to_nat(2u);
v___x_2622_ = lean_nat_mul(v___x_2621_, v_size_2615_);
v___x_2623_ = lean_nat_dec_lt(v_size_2616_, v___x_2622_);
lean_dec(v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2652_; 
lean_inc(v_r_2620_);
lean_inc(v_l_2619_);
lean_inc(v_v_2618_);
lean_inc(v_k_2617_);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_r_2603_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; lean_object* v_unused_2654_; lean_object* v_unused_2655_; lean_object* v_unused_2656_; lean_object* v_unused_2657_; 
v_unused_2653_ = lean_ctor_get(v_r_2603_, 4);
lean_dec(v_unused_2653_);
v_unused_2654_ = lean_ctor_get(v_r_2603_, 3);
lean_dec(v_unused_2654_);
v_unused_2655_ = lean_ctor_get(v_r_2603_, 2);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v_r_2603_, 1);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_r_2603_, 0);
lean_dec(v_unused_2657_);
v___x_2625_ = v_r_2603_;
v_isShared_2626_ = v_isSharedCheck_2652_;
goto v_resetjp_2624_;
}
else
{
lean_dec(v_r_2603_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2652_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___x_2640_; lean_object* v___y_2642_; 
v___x_2627_ = lean_nat_add(v___x_2597_, v_size_2599_);
lean_dec(v_size_2599_);
v___x_2628_ = lean_nat_add(v___x_2627_, v_size_2598_);
lean_dec(v___x_2627_);
v___x_2640_ = lean_nat_add(v___x_2597_, v_size_2615_);
if (lean_obj_tag(v_l_2619_) == 0)
{
lean_object* v_size_2650_; 
v_size_2650_ = lean_ctor_get(v_l_2619_, 0);
lean_inc(v_size_2650_);
v___y_2642_ = v_size_2650_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_unsigned_to_nat(0u);
v___y_2642_ = v___x_2651_;
goto v___jp_2641_;
}
v___jp_2629_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = lean_nat_add(v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec(v___y_2631_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 4, v_impl_2596_);
lean_ctor_set(v___x_2625_, 3, v_r_2620_);
lean_ctor_set(v___x_2625_, 2, v_v_2588_);
lean_ctor_set(v___x_2625_, 1, v_k_2587_);
lean_ctor_set(v___x_2625_, 0, v___x_2633_);
v___x_2635_ = v___x_2625_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2639_, 3, v_r_2620_);
lean_ctor_set(v_reuseFailAlloc_2639_, 4, v_impl_2596_);
v___x_2635_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2637_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 4, v___x_2635_);
lean_ctor_set(v___x_2613_, 3, v___y_2630_);
lean_ctor_set(v___x_2613_, 2, v_v_2618_);
lean_ctor_set(v___x_2613_, 1, v_k_2617_);
lean_ctor_set(v___x_2613_, 0, v___x_2628_);
v___x_2637_ = v___x_2613_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_k_2617_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_v_2618_);
lean_ctor_set(v_reuseFailAlloc_2638_, 3, v___y_2630_);
lean_ctor_set(v_reuseFailAlloc_2638_, 4, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
v___jp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_nat_add(v___x_2640_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec(v___x_2640_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_l_2619_);
lean_ctor_set(v___x_2592_, 3, v_l_2602_);
lean_ctor_set(v___x_2592_, 2, v_v_2601_);
lean_ctor_set(v___x_2592_, 1, v_k_2600_);
lean_ctor_set(v___x_2592_, 0, v___x_2643_);
v___x_2645_ = v___x_2592_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_k_2600_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_v_2601_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_l_2602_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_l_2619_);
v___x_2645_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_nat_add(v___x_2597_, v_size_2598_);
lean_dec(v_size_2598_);
if (lean_obj_tag(v_r_2620_) == 0)
{
lean_object* v_size_2647_; 
v_size_2647_ = lean_ctor_get(v_r_2620_, 0);
lean_inc(v_size_2647_);
v___y_2630_ = v___x_2645_;
v___y_2631_ = v___x_2646_;
v___y_2632_ = v_size_2647_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_unsigned_to_nat(0u);
v___y_2630_ = v___x_2645_;
v___y_2631_ = v___x_2646_;
v___y_2632_ = v___x_2648_;
goto v___jp_2629_;
}
}
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
lean_del_object(v___x_2592_);
v___x_2658_ = lean_nat_add(v___x_2597_, v_size_2599_);
lean_dec(v_size_2599_);
v___x_2659_ = lean_nat_add(v___x_2658_, v_size_2598_);
lean_dec(v___x_2658_);
v___x_2660_ = lean_nat_add(v___x_2597_, v_size_2598_);
lean_dec(v_size_2598_);
v___x_2661_ = lean_nat_add(v___x_2660_, v_size_2616_);
lean_dec(v___x_2660_);
lean_inc_ref(v_impl_2596_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 4, v_impl_2596_);
lean_ctor_set(v___x_2613_, 3, v_r_2603_);
lean_ctor_set(v___x_2613_, 2, v_v_2588_);
lean_ctor_set(v___x_2613_, 1, v_k_2587_);
lean_ctor_set(v___x_2613_, 0, v___x_2661_);
v___x_2663_ = v___x_2613_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v_r_2603_);
lean_ctor_set(v_reuseFailAlloc_2676_, 4, v_impl_2596_);
v___x_2663_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v_isSharedCheck_2670_ = !lean_is_exclusive(v_impl_2596_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; lean_object* v_unused_2672_; lean_object* v_unused_2673_; lean_object* v_unused_2674_; lean_object* v_unused_2675_; 
v_unused_2671_ = lean_ctor_get(v_impl_2596_, 4);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_impl_2596_, 3);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_impl_2596_, 2);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_impl_2596_, 1);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_impl_2596_, 0);
lean_dec(v_unused_2675_);
v___x_2665_ = v_impl_2596_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v_impl_2596_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 4, v___x_2663_);
lean_ctor_set(v___x_2665_, 3, v_l_2602_);
lean_ctor_set(v___x_2665_, 2, v_v_2601_);
lean_ctor_set(v___x_2665_, 1, v_k_2600_);
lean_ctor_set(v___x_2665_, 0, v___x_2659_);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_k_2600_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_v_2601_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_l_2602_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v___x_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
v_size_2683_ = lean_ctor_get(v_impl_2596_, 0);
lean_inc(v_size_2683_);
v___x_2684_ = lean_nat_add(v___x_2597_, v_size_2683_);
lean_dec(v_size_2683_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_impl_2596_);
lean_ctor_set(v___x_2592_, 0, v___x_2684_);
v___x_2686_ = v___x_2592_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_impl_2596_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
else
{
if (lean_obj_tag(v_l_2589_) == 0)
{
lean_object* v_l_2688_; 
v_l_2688_ = lean_ctor_get(v_l_2589_, 3);
if (lean_obj_tag(v_l_2688_) == 0)
{
lean_object* v_r_2689_; 
lean_inc_ref(v_l_2688_);
v_r_2689_ = lean_ctor_get(v_l_2589_, 4);
lean_inc(v_r_2689_);
if (lean_obj_tag(v_r_2689_) == 0)
{
lean_object* v_size_2690_; lean_object* v_k_2691_; lean_object* v_v_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2705_; 
v_size_2690_ = lean_ctor_get(v_l_2589_, 0);
v_k_2691_ = lean_ctor_get(v_l_2589_, 1);
v_v_2692_ = lean_ctor_get(v_l_2589_, 2);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2706_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_2707_);
v___x_2694_ = v_l_2589_;
v_isShared_2695_ = v_isSharedCheck_2705_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_v_2692_);
lean_inc(v_k_2691_);
lean_inc(v_size_2690_);
lean_dec(v_l_2589_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2705_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v_size_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v_size_2696_ = lean_ctor_get(v_r_2689_, 0);
v___x_2697_ = lean_nat_add(v___x_2597_, v_size_2690_);
lean_dec(v_size_2690_);
v___x_2698_ = lean_nat_add(v___x_2597_, v_size_2696_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 4, v_impl_2596_);
lean_ctor_set(v___x_2694_, 3, v_r_2689_);
lean_ctor_set(v___x_2694_, 2, v_v_2588_);
lean_ctor_set(v___x_2694_, 1, v_k_2587_);
lean_ctor_set(v___x_2694_, 0, v___x_2698_);
v___x_2700_ = v___x_2694_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_r_2689_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v_impl_2596_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_2700_);
lean_ctor_set(v___x_2592_, 3, v_l_2688_);
lean_ctor_set(v___x_2592_, 2, v_v_2692_);
lean_ctor_set(v___x_2592_, 1, v_k_2691_);
lean_ctor_set(v___x_2592_, 0, v___x_2697_);
v___x_2702_ = v___x_2592_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_k_2691_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_v_2692_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_l_2688_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_k_2708_; lean_object* v_v_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2720_; 
v_k_2708_ = lean_ctor_get(v_l_2589_, 1);
v_v_2709_ = lean_ctor_get(v_l_2589_, 2);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_2720_ == 0)
{
lean_object* v_unused_2721_; lean_object* v_unused_2722_; lean_object* v_unused_2723_; 
v_unused_2721_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_2722_);
v_unused_2723_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_2723_);
v___x_2711_ = v_l_2589_;
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_v_2709_);
lean_inc(v_k_2708_);
lean_dec(v_l_2589_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = lean_unsigned_to_nat(3u);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 3, v_r_2689_);
lean_ctor_set(v___x_2711_, 2, v_v_2588_);
lean_ctor_set(v___x_2711_, 1, v_k_2587_);
lean_ctor_set(v___x_2711_, 0, v___x_2597_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2719_, 3, v_r_2689_);
lean_ctor_set(v_reuseFailAlloc_2719_, 4, v_r_2689_);
v___x_2715_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2717_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_2715_);
lean_ctor_set(v___x_2592_, 3, v_l_2688_);
lean_ctor_set(v___x_2592_, 2, v_v_2709_);
lean_ctor_set(v___x_2592_, 1, v_k_2708_);
lean_ctor_set(v___x_2592_, 0, v___x_2713_);
v___x_2717_ = v___x_2592_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_k_2708_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_v_2709_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v_l_2688_);
lean_ctor_set(v_reuseFailAlloc_2718_, 4, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
else
{
lean_object* v_r_2724_; 
v_r_2724_ = lean_ctor_get(v_l_2589_, 4);
lean_inc(v_r_2724_);
if (lean_obj_tag(v_r_2724_) == 0)
{
lean_object* v_k_2725_; lean_object* v_v_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2749_; 
lean_inc(v_l_2688_);
v_k_2725_ = lean_ctor_get(v_l_2589_, 1);
v_v_2726_ = lean_ctor_get(v_l_2589_, 2);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2750_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_2752_);
v___x_2728_ = v_l_2589_;
v_isShared_2729_ = v_isSharedCheck_2749_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_v_2726_);
lean_inc(v_k_2725_);
lean_dec(v_l_2589_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2749_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v_k_2730_; lean_object* v_v_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2745_; 
v_k_2730_ = lean_ctor_get(v_r_2724_, 1);
v_v_2731_ = lean_ctor_get(v_r_2724_, 2);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_r_2724_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2746_ = lean_ctor_get(v_r_2724_, 4);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_r_2724_, 3);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_r_2724_, 0);
lean_dec(v_unused_2748_);
v___x_2733_ = v_r_2724_;
v_isShared_2734_ = v_isSharedCheck_2745_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_v_2731_);
lean_inc(v_k_2730_);
lean_dec(v_r_2724_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2745_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = lean_unsigned_to_nat(3u);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 4, v_l_2688_);
lean_ctor_set(v___x_2733_, 3, v_l_2688_);
lean_ctor_set(v___x_2733_, 2, v_v_2726_);
lean_ctor_set(v___x_2733_, 1, v_k_2725_);
lean_ctor_set(v___x_2733_, 0, v___x_2597_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_l_2688_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_l_2688_);
v___x_2737_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2739_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 4, v_l_2688_);
lean_ctor_set(v___x_2728_, 2, v_v_2588_);
lean_ctor_set(v___x_2728_, 1, v_k_2587_);
lean_ctor_set(v___x_2728_, 0, v___x_2597_);
v___x_2739_ = v___x_2728_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_l_2688_);
lean_ctor_set(v_reuseFailAlloc_2743_, 4, v_l_2688_);
v___x_2739_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2741_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_2739_);
lean_ctor_set(v___x_2592_, 3, v___x_2737_);
lean_ctor_set(v___x_2592_, 2, v_v_2731_);
lean_ctor_set(v___x_2592_, 1, v_k_2730_);
lean_ctor_set(v___x_2592_, 0, v___x_2735_);
v___x_2741_ = v___x_2592_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_k_2730_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_v_2731_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = lean_unsigned_to_nat(2u);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_r_2724_);
lean_ctor_set(v___x_2592_, 0, v___x_2753_);
v___x_2755_ = v___x_2592_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_r_2724_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v___x_2758_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_l_2589_);
lean_ctor_set(v___x_2592_, 0, v___x_2597_);
v___x_2758_ = v___x_2592_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2759_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2759_, 4, v_l_2589_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_del_object(v___x_2592_);
lean_dec(v_v_2588_);
lean_dec(v_k_2587_);
if (lean_obj_tag(v_l_2589_) == 0)
{
if (lean_obj_tag(v_r_2590_) == 0)
{
lean_object* v_size_2760_; lean_object* v_k_2761_; lean_object* v_v_2762_; lean_object* v_l_2763_; lean_object* v_r_2764_; lean_object* v_size_2765_; lean_object* v_k_2766_; lean_object* v_v_2767_; lean_object* v_l_2768_; lean_object* v_r_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_size_2760_ = lean_ctor_get(v_l_2589_, 0);
v_k_2761_ = lean_ctor_get(v_l_2589_, 1);
v_v_2762_ = lean_ctor_get(v_l_2589_, 2);
v_l_2763_ = lean_ctor_get(v_l_2589_, 3);
v_r_2764_ = lean_ctor_get(v_l_2589_, 4);
lean_inc(v_r_2764_);
v_size_2765_ = lean_ctor_get(v_r_2590_, 0);
v_k_2766_ = lean_ctor_get(v_r_2590_, 1);
v_v_2767_ = lean_ctor_get(v_r_2590_, 2);
v_l_2768_ = lean_ctor_get(v_r_2590_, 3);
lean_inc(v_l_2768_);
v_r_2769_ = lean_ctor_get(v_r_2590_, 4);
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_dec_lt(v_size_2760_, v_size_2765_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2907_; 
lean_inc(v_l_2763_);
lean_inc(v_v_2762_);
lean_inc(v_k_2761_);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; lean_object* v_unused_2909_; lean_object* v_unused_2910_; lean_object* v_unused_2911_; lean_object* v_unused_2912_; 
v_unused_2908_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_2909_);
v_unused_2910_ = lean_ctor_get(v_l_2589_, 2);
lean_dec(v_unused_2910_);
v_unused_2911_ = lean_ctor_get(v_l_2589_, 1);
lean_dec(v_unused_2911_);
v_unused_2912_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_2912_);
v___x_2773_ = v_l_2589_;
v_isShared_2774_ = v_isSharedCheck_2907_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_l_2589_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2907_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v_tree_2776_; 
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2761_, v_v_2762_, v_l_2763_, v_r_2764_);
v_tree_2776_ = lean_ctor_get(v___x_2775_, 2);
lean_inc(v_tree_2776_);
if (lean_obj_tag(v_tree_2776_) == 0)
{
lean_object* v_k_2777_; lean_object* v_v_2778_; lean_object* v_size_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v_k_2777_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_k_2777_);
v_v_2778_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_v_2778_);
lean_dec_ref(v___x_2775_);
v_size_2779_ = lean_ctor_get(v_tree_2776_, 0);
v___x_2780_ = lean_unsigned_to_nat(3u);
v___x_2781_ = lean_nat_mul(v___x_2780_, v_size_2779_);
v___x_2782_ = lean_nat_dec_lt(v___x_2781_, v_size_2765_);
lean_dec(v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
lean_dec(v_l_2768_);
v___x_2783_ = lean_nat_add(v___x_2770_, v_size_2779_);
v___x_2784_ = lean_nat_add(v___x_2783_, v_size_2765_);
lean_dec(v___x_2783_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v_r_2590_);
lean_ctor_set(v___x_2773_, 3, v_tree_2776_);
lean_ctor_set(v___x_2773_, 2, v_v_2778_);
lean_ctor_set(v___x_2773_, 1, v_k_2777_);
lean_ctor_set(v___x_2773_, 0, v___x_2784_);
v___x_2786_ = v___x_2773_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_k_2777_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_v_2778_);
lean_ctor_set(v_reuseFailAlloc_2787_, 3, v_tree_2776_);
lean_ctor_set(v_reuseFailAlloc_2787_, 4, v_r_2590_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
else
{
lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2842_; 
lean_inc(v_r_2769_);
lean_inc(v_v_2767_);
lean_inc(v_k_2766_);
lean_inc(v_size_2765_);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; lean_object* v_unused_2844_; lean_object* v_unused_2845_; lean_object* v_unused_2846_; lean_object* v_unused_2847_; 
v_unused_2843_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_2843_);
v_unused_2844_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_2844_);
v_unused_2845_ = lean_ctor_get(v_r_2590_, 2);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_r_2590_, 1);
lean_dec(v_unused_2846_);
v_unused_2847_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_2847_);
v___x_2789_ = v_r_2590_;
v_isShared_2790_ = v_isSharedCheck_2842_;
goto v_resetjp_2788_;
}
else
{
lean_dec(v_r_2590_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2842_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_size_2791_; lean_object* v_k_2792_; lean_object* v_v_2793_; lean_object* v_l_2794_; lean_object* v_r_2795_; lean_object* v_size_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v_size_2791_ = lean_ctor_get(v_l_2768_, 0);
v_k_2792_ = lean_ctor_get(v_l_2768_, 1);
v_v_2793_ = lean_ctor_get(v_l_2768_, 2);
v_l_2794_ = lean_ctor_get(v_l_2768_, 3);
v_r_2795_ = lean_ctor_get(v_l_2768_, 4);
v_size_2796_ = lean_ctor_get(v_r_2769_, 0);
v___x_2797_ = lean_unsigned_to_nat(2u);
v___x_2798_ = lean_nat_mul(v___x_2797_, v_size_2796_);
v___x_2799_ = lean_nat_dec_lt(v_size_2791_, v___x_2798_);
lean_dec(v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2827_; 
lean_inc(v_r_2795_);
lean_inc(v_l_2794_);
lean_inc(v_v_2793_);
lean_inc(v_k_2792_);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_l_2768_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; lean_object* v_unused_2831_; lean_object* v_unused_2832_; 
v_unused_2828_ = lean_ctor_get(v_l_2768_, 4);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_l_2768_, 3);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_l_2768_, 2);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_l_2768_, 1);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_l_2768_, 0);
lean_dec(v_unused_2832_);
v___x_2801_ = v_l_2768_;
v_isShared_2802_ = v_isSharedCheck_2827_;
goto v_resetjp_2800_;
}
else
{
lean_dec(v_l_2768_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2827_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2817_; 
v___x_2803_ = lean_nat_add(v___x_2770_, v_size_2779_);
v___x_2804_ = lean_nat_add(v___x_2803_, v_size_2765_);
lean_dec(v_size_2765_);
if (lean_obj_tag(v_l_2794_) == 0)
{
lean_object* v_size_2825_; 
v_size_2825_ = lean_ctor_get(v_l_2794_, 0);
lean_inc(v_size_2825_);
v___y_2817_ = v_size_2825_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_unsigned_to_nat(0u);
v___y_2817_ = v___x_2826_;
goto v___jp_2816_;
}
v___jp_2805_:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_nat_add(v___y_2806_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec(v___y_2806_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 4, v_r_2769_);
lean_ctor_set(v___x_2801_, 3, v_r_2795_);
lean_ctor_set(v___x_2801_, 2, v_v_2767_);
lean_ctor_set(v___x_2801_, 1, v_k_2766_);
lean_ctor_set(v___x_2801_, 0, v___x_2809_);
v___x_2811_ = v___x_2801_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_r_2795_);
lean_ctor_set(v_reuseFailAlloc_2815_, 4, v_r_2769_);
v___x_2811_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 4, v___x_2811_);
lean_ctor_set(v___x_2789_, 3, v___y_2807_);
lean_ctor_set(v___x_2789_, 2, v_v_2793_);
lean_ctor_set(v___x_2789_, 1, v_k_2792_);
lean_ctor_set(v___x_2789_, 0, v___x_2804_);
v___x_2813_ = v___x_2789_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_k_2792_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_v_2793_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v___y_2807_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
v___jp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2818_ = lean_nat_add(v___x_2803_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec(v___x_2803_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v_l_2794_);
lean_ctor_set(v___x_2773_, 3, v_tree_2776_);
lean_ctor_set(v___x_2773_, 2, v_v_2778_);
lean_ctor_set(v___x_2773_, 1, v_k_2777_);
lean_ctor_set(v___x_2773_, 0, v___x_2818_);
v___x_2820_ = v___x_2773_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_k_2777_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_v_2778_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_tree_2776_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_l_2794_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_nat_add(v___x_2770_, v_size_2796_);
if (lean_obj_tag(v_r_2795_) == 0)
{
lean_object* v_size_2822_; 
v_size_2822_ = lean_ctor_get(v_r_2795_, 0);
lean_inc(v_size_2822_);
v___y_2806_ = v___x_2821_;
v___y_2807_ = v___x_2820_;
v___y_2808_ = v_size_2822_;
goto v___jp_2805_;
}
else
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_unsigned_to_nat(0u);
v___y_2806_ = v___x_2821_;
v___y_2807_ = v___x_2820_;
v___y_2808_ = v___x_2823_;
goto v___jp_2805_;
}
}
}
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2833_ = lean_nat_add(v___x_2770_, v_size_2779_);
v___x_2834_ = lean_nat_add(v___x_2833_, v_size_2765_);
lean_dec(v_size_2765_);
v___x_2835_ = lean_nat_add(v___x_2833_, v_size_2791_);
lean_dec(v___x_2833_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 4, v_l_2768_);
lean_ctor_set(v___x_2789_, 3, v_tree_2776_);
lean_ctor_set(v___x_2789_, 2, v_v_2778_);
lean_ctor_set(v___x_2789_, 1, v_k_2777_);
lean_ctor_set(v___x_2789_, 0, v___x_2835_);
v___x_2837_ = v___x_2789_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2777_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2778_);
lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_tree_2776_);
lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_l_2768_);
v___x_2837_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v_r_2769_);
lean_ctor_set(v___x_2773_, 3, v___x_2837_);
lean_ctor_set(v___x_2773_, 2, v_v_2767_);
lean_ctor_set(v___x_2773_, 1, v_k_2766_);
lean_ctor_set(v___x_2773_, 0, v___x_2834_);
v___x_2839_ = v___x_2773_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_r_2769_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
}
else
{
lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2901_; 
lean_inc(v_r_2769_);
lean_inc(v_v_2767_);
lean_inc(v_k_2766_);
lean_inc(v_size_2765_);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; lean_object* v_unused_2903_; lean_object* v_unused_2904_; lean_object* v_unused_2905_; lean_object* v_unused_2906_; 
v_unused_2902_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_2902_);
v_unused_2903_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_r_2590_, 2);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_r_2590_, 1);
lean_dec(v_unused_2905_);
v_unused_2906_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_2906_);
v___x_2849_ = v_r_2590_;
v_isShared_2850_ = v_isSharedCheck_2901_;
goto v_resetjp_2848_;
}
else
{
lean_dec(v_r_2590_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2901_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
if (lean_obj_tag(v_l_2768_) == 0)
{
if (lean_obj_tag(v_r_2769_) == 0)
{
lean_object* v_k_2851_; lean_object* v_v_2852_; lean_object* v_size_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v_k_2851_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_k_2851_);
v_v_2852_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_v_2852_);
lean_dec_ref(v___x_2775_);
v_size_2853_ = lean_ctor_get(v_l_2768_, 0);
v___x_2854_ = lean_nat_add(v___x_2770_, v_size_2765_);
lean_dec(v_size_2765_);
v___x_2855_ = lean_nat_add(v___x_2770_, v_size_2853_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 4, v_l_2768_);
lean_ctor_set(v___x_2849_, 3, v_tree_2776_);
lean_ctor_set(v___x_2849_, 2, v_v_2852_);
lean_ctor_set(v___x_2849_, 1, v_k_2851_);
lean_ctor_set(v___x_2849_, 0, v___x_2855_);
v___x_2857_ = v___x_2849_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_k_2851_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_v_2852_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_tree_2776_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_l_2768_);
v___x_2857_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2859_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v_r_2769_);
lean_ctor_set(v___x_2773_, 3, v___x_2857_);
lean_ctor_set(v___x_2773_, 2, v_v_2767_);
lean_ctor_set(v___x_2773_, 1, v_k_2766_);
lean_ctor_set(v___x_2773_, 0, v___x_2854_);
v___x_2859_ = v___x_2773_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2860_, 3, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2860_, 4, v_r_2769_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
lean_object* v_k_2862_; lean_object* v_v_2863_; lean_object* v_k_2864_; lean_object* v_v_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_size_2765_);
v_k_2862_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_k_2862_);
v_v_2863_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_v_2863_);
lean_dec_ref(v___x_2775_);
v_k_2864_ = lean_ctor_get(v_l_2768_, 1);
v_v_2865_ = lean_ctor_get(v_l_2768_, 2);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_l_2768_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; lean_object* v_unused_2881_; lean_object* v_unused_2882_; 
v_unused_2880_ = lean_ctor_get(v_l_2768_, 4);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_l_2768_, 3);
lean_dec(v_unused_2881_);
v_unused_2882_ = lean_ctor_get(v_l_2768_, 0);
lean_dec(v_unused_2882_);
v___x_2867_ = v_l_2768_;
v_isShared_2868_ = v_isSharedCheck_2879_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_v_2865_);
lean_inc(v_k_2864_);
lean_dec(v_l_2768_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2879_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2869_ = lean_unsigned_to_nat(3u);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 4, v_r_2769_);
lean_ctor_set(v___x_2867_, 3, v_r_2769_);
lean_ctor_set(v___x_2867_, 2, v_v_2863_);
lean_ctor_set(v___x_2867_, 1, v_k_2862_);
lean_ctor_set(v___x_2867_, 0, v___x_2770_);
v___x_2871_ = v___x_2867_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_k_2862_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v_v_2863_);
lean_ctor_set(v_reuseFailAlloc_2878_, 3, v_r_2769_);
lean_ctor_set(v_reuseFailAlloc_2878_, 4, v_r_2769_);
v___x_2871_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 3, v_r_2769_);
lean_ctor_set(v___x_2849_, 0, v___x_2770_);
v___x_2873_ = v___x_2849_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_r_2769_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_r_2769_);
v___x_2873_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v___x_2873_);
lean_ctor_set(v___x_2773_, 3, v___x_2871_);
lean_ctor_set(v___x_2773_, 2, v_v_2865_);
lean_ctor_set(v___x_2773_, 1, v_k_2864_);
lean_ctor_set(v___x_2773_, 0, v___x_2869_);
v___x_2875_ = v___x_2773_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_k_2864_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_v_2865_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2769_) == 0)
{
lean_object* v_k_2883_; lean_object* v_v_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
lean_dec(v_size_2765_);
v_k_2883_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_k_2883_);
v_v_2884_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_v_2884_);
lean_dec_ref(v___x_2775_);
v___x_2885_ = lean_unsigned_to_nat(3u);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 4, v_l_2768_);
lean_ctor_set(v___x_2849_, 2, v_v_2884_);
lean_ctor_set(v___x_2849_, 1, v_k_2883_);
lean_ctor_set(v___x_2849_, 0, v___x_2770_);
v___x_2887_ = v___x_2849_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_k_2883_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_v_2884_);
lean_ctor_set(v_reuseFailAlloc_2891_, 3, v_l_2768_);
lean_ctor_set(v_reuseFailAlloc_2891_, 4, v_l_2768_);
v___x_2887_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v_r_2769_);
lean_ctor_set(v___x_2773_, 3, v___x_2887_);
lean_ctor_set(v___x_2773_, 2, v_v_2767_);
lean_ctor_set(v___x_2773_, 1, v_k_2766_);
lean_ctor_set(v___x_2773_, 0, v___x_2885_);
v___x_2889_ = v___x_2773_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2890_, 3, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2890_, 4, v_r_2769_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v_k_2892_; lean_object* v_v_2893_; lean_object* v___x_2895_; 
v_k_2892_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_k_2892_);
v_v_2893_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_v_2893_);
lean_dec_ref(v___x_2775_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 3, v_r_2769_);
v___x_2895_ = v___x_2849_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_size_2765_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_r_2769_);
lean_ctor_set(v_reuseFailAlloc_2900_, 4, v_r_2769_);
v___x_2895_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_unsigned_to_nat(2u);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v___x_2895_);
lean_ctor_set(v___x_2773_, 3, v_r_2769_);
lean_ctor_set(v___x_2773_, 2, v_v_2893_);
lean_ctor_set(v___x_2773_, 1, v_k_2892_);
lean_ctor_set(v___x_2773_, 0, v___x_2896_);
v___x_2898_ = v___x_2773_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_k_2892_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_v_2893_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_r_2769_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v___x_2895_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
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
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3065_; 
lean_inc(v_r_2769_);
lean_inc(v_v_2767_);
lean_inc(v_k_2766_);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; lean_object* v_unused_3067_; lean_object* v_unused_3068_; lean_object* v_unused_3069_; lean_object* v_unused_3070_; 
v_unused_3066_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_3066_);
v_unused_3067_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v_r_2590_, 2);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v_r_2590_, 1);
lean_dec(v_unused_3069_);
v_unused_3070_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_3070_);
v___x_2914_ = v_r_2590_;
v_isShared_2915_ = v_isSharedCheck_3065_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v_r_2590_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3065_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v_tree_2917_; 
v___x_2916_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2766_, v_v_2767_, v_l_2768_, v_r_2769_);
v_tree_2917_ = lean_ctor_get(v___x_2916_, 2);
lean_inc(v_tree_2917_);
if (lean_obj_tag(v_tree_2917_) == 0)
{
lean_object* v_k_2918_; lean_object* v_v_2919_; lean_object* v_size_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v_k_2918_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_k_2918_);
v_v_2919_ = lean_ctor_get(v___x_2916_, 1);
lean_inc(v_v_2919_);
lean_dec_ref(v___x_2916_);
v_size_2920_ = lean_ctor_get(v_tree_2917_, 0);
v___x_2921_ = lean_unsigned_to_nat(3u);
v___x_2922_ = lean_nat_mul(v___x_2921_, v_size_2920_);
v___x_2923_ = lean_nat_dec_lt(v___x_2922_, v_size_2760_);
lean_dec(v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
lean_dec(v_r_2764_);
v___x_2924_ = lean_nat_add(v___x_2770_, v_size_2760_);
v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2920_);
lean_dec(v___x_2924_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_tree_2917_);
lean_ctor_set(v___x_2914_, 3, v_l_2589_);
lean_ctor_set(v___x_2914_, 2, v_v_2919_);
lean_ctor_set(v___x_2914_, 1, v_k_2918_);
lean_ctor_set(v___x_2914_, 0, v___x_2925_);
v___x_2927_ = v___x_2914_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_k_2918_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_v_2919_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2928_, 4, v_tree_2917_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
else
{
lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2994_; 
lean_inc(v_l_2763_);
lean_inc(v_v_2762_);
lean_inc(v_k_2761_);
lean_inc(v_size_2760_);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; lean_object* v_unused_2999_; 
v_unused_2995_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_l_2589_, 2);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_l_2589_, 1);
lean_dec(v_unused_2998_);
v_unused_2999_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_2999_);
v___x_2930_ = v_l_2589_;
v_isShared_2931_ = v_isSharedCheck_2994_;
goto v_resetjp_2929_;
}
else
{
lean_dec(v_l_2589_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2994_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v_size_2932_; lean_object* v_size_2933_; lean_object* v_k_2934_; lean_object* v_v_2935_; lean_object* v_l_2936_; lean_object* v_r_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_size_2932_ = lean_ctor_get(v_l_2763_, 0);
v_size_2933_ = lean_ctor_get(v_r_2764_, 0);
v_k_2934_ = lean_ctor_get(v_r_2764_, 1);
v_v_2935_ = lean_ctor_get(v_r_2764_, 2);
v_l_2936_ = lean_ctor_get(v_r_2764_, 3);
v_r_2937_ = lean_ctor_get(v_r_2764_, 4);
v___x_2938_ = lean_unsigned_to_nat(2u);
v___x_2939_ = lean_nat_mul(v___x_2938_, v_size_2932_);
v___x_2940_ = lean_nat_dec_lt(v_size_2933_, v___x_2939_);
lean_dec(v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2978_; 
lean_inc(v_r_2937_);
lean_inc(v_l_2936_);
lean_inc(v_v_2935_);
lean_inc(v_k_2934_);
lean_del_object(v___x_2930_);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_r_2764_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; lean_object* v_unused_2983_; 
v_unused_2979_ = lean_ctor_get(v_r_2764_, 4);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_r_2764_, 3);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_r_2764_, 2);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_r_2764_, 1);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_r_2764_, 0);
lean_dec(v_unused_2983_);
v___x_2942_ = v_r_2764_;
v_isShared_2943_ = v_isSharedCheck_2978_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v_r_2764_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2978_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___x_2966_; lean_object* v___y_2968_; 
v___x_2944_ = lean_nat_add(v___x_2770_, v_size_2760_);
lean_dec(v_size_2760_);
v___x_2945_ = lean_nat_add(v___x_2944_, v_size_2920_);
lean_dec(v___x_2944_);
v___x_2966_ = lean_nat_add(v___x_2770_, v_size_2932_);
if (lean_obj_tag(v_l_2936_) == 0)
{
lean_object* v_size_2976_; 
v_size_2976_ = lean_ctor_get(v_l_2936_, 0);
lean_inc(v_size_2976_);
v___y_2968_ = v_size_2976_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_unsigned_to_nat(0u);
v___y_2968_ = v___x_2977_;
goto v___jp_2967_;
}
v___jp_2946_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_nat_add(v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec(v___y_2948_);
lean_inc_ref(v_tree_2917_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 4, v_tree_2917_);
lean_ctor_set(v___x_2942_, 3, v_r_2937_);
lean_ctor_set(v___x_2942_, 2, v_v_2919_);
lean_ctor_set(v___x_2942_, 1, v_k_2918_);
lean_ctor_set(v___x_2942_, 0, v___x_2950_);
v___x_2952_ = v___x_2942_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_k_2918_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_v_2919_);
lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_r_2937_);
lean_ctor_set(v_reuseFailAlloc_2965_, 4, v_tree_2917_);
v___x_2952_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_isSharedCheck_2959_ = !lean_is_exclusive(v_tree_2917_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; lean_object* v_unused_2961_; lean_object* v_unused_2962_; lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2960_ = lean_ctor_get(v_tree_2917_, 4);
lean_dec(v_unused_2960_);
v_unused_2961_ = lean_ctor_get(v_tree_2917_, 3);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v_tree_2917_, 2);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_tree_2917_, 1);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v_tree_2917_, 0);
lean_dec(v_unused_2964_);
v___x_2954_ = v_tree_2917_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v_tree_2917_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 4, v___x_2952_);
lean_ctor_set(v___x_2954_, 3, v___y_2947_);
lean_ctor_set(v___x_2954_, 2, v_v_2935_);
lean_ctor_set(v___x_2954_, 1, v_k_2934_);
lean_ctor_set(v___x_2954_, 0, v___x_2945_);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_k_2934_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_v_2935_);
lean_ctor_set(v_reuseFailAlloc_2958_, 3, v___y_2947_);
lean_ctor_set(v_reuseFailAlloc_2958_, 4, v___x_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = lean_nat_add(v___x_2966_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec(v___x_2966_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_l_2936_);
lean_ctor_set(v___x_2914_, 3, v_l_2763_);
lean_ctor_set(v___x_2914_, 2, v_v_2762_);
lean_ctor_set(v___x_2914_, 1, v_k_2761_);
lean_ctor_set(v___x_2914_, 0, v___x_2969_);
v___x_2971_ = v___x_2914_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_k_2761_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_v_2762_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_l_2763_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_l_2936_);
v___x_2971_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_nat_add(v___x_2770_, v_size_2920_);
if (lean_obj_tag(v_r_2937_) == 0)
{
lean_object* v_size_2973_; 
v_size_2973_ = lean_ctor_get(v_r_2937_, 0);
lean_inc(v_size_2973_);
v___y_2947_ = v___x_2971_;
v___y_2948_ = v___x_2972_;
v___y_2949_ = v_size_2973_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v___y_2947_ = v___x_2971_;
v___y_2948_ = v___x_2972_;
v___y_2949_ = v___x_2974_;
goto v___jp_2946_;
}
}
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2984_ = lean_nat_add(v___x_2770_, v_size_2760_);
lean_dec(v_size_2760_);
v___x_2985_ = lean_nat_add(v___x_2984_, v_size_2920_);
lean_dec(v___x_2984_);
v___x_2986_ = lean_nat_add(v___x_2770_, v_size_2920_);
v___x_2987_ = lean_nat_add(v___x_2986_, v_size_2933_);
lean_dec(v___x_2986_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_tree_2917_);
lean_ctor_set(v___x_2914_, 3, v_r_2764_);
lean_ctor_set(v___x_2914_, 2, v_v_2919_);
lean_ctor_set(v___x_2914_, 1, v_k_2918_);
lean_ctor_set(v___x_2914_, 0, v___x_2987_);
v___x_2989_ = v___x_2914_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2918_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2919_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_r_2764_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_tree_2917_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 4, v___x_2989_);
lean_ctor_set(v___x_2930_, 0, v___x_2985_);
v___x_2991_ = v___x_2930_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_k_2761_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_v_2762_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_l_2763_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2763_) == 0)
{
lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3023_; 
lean_inc_ref(v_l_2763_);
lean_inc(v_v_2762_);
lean_inc(v_k_2761_);
lean_inc(v_size_2760_);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; lean_object* v_unused_3025_; lean_object* v_unused_3026_; lean_object* v_unused_3027_; lean_object* v_unused_3028_; 
v_unused_3024_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_3025_);
v_unused_3026_ = lean_ctor_get(v_l_2589_, 2);
lean_dec(v_unused_3026_);
v_unused_3027_ = lean_ctor_get(v_l_2589_, 1);
lean_dec(v_unused_3027_);
v_unused_3028_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_3028_);
v___x_3001_ = v_l_2589_;
v_isShared_3002_ = v_isSharedCheck_3023_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v_l_2589_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3023_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
if (lean_obj_tag(v_r_2764_) == 0)
{
lean_object* v_k_3003_; lean_object* v_v_3004_; lean_object* v_size_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v_k_3003_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_k_3003_);
v_v_3004_ = lean_ctor_get(v___x_2916_, 1);
lean_inc(v_v_3004_);
lean_dec_ref(v___x_2916_);
v_size_3005_ = lean_ctor_get(v_r_2764_, 0);
v___x_3006_ = lean_nat_add(v___x_2770_, v_size_2760_);
lean_dec(v_size_2760_);
v___x_3007_ = lean_nat_add(v___x_2770_, v_size_3005_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_tree_2917_);
lean_ctor_set(v___x_2914_, 3, v_r_2764_);
lean_ctor_set(v___x_2914_, 2, v_v_3004_);
lean_ctor_set(v___x_2914_, 1, v_k_3003_);
lean_ctor_set(v___x_2914_, 0, v___x_3007_);
v___x_3009_ = v___x_2914_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_3004_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_r_2764_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_tree_2917_);
v___x_3009_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3011_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 4, v___x_3009_);
lean_ctor_set(v___x_3001_, 0, v___x_3006_);
v___x_3011_ = v___x_3001_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_2761_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_2762_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_l_2763_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
else
{
lean_object* v_k_3014_; lean_object* v_v_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
lean_dec(v_size_2760_);
v_k_3014_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_k_3014_);
v_v_3015_ = lean_ctor_get(v___x_2916_, 1);
lean_inc(v_v_3015_);
lean_dec_ref(v___x_2916_);
v___x_3016_ = lean_unsigned_to_nat(3u);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_r_2764_);
lean_ctor_set(v___x_2914_, 3, v_r_2764_);
lean_ctor_set(v___x_2914_, 2, v_v_3015_);
lean_ctor_set(v___x_2914_, 1, v_k_3014_);
lean_ctor_set(v___x_2914_, 0, v___x_2770_);
v___x_3018_ = v___x_2914_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_k_3014_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_v_3015_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_r_2764_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_r_2764_);
v___x_3018_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3020_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 4, v___x_3018_);
lean_ctor_set(v___x_3001_, 0, v___x_3016_);
v___x_3020_ = v___x_3001_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_k_2761_);
lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_v_2762_);
lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_l_2763_);
lean_ctor_set(v_reuseFailAlloc_3021_, 4, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2764_) == 0)
{
lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3053_; 
lean_inc(v_l_2763_);
lean_inc(v_v_2762_);
lean_inc(v_k_2761_);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_l_2589_);
if (v_isSharedCheck_3053_ == 0)
{
lean_object* v_unused_3054_; lean_object* v_unused_3055_; lean_object* v_unused_3056_; lean_object* v_unused_3057_; lean_object* v_unused_3058_; 
v_unused_3054_ = lean_ctor_get(v_l_2589_, 4);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v_l_2589_, 3);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_l_2589_, 2);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v_l_2589_, 1);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v_l_2589_, 0);
lean_dec(v_unused_3058_);
v___x_3030_ = v_l_2589_;
v_isShared_3031_ = v_isSharedCheck_3053_;
goto v_resetjp_3029_;
}
else
{
lean_dec(v_l_2589_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3053_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v_k_3032_; lean_object* v_v_3033_; lean_object* v_k_3034_; lean_object* v_v_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3049_; 
v_k_3032_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_k_3032_);
v_v_3033_ = lean_ctor_get(v___x_2916_, 1);
lean_inc(v_v_3033_);
lean_dec_ref(v___x_2916_);
v_k_3034_ = lean_ctor_get(v_r_2764_, 1);
v_v_3035_ = lean_ctor_get(v_r_2764_, 2);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_r_2764_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; lean_object* v_unused_3051_; lean_object* v_unused_3052_; 
v_unused_3050_ = lean_ctor_get(v_r_2764_, 4);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v_r_2764_, 3);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v_r_2764_, 0);
lean_dec(v_unused_3052_);
v___x_3037_ = v_r_2764_;
v_isShared_3038_ = v_isSharedCheck_3049_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_v_3035_);
lean_inc(v_k_3034_);
lean_dec(v_r_2764_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3049_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = lean_unsigned_to_nat(3u);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 4, v_l_2763_);
lean_ctor_set(v___x_3037_, 3, v_l_2763_);
lean_ctor_set(v___x_3037_, 2, v_v_2762_);
lean_ctor_set(v___x_3037_, 1, v_k_2761_);
lean_ctor_set(v___x_3037_, 0, v___x_2770_);
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_k_2761_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_v_2762_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_l_2763_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_l_2763_);
v___x_3041_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_l_2763_);
lean_ctor_set(v___x_2914_, 3, v_l_2763_);
lean_ctor_set(v___x_2914_, 2, v_v_3033_);
lean_ctor_set(v___x_2914_, 1, v_k_3032_);
lean_ctor_set(v___x_2914_, 0, v___x_2770_);
v___x_3043_ = v___x_2914_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_k_3032_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_v_3033_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_l_2763_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_l_2763_);
v___x_3043_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3045_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 4, v___x_3043_);
lean_ctor_set(v___x_3030_, 3, v___x_3041_);
lean_ctor_set(v___x_3030_, 2, v_v_3035_);
lean_ctor_set(v___x_3030_, 1, v_k_3034_);
lean_ctor_set(v___x_3030_, 0, v___x_3039_);
v___x_3045_ = v___x_3030_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_k_3034_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_v_3035_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
else
{
lean_object* v_k_3059_; lean_object* v_v_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v_k_3059_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_k_3059_);
v_v_3060_ = lean_ctor_get(v___x_2916_, 1);
lean_inc(v_v_3060_);
lean_dec_ref(v___x_2916_);
v___x_3061_ = lean_unsigned_to_nat(2u);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 4, v_r_2764_);
lean_ctor_set(v___x_2914_, 3, v_l_2589_);
lean_ctor_set(v___x_2914_, 2, v_v_3060_);
lean_ctor_set(v___x_2914_, 1, v_k_3059_);
lean_ctor_set(v___x_2914_, 0, v___x_3061_);
v___x_3063_ = v___x_2914_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_k_3059_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_v_3060_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_r_2764_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
}
else
{
return v_l_2589_;
}
}
else
{
return v_r_2590_;
}
}
}
else
{
lean_object* v_impl_3071_; lean_object* v___x_3072_; 
v_impl_3071_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2585_, v_l_2589_);
v___x_3072_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3071_) == 0)
{
if (lean_obj_tag(v_r_2590_) == 0)
{
lean_object* v_size_3073_; lean_object* v_size_3074_; lean_object* v_k_3075_; lean_object* v_v_3076_; lean_object* v_l_3077_; lean_object* v_r_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_size_3073_ = lean_ctor_get(v_impl_3071_, 0);
lean_inc(v_size_3073_);
v_size_3074_ = lean_ctor_get(v_r_2590_, 0);
v_k_3075_ = lean_ctor_get(v_r_2590_, 1);
v_v_3076_ = lean_ctor_get(v_r_2590_, 2);
v_l_3077_ = lean_ctor_get(v_r_2590_, 3);
lean_inc(v_l_3077_);
v_r_3078_ = lean_ctor_get(v_r_2590_, 4);
v___x_3079_ = lean_unsigned_to_nat(3u);
v___x_3080_ = lean_nat_mul(v___x_3079_, v_size_3073_);
v___x_3081_ = lean_nat_dec_lt(v___x_3080_, v_size_3074_);
lean_dec(v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_dec(v_l_3077_);
v___x_3082_ = lean_nat_add(v___x_3072_, v_size_3073_);
lean_dec(v_size_3073_);
v___x_3083_ = lean_nat_add(v___x_3082_, v_size_3074_);
lean_dec(v___x_3082_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 3, v_impl_3071_);
lean_ctor_set(v___x_2592_, 0, v___x_3083_);
v___x_3085_ = v___x_2592_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_impl_3071_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_r_2590_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
else
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3150_; 
lean_inc(v_r_3078_);
lean_inc(v_v_3076_);
lean_inc(v_k_3075_);
lean_inc(v_size_3074_);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; 
v_unused_3151_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_r_2590_, 2);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_r_2590_, 1);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_3155_);
v___x_3088_ = v_r_2590_;
v_isShared_3089_ = v_isSharedCheck_3150_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v_r_2590_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3150_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v_size_3090_; lean_object* v_k_3091_; lean_object* v_v_3092_; lean_object* v_l_3093_; lean_object* v_r_3094_; lean_object* v_size_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_size_3090_ = lean_ctor_get(v_l_3077_, 0);
v_k_3091_ = lean_ctor_get(v_l_3077_, 1);
v_v_3092_ = lean_ctor_get(v_l_3077_, 2);
v_l_3093_ = lean_ctor_get(v_l_3077_, 3);
v_r_3094_ = lean_ctor_get(v_l_3077_, 4);
v_size_3095_ = lean_ctor_get(v_r_3078_, 0);
v___x_3096_ = lean_unsigned_to_nat(2u);
v___x_3097_ = lean_nat_mul(v___x_3096_, v_size_3095_);
v___x_3098_ = lean_nat_dec_lt(v_size_3090_, v___x_3097_);
lean_dec(v___x_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3126_; 
lean_inc(v_r_3094_);
lean_inc(v_l_3093_);
lean_inc(v_v_3092_);
lean_inc(v_k_3091_);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_l_3077_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; 
v_unused_3127_ = lean_ctor_get(v_l_3077_, 4);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_l_3077_, 3);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_l_3077_, 2);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_l_3077_, 1);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_l_3077_, 0);
lean_dec(v_unused_3131_);
v___x_3100_ = v_l_3077_;
v_isShared_3101_ = v_isSharedCheck_3126_;
goto v_resetjp_3099_;
}
else
{
lean_dec(v_l_3077_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3126_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3116_; 
v___x_3102_ = lean_nat_add(v___x_3072_, v_size_3073_);
lean_dec(v_size_3073_);
v___x_3103_ = lean_nat_add(v___x_3102_, v_size_3074_);
lean_dec(v_size_3074_);
if (lean_obj_tag(v_l_3093_) == 0)
{
lean_object* v_size_3124_; 
v_size_3124_ = lean_ctor_get(v_l_3093_, 0);
lean_inc(v_size_3124_);
v___y_3116_ = v_size_3124_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_unsigned_to_nat(0u);
v___y_3116_ = v___x_3125_;
goto v___jp_3115_;
}
v___jp_3104_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = lean_nat_add(v___y_3105_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec(v___y_3105_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_r_3078_);
lean_ctor_set(v___x_3100_, 3, v_r_3094_);
lean_ctor_set(v___x_3100_, 2, v_v_3076_);
lean_ctor_set(v___x_3100_, 1, v_k_3075_);
lean_ctor_set(v___x_3100_, 0, v___x_3108_);
v___x_3110_ = v___x_3100_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_3075_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_3076_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_r_3094_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_r_3078_);
v___x_3110_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3112_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 4, v___x_3110_);
lean_ctor_set(v___x_3088_, 3, v___y_3106_);
lean_ctor_set(v___x_3088_, 2, v_v_3092_);
lean_ctor_set(v___x_3088_, 1, v_k_3091_);
lean_ctor_set(v___x_3088_, 0, v___x_3103_);
v___x_3112_ = v___x_3088_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_k_3091_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_v_3092_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v___y_3106_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = lean_nat_add(v___x_3102_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec(v___x_3102_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_l_3093_);
lean_ctor_set(v___x_2592_, 3, v_impl_3071_);
lean_ctor_set(v___x_2592_, 0, v___x_3117_);
v___x_3119_ = v___x_2592_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_impl_3071_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_l_3093_);
v___x_3119_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_nat_add(v___x_3072_, v_size_3095_);
if (lean_obj_tag(v_r_3094_) == 0)
{
lean_object* v_size_3121_; 
v_size_3121_ = lean_ctor_get(v_r_3094_, 0);
lean_inc(v_size_3121_);
v___y_3105_ = v___x_3120_;
v___y_3106_ = v___x_3119_;
v___y_3107_ = v_size_3121_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_unsigned_to_nat(0u);
v___y_3105_ = v___x_3120_;
v___y_3106_ = v___x_3119_;
v___y_3107_ = v___x_3122_;
goto v___jp_3104_;
}
}
}
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_del_object(v___x_2592_);
v___x_3132_ = lean_nat_add(v___x_3072_, v_size_3073_);
lean_dec(v_size_3073_);
v___x_3133_ = lean_nat_add(v___x_3132_, v_size_3074_);
lean_dec(v_size_3074_);
v___x_3134_ = lean_nat_add(v___x_3132_, v_size_3090_);
lean_dec(v___x_3132_);
lean_inc_ref(v_impl_3071_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 4, v_l_3077_);
lean_ctor_set(v___x_3088_, 3, v_impl_3071_);
lean_ctor_set(v___x_3088_, 2, v_v_2588_);
lean_ctor_set(v___x_3088_, 1, v_k_2587_);
lean_ctor_set(v___x_3088_, 0, v___x_3134_);
v___x_3136_ = v___x_3088_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_impl_3071_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_l_3077_);
v___x_3136_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_isSharedCheck_3143_ = !lean_is_exclusive(v_impl_3071_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; 
v_unused_3144_ = lean_ctor_get(v_impl_3071_, 4);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_impl_3071_, 3);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v_impl_3071_, 2);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_impl_3071_, 1);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_impl_3071_, 0);
lean_dec(v_unused_3148_);
v___x_3138_ = v_impl_3071_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_dec(v_impl_3071_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 4, v_r_3078_);
lean_ctor_set(v___x_3138_, 3, v___x_3136_);
lean_ctor_set(v___x_3138_, 2, v_v_3076_);
lean_ctor_set(v___x_3138_, 1, v_k_3075_);
lean_ctor_set(v___x_3138_, 0, v___x_3133_);
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_k_3075_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_v_3076_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_r_3078_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v_size_3156_ = lean_ctor_get(v_impl_3071_, 0);
lean_inc(v_size_3156_);
v___x_3157_ = lean_nat_add(v___x_3072_, v_size_3156_);
lean_dec(v_size_3156_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 3, v_impl_3071_);
lean_ctor_set(v___x_2592_, 0, v___x_3157_);
v___x_3159_ = v___x_2592_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_impl_3071_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_r_2590_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
if (lean_obj_tag(v_r_2590_) == 0)
{
lean_object* v_l_3161_; 
v_l_3161_ = lean_ctor_get(v_r_2590_, 3);
lean_inc(v_l_3161_);
if (lean_obj_tag(v_l_3161_) == 0)
{
lean_object* v_r_3162_; 
v_r_3162_ = lean_ctor_get(v_r_2590_, 4);
lean_inc(v_r_3162_);
if (lean_obj_tag(v_r_3162_) == 0)
{
lean_object* v_size_3163_; lean_object* v_k_3164_; lean_object* v_v_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3178_; 
v_size_3163_ = lean_ctor_get(v_r_2590_, 0);
v_k_3164_ = lean_ctor_get(v_r_2590_, 1);
v_v_3165_ = lean_ctor_get(v_r_2590_, 2);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; lean_object* v_unused_3180_; 
v_unused_3179_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_3180_);
v___x_3167_ = v_r_2590_;
v_isShared_3168_ = v_isSharedCheck_3178_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_v_3165_);
lean_inc(v_k_3164_);
lean_inc(v_size_3163_);
lean_dec(v_r_2590_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3178_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_size_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
v_size_3169_ = lean_ctor_get(v_l_3161_, 0);
v___x_3170_ = lean_nat_add(v___x_3072_, v_size_3163_);
lean_dec(v_size_3163_);
v___x_3171_ = lean_nat_add(v___x_3072_, v_size_3169_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_l_3161_);
lean_ctor_set(v___x_3167_, 3, v_impl_3071_);
lean_ctor_set(v___x_3167_, 2, v_v_2588_);
lean_ctor_set(v___x_3167_, 1, v_k_2587_);
lean_ctor_set(v___x_3167_, 0, v___x_3171_);
v___x_3173_ = v___x_3167_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_impl_3071_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_l_3161_);
v___x_3173_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3175_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_r_3162_);
lean_ctor_set(v___x_2592_, 3, v___x_3173_);
lean_ctor_set(v___x_2592_, 2, v_v_3165_);
lean_ctor_set(v___x_2592_, 1, v_k_3164_);
lean_ctor_set(v___x_2592_, 0, v___x_3170_);
v___x_3175_ = v___x_2592_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_k_3164_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_v_3165_);
lean_ctor_set(v_reuseFailAlloc_3176_, 3, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3176_, 4, v_r_3162_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_k_3181_; lean_object* v_v_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3205_; 
v_k_3181_ = lean_ctor_get(v_r_2590_, 1);
v_v_3182_ = lean_ctor_get(v_r_2590_, 2);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; lean_object* v_unused_3208_; 
v_unused_3206_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_3208_);
v___x_3184_ = v_r_2590_;
v_isShared_3185_ = v_isSharedCheck_3205_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_v_3182_);
lean_inc(v_k_3181_);
lean_dec(v_r_2590_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3205_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_k_3186_; lean_object* v_v_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3201_; 
v_k_3186_ = lean_ctor_get(v_l_3161_, 1);
v_v_3187_ = lean_ctor_get(v_l_3161_, 2);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_l_3161_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; lean_object* v_unused_3203_; lean_object* v_unused_3204_; 
v_unused_3202_ = lean_ctor_get(v_l_3161_, 4);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_l_3161_, 3);
lean_dec(v_unused_3203_);
v_unused_3204_ = lean_ctor_get(v_l_3161_, 0);
lean_dec(v_unused_3204_);
v___x_3189_ = v_l_3161_;
v_isShared_3190_ = v_isSharedCheck_3201_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_v_3187_);
lean_inc(v_k_3186_);
lean_dec(v_l_3161_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3201_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_unsigned_to_nat(3u);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 4, v_r_3162_);
lean_ctor_set(v___x_3189_, 3, v_r_3162_);
lean_ctor_set(v___x_3189_, 2, v_v_2588_);
lean_ctor_set(v___x_3189_, 1, v_k_2587_);
lean_ctor_set(v___x_3189_, 0, v___x_3072_);
v___x_3193_ = v___x_3189_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3200_, 3, v_r_3162_);
lean_ctor_set(v_reuseFailAlloc_3200_, 4, v_r_3162_);
v___x_3193_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 3, v_r_3162_);
lean_ctor_set(v___x_3184_, 0, v___x_3072_);
v___x_3195_ = v___x_3184_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_k_3181_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_v_3182_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_r_3162_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_r_3162_);
v___x_3195_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3197_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_3195_);
lean_ctor_set(v___x_2592_, 3, v___x_3193_);
lean_ctor_set(v___x_2592_, 2, v_v_3187_);
lean_ctor_set(v___x_2592_, 1, v_k_3186_);
lean_ctor_set(v___x_2592_, 0, v___x_3191_);
v___x_3197_ = v___x_2592_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_3186_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_3187_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3209_; 
v_r_3209_ = lean_ctor_get(v_r_2590_, 4);
lean_inc(v_r_3209_);
if (lean_obj_tag(v_r_3209_) == 0)
{
lean_object* v_k_3210_; lean_object* v_v_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3222_; 
v_k_3210_ = lean_ctor_get(v_r_2590_, 1);
v_v_3211_ = lean_ctor_get(v_r_2590_, 2);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; 
v_unused_3223_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_3225_);
v___x_3213_ = v_r_2590_;
v_isShared_3214_ = v_isSharedCheck_3222_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_v_3211_);
lean_inc(v_k_3210_);
lean_dec(v_r_2590_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3222_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3215_ = lean_unsigned_to_nat(3u);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 4, v_l_3161_);
lean_ctor_set(v___x_3213_, 2, v_v_2588_);
lean_ctor_set(v___x_3213_, 1, v_k_2587_);
lean_ctor_set(v___x_3213_, 0, v___x_3072_);
v___x_3217_ = v___x_3213_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_l_3161_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_l_3161_);
v___x_3217_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_r_3209_);
lean_ctor_set(v___x_2592_, 3, v___x_3217_);
lean_ctor_set(v___x_2592_, 2, v_v_3211_);
lean_ctor_set(v___x_2592_, 1, v_k_3210_);
lean_ctor_set(v___x_2592_, 0, v___x_3215_);
v___x_3219_ = v___x_2592_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_k_3210_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_v_3211_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_r_3209_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_size_3226_; lean_object* v_k_3227_; lean_object* v_v_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3239_; 
v_size_3226_ = lean_ctor_get(v_r_2590_, 0);
v_k_3227_ = lean_ctor_get(v_r_2590_, 1);
v_v_3228_ = lean_ctor_get(v_r_2590_, 2);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; lean_object* v_unused_3241_; 
v_unused_3240_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_3240_);
v_unused_3241_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_3241_);
v___x_3230_ = v_r_2590_;
v_isShared_3231_ = v_isSharedCheck_3239_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_v_3228_);
lean_inc(v_k_3227_);
lean_inc(v_size_3226_);
lean_dec(v_r_2590_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3239_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 3, v_r_3209_);
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_size_3226_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_k_3227_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_v_3228_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_r_3209_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v_r_3209_);
v___x_3233_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_unsigned_to_nat(2u);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_3233_);
lean_ctor_set(v___x_2592_, 3, v_r_3209_);
lean_ctor_set(v___x_2592_, 0, v___x_3234_);
v___x_3236_ = v___x_2592_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_r_3209_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v___x_3233_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
}
else
{
lean_object* v___x_3243_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 3, v_r_2590_);
lean_ctor_set(v___x_2592_, 0, v___x_3072_);
v___x_3243_ = v___x_2592_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_r_2590_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v_r_2590_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
}
else
{
return v_t_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3247_, lean_object* v_t_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3247_, v_t_3248_);
lean_dec(v_k_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3250_, lean_object* v_j_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3251_, v_ctx_3250_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3253_, lean_object* v_j_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3253_, v_j_3254_);
lean_dec(v_j_3254_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3256_, lean_object* v_k_3257_, lean_object* v_t_3258_, lean_object* v_h_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3257_, v_t_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3261_, lean_object* v_k_3262_, lean_object* v_t_3263_, lean_object* v_h_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3261_, v_k_3262_, v_t_3263_, v_h_3264_);
lean_dec(v_k_3262_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_3266_, v_x_3267_);
if (lean_obj_tag(v___x_3268_) == 1)
{
lean_object* v_val_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3282_; 
v_val_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3282_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_val_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3282_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
switch(lean_obj_tag(v_val_3269_))
{
case 0:
{
lean_object* v_a_3273_; lean_object* v___x_3275_; 
v_a_3273_ = lean_ctor_get(v_val_3269_, 0);
lean_inc(v_a_3273_);
lean_dec_ref(v_val_3269_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v_a_3273_);
v___x_3275_ = v___x_3271_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
case 1:
{
lean_object* v_a_3277_; lean_object* v___x_3279_; 
v_a_3277_ = lean_ctor_get(v_val_3269_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v_val_3269_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v_a_3277_);
v___x_3279_ = v___x_3271_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
default: 
{
lean_object* v___x_3281_; 
lean_del_object(v___x_3271_);
lean_dec(v_val_3269_);
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
}
}
}
else
{
lean_object* v___x_3283_; 
lean_dec(v___x_3268_);
v___x_3283_ = lean_box(0);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3284_, lean_object* v_x_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_IR_LocalContext_getType(v_ctx_3284_, v_x_3285_);
lean_dec(v_x_3285_);
lean_dec(v_ctx_3284_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_3287_, v_x_3288_);
if (lean_obj_tag(v___x_3289_) == 1)
{
lean_object* v_val_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3299_; 
v_val_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3299_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_val_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3299_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
if (lean_obj_tag(v_val_3290_) == 1)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; 
v_a_3294_ = lean_ctor_get(v_val_3290_, 1);
lean_inc_ref(v_a_3294_);
lean_dec_ref(v_val_3290_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_a_3294_);
v___x_3296_ = v___x_3292_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
else
{
lean_object* v___x_3298_; 
lean_del_object(v___x_3292_);
lean_dec(v_val_3290_);
v___x_3298_ = lean_box(0);
return v___x_3298_;
}
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v___x_3289_);
v___x_3300_ = lean_box(0);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_IR_LocalContext_getValue(v_ctx_3301_, v_x_3302_);
lean_dec(v_x_3302_);
lean_dec(v_ctx_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3304_, lean_object* v_v_u2081_3305_, lean_object* v_v_u2082_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_00_u03c1_3304_, v_v_u2081_3305_);
if (lean_obj_tag(v___x_3307_) == 0)
{
uint8_t v___x_3308_; 
v___x_3308_ = lean_nat_dec_eq(v_v_u2081_3305_, v_v_u2082_3306_);
return v___x_3308_;
}
else
{
lean_object* v_val_3309_; uint8_t v___x_3310_; 
v_val_3309_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_val_3309_);
lean_dec_ref(v___x_3307_);
v___x_3310_ = lean_nat_dec_eq(v_val_3309_, v_v_u2082_3306_);
lean_dec(v_val_3309_);
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3311_, lean_object* v_v_u2081_3312_, lean_object* v_v_u2082_3313_){
_start:
{
uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_res_3314_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3311_, v_v_u2081_3312_, v_v_u2082_3313_);
lean_dec(v_v_u2082_3313_);
lean_dec(v_v_u2081_3312_);
lean_dec(v_00_u03c1_3311_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
if (lean_obj_tag(v_x_3320_) == 0)
{
lean_object* v_id_3321_; lean_object* v_id_3322_; uint8_t v___x_3323_; 
v_id_3321_ = lean_ctor_get(v_x_3319_, 0);
v_id_3322_ = lean_ctor_get(v_x_3320_, 0);
v___x_3323_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3318_, v_id_3321_, v_id_3322_);
return v___x_3323_;
}
else
{
uint8_t v___x_3324_; 
v___x_3324_ = 0;
return v___x_3324_;
}
}
else
{
if (lean_obj_tag(v_x_3320_) == 1)
{
uint8_t v___x_3325_; 
v___x_3325_ = 1;
return v___x_3325_;
}
else
{
uint8_t v___x_3326_; 
v___x_3326_ = 0;
return v___x_3326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_){
_start:
{
uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_res_3330_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3327_, v_x_3328_, v_x_3329_);
lean_dec(v_x_3329_);
lean_dec(v_x_3328_);
lean_dec(v_00_u03c1_3327_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3334_, lean_object* v_xs_3335_, lean_object* v_ys_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v_zero_3338_; uint8_t v_isZero_3339_; 
v_zero_3338_ = lean_unsigned_to_nat(0u);
v_isZero_3339_ = lean_nat_dec_eq(v_x_3337_, v_zero_3338_);
if (v_isZero_3339_ == 1)
{
lean_dec(v_x_3337_);
return v_isZero_3339_;
}
else
{
lean_object* v_one_3340_; lean_object* v_n_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_one_3340_ = lean_unsigned_to_nat(1u);
v_n_3341_ = lean_nat_sub(v_x_3337_, v_one_3340_);
lean_dec(v_x_3337_);
v___x_3342_ = lean_array_fget_borrowed(v_xs_3335_, v_n_3341_);
v___x_3343_ = lean_array_fget_borrowed(v_ys_3336_, v_n_3341_);
v___x_3344_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3334_, v___x_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_dec(v_n_3341_);
return v___x_3344_;
}
else
{
v_x_3337_ = v_n_3341_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3346_, lean_object* v_xs_3347_, lean_object* v_ys_3348_, lean_object* v_x_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3346_, v_xs_3347_, v_ys_3348_, v_x_3349_);
lean_dec_ref(v_ys_3348_);
lean_dec_ref(v_xs_3347_);
lean_dec(v_00_u03c1_3346_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3352_, lean_object* v_args_u2081_3353_, lean_object* v_args_u2082_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3355_ = lean_array_get_size(v_args_u2081_3353_);
v___x_3356_ = lean_array_get_size(v_args_u2082_3354_);
v___x_3357_ = lean_nat_dec_eq(v___x_3355_, v___x_3356_);
if (v___x_3357_ == 0)
{
return v___x_3357_;
}
else
{
uint8_t v___x_3358_; 
v___x_3358_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3352_, v_args_u2081_3353_, v_args_u2082_3354_, v___x_3355_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3359_, lean_object* v_args_u2081_3360_, lean_object* v_args_u2082_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3359_, v_args_u2081_3360_, v_args_u2082_3361_);
lean_dec_ref(v_args_u2082_3361_);
lean_dec_ref(v_args_u2081_3360_);
lean_dec(v_00_u03c1_3359_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3364_, lean_object* v_xs_3365_, lean_object* v_ys_3366_, lean_object* v_hsz_3367_, lean_object* v_x_3368_, lean_object* v_x_3369_){
_start:
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3364_, v_xs_3365_, v_ys_3366_, v_x_3368_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3371_, lean_object* v_xs_3372_, lean_object* v_ys_3373_, lean_object* v_hsz_3374_, lean_object* v_x_3375_, lean_object* v_x_3376_){
_start:
{
uint8_t v_res_3377_; lean_object* v_r_3378_; 
v_res_3377_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3371_, v_xs_3372_, v_ys_3373_, v_hsz_3374_, v_x_3375_, v_x_3376_);
lean_dec_ref(v_ys_3373_);
lean_dec_ref(v_xs_3372_);
lean_dec(v_00_u03c1_3371_);
v_r_3378_ = lean_box(v_res_3377_);
return v_r_3378_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* v_00_u03c1_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_){
_start:
{
lean_object* v_n_u2081_3385_; lean_object* v_x_u2081_3386_; lean_object* v_n_u2082_3387_; lean_object* v_x_u2082_3388_; lean_object* v_c_u2081_3392_; lean_object* v_ys_u2081_3393_; lean_object* v_c_u2082_3394_; lean_object* v_ys_u2082_3395_; 
switch(lean_obj_tag(v_x_3382_))
{
case 0:
{
if (lean_obj_tag(v_x_3383_) == 0)
{
lean_object* v_i_3398_; lean_object* v_ys_3399_; lean_object* v_i_3400_; lean_object* v_ys_3401_; uint8_t v___x_3402_; 
v_i_3398_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3399_ = lean_ctor_get(v_x_3382_, 1);
v_i_3400_ = lean_ctor_get(v_x_3383_, 0);
v_ys_3401_ = lean_ctor_get(v_x_3383_, 1);
v___x_3402_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3398_, v_i_3400_);
if (v___x_3402_ == 0)
{
return v___x_3402_;
}
else
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3381_, v_ys_3399_, v_ys_3401_);
return v___x_3403_;
}
}
else
{
uint8_t v___x_3404_; 
v___x_3404_ = 0;
return v___x_3404_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3383_) == 1)
{
lean_object* v_n_3405_; lean_object* v_x_3406_; lean_object* v_n_3407_; lean_object* v_x_3408_; 
v_n_3405_ = lean_ctor_get(v_x_3382_, 0);
v_x_3406_ = lean_ctor_get(v_x_3382_, 1);
v_n_3407_ = lean_ctor_get(v_x_3383_, 0);
v_x_3408_ = lean_ctor_get(v_x_3383_, 1);
v_n_u2081_3385_ = v_n_3405_;
v_x_u2081_3386_ = v_x_3406_;
v_n_u2082_3387_ = v_n_3407_;
v_x_u2082_3388_ = v_x_3408_;
goto v___jp_3384_;
}
else
{
uint8_t v___x_3409_; 
v___x_3409_ = 0;
return v___x_3409_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3383_) == 2)
{
lean_object* v_x_3410_; lean_object* v_i_3411_; uint8_t v_updtHeader_3412_; lean_object* v_ys_3413_; lean_object* v_x_3414_; lean_object* v_i_3415_; uint8_t v_updtHeader_3416_; lean_object* v_ys_3417_; uint8_t v___y_3419_; uint8_t v___x_3422_; 
v_x_3410_ = lean_ctor_get(v_x_3382_, 0);
v_i_3411_ = lean_ctor_get(v_x_3382_, 1);
v_updtHeader_3412_ = lean_ctor_get_uint8(v_x_3382_, sizeof(void*)*3);
v_ys_3413_ = lean_ctor_get(v_x_3382_, 2);
v_x_3414_ = lean_ctor_get(v_x_3383_, 0);
v_i_3415_ = lean_ctor_get(v_x_3383_, 1);
v_updtHeader_3416_ = lean_ctor_get_uint8(v_x_3383_, sizeof(void*)*3);
v_ys_3417_ = lean_ctor_get(v_x_3383_, 2);
v___x_3422_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_3410_, v_x_3414_);
if (v___x_3422_ == 0)
{
v___y_3419_ = v___x_3422_;
goto v___jp_3418_;
}
else
{
uint8_t v___x_3423_; 
v___x_3423_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3411_, v_i_3415_);
v___y_3419_ = v___x_3423_;
goto v___jp_3418_;
}
v___jp_3418_:
{
if (v___y_3419_ == 0)
{
return v___y_3419_;
}
else
{
if (v_updtHeader_3412_ == 0)
{
if (v_updtHeader_3416_ == 0)
{
uint8_t v___x_3420_; 
v___x_3420_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3381_, v_ys_3413_, v_ys_3417_);
return v___x_3420_;
}
else
{
return v_updtHeader_3412_;
}
}
else
{
if (v_updtHeader_3416_ == 0)
{
return v_updtHeader_3416_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3381_, v_ys_3413_, v_ys_3417_);
return v___x_3421_;
}
}
}
}
}
else
{
uint8_t v___x_3424_; 
v___x_3424_ = 0;
return v___x_3424_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3383_) == 3)
{
lean_object* v_i_3425_; lean_object* v_x_3426_; lean_object* v_i_3427_; lean_object* v_x_3428_; 
v_i_3425_ = lean_ctor_get(v_x_3382_, 0);
v_x_3426_ = lean_ctor_get(v_x_3382_, 1);
v_i_3427_ = lean_ctor_get(v_x_3383_, 0);
v_x_3428_ = lean_ctor_get(v_x_3383_, 1);
v_n_u2081_3385_ = v_i_3425_;
v_x_u2081_3386_ = v_x_3426_;
v_n_u2082_3387_ = v_i_3427_;
v_x_u2082_3388_ = v_x_3428_;
goto v___jp_3384_;
}
else
{
uint8_t v___x_3429_; 
v___x_3429_ = 0;
return v___x_3429_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3383_) == 4)
{
lean_object* v_i_3430_; lean_object* v_x_3431_; lean_object* v_i_3432_; lean_object* v_x_3433_; 
v_i_3430_ = lean_ctor_get(v_x_3382_, 0);
v_x_3431_ = lean_ctor_get(v_x_3382_, 1);
v_i_3432_ = lean_ctor_get(v_x_3383_, 0);
v_x_3433_ = lean_ctor_get(v_x_3383_, 1);
v_n_u2081_3385_ = v_i_3430_;
v_x_u2081_3386_ = v_x_3431_;
v_n_u2082_3387_ = v_i_3432_;
v_x_u2082_3388_ = v_x_3433_;
goto v___jp_3384_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = 0;
return v___x_3434_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3383_) == 5)
{
lean_object* v_n_3435_; lean_object* v_offset_3436_; lean_object* v_x_3437_; lean_object* v_n_3438_; lean_object* v_offset_3439_; lean_object* v_x_3440_; uint8_t v___y_3442_; uint8_t v___x_3444_; 
v_n_3435_ = lean_ctor_get(v_x_3382_, 0);
v_offset_3436_ = lean_ctor_get(v_x_3382_, 1);
v_x_3437_ = lean_ctor_get(v_x_3382_, 2);
v_n_3438_ = lean_ctor_get(v_x_3383_, 0);
v_offset_3439_ = lean_ctor_get(v_x_3383_, 1);
v_x_3440_ = lean_ctor_get(v_x_3383_, 2);
v___x_3444_ = lean_nat_dec_eq(v_n_3435_, v_n_3438_);
if (v___x_3444_ == 0)
{
v___y_3442_ = v___x_3444_;
goto v___jp_3441_;
}
else
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_nat_dec_eq(v_offset_3436_, v_offset_3439_);
v___y_3442_ = v___x_3445_;
goto v___jp_3441_;
}
v___jp_3441_:
{
if (v___y_3442_ == 0)
{
return v___y_3442_;
}
else
{
uint8_t v___x_3443_; 
v___x_3443_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_3437_, v_x_3440_);
return v___x_3443_;
}
}
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = 0;
return v___x_3446_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3383_) == 6)
{
lean_object* v_c_3447_; lean_object* v_ys_3448_; lean_object* v_c_3449_; lean_object* v_ys_3450_; 
v_c_3447_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3448_ = lean_ctor_get(v_x_3382_, 1);
v_c_3449_ = lean_ctor_get(v_x_3383_, 0);
v_ys_3450_ = lean_ctor_get(v_x_3383_, 1);
v_c_u2081_3392_ = v_c_3447_;
v_ys_u2081_3393_ = v_ys_3448_;
v_c_u2082_3394_ = v_c_3449_;
v_ys_u2082_3395_ = v_ys_3450_;
goto v___jp_3391_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = 0;
return v___x_3451_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3383_) == 7)
{
lean_object* v_c_3452_; lean_object* v_ys_3453_; lean_object* v_c_3454_; lean_object* v_ys_3455_; 
v_c_3452_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3453_ = lean_ctor_get(v_x_3382_, 1);
v_c_3454_ = lean_ctor_get(v_x_3383_, 0);
v_ys_3455_ = lean_ctor_get(v_x_3383_, 1);
v_c_u2081_3392_ = v_c_3452_;
v_ys_u2081_3393_ = v_ys_3453_;
v_c_u2082_3394_ = v_c_3454_;
v_ys_u2082_3395_ = v_ys_3455_;
goto v___jp_3391_;
}
else
{
uint8_t v___x_3456_; 
v___x_3456_ = 0;
return v___x_3456_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3383_) == 8)
{
lean_object* v_x_3457_; lean_object* v_ys_3458_; lean_object* v_x_3459_; lean_object* v_ys_3460_; uint8_t v___x_3461_; 
v_x_3457_ = lean_ctor_get(v_x_3382_, 0);
v_ys_3458_ = lean_ctor_get(v_x_3382_, 1);
v_x_3459_ = lean_ctor_get(v_x_3383_, 0);
v_ys_3460_ = lean_ctor_get(v_x_3383_, 1);
v___x_3461_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_3457_, v_x_3459_);
if (v___x_3461_ == 0)
{
return v___x_3461_;
}
else
{
uint8_t v___x_3462_; 
v___x_3462_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3381_, v_ys_3458_, v_ys_3460_);
return v___x_3462_;
}
}
else
{
uint8_t v___x_3463_; 
v___x_3463_ = 0;
return v___x_3463_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3383_) == 9)
{
lean_object* v_ty_3464_; lean_object* v_x_3465_; lean_object* v_ty_3466_; lean_object* v_x_3467_; uint8_t v___x_3468_; 
v_ty_3464_ = lean_ctor_get(v_x_3382_, 0);
v_x_3465_ = lean_ctor_get(v_x_3382_, 1);
v_ty_3466_ = lean_ctor_get(v_x_3383_, 0);
v_x_3467_ = lean_ctor_get(v_x_3383_, 1);
v___x_3468_ = l_Lean_IR_instBEqIRType_beq(v_ty_3464_, v_ty_3466_);
if (v___x_3468_ == 0)
{
return v___x_3468_;
}
else
{
uint8_t v___x_3469_; 
v___x_3469_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_3465_, v_x_3467_);
return v___x_3469_;
}
}
else
{
uint8_t v___x_3470_; 
v___x_3470_ = 0;
return v___x_3470_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3383_) == 10)
{
lean_object* v_x_3471_; lean_object* v_x_3472_; uint8_t v___x_3473_; 
v_x_3471_ = lean_ctor_get(v_x_3382_, 0);
v_x_3472_ = lean_ctor_get(v_x_3383_, 0);
v___x_3473_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_3471_, v_x_3472_);
return v___x_3473_;
}
else
{
uint8_t v___x_3474_; 
v___x_3474_ = 0;
return v___x_3474_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3383_) == 11)
{
lean_object* v_v_3475_; lean_object* v_v_3476_; uint8_t v___x_3477_; 
v_v_3475_ = lean_ctor_get(v_x_3382_, 0);
v_v_3476_ = lean_ctor_get(v_x_3383_, 0);
v___x_3477_ = l_Lean_IR_instBEqLitVal_beq(v_v_3475_, v_v_3476_);
return v___x_3477_;
}
else
{
uint8_t v___x_3478_; 
v___x_3478_ = 0;
return v___x_3478_;
}
}
default: 
{
if (lean_obj_tag(v_x_3383_) == 12)
{
lean_object* v_x_3479_; lean_object* v_x_3480_; uint8_t v___x_3481_; 
v_x_3479_ = lean_ctor_get(v_x_3382_, 0);
v_x_3480_ = lean_ctor_get(v_x_3383_, 0);
v___x_3481_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_3479_, v_x_3480_);
return v___x_3481_;
}
else
{
uint8_t v___x_3482_; 
v___x_3482_ = 0;
return v___x_3482_;
}
}
}
v___jp_3384_:
{
uint8_t v___x_3389_; 
v___x_3389_ = lean_nat_dec_eq(v_n_u2081_3385_, v_n_u2082_3387_);
if (v___x_3389_ == 0)
{
return v___x_3389_;
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3381_, v_x_u2081_3386_, v_x_u2082_3388_);
return v___x_3390_;
}
}
v___jp_3391_:
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_name_eq(v_c_u2081_3392_, v_c_u2082_3394_);
if (v___x_3396_ == 0)
{
return v___x_3396_;
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3381_, v_ys_u2081_3393_, v_ys_u2082_3395_);
return v___x_3397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* v_00_u03c1_3483_, lean_object* v_x_3484_, lean_object* v_x_3485_){
_start:
{
uint8_t v_res_3486_; lean_object* v_r_3487_; 
v_res_3486_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_3483_, v_x_3484_, v_x_3485_);
lean_dec_ref(v_x_3485_);
lean_dec_ref(v_x_3484_);
lean_dec(v_00_u03c1_3483_);
v_r_3487_ = lean_box(v_res_3486_);
return v_r_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3490_, lean_object* v_x_u2081_3491_, lean_object* v_x_u2082_3492_){
_start:
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_nat_dec_eq(v_x_u2081_3491_, v_x_u2082_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3491_, v_x_u2082_3492_, v_00_u03c1_3490_);
return v___x_3494_;
}
else
{
lean_dec(v_x_u2082_3492_);
lean_dec(v_x_u2081_3491_);
return v_00_u03c1_3490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3495_, lean_object* v_p_u2081_3496_, lean_object* v_p_u2082_3497_){
_start:
{
lean_object* v_x_3498_; uint8_t v_borrow_3499_; lean_object* v_ty_3500_; lean_object* v_x_3501_; uint8_t v_borrow_3502_; lean_object* v_ty_3503_; uint8_t v___y_3505_; uint8_t v___x_3509_; 
v_x_3498_ = lean_ctor_get(v_p_u2081_3496_, 0);
lean_inc(v_x_3498_);
v_borrow_3499_ = lean_ctor_get_uint8(v_p_u2081_3496_, sizeof(void*)*2);
v_ty_3500_ = lean_ctor_get(v_p_u2081_3496_, 1);
lean_inc(v_ty_3500_);
lean_dec_ref(v_p_u2081_3496_);
v_x_3501_ = lean_ctor_get(v_p_u2082_3497_, 0);
lean_inc(v_x_3501_);
v_borrow_3502_ = lean_ctor_get_uint8(v_p_u2082_3497_, sizeof(void*)*2);
v_ty_3503_ = lean_ctor_get(v_p_u2082_3497_, 1);
lean_inc(v_ty_3503_);
lean_dec_ref(v_p_u2082_3497_);
v___x_3509_ = l_Lean_IR_instBEqIRType_beq(v_ty_3500_, v_ty_3503_);
lean_dec(v_ty_3503_);
lean_dec(v_ty_3500_);
if (v___x_3509_ == 0)
{
v___y_3505_ = v___x_3509_;
goto v___jp_3504_;
}
else
{
if (v_borrow_3499_ == 0)
{
if (v_borrow_3502_ == 0)
{
v___y_3505_ = v___x_3509_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3510_; 
lean_dec(v_x_3501_);
lean_dec(v_x_3498_);
lean_dec(v_00_u03c1_3495_);
v___x_3510_ = lean_box(0);
return v___x_3510_;
}
}
else
{
v___y_3505_ = v_borrow_3502_;
goto v___jp_3504_;
}
}
v___jp_3504_:
{
if (v___y_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v_x_3501_);
lean_dec(v_x_3498_);
lean_dec(v_00_u03c1_3495_);
v___x_3506_ = lean_box(0);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = l_Lean_IR_addVarRename(v_00_u03c1_3495_, v_x_3498_, v_x_3501_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
return v___x_3508_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3511_, lean_object* v_ps_u2081_3512_, lean_object* v_ps_u2082_3513_, lean_object* v_a_3514_, lean_object* v_b_3515_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_nat_dec_lt(v_a_3514_, v_upperBound_3511_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v_a_3514_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_b_3515_);
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3518_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_3519_ = lean_array_get_borrowed(v___x_3518_, v_ps_u2081_3512_, v_a_3514_);
v___x_3520_ = lean_array_get_borrowed(v___x_3518_, v_ps_u2082_3513_, v_a_3514_);
lean_inc(v___x_3520_);
lean_inc(v___x_3519_);
v___x_3521_ = l_Lean_IR_addParamRename(v_b_3515_, v___x_3519_, v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_dec(v_a_3514_);
return v___x_3521_;
}
else
{
lean_object* v_val_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_val_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_val_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = lean_unsigned_to_nat(1u);
v___x_3524_ = lean_nat_add(v_a_3514_, v___x_3523_);
lean_dec(v_a_3514_);
v_a_3514_ = v___x_3524_;
v_b_3515_ = v_val_3522_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_3526_, lean_object* v_ps_u2081_3527_, lean_object* v_ps_u2082_3528_, lean_object* v_a_3529_, lean_object* v_b_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3526_, v_ps_u2081_3527_, v_ps_u2082_3528_, v_a_3529_, v_b_3530_);
lean_dec_ref(v_ps_u2082_3528_);
lean_dec_ref(v_ps_u2081_3527_);
lean_dec(v_upperBound_3526_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_3532_, lean_object* v_ps_u2081_3533_, lean_object* v_ps_u2082_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v___x_3535_ = lean_array_get_size(v_ps_u2081_3533_);
v___x_3536_ = lean_array_get_size(v_ps_u2082_3534_);
v___x_3537_ = lean_nat_dec_eq(v___x_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
lean_dec(v_00_u03c1_3532_);
v___x_3538_ = lean_box(0);
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_3535_, v_ps_u2081_3533_, v_ps_u2082_3534_, v___x_3539_, v_00_u03c1_3532_);
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
lean_dec_ref(v_x_3564_);
v_x_3601_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3601_);
v_ty_3602_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_ty_3602_);
v_e_3603_ = lean_ctor_get(v_x_3565_, 2);
lean_inc_ref(v_e_3603_);
v_b_3604_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3604_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_j_3616_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_j_3616_);
v_xs_3617_ = lean_ctor_get(v_x_3565_, 1);
lean_inc_ref(v_xs_3617_);
v_v_3618_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_v_3618_);
v_b_3619_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3619_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v___x_3620_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3631_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3631_);
v_i_3632_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_i_3632_);
v_y_3633_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_y_3633_);
v_b_3634_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3634_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3645_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3645_);
v_cidx_3646_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_cidx_3646_);
v_b_3647_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_b_3647_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3658_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3658_);
v_i_3659_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_i_3659_);
v_y_3660_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_y_3660_);
v_b_3661_ = lean_ctor_get(v_x_3565_, 3);
lean_inc(v_b_3661_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3695_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3695_);
v_n_3696_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_n_3696_);
v_c_3697_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3);
v_persistent_3698_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3 + 1);
v_b_3699_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_b_3699_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3706_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3706_);
v_n_3707_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_n_3707_);
v_c_3708_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3);
v_persistent_3709_ = lean_ctor_get_uint8(v_x_3565_, sizeof(void*)*3 + 1);
v_b_3710_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_b_3710_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3714_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3714_);
v_b_3715_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_b_3715_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_tid_3722_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_tid_3722_);
v_x_3723_ = lean_ctor_get(v_x_3565_, 1);
lean_inc(v_x_3723_);
v_cs_3724_ = lean_ctor_get(v_x_3565_, 3);
lean_inc_ref(v_cs_3724_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_x_3735_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_x_3735_);
lean_dec_ref(v_x_3565_);
v___x_3736_ = l_Lean_IR_Arg_alphaEqv(v_x_3563_, v_x_3734_, v_x_3735_);
lean_dec(v_x_3735_);
lean_dec(v_x_3734_);
lean_dec(v_x_3563_);
return v___x_3736_;
}
else
{
uint8_t v___x_3737_; 
lean_dec_ref(v_x_3564_);
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
lean_dec_ref(v_x_3564_);
v_j_3740_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_j_3740_);
v_ys_3741_ = lean_ctor_get(v_x_3565_, 1);
lean_inc_ref(v_ys_3741_);
lean_dec_ref(v_x_3565_);
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
lean_dec_ref(v_x_3564_);
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
