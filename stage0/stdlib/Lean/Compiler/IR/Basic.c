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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_IR_instBEqIRType_beq_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctor_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctor_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reset_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reset_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reuse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reuse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uproj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uproj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sproj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sproj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_fap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_fap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_pap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_pap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_box_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_box_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unbox_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unbox_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint8Lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint8Lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint16Lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint16Lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint32Lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint32Lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint64Lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint64Lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_usizeLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_usizeLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_natLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_natLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_strLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_strLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isShared_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isShared_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 27}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value)}};
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
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isVarDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isVarDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_targetVar_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_FnBody_targetVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Compiler.IR.Basic"};
static const lean_object* l_Lean_IR_FnBody_targetVar___closed__0 = (const lean_object*)&l_Lean_IR_FnBody_targetVar___closed__0_value;
static const lean_string_object l_Lean_IR_FnBody_targetVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.IR.FnBody.targetVar"};
static const lean_object* l_Lean_IR_FnBody_targetVar___closed__1 = (const lean_object*)&l_Lean_IR_FnBody_targetVar___closed__1_value;
static const lean_string_object l_Lean_IR_FnBody_targetVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "expected var decl"};
static const lean_object* l_Lean_IR_FnBody_targetVar___closed__2 = (const lean_object*)&l_Lean_IR_FnBody_targetVar___closed__2_value;
static lean_once_cell_t l_Lean_IR_FnBody_targetVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_FnBody_targetVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_targetType_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_FnBody_targetType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.IR.FnBody.targetType"};
static const lean_object* l_Lean_IR_FnBody_targetType___closed__0 = (const lean_object*)&l_Lean_IR_FnBody_targetType___closed__0_value;
static lean_once_cell_t l_Lean_IR_FnBody_targetType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_FnBody_targetType___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_setTargetVar_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_FnBody_setTargetVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.IR.FnBody.setTargetVar"};
static const lean_object* l_Lean_IR_FnBody_setTargetVar___closed__0 = (const lean_object*)&l_Lean_IR_FnBody_setTargetVar___closed__0_value;
static lean_once_cell_t l_Lean_IR_FnBody_setTargetVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_FnBody_setTargetVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTargetVar(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_IR_Decl_getInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_Decl_getInfo___closed__0 = (const lean_object*)&l_Lean_IR_Decl_getInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_Decl_updateBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.IR.Decl.updateBody!"};
static const lean_object* l_Lean_IR_Decl_updateBody_x21___closed__0 = (const lean_object*)&l_Lean_IR_Decl_updateBody_x21___closed__0_value;
static const lean_string_object l_Lean_IR_Decl_updateBody_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected definition"};
static const lean_object* l_Lean_IR_Decl_updateBody_x21___closed__1 = (const lean_object*)&l_Lean_IR_Decl_updateBody_x21___closed__1_value;
static lean_once_cell_t l_Lean_IR_Decl_updateBody_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx___impl(lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_tag_nat(v_x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorIdx___impl___boxed(lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_IR_IRType_ctorIdx___impl(v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim___redArg(lean_object* v_t_140_, lean_object* v_k_141_){
_start:
{
switch(lean_obj_tag(v_t_140_))
{
case 10:
{
lean_object* v_leanTypeName_142_; lean_object* v_types_143_; lean_object* v___x_144_; 
v_leanTypeName_142_ = lean_ctor_get(v_t_140_, 0);
lean_inc(v_leanTypeName_142_);
v_types_143_ = lean_ctor_get(v_t_140_, 1);
lean_inc_ref(v_types_143_);
lean_dec_ref_known(v_t_140_, 2);
v___x_144_ = lean_apply_2(v_k_141_, v_leanTypeName_142_, v_types_143_);
return v___x_144_;
}
case 11:
{
lean_object* v_leanTypeName_145_; lean_object* v_types_146_; lean_object* v___x_147_; 
v_leanTypeName_145_ = lean_ctor_get(v_t_140_, 0);
lean_inc(v_leanTypeName_145_);
v_types_146_ = lean_ctor_get(v_t_140_, 1);
lean_inc_ref(v_types_146_);
lean_dec_ref_known(v_t_140_, 2);
v___x_147_ = lean_apply_2(v_k_141_, v_leanTypeName_145_, v_types_146_);
return v___x_147_;
}
default: 
{
lean_dec(v_t_140_);
return v_k_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim(lean_object* v_motive__1_148_, lean_object* v_ctorIdx_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_150_, v_k_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_ctorElim___boxed(lean_object* v_motive__1_154_, lean_object* v_ctorIdx_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_k_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_IR_IRType_ctorElim(v_motive__1_154_, v_ctorIdx_155_, v_t_156_, v_h_157_, v_k_158_);
lean_dec(v_ctorIdx_155_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float_elim___redArg(lean_object* v_t_160_, lean_object* v_float_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_160_, v_float_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float_elim(lean_object* v_motive__1_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_float_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_164_, v_float_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint8_elim___redArg(lean_object* v_t_168_, lean_object* v_uint8_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_168_, v_uint8_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint8_elim(lean_object* v_motive__1_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_uint8_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_172_, v_uint8_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint16_elim___redArg(lean_object* v_t_176_, lean_object* v_uint16_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_176_, v_uint16_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint16_elim(lean_object* v_motive__1_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_uint16_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_180_, v_uint16_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint32_elim___redArg(lean_object* v_t_184_, lean_object* v_uint32_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_184_, v_uint32_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint32_elim(lean_object* v_motive__1_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_uint32_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_188_, v_uint32_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint64_elim___redArg(lean_object* v_t_192_, lean_object* v_uint64_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_192_, v_uint64_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_uint64_elim(lean_object* v_motive__1_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_uint64_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_196_, v_uint64_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_usize_elim___redArg(lean_object* v_t_200_, lean_object* v_usize_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_200_, v_usize_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_usize_elim(lean_object* v_motive__1_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_usize_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_204_, v_usize_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_erased_elim___redArg(lean_object* v_t_208_, lean_object* v_erased_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_208_, v_erased_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_erased_elim(lean_object* v_motive__1_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_erased_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_212_, v_erased_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_object_elim___redArg(lean_object* v_t_216_, lean_object* v_object_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_216_, v_object_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_object_elim(lean_object* v_motive__1_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_object_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_220_, v_object_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tobject_elim___redArg(lean_object* v_t_224_, lean_object* v_tobject_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_224_, v_tobject_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tobject_elim(lean_object* v_motive__1_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_tobject_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_228_, v_tobject_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float32_elim___redArg(lean_object* v_t_232_, lean_object* v_float32_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_232_, v_float32_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_float32_elim(lean_object* v_motive__1_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_float32_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_236_, v_float32_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_struct_elim___redArg(lean_object* v_t_240_, lean_object* v_struct_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_240_, v_struct_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_struct_elim(lean_object* v_motive__1_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_struct_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_244_, v_struct_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_union_elim___redArg(lean_object* v_t_248_, lean_object* v_union_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_248_, v_union_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_union_elim(lean_object* v_motive__1_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_union_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_252_, v_union_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tagged_elim___redArg(lean_object* v_t_256_, lean_object* v_tagged_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_256_, v_tagged_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_tagged_elim(lean_object* v_motive__1_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_tagged_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_260_, v_tagged_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_void_elim___redArg(lean_object* v_t_264_, lean_object* v_void_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_264_, v_void_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_void_elim(lean_object* v_motive__1_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_void_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_268_, v_void_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedIRType_default(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedIRType(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
if (lean_obj_tag(v_x_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 1;
return v___x_276_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
}
else
{
if (lean_obj_tag(v_x_275_) == 0)
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
else
{
lean_object* v_val_279_; lean_object* v_val_280_; uint8_t v___x_281_; 
v_val_279_ = lean_ctor_get(v_x_274_, 0);
v_val_280_ = lean_ctor_get(v_x_275_, 0);
v___x_281_ = lean_name_eq(v_val_279_, v_val_280_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_IR_instBEqIRType_beq_spec__0___boxed(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_instBEqOption_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(v_x_282_, v_x_283_);
lean_dec(v_x_283_);
lean_dec(v_x_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqIRType_beq(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v_decide_290_; 
v___x_288_ = lean_obj_tag_nat(v_x_286_);
v___x_289_ = lean_obj_tag_nat(v_x_287_);
v_decide_290_ = lean_nat_dec_eq(v___x_288_, v___x_289_);
if (v_decide_290_ == 0)
{
return v_decide_290_;
}
else
{
switch(lean_obj_tag(v_x_286_))
{
case 10:
{
lean_object* v_leanTypeName_291_; lean_object* v_types_292_; lean_object* v_leanTypeName_293_; lean_object* v_types_294_; uint8_t v___x_295_; 
v_leanTypeName_291_ = lean_ctor_get(v_x_286_, 0);
v_types_292_ = lean_ctor_get(v_x_286_, 1);
v_leanTypeName_293_ = lean_ctor_get(v_x_287_, 0);
v_types_294_ = lean_ctor_get(v_x_287_, 1);
v___x_295_ = l_instBEqOption_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(v_leanTypeName_291_, v_leanTypeName_293_);
if (v___x_295_ == 0)
{
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_array_get_size(v_types_292_);
v___x_297_ = lean_array_get_size(v_types_294_);
v___x_298_ = lean_nat_dec_eq(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_types_292_, v_types_294_, v___x_296_);
return v___x_299_;
}
}
}
case 11:
{
lean_object* v_leanTypeName_300_; lean_object* v_types_301_; lean_object* v_leanTypeName_302_; lean_object* v_types_303_; uint8_t v___x_304_; 
v_leanTypeName_300_ = lean_ctor_get(v_x_286_, 0);
v_types_301_ = lean_ctor_get(v_x_286_, 1);
v_leanTypeName_302_ = lean_ctor_get(v_x_287_, 0);
v_types_303_ = lean_ctor_get(v_x_287_, 1);
v___x_304_ = lean_name_eq(v_leanTypeName_300_, v_leanTypeName_302_);
if (v___x_304_ == 0)
{
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_array_get_size(v_types_301_);
v___x_306_ = lean_array_get_size(v_types_303_);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
return v___x_307_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_types_301_, v_types_303_, v___x_305_);
return v___x_308_;
}
}
}
default: 
{
return v_decide_290_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(lean_object* v_xs_309_, lean_object* v_ys_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_zero_312_; uint8_t v_isZero_313_; 
v_zero_312_ = lean_unsigned_to_nat(0u);
v_isZero_313_ = lean_nat_dec_eq(v_x_311_, v_zero_312_);
if (v_isZero_313_ == 1)
{
lean_dec(v_x_311_);
return v_isZero_313_;
}
else
{
lean_object* v_one_314_; lean_object* v_n_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_one_314_ = lean_unsigned_to_nat(1u);
v_n_315_ = lean_nat_sub(v_x_311_, v_one_314_);
lean_dec(v_x_311_);
v___x_316_ = lean_array_fget_borrowed(v_xs_309_, v_n_315_);
v___x_317_ = lean_array_fget_borrowed(v_ys_310_, v_n_315_);
v___x_318_ = l_Lean_IR_instBEqIRType_beq(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_n_315_);
return v___x_318_;
}
else
{
v_x_311_ = v_n_315_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg___boxed(lean_object* v_xs_320_, lean_object* v_ys_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_xs_320_, v_ys_321_, v_x_322_);
lean_dec_ref(v_ys_321_);
lean_dec_ref(v_xs_320_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqIRType_beq___boxed(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lean_IR_instBEqIRType_beq(v_x_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_x_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(lean_object* v_xs_329_, lean_object* v_ys_330_, lean_object* v_hsz_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(v_xs_329_, v_ys_330_, v_x_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___boxed(lean_object* v_xs_335_, lean_object* v_ys_336_, lean_object* v_hsz_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(v_xs_335_, v_ys_336_, v_hsz_337_, v_x_338_, v_x_339_);
lean_dec_ref(v_ys_336_);
lean_dec_ref(v_xs_335_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1));
return v___x_352_;
}
else
{
lean_object* v_val_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_val_353_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v_x_350_, 1);
v___x_354_ = ((lean_object*)(l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3));
v___x_355_ = lean_unsigned_to_nat(1024u);
v___x_356_ = l_Lean_Name_reprPrec(v_val_353_, v___x_355_);
v___x_357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_354_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Repr_addAppParen(v___x_357_, v_x_351_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___boxed(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(v_x_359_, v_x_360_);
lean_dec(v_x_360_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_IR_instReprIRType_repr___closed__24(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(2u);
v___x_399_ = lean_nat_to_int(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_IR_instReprIRType_repr___closed__25(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_to_int(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_dec(v_x_414_);
return v_x_415_;
}
else
{
lean_object* v_head_417_; lean_object* v_tail_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
v_head_417_ = lean_ctor_get(v_x_416_, 0);
v_tail_418_ = lean_ctor_get(v_x_416_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_429_ == 0)
{
v___x_420_ = v_x_416_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_tail_418_);
lean_inc(v_head_417_);
lean_dec(v_x_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
lean_inc(v_x_414_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 5);
lean_ctor_set(v___x_420_, 1, v_x_414_);
lean_ctor_set(v___x_420_, 0, v_x_415_);
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_x_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_x_414_);
v___x_423_ = v_reuseFailAlloc_428_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = l_Lean_IR_instReprIRType_repr(v_head_417_, v___x_424_);
v___x_426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_423_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v_x_415_ = v___x_426_;
v_x_416_ = v_tail_418_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_dec(v_x_430_);
return v_x_431_;
}
else
{
lean_object* v_head_433_; lean_object* v_tail_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
v_head_433_ = lean_ctor_get(v_x_432_, 0);
v_tail_434_ = lean_ctor_get(v_x_432_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_445_ == 0)
{
v___x_436_ = v_x_432_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_tail_434_);
lean_inc(v_head_433_);
lean_dec(v_x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
lean_inc(v_x_430_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 5);
lean_ctor_set(v___x_436_, 1, v_x_430_);
lean_ctor_set(v___x_436_, 0, v_x_431_);
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_x_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_x_430_);
v___x_439_ = v_reuseFailAlloc_444_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = l_Lean_IR_instReprIRType_repr(v_head_433_, v___x_440_);
v___x_442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_439_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(v_x_430_, v___x_442_, v_tail_434_);
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v___x_448_; 
lean_dec(v_x_447_);
v___x_448_ = lean_box(0);
return v___x_448_;
}
else
{
lean_object* v_tail_449_; 
v_tail_449_ = lean_ctor_get(v_x_446_, 1);
if (lean_obj_tag(v_tail_449_) == 0)
{
lean_object* v_head_450_; lean_object* v___x_451_; 
lean_dec(v_x_447_);
v_head_450_ = lean_ctor_get(v_x_446_, 0);
lean_inc(v_head_450_);
lean_dec_ref_known(v_x_446_, 2);
v___x_451_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_450_);
return v___x_451_;
}
else
{
lean_object* v_head_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_tail_449_);
v_head_452_ = lean_ctor_get(v_x_446_, 0);
lean_inc(v_head_452_);
lean_dec_ref_known(v_x_446_, 2);
v___x_453_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_452_);
v___x_454_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(v_x_447_, v___x_453_, v_tail_449_);
return v___x_454_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0));
v___x_457_ = lean_string_length(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_obj_once(&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5, &l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5);
v___x_459_ = lean_nat_to_int(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(lean_object* v_xs_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_array_get_size(v_xs_468_);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_472_ = lean_array_to_list(v_xs_468_);
v___x_473_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3));
v___x_474_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(v___x_472_, v___x_473_);
v___x_475_ = lean_obj_once(&l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6, &l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6);
v___x_476_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7));
v___x_477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_474_);
v___x_478_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8));
v___x_479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_475_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = l_Std_Format_fill(v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; 
lean_dec_ref(v_xs_468_);
v___x_482_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10));
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType_repr(lean_object* v_x_489_, lean_object* v_prec_490_){
_start:
{
lean_object* v___y_492_; lean_object* v___y_499_; lean_object* v___y_506_; lean_object* v___y_513_; lean_object* v___y_520_; lean_object* v___y_527_; lean_object* v___y_534_; lean_object* v___y_541_; lean_object* v___y_548_; lean_object* v___y_555_; lean_object* v___y_562_; lean_object* v___y_569_; 
switch(lean_obj_tag(v_x_489_))
{
case 0:
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1024u);
v___x_576_ = lean_nat_dec_le(v___x_575_, v_prec_490_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_492_ = v___x_577_;
goto v___jp_491_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_492_ = v___x_578_;
goto v___jp_491_;
}
}
case 1:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1024u);
v___x_580_ = lean_nat_dec_le(v___x_579_, v_prec_490_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_499_ = v___x_581_;
goto v___jp_498_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_499_ = v___x_582_;
goto v___jp_498_;
}
}
case 2:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1024u);
v___x_584_ = lean_nat_dec_le(v___x_583_, v_prec_490_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_506_ = v___x_585_;
goto v___jp_505_;
}
else
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_506_ = v___x_586_;
goto v___jp_505_;
}
}
case 3:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(1024u);
v___x_588_ = lean_nat_dec_le(v___x_587_, v_prec_490_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_513_ = v___x_589_;
goto v___jp_512_;
}
else
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_513_ = v___x_590_;
goto v___jp_512_;
}
}
case 4:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1024u);
v___x_592_ = lean_nat_dec_le(v___x_591_, v_prec_490_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_520_ = v___x_593_;
goto v___jp_519_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_520_ = v___x_594_;
goto v___jp_519_;
}
}
case 5:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1024u);
v___x_596_ = lean_nat_dec_le(v___x_595_, v_prec_490_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_527_ = v___x_597_;
goto v___jp_526_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_527_ = v___x_598_;
goto v___jp_526_;
}
}
case 6:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1024u);
v___x_600_ = lean_nat_dec_le(v___x_599_, v_prec_490_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_534_ = v___x_601_;
goto v___jp_533_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_534_ = v___x_602_;
goto v___jp_533_;
}
}
case 7:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1024u);
v___x_604_ = lean_nat_dec_le(v___x_603_, v_prec_490_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_541_ = v___x_605_;
goto v___jp_540_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_541_ = v___x_606_;
goto v___jp_540_;
}
}
case 8:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(1024u);
v___x_608_ = lean_nat_dec_le(v___x_607_, v_prec_490_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_548_ = v___x_609_;
goto v___jp_547_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_548_ = v___x_610_;
goto v___jp_547_;
}
}
case 9:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1024u);
v___x_612_ = lean_nat_dec_le(v___x_611_, v_prec_490_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_555_ = v___x_613_;
goto v___jp_554_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_555_ = v___x_614_;
goto v___jp_554_;
}
}
case 10:
{
lean_object* v_leanTypeName_615_; lean_object* v_types_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_640_; 
v_leanTypeName_615_ = lean_ctor_get(v_x_489_, 0);
v_types_616_ = lean_ctor_get(v_x_489_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_489_);
if (v_isSharedCheck_640_ == 0)
{
v___x_618_ = v_x_489_;
v_isShared_619_ = v_isSharedCheck_640_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_types_616_);
lean_inc(v_leanTypeName_615_);
lean_dec(v_x_489_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_640_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___y_621_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(1024u);
v___x_637_ = lean_nat_dec_le(v___x_636_, v_prec_490_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_621_ = v___x_638_;
goto v___jp_620_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_621_ = v___x_639_;
goto v___jp_620_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_622_ = lean_box(1);
v___x_623_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__28));
v___x_624_ = lean_unsigned_to_nat(1024u);
v___x_625_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(v_leanTypeName_615_, v___x_624_);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 5);
lean_ctor_set(v___x_618_, 1, v___x_625_);
lean_ctor_set(v___x_618_, 0, v___x_623_);
v___x_627_ = v___x_618_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_635_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_622_);
v___x_629_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_616_);
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_inc(v___y_621_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___y_621_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*1, v___x_632_);
v___x_634_ = l_Repr_addAppParen(v___x_633_, v_prec_490_);
return v___x_634_;
}
}
}
}
case 11:
{
lean_object* v_leanTypeName_641_; lean_object* v_types_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_666_; 
v_leanTypeName_641_ = lean_ctor_get(v_x_489_, 0);
v_types_642_ = lean_ctor_get(v_x_489_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_489_);
if (v_isSharedCheck_666_ == 0)
{
v___x_644_ = v_x_489_;
v_isShared_645_ = v_isSharedCheck_666_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_types_642_);
lean_inc(v_leanTypeName_641_);
lean_dec(v_x_489_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_666_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___y_647_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(1024u);
v___x_663_ = lean_nat_dec_le(v___x_662_, v_prec_490_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_647_ = v___x_664_;
goto v___jp_646_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_647_ = v___x_665_;
goto v___jp_646_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_648_ = lean_box(1);
v___x_649_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__31));
v___x_650_ = lean_unsigned_to_nat(1024u);
v___x_651_ = l_Lean_Name_reprPrec(v_leanTypeName_641_, v___x_650_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 5);
lean_ctor_set(v___x_644_, 1, v___x_651_);
lean_ctor_set(v___x_644_, 0, v___x_649_);
v___x_653_ = v___x_644_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_661_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_648_);
v___x_655_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_642_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_inc(v___y_647_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_647_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = 0;
v___x_659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v___x_658_);
v___x_660_ = l_Repr_addAppParen(v___x_659_, v_prec_490_);
return v___x_660_;
}
}
}
}
case 12:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(1024u);
v___x_668_ = lean_nat_dec_le(v___x_667_, v_prec_490_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_562_ = v___x_669_;
goto v___jp_561_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_562_ = v___x_670_;
goto v___jp_561_;
}
}
default: 
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(1024u);
v___x_672_ = lean_nat_dec_le(v___x_671_, v_prec_490_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_569_ = v___x_673_;
goto v___jp_568_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_569_ = v___x_674_;
goto v___jp_568_;
}
}
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_493_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__1));
lean_inc(v___y_492_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___y_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
v___x_497_ = l_Repr_addAppParen(v___x_496_, v_prec_490_);
return v___x_497_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_500_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__3));
lean_inc(v___y_499_);
v___x_501_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_501_, 0, v___y_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = 0;
v___x_503_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*1, v___x_502_);
v___x_504_ = l_Repr_addAppParen(v___x_503_, v_prec_490_);
return v___x_504_;
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_507_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__5));
lean_inc(v___y_506_);
v___x_508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_508_, 0, v___y_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = 0;
v___x_510_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1, v___x_509_);
v___x_511_ = l_Repr_addAppParen(v___x_510_, v_prec_490_);
return v___x_511_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_514_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__7));
lean_inc(v___y_513_);
v___x_515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_515_, 0, v___y_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = 0;
v___x_517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1, v___x_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_490_);
return v___x_518_;
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__9));
lean_inc(v___y_520_);
v___x_522_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_522_, 0, v___y_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = 0;
v___x_524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*1, v___x_523_);
v___x_525_ = l_Repr_addAppParen(v___x_524_, v_prec_490_);
return v___x_525_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__11));
lean_inc(v___y_527_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = 0;
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
v___x_532_ = l_Repr_addAppParen(v___x_531_, v_prec_490_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_535_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__13));
lean_inc(v___y_534_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*1, v___x_537_);
v___x_539_ = l_Repr_addAppParen(v___x_538_, v_prec_490_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_542_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__15));
lean_inc(v___y_541_);
v___x_543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_543_, 0, v___y_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = 0;
v___x_545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
v___x_546_ = l_Repr_addAppParen(v___x_545_, v_prec_490_);
return v___x_546_;
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_549_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__17));
lean_inc(v___y_548_);
v___x_550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_550_, 0, v___y_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = 0;
v___x_552_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*1, v___x_551_);
v___x_553_ = l_Repr_addAppParen(v___x_552_, v_prec_490_);
return v___x_553_;
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__19));
lean_inc(v___y_555_);
v___x_557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_557_, 0, v___y_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = 0;
v___x_559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*1, v___x_558_);
v___x_560_ = l_Repr_addAppParen(v___x_559_, v_prec_490_);
return v___x_560_;
}
v___jp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_563_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__21));
lean_inc(v___y_562_);
v___x_564_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
v___x_567_ = l_Repr_addAppParen(v___x_566_, v_prec_490_);
return v___x_567_;
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_570_ = ((lean_object*)(l_Lean_IR_instReprIRType_repr___closed__23));
lean_inc(v___y_569_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v___y_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = 0;
v___x_573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*1, v___x_572_);
v___x_574_ = l_Repr_addAppParen(v___x_573_, v_prec_490_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(lean_object* v___y_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_IR_instReprIRType_repr(v___y_675_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType_repr___boxed(lean_object* v_x_678_, lean_object* v_prec_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_IR_instReprIRType_repr(v_x_678_, v_prec_679_);
lean_dec(v_prec_679_);
return v_res_680_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object* v_x_683_){
_start:
{
switch(lean_obj_tag(v_x_683_))
{
case 0:
{
uint8_t v___x_684_; 
v___x_684_ = 1;
return v___x_684_;
}
case 9:
{
uint8_t v___x_685_; 
v___x_685_ = 1;
return v___x_685_;
}
case 1:
{
uint8_t v___x_686_; 
v___x_686_ = 1;
return v___x_686_;
}
case 2:
{
uint8_t v___x_687_; 
v___x_687_ = 1;
return v___x_687_;
}
case 3:
{
uint8_t v___x_688_; 
v___x_688_ = 1;
return v___x_688_;
}
case 4:
{
uint8_t v___x_689_; 
v___x_689_ = 1;
return v___x_689_;
}
case 5:
{
uint8_t v___x_690_; 
v___x_690_ = 1;
return v___x_690_;
}
default: 
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Lean_IR_IRType_isScalar(v_x_692_);
lean_dec(v_x_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isObj(lean_object* v_x_695_){
_start:
{
switch(lean_obj_tag(v_x_695_))
{
case 7:
{
uint8_t v___x_696_; 
v___x_696_ = 1;
return v___x_696_;
}
case 12:
{
uint8_t v___x_697_; 
v___x_697_ = 1;
return v___x_697_;
}
case 8:
{
uint8_t v___x_698_; 
v___x_698_ = 1;
return v___x_698_;
}
case 13:
{
uint8_t v___x_699_; 
v___x_699_ = 1;
return v___x_699_;
}
default: 
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object* v_x_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Lean_IR_IRType_isObj(v_x_701_);
lean_dec(v_x_701_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isPossibleRef(lean_object* v_x_704_){
_start:
{
switch(lean_obj_tag(v_x_704_))
{
case 7:
{
uint8_t v___x_705_; 
v___x_705_ = 1;
return v___x_705_;
}
case 8:
{
uint8_t v___x_706_; 
v___x_706_ = 1;
return v___x_706_;
}
default: 
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isPossibleRef___boxed(lean_object* v_x_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l_Lean_IR_IRType_isPossibleRef(v_x_708_);
lean_dec(v_x_708_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isDefiniteRef(lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 7)
{
uint8_t v___x_712_; 
v___x_712_ = 1;
return v___x_712_;
}
else
{
uint8_t v___x_713_; 
v___x_713_ = 0;
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isDefiniteRef___boxed(lean_object* v_x_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lean_IR_IRType_isDefiniteRef(v_x_714_);
lean_dec(v_x_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isErased(lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_717_) == 6)
{
uint8_t v___x_718_; 
v___x_718_ = 1;
return v___x_718_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = 0;
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isErased___boxed(lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_IR_IRType_isErased(v_x_720_);
lean_dec(v_x_720_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isVoid(lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 13)
{
uint8_t v___x_724_; 
v___x_724_ = 1;
return v___x_724_;
}
else
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isVoid___boxed(lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_Lean_IR_IRType_isVoid(v_x_726_);
lean_dec(v_x_726_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_boxed(lean_object* v_x_729_){
_start:
{
switch(lean_obj_tag(v_x_729_))
{
case 7:
{
return v_x_729_;
}
case 0:
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(7);
return v___x_730_;
}
case 9:
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(7);
return v___x_731_;
}
case 13:
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(12);
return v___x_732_;
}
case 12:
{
return v_x_729_;
}
case 1:
{
lean_object* v___x_733_; 
v___x_733_ = lean_box(12);
return v___x_733_;
}
case 2:
{
lean_object* v___x_734_; 
v___x_734_ = lean_box(12);
return v___x_734_;
}
default: 
{
lean_object* v___x_735_; 
v___x_735_ = lean_box(8);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_boxed___boxed(lean_object* v_x_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_IR_IRType_boxed(v_x_736_);
lean_dec(v_x_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx___impl(lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_tag_nat(v_x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorIdx___impl___boxed(lean_object* v_x_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_IR_Arg_ctorIdx___impl(v_x_740_);
lean_dec(v_x_740_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim___redArg(lean_object* v_t_742_, lean_object* v_k_743_){
_start:
{
if (lean_obj_tag(v_t_742_) == 0)
{
lean_object* v_id_744_; lean_object* v___x_745_; 
v_id_744_ = lean_ctor_get(v_t_742_, 0);
lean_inc(v_id_744_);
lean_dec_ref_known(v_t_742_, 1);
v___x_745_ = lean_apply_1(v_k_743_, v_id_744_);
return v___x_745_;
}
else
{
return v_k_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim(lean_object* v_motive_746_, lean_object* v_ctorIdx_747_, lean_object* v_t_748_, lean_object* v_h_749_, lean_object* v_k_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_748_, v_k_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_ctorElim___boxed(lean_object* v_motive_752_, lean_object* v_ctorIdx_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_k_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_IR_Arg_ctorElim(v_motive_752_, v_ctorIdx_753_, v_t_754_, v_h_755_, v_k_756_);
lean_dec(v_ctorIdx_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_var_elim___redArg(lean_object* v_t_758_, lean_object* v_var_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_758_, v_var_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_var_elim(lean_object* v_motive_761_, lean_object* v_t_762_, lean_object* v_h_763_, lean_object* v_var_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_762_, v_var_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_erased_elim___redArg(lean_object* v_t_766_, lean_object* v_erased_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_766_, v_erased_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_erased_elim(lean_object* v_motive_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_erased_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_770_, v_erased_772_);
return v___x_773_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqArg_beq(lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v_id_780_; lean_object* v_id_781_; uint8_t v___x_782_; 
v_id_780_ = lean_ctor_get(v_x_778_, 0);
v_id_781_ = lean_ctor_get(v_x_779_, 0);
v___x_782_ = lean_nat_dec_eq(v_id_780_, v_id_781_);
return v___x_782_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
else
{
if (lean_obj_tag(v_x_779_) == 1)
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqArg_beq___boxed(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Lean_IR_instBEqArg_beq(v_x_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec(v_x_786_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprArg_repr(lean_object* v_x_801_, lean_object* v_prec_802_){
_start:
{
lean_object* v___y_804_; 
if (lean_obj_tag(v_x_801_) == 0)
{
lean_object* v_id_810_; lean_object* v___y_812_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_id_810_ = lean_ctor_get(v_x_801_, 0);
lean_inc(v_id_810_);
lean_dec_ref_known(v_x_801_, 1);
v___x_820_ = lean_unsigned_to_nat(1024u);
v___x_821_ = lean_nat_dec_le(v___x_820_, v_prec_802_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_812_ = v___x_822_;
goto v___jp_811_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_812_ = v___x_823_;
goto v___jp_811_;
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = ((lean_object*)(l_Lean_IR_instReprArg_repr___closed__4));
v___x_814_ = l_Lean_IR_instReprVarId_repr___redArg(v_id_810_);
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
lean_inc(v___y_812_);
v___x_816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_816_, 0, v___y_812_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = 0;
v___x_818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*1, v___x_817_);
v___x_819_ = l_Repr_addAppParen(v___x_818_, v_prec_802_);
return v___x_819_;
}
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(1024u);
v___x_825_ = lean_nat_dec_le(v___x_824_, v_prec_802_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__24, &l_Lean_IR_instReprIRType_repr___closed__24_once, _init_l_Lean_IR_instReprIRType_repr___closed__24);
v___y_804_ = v___x_826_;
goto v___jp_803_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = lean_obj_once(&l_Lean_IR_instReprIRType_repr___closed__25, &l_Lean_IR_instReprIRType_repr___closed__25_once, _init_l_Lean_IR_instReprIRType_repr___closed__25);
v___y_804_ = v___x_827_;
goto v___jp_803_;
}
}
v___jp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_805_ = ((lean_object*)(l_Lean_IR_instReprArg_repr___closed__1));
lean_inc(v___y_804_);
v___x_806_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_806_, 0, v___y_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = 0;
v___x_808_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*1, v___x_807_);
v___x_809_ = l_Repr_addAppParen(v___x_808_, v_prec_802_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprArg_repr___boxed(lean_object* v_x_828_, lean_object* v_prec_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_IR_instReprArg_repr(v_x_828_, v_prec_829_);
lean_dec(v_prec_829_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_beq(lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_id_835_; lean_object* v_id_836_; uint8_t v___x_837_; 
v_id_835_ = lean_ctor_get(v_x_833_, 0);
v_id_836_ = lean_ctor_get(v_x_834_, 0);
v___x_837_ = lean_nat_dec_eq(v_id_835_, v_id_836_);
return v___x_837_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = 0;
return v___x_838_;
}
}
else
{
if (lean_obj_tag(v_x_834_) == 1)
{
uint8_t v___x_839_; 
v___x_839_ = 1;
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
v___x_840_ = 0;
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_beq___boxed(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l_Lean_IR_Arg_beq(v_x_841_, v_x_842_);
lean_dec(v_x_842_);
lean_dec(v_x_841_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx___impl(lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_tag_nat(v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorIdx___impl___boxed(lean_object* v_x_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_IR_LitVal_ctorIdx___impl(v_x_847_);
lean_dec_ref(v_x_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim___redArg(lean_object* v_t_849_, lean_object* v_k_850_){
_start:
{
if (lean_obj_tag(v_t_849_) == 0)
{
lean_object* v_v_851_; lean_object* v___x_852_; 
v_v_851_ = lean_ctor_get(v_t_849_, 0);
lean_inc(v_v_851_);
lean_dec_ref_known(v_t_849_, 1);
v___x_852_ = lean_apply_1(v_k_850_, v_v_851_);
return v___x_852_;
}
else
{
lean_object* v_v_853_; lean_object* v___x_854_; 
v_v_853_ = lean_ctor_get(v_t_849_, 0);
lean_inc_ref(v_v_853_);
lean_dec_ref_known(v_t_849_, 1);
v___x_854_ = lean_apply_1(v_k_850_, v_v_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim(lean_object* v_motive_855_, lean_object* v_ctorIdx_856_, lean_object* v_t_857_, lean_object* v_h_858_, lean_object* v_k_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_857_, v_k_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_ctorElim___boxed(lean_object* v_motive_861_, lean_object* v_ctorIdx_862_, lean_object* v_t_863_, lean_object* v_h_864_, lean_object* v_k_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_IR_LitVal_ctorElim(v_motive_861_, v_ctorIdx_862_, v_t_863_, v_h_864_, v_k_865_);
lean_dec(v_ctorIdx_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_num_elim___redArg(lean_object* v_t_867_, lean_object* v_num_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_867_, v_num_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_num_elim(lean_object* v_motive_870_, lean_object* v_t_871_, lean_object* v_h_872_, lean_object* v_num_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_871_, v_num_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_str_elim___redArg(lean_object* v_t_875_, lean_object* v_str_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_875_, v_str_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_str_elim(lean_object* v_motive_878_, lean_object* v_t_879_, lean_object* v_h_880_, lean_object* v_str_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_879_, v_str_881_);
return v___x_882_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqLitVal_beq(lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
if (lean_obj_tag(v_x_888_) == 0)
{
lean_object* v_v_889_; lean_object* v_v_890_; uint8_t v___x_891_; 
v_v_889_ = lean_ctor_get(v_x_887_, 0);
v_v_890_ = lean_ctor_get(v_x_888_, 0);
v___x_891_ = lean_nat_dec_eq(v_v_889_, v_v_890_);
return v___x_891_;
}
else
{
uint8_t v___x_892_; 
v___x_892_ = 0;
return v___x_892_;
}
}
else
{
if (lean_obj_tag(v_x_888_) == 1)
{
lean_object* v_v_893_; lean_object* v_v_894_; uint8_t v___x_895_; 
v_v_893_ = lean_ctor_get(v_x_887_, 0);
v_v_894_ = lean_ctor_get(v_x_888_, 0);
v___x_895_ = lean_string_dec_eq(v_v_893_, v_v_894_);
return v___x_895_;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = 0;
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqLitVal_beq___boxed(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l_Lean_IR_instBEqLitVal_beq(v_x_897_, v_x_898_);
lean_dec_ref(v_x_898_);
lean_dec_ref(v_x_897_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqCtorInfo_beq(lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v_name_910_; lean_object* v_cidx_911_; lean_object* v_size_912_; lean_object* v_usize_913_; lean_object* v_ssize_914_; lean_object* v_name_915_; lean_object* v_cidx_916_; lean_object* v_size_917_; lean_object* v_usize_918_; lean_object* v_ssize_919_; uint8_t v___x_920_; 
v_name_910_ = lean_ctor_get(v_x_908_, 0);
v_cidx_911_ = lean_ctor_get(v_x_908_, 1);
v_size_912_ = lean_ctor_get(v_x_908_, 2);
v_usize_913_ = lean_ctor_get(v_x_908_, 3);
v_ssize_914_ = lean_ctor_get(v_x_908_, 4);
v_name_915_ = lean_ctor_get(v_x_909_, 0);
v_cidx_916_ = lean_ctor_get(v_x_909_, 1);
v_size_917_ = lean_ctor_get(v_x_909_, 2);
v_usize_918_ = lean_ctor_get(v_x_909_, 3);
v_ssize_919_ = lean_ctor_get(v_x_909_, 4);
v___x_920_ = lean_name_eq(v_name_910_, v_name_915_);
if (v___x_920_ == 0)
{
return v___x_920_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_eq(v_cidx_911_, v_cidx_916_);
if (v___x_921_ == 0)
{
return v___x_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = lean_nat_dec_eq(v_size_912_, v_size_917_);
if (v___x_922_ == 0)
{
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = lean_nat_dec_eq(v_usize_913_, v_usize_918_);
if (v___x_923_ == 0)
{
return v___x_923_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = lean_nat_dec_eq(v_ssize_914_, v_ssize_919_);
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqCtorInfo_beq___boxed(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_Lean_IR_instBEqCtorInfo_beq(v_x_925_, v_x_926_);
lean_dec_ref(v_x_926_);
lean_dec_ref(v_x_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(8u);
v___x_941_ = lean_nat_to_int(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(9u);
v___x_952_ = lean_nat_to_int(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr___redArg(lean_object* v_x_956_){
_start:
{
lean_object* v_name_957_; lean_object* v_cidx_958_; lean_object* v_size_959_; lean_object* v_usize_960_; lean_object* v_ssize_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_name_957_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_name_957_);
v_cidx_958_ = lean_ctor_get(v_x_956_, 1);
lean_inc(v_cidx_958_);
v_size_959_ = lean_ctor_get(v_x_956_, 2);
lean_inc(v_size_959_);
v_usize_960_ = lean_ctor_get(v_x_956_, 3);
lean_inc(v_usize_960_);
v_ssize_961_ = lean_ctor_get(v_x_956_, 4);
lean_inc(v_ssize_961_);
lean_dec_ref(v_x_956_);
v___x_962_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__5));
v___x_963_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3));
v___x_964_ = lean_obj_once(&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4, &l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once, _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = l_Lean_Name_reprPrec(v_name_957_, v___x_965_);
v___x_967_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_964_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = 0;
v___x_969_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*1, v___x_968_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_963_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2));
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_box(1);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6));
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_962_);
v___x_978_ = l_Nat_reprFast(v_cidx_958_);
v___x_979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_964_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*1, v___x_968_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_977_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_971_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_973_);
v___x_985_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_962_);
v___x_988_ = l_Nat_reprFast(v_size_959_);
v___x_989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
v___x_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_964_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_968_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_987_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_971_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_973_);
v___x_995_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10));
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_962_);
v___x_998_ = lean_obj_once(&l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11, &l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once, _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11);
v___x_999_ = l_Nat_reprFast(v_usize_960_);
v___x_1000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
v___x_1001_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_998_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*1, v___x_968_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_997_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_971_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_973_);
v___x_1006_ = ((lean_object*)(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_962_);
v___x_1009_ = l_Nat_reprFast(v_ssize_961_);
v___x_1010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_998_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_968_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1008_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_1015_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1013_);
v___x_1017_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1014_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*1, v___x_968_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr(lean_object* v_x_1021_, lean_object* v_prec_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_IR_instReprCtorInfo_repr___redArg(v_x_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo_repr___boxed(lean_object* v_x_1024_, lean_object* v_prec_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_IR_instReprCtorInfo_repr(v_x_1024_, v_prec_1025_);
lean_dec(v_prec_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object* v_info_1029_){
_start:
{
lean_object* v_size_1030_; lean_object* v_usize_1031_; lean_object* v_ssize_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_size_1030_ = lean_ctor_get(v_info_1029_, 2);
v_usize_1031_ = lean_ctor_get(v_info_1029_, 3);
v_ssize_1032_ = lean_ctor_get(v_info_1029_, 4);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_nat_dec_lt(v___x_1033_, v_size_1030_);
if (v___x_1034_ == 0)
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_nat_dec_lt(v___x_1033_, v_usize_1031_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_nat_dec_lt(v___x_1033_, v_ssize_1032_);
return v___x_1036_;
}
else
{
return v___x_1035_;
}
}
else
{
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object* v_info_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = l_Lean_IR_CtorInfo_isRef(v_info_1037_);
lean_dec_ref(v_info_1037_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object* v_info_1040_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = l_Lean_IR_CtorInfo_isRef(v_info_1040_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; 
v___x_1042_ = 1;
return v___x_1042_;
}
else
{
uint8_t v___x_1043_; 
v___x_1043_ = 0;
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object* v_info_1044_){
_start:
{
uint8_t v_res_1045_; lean_object* v_r_1046_; 
v_res_1045_ = l_Lean_IR_CtorInfo_isScalar(v_info_1044_);
lean_dec_ref(v_info_1044_);
v_r_1046_ = lean_box(v_res_1045_);
return v_r_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type(lean_object* v_info_1047_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_IR_CtorInfo_isRef(v_info_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(12);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_box(7);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_type___boxed(lean_object* v_info_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_IR_CtorInfo_type(v_info_1051_);
lean_dec_ref(v_info_1051_);
return v_res_1052_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(5u);
v___x_1069_ = lean_nat_to_int(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_unsigned_to_nat(10u);
v___x_1074_ = lean_nat_to_int(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(6u);
v___x_1079_ = lean_nat_to_int(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___redArg(lean_object* v_x_1080_){
_start:
{
lean_object* v_x_1081_; uint8_t v_borrow_1082_; lean_object* v_ty_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_x_1081_ = lean_ctor_get(v_x_1080_, 0);
lean_inc(v_x_1081_);
v_borrow_1082_ = lean_ctor_get_uint8(v_x_1080_, sizeof(void*)*2);
v_ty_1083_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_ty_1083_);
lean_dec_ref(v_x_1080_);
v___x_1084_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__5));
v___x_1085_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__3));
v___x_1086_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__4, &l_Lean_IR_instReprParam_repr___redArg___closed__4_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__4);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_1081_);
v___x_1089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = 0;
v___x_1091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1085_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2));
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_box(1);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__6));
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1084_);
v___x_1100_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__7, &l_Lean_IR_instReprParam_repr___redArg___closed__7_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__7);
v___x_1101_ = l_Bool_repr___redArg(v_borrow_1082_);
v___x_1102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*1, v___x_1090_);
v___x_1104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1099_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1093_);
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1095_);
v___x_1107_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__9));
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1084_);
v___x_1110_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__10, &l_Lean_IR_instReprParam_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__10);
v___x_1111_ = l_Lean_IR_instReprIRType_repr(v_ty_1083_, v___x_1087_);
v___x_1112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*1, v___x_1090_);
v___x_1114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1109_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_1116_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_1117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___x_1114_);
v___x_1118_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_1119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1115_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*1, v___x_1090_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr(lean_object* v_x_1122_, lean_object* v_prec_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_IR_instReprParam_repr___redArg(v_x_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___boxed(lean_object* v_x_1125_, lean_object* v_prec_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_IR_instReprParam_repr(v_x_1125_, v_prec_1126_);
lean_dec(v_prec_1126_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___impl(lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_tag_nat(v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___impl___boxed(lean_object* v_x_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_IR_Alt_ctorIdx___impl(v_x_1132_);
lean_dec_ref(v_x_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___redArg(lean_object* v_t_1134_, lean_object* v_k_1135_){
_start:
{
if (lean_obj_tag(v_t_1134_) == 0)
{
lean_object* v_info_1136_; lean_object* v_b_1137_; lean_object* v___x_1138_; 
v_info_1136_ = lean_ctor_get(v_t_1134_, 0);
lean_inc_ref(v_info_1136_);
v_b_1137_ = lean_ctor_get(v_t_1134_, 1);
lean_inc(v_b_1137_);
lean_dec_ref_known(v_t_1134_, 2);
v___x_1138_ = lean_apply_2(v_k_1135_, v_info_1136_, v_b_1137_);
return v___x_1138_;
}
else
{
lean_object* v_b_1139_; lean_object* v___x_1140_; 
v_b_1139_ = lean_ctor_get(v_t_1134_, 0);
lean_inc(v_b_1139_);
lean_dec_ref_known(v_t_1134_, 1);
v___x_1140_ = lean_apply_1(v_k_1135_, v_b_1139_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim(lean_object* v_motive__1_1141_, lean_object* v_ctorIdx_1142_, lean_object* v_t_1143_, lean_object* v_h_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1143_, v_k_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___boxed(lean_object* v_motive__1_1147_, lean_object* v_ctorIdx_1148_, lean_object* v_t_1149_, lean_object* v_h_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_IR_Alt_ctorElim(v_motive__1_1147_, v_ctorIdx_1148_, v_t_1149_, v_h_1150_, v_k_1151_);
lean_dec(v_ctorIdx_1148_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim___redArg(lean_object* v_t_1153_, lean_object* v_ctor_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1153_, v_ctor_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim(lean_object* v_motive__1_1156_, lean_object* v_t_1157_, lean_object* v_h_1158_, lean_object* v_ctor_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1157_, v_ctor_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim___redArg(lean_object* v_t_1161_, lean_object* v_default_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1161_, v_default_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim(lean_object* v_motive__1_1164_, lean_object* v_t_1165_, lean_object* v_h_1166_, lean_object* v_default_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1165_, v_default_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___impl(lean_object* v_x_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_tag_nat(v_x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___impl___boxed(lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_IR_FnBody_ctorIdx___impl(v_x_1171_);
lean_dec(v_x_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___redArg(lean_object* v_t_1173_, lean_object* v_k_1174_){
_start:
{
switch(lean_obj_tag(v_t_1173_))
{
case 0:
{
lean_object* v_tgt_1175_; lean_object* v_b_1176_; lean_object* v_i_1177_; lean_object* v_ys_1178_; lean_object* v___x_1179_; 
v_tgt_1175_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1175_);
v_b_1176_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1176_);
v_i_1177_ = lean_ctor_get(v_t_1173_, 2);
lean_inc_ref(v_i_1177_);
v_ys_1178_ = lean_ctor_get(v_t_1173_, 3);
lean_inc_ref(v_ys_1178_);
lean_dec_ref_known(v_t_1173_, 4);
v___x_1179_ = lean_apply_4(v_k_1174_, v_tgt_1175_, v_b_1176_, v_i_1177_, v_ys_1178_);
return v___x_1179_;
}
case 2:
{
lean_object* v_tgt_1180_; lean_object* v_b_1181_; lean_object* v_x_1182_; lean_object* v_i_1183_; uint8_t v_updtHeader_1184_; lean_object* v_ys_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_tgt_1180_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1180_);
v_b_1181_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1181_);
v_x_1182_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_x_1182_);
v_i_1183_ = lean_ctor_get(v_t_1173_, 3);
lean_inc_ref(v_i_1183_);
v_updtHeader_1184_ = lean_ctor_get_uint8(v_t_1173_, sizeof(void*)*5);
v_ys_1185_ = lean_ctor_get(v_t_1173_, 4);
lean_inc_ref(v_ys_1185_);
lean_dec_ref_known(v_t_1173_, 5);
v___x_1186_ = lean_box(v_updtHeader_1184_);
v___x_1187_ = lean_apply_6(v_k_1174_, v_tgt_1180_, v_b_1181_, v_x_1182_, v_i_1183_, v___x_1186_, v_ys_1185_);
return v___x_1187_;
}
case 5:
{
lean_object* v_tgt_1188_; lean_object* v_b_1189_; lean_object* v_ty_1190_; lean_object* v_n_1191_; lean_object* v_offset_1192_; lean_object* v_x_1193_; lean_object* v___x_1194_; 
v_tgt_1188_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1188_);
v_b_1189_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1189_);
v_ty_1190_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_ty_1190_);
v_n_1191_ = lean_ctor_get(v_t_1173_, 3);
lean_inc(v_n_1191_);
v_offset_1192_ = lean_ctor_get(v_t_1173_, 4);
lean_inc(v_offset_1192_);
v_x_1193_ = lean_ctor_get(v_t_1173_, 5);
lean_inc(v_x_1193_);
lean_dec_ref_known(v_t_1173_, 6);
v___x_1194_ = lean_apply_6(v_k_1174_, v_tgt_1188_, v_b_1189_, v_ty_1190_, v_n_1191_, v_offset_1192_, v_x_1193_);
return v___x_1194_;
}
case 6:
{
lean_object* v_tgt_1195_; lean_object* v_b_1196_; lean_object* v_ty_1197_; lean_object* v_c_1198_; lean_object* v_ys_1199_; lean_object* v___x_1200_; 
v_tgt_1195_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1195_);
v_b_1196_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1196_);
v_ty_1197_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_ty_1197_);
v_c_1198_ = lean_ctor_get(v_t_1173_, 3);
lean_inc(v_c_1198_);
v_ys_1199_ = lean_ctor_get(v_t_1173_, 4);
lean_inc_ref(v_ys_1199_);
lean_dec_ref_known(v_t_1173_, 5);
v___x_1200_ = lean_apply_5(v_k_1174_, v_tgt_1195_, v_b_1196_, v_ty_1197_, v_c_1198_, v_ys_1199_);
return v___x_1200_;
}
case 7:
{
lean_object* v_tgt_1201_; lean_object* v_b_1202_; lean_object* v_c_1203_; lean_object* v_ys_1204_; lean_object* v___x_1205_; 
v_tgt_1201_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1201_);
v_b_1202_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1202_);
v_c_1203_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_c_1203_);
v_ys_1204_ = lean_ctor_get(v_t_1173_, 3);
lean_inc_ref(v_ys_1204_);
lean_dec_ref_known(v_t_1173_, 4);
v___x_1205_ = lean_apply_4(v_k_1174_, v_tgt_1201_, v_b_1202_, v_c_1203_, v_ys_1204_);
return v___x_1205_;
}
case 8:
{
lean_object* v_tgt_1206_; lean_object* v_b_1207_; lean_object* v_x_1208_; lean_object* v_ys_1209_; lean_object* v___x_1210_; 
v_tgt_1206_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1206_);
v_b_1207_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1207_);
v_x_1208_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_x_1208_);
v_ys_1209_ = lean_ctor_get(v_t_1173_, 3);
lean_inc_ref(v_ys_1209_);
lean_dec_ref_known(v_t_1173_, 4);
v___x_1210_ = lean_apply_4(v_k_1174_, v_tgt_1206_, v_b_1207_, v_x_1208_, v_ys_1209_);
return v___x_1210_;
}
case 11:
{
lean_object* v_tgt_1211_; lean_object* v_b_1212_; uint8_t v_v_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_tgt_1211_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1211_);
v_b_1212_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1212_);
v_v_1213_ = lean_ctor_get_uint8(v_t_1173_, sizeof(void*)*2);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1214_ = lean_box(v_v_1213_);
v___x_1215_ = lean_apply_3(v_k_1174_, v_tgt_1211_, v_b_1212_, v___x_1214_);
return v___x_1215_;
}
case 12:
{
lean_object* v_tgt_1216_; lean_object* v_b_1217_; uint16_t v_v_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_tgt_1216_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1216_);
v_b_1217_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1217_);
v_v_1218_ = lean_ctor_get_uint16(v_t_1173_, sizeof(void*)*2);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1219_ = lean_box(v_v_1218_);
v___x_1220_ = lean_apply_3(v_k_1174_, v_tgt_1216_, v_b_1217_, v___x_1219_);
return v___x_1220_;
}
case 13:
{
lean_object* v_tgt_1221_; lean_object* v_b_1222_; uint32_t v_v_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_tgt_1221_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1221_);
v_b_1222_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1222_);
v_v_1223_ = lean_ctor_get_uint32(v_t_1173_, sizeof(void*)*2);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1224_ = lean_box_uint32(v_v_1223_);
v___x_1225_ = lean_apply_3(v_k_1174_, v_tgt_1221_, v_b_1222_, v___x_1224_);
return v___x_1225_;
}
case 14:
{
lean_object* v_tgt_1226_; lean_object* v_b_1227_; uint64_t v_v_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_tgt_1226_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1226_);
v_b_1227_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1227_);
v_v_1228_ = lean_ctor_get_uint64(v_t_1173_, sizeof(void*)*2);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1229_ = lean_box_uint64(v_v_1228_);
v___x_1230_ = lean_apply_3(v_k_1174_, v_tgt_1226_, v_b_1227_, v___x_1229_);
return v___x_1230_;
}
case 15:
{
lean_object* v_tgt_1231_; lean_object* v_b_1232_; uint64_t v_v_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_tgt_1231_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1231_);
v_b_1232_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1232_);
v_v_1233_ = lean_ctor_get_uint64(v_t_1173_, sizeof(void*)*2);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1234_ = lean_box_uint64(v_v_1233_);
v___x_1235_ = lean_apply_3(v_k_1174_, v_tgt_1231_, v_b_1232_, v___x_1234_);
return v___x_1235_;
}
case 16:
{
lean_object* v_tgt_1236_; lean_object* v_b_1237_; lean_object* v_v_1238_; lean_object* v___x_1239_; 
v_tgt_1236_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1236_);
v_b_1237_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1237_);
v_v_1238_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_v_1238_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1239_ = lean_apply_3(v_k_1174_, v_tgt_1236_, v_b_1237_, v_v_1238_);
return v___x_1239_;
}
case 17:
{
lean_object* v_tgt_1240_; lean_object* v_b_1241_; lean_object* v_v_1242_; lean_object* v___x_1243_; 
v_tgt_1240_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1240_);
v_b_1241_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1241_);
v_v_1242_ = lean_ctor_get(v_t_1173_, 2);
lean_inc_ref(v_v_1242_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1243_ = lean_apply_3(v_k_1174_, v_tgt_1240_, v_b_1241_, v_v_1242_);
return v___x_1243_;
}
case 18:
{
lean_object* v_tgt_1244_; lean_object* v_b_1245_; lean_object* v_x_1246_; lean_object* v___x_1247_; 
v_tgt_1244_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1244_);
v_b_1245_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1245_);
v_x_1246_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_x_1246_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1247_ = lean_apply_3(v_k_1174_, v_tgt_1244_, v_b_1245_, v_x_1246_);
return v___x_1247_;
}
case 19:
{
lean_object* v_j_1248_; lean_object* v_xs_1249_; lean_object* v_v_1250_; lean_object* v_b_1251_; lean_object* v___x_1252_; 
v_j_1248_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_j_1248_);
v_xs_1249_ = lean_ctor_get(v_t_1173_, 1);
lean_inc_ref(v_xs_1249_);
v_v_1250_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_v_1250_);
v_b_1251_ = lean_ctor_get(v_t_1173_, 3);
lean_inc(v_b_1251_);
lean_dec_ref_known(v_t_1173_, 4);
v___x_1252_ = lean_apply_4(v_k_1174_, v_j_1248_, v_xs_1249_, v_v_1250_, v_b_1251_);
return v___x_1252_;
}
case 21:
{
lean_object* v_x_1253_; lean_object* v_cidx_1254_; lean_object* v_b_1255_; lean_object* v___x_1256_; 
v_x_1253_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_x_1253_);
v_cidx_1254_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_cidx_1254_);
v_b_1255_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_b_1255_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1256_ = lean_apply_3(v_k_1174_, v_x_1253_, v_cidx_1254_, v_b_1255_);
return v___x_1256_;
}
case 23:
{
lean_object* v_x_1257_; lean_object* v_i_1258_; lean_object* v_offset_1259_; lean_object* v_y_1260_; lean_object* v_ty_1261_; lean_object* v_b_1262_; lean_object* v___x_1263_; 
v_x_1257_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_x_1257_);
v_i_1258_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_i_1258_);
v_offset_1259_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_offset_1259_);
v_y_1260_ = lean_ctor_get(v_t_1173_, 3);
lean_inc(v_y_1260_);
v_ty_1261_ = lean_ctor_get(v_t_1173_, 4);
lean_inc(v_ty_1261_);
v_b_1262_ = lean_ctor_get(v_t_1173_, 5);
lean_inc(v_b_1262_);
lean_dec_ref_known(v_t_1173_, 6);
v___x_1263_ = lean_apply_6(v_k_1174_, v_x_1257_, v_i_1258_, v_offset_1259_, v_y_1260_, v_ty_1261_, v_b_1262_);
return v___x_1263_;
}
case 24:
{
lean_object* v_x_1264_; lean_object* v_n_1265_; uint8_t v_c_1266_; uint8_t v_persistent_1267_; lean_object* v_b_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_x_1264_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_x_1264_);
v_n_1265_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_n_1265_);
v_c_1266_ = lean_ctor_get_uint8(v_t_1173_, sizeof(void*)*3);
v_persistent_1267_ = lean_ctor_get_uint8(v_t_1173_, sizeof(void*)*3 + 1);
v_b_1268_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_b_1268_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1269_ = lean_box(v_c_1266_);
v___x_1270_ = lean_box(v_persistent_1267_);
v___x_1271_ = lean_apply_5(v_k_1174_, v_x_1264_, v_n_1265_, v___x_1269_, v___x_1270_, v_b_1268_);
return v___x_1271_;
}
case 25:
{
lean_object* v_x_1272_; lean_object* v_n_1273_; uint8_t v_c_1274_; uint8_t v_persistent_1275_; lean_object* v_b_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_x_1272_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_x_1272_);
v_n_1273_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_n_1273_);
v_c_1274_ = lean_ctor_get_uint8(v_t_1173_, sizeof(void*)*3);
v_persistent_1275_ = lean_ctor_get_uint8(v_t_1173_, sizeof(void*)*3 + 1);
v_b_1276_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_b_1276_);
lean_dec_ref_known(v_t_1173_, 3);
v___x_1277_ = lean_box(v_c_1274_);
v___x_1278_ = lean_box(v_persistent_1275_);
v___x_1279_ = lean_apply_5(v_k_1174_, v_x_1272_, v_n_1273_, v___x_1277_, v___x_1278_, v_b_1276_);
return v___x_1279_;
}
case 26:
{
lean_object* v_x_1280_; lean_object* v_b_1281_; lean_object* v___x_1282_; 
v_x_1280_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_x_1280_);
v_b_1281_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1281_);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1282_ = lean_apply_2(v_k_1174_, v_x_1280_, v_b_1281_);
return v___x_1282_;
}
case 27:
{
lean_object* v_tid_1283_; lean_object* v_x_1284_; lean_object* v_xType_1285_; lean_object* v_cs_1286_; lean_object* v___x_1287_; 
v_tid_1283_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tid_1283_);
v_x_1284_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_x_1284_);
v_xType_1285_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_xType_1285_);
v_cs_1286_ = lean_ctor_get(v_t_1173_, 3);
lean_inc_ref(v_cs_1286_);
lean_dec_ref_known(v_t_1173_, 4);
v___x_1287_ = lean_apply_4(v_k_1174_, v_tid_1283_, v_x_1284_, v_xType_1285_, v_cs_1286_);
return v___x_1287_;
}
case 28:
{
lean_object* v_x_1288_; lean_object* v___x_1289_; 
v_x_1288_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_x_1288_);
lean_dec_ref_known(v_t_1173_, 1);
v___x_1289_ = lean_apply_1(v_k_1174_, v_x_1288_);
return v___x_1289_;
}
case 29:
{
lean_object* v_j_1290_; lean_object* v_ys_1291_; lean_object* v___x_1292_; 
v_j_1290_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_j_1290_);
v_ys_1291_ = lean_ctor_get(v_t_1173_, 1);
lean_inc_ref(v_ys_1291_);
lean_dec_ref_known(v_t_1173_, 2);
v___x_1292_ = lean_apply_2(v_k_1174_, v_j_1290_, v_ys_1291_);
return v___x_1292_;
}
case 30:
{
return v_k_1174_;
}
default: 
{
lean_object* v_tgt_1293_; lean_object* v_b_1294_; lean_object* v_n_1295_; lean_object* v_x_1296_; lean_object* v___x_1297_; 
v_tgt_1293_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_tgt_1293_);
v_b_1294_ = lean_ctor_get(v_t_1173_, 1);
lean_inc(v_b_1294_);
v_n_1295_ = lean_ctor_get(v_t_1173_, 2);
lean_inc(v_n_1295_);
v_x_1296_ = lean_ctor_get(v_t_1173_, 3);
lean_inc(v_x_1296_);
lean_dec(v_t_1173_);
v___x_1297_ = lean_apply_4(v_k_1174_, v_tgt_1293_, v_b_1294_, v_n_1295_, v_x_1296_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim(lean_object* v_motive__2_1298_, lean_object* v_ctorIdx_1299_, lean_object* v_t_1300_, lean_object* v_h_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1300_, v_k_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___boxed(lean_object* v_motive__2_1304_, lean_object* v_ctorIdx_1305_, lean_object* v_t_1306_, lean_object* v_h_1307_, lean_object* v_k_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_IR_FnBody_ctorElim(v_motive__2_1304_, v_ctorIdx_1305_, v_t_1306_, v_h_1307_, v_k_1308_);
lean_dec(v_ctorIdx_1305_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctor_elim___redArg(lean_object* v_t_1310_, lean_object* v_ctor_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1310_, v_ctor_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctor_elim(lean_object* v_motive__2_1313_, lean_object* v_t_1314_, lean_object* v_h_1315_, lean_object* v_ctor_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1314_, v_ctor_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reset_elim___redArg(lean_object* v_t_1318_, lean_object* v_reset_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1318_, v_reset_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reset_elim(lean_object* v_motive__2_1321_, lean_object* v_t_1322_, lean_object* v_h_1323_, lean_object* v_reset_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1322_, v_reset_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reuse_elim___redArg(lean_object* v_t_1326_, lean_object* v_reuse_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1326_, v_reuse_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_reuse_elim(lean_object* v_motive__2_1329_, lean_object* v_t_1330_, lean_object* v_h_1331_, lean_object* v_reuse_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1330_, v_reuse_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_proj_elim___redArg(lean_object* v_t_1334_, lean_object* v_proj_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1334_, v_proj_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_proj_elim(lean_object* v_motive__2_1337_, lean_object* v_t_1338_, lean_object* v_h_1339_, lean_object* v_proj_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1338_, v_proj_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uproj_elim___redArg(lean_object* v_t_1342_, lean_object* v_uproj_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1342_, v_uproj_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uproj_elim(lean_object* v_motive__2_1345_, lean_object* v_t_1346_, lean_object* v_h_1347_, lean_object* v_uproj_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1346_, v_uproj_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sproj_elim___redArg(lean_object* v_t_1350_, lean_object* v_sproj_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1350_, v_sproj_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sproj_elim(lean_object* v_motive__2_1353_, lean_object* v_t_1354_, lean_object* v_h_1355_, lean_object* v_sproj_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1354_, v_sproj_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_fap_elim___redArg(lean_object* v_t_1358_, lean_object* v_fap_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1358_, v_fap_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_fap_elim(lean_object* v_motive__2_1361_, lean_object* v_t_1362_, lean_object* v_h_1363_, lean_object* v_fap_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1362_, v_fap_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_pap_elim___redArg(lean_object* v_t_1366_, lean_object* v_pap_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1366_, v_pap_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_pap_elim(lean_object* v_motive__2_1369_, lean_object* v_t_1370_, lean_object* v_h_1371_, lean_object* v_pap_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1370_, v_pap_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ap_elim___redArg(lean_object* v_t_1374_, lean_object* v_ap_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1374_, v_ap_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ap_elim(lean_object* v_motive__2_1377_, lean_object* v_t_1378_, lean_object* v_h_1379_, lean_object* v_ap_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1378_, v_ap_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_box_elim___redArg(lean_object* v_t_1382_, lean_object* v_box_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1382_, v_box_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_box_elim(lean_object* v_motive__2_1385_, lean_object* v_t_1386_, lean_object* v_h_1387_, lean_object* v_box_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1386_, v_box_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unbox_elim___redArg(lean_object* v_t_1390_, lean_object* v_unbox_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1390_, v_unbox_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unbox_elim(lean_object* v_motive__2_1393_, lean_object* v_t_1394_, lean_object* v_h_1395_, lean_object* v_unbox_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1394_, v_unbox_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint8Lit_elim___redArg(lean_object* v_t_1398_, lean_object* v_uint8Lit_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1398_, v_uint8Lit_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint8Lit_elim(lean_object* v_motive__2_1401_, lean_object* v_t_1402_, lean_object* v_h_1403_, lean_object* v_uint8Lit_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1402_, v_uint8Lit_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint16Lit_elim___redArg(lean_object* v_t_1406_, lean_object* v_uint16Lit_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1406_, v_uint16Lit_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint16Lit_elim(lean_object* v_motive__2_1409_, lean_object* v_t_1410_, lean_object* v_h_1411_, lean_object* v_uint16Lit_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1410_, v_uint16Lit_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint32Lit_elim___redArg(lean_object* v_t_1414_, lean_object* v_uint32Lit_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1414_, v_uint32Lit_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint32Lit_elim(lean_object* v_motive__2_1417_, lean_object* v_t_1418_, lean_object* v_h_1419_, lean_object* v_uint32Lit_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1418_, v_uint32Lit_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint64Lit_elim___redArg(lean_object* v_t_1422_, lean_object* v_uint64Lit_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1422_, v_uint64Lit_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uint64Lit_elim(lean_object* v_motive__2_1425_, lean_object* v_t_1426_, lean_object* v_h_1427_, lean_object* v_uint64Lit_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1426_, v_uint64Lit_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_usizeLit_elim___redArg(lean_object* v_t_1430_, lean_object* v_usizeLit_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1430_, v_usizeLit_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_usizeLit_elim(lean_object* v_motive__2_1433_, lean_object* v_t_1434_, lean_object* v_h_1435_, lean_object* v_usizeLit_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1434_, v_usizeLit_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_natLit_elim___redArg(lean_object* v_t_1438_, lean_object* v_natLit_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1438_, v_natLit_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_natLit_elim(lean_object* v_motive__2_1441_, lean_object* v_t_1442_, lean_object* v_h_1443_, lean_object* v_natLit_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1442_, v_natLit_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_strLit_elim___redArg(lean_object* v_t_1446_, lean_object* v_strLit_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1446_, v_strLit_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_strLit_elim(lean_object* v_motive__2_1449_, lean_object* v_t_1450_, lean_object* v_h_1451_, lean_object* v_strLit_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1450_, v_strLit_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isShared_elim___redArg(lean_object* v_t_1454_, lean_object* v_isShared_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1454_, v_isShared_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isShared_elim(lean_object* v_motive__2_1457_, lean_object* v_t_1458_, lean_object* v_h_1459_, lean_object* v_isShared_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1458_, v_isShared_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim___redArg(lean_object* v_t_1462_, lean_object* v_jdecl_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1462_, v_jdecl_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim(lean_object* v_motive__2_1465_, lean_object* v_t_1466_, lean_object* v_h_1467_, lean_object* v_jdecl_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1466_, v_jdecl_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim___redArg(lean_object* v_t_1470_, lean_object* v_set_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1470_, v_set_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim(lean_object* v_motive__2_1473_, lean_object* v_t_1474_, lean_object* v_h_1475_, lean_object* v_set_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1474_, v_set_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim___redArg(lean_object* v_t_1478_, lean_object* v_setTag_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1478_, v_setTag_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim(lean_object* v_motive__2_1481_, lean_object* v_t_1482_, lean_object* v_h_1483_, lean_object* v_setTag_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1482_, v_setTag_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim___redArg(lean_object* v_t_1486_, lean_object* v_uset_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1486_, v_uset_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim(lean_object* v_motive__2_1489_, lean_object* v_t_1490_, lean_object* v_h_1491_, lean_object* v_uset_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1490_, v_uset_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim___redArg(lean_object* v_t_1494_, lean_object* v_sset_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1494_, v_sset_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim(lean_object* v_motive__2_1497_, lean_object* v_t_1498_, lean_object* v_h_1499_, lean_object* v_sset_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1498_, v_sset_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim___redArg(lean_object* v_t_1502_, lean_object* v_inc_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1502_, v_inc_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim(lean_object* v_motive__2_1505_, lean_object* v_t_1506_, lean_object* v_h_1507_, lean_object* v_inc_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1506_, v_inc_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim___redArg(lean_object* v_t_1510_, lean_object* v_dec_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1510_, v_dec_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim(lean_object* v_motive__2_1513_, lean_object* v_t_1514_, lean_object* v_h_1515_, lean_object* v_dec_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1514_, v_dec_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim___redArg(lean_object* v_t_1518_, lean_object* v_del_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1518_, v_del_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim(lean_object* v_motive__2_1521_, lean_object* v_t_1522_, lean_object* v_h_1523_, lean_object* v_del_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1522_, v_del_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim___redArg(lean_object* v_t_1526_, lean_object* v_case_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1526_, v_case_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim(lean_object* v_motive__2_1529_, lean_object* v_t_1530_, lean_object* v_h_1531_, lean_object* v_case_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1530_, v_case_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim___redArg(lean_object* v_t_1534_, lean_object* v_ret_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1534_, v_ret_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim(lean_object* v_motive__2_1537_, lean_object* v_t_1538_, lean_object* v_h_1539_, lean_object* v_ret_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1538_, v_ret_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim___redArg(lean_object* v_t_1542_, lean_object* v_jmp_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1542_, v_jmp_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim(lean_object* v_motive__2_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_jmp_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1546_, v_jmp_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim___redArg(lean_object* v_t_1550_, lean_object* v_unreachable_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1550_, v_unreachable_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim(lean_object* v_motive__2_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_unreachable_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1554_, v_unreachable_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_nil(void){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_box(30);
return v___x_1572_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* v_x_1573_){
_start:
{
switch(lean_obj_tag(v_x_1573_))
{
case 27:
{
uint8_t v___x_1574_; 
v___x_1574_ = 1;
return v___x_1574_;
}
case 28:
{
uint8_t v___x_1575_; 
v___x_1575_ = 1;
return v___x_1575_;
}
case 29:
{
uint8_t v___x_1576_; 
v___x_1576_ = 1;
return v___x_1576_;
}
case 30:
{
uint8_t v___x_1577_; 
v___x_1577_ = 1;
return v___x_1577_;
}
default: 
{
uint8_t v___x_1578_; 
v___x_1578_ = 0;
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object* v_x_1579_){
_start:
{
uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_res_1580_ = l_Lean_IR_FnBody_isTerminal(v_x_1579_);
lean_dec(v_x_1579_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isVarDecl(lean_object* v_x_1582_){
_start:
{
switch(lean_obj_tag(v_x_1582_))
{
case 0:
{
uint8_t v___x_1583_; 
v___x_1583_ = 1;
return v___x_1583_;
}
case 1:
{
uint8_t v___x_1584_; 
v___x_1584_ = 1;
return v___x_1584_;
}
case 2:
{
uint8_t v___x_1585_; 
v___x_1585_ = 1;
return v___x_1585_;
}
case 3:
{
uint8_t v___x_1586_; 
v___x_1586_ = 1;
return v___x_1586_;
}
case 4:
{
uint8_t v___x_1587_; 
v___x_1587_ = 1;
return v___x_1587_;
}
case 5:
{
uint8_t v___x_1588_; 
v___x_1588_ = 1;
return v___x_1588_;
}
case 6:
{
uint8_t v___x_1589_; 
v___x_1589_ = 1;
return v___x_1589_;
}
case 7:
{
uint8_t v___x_1590_; 
v___x_1590_ = 1;
return v___x_1590_;
}
case 8:
{
uint8_t v___x_1591_; 
v___x_1591_ = 1;
return v___x_1591_;
}
case 9:
{
uint8_t v___x_1592_; 
v___x_1592_ = 1;
return v___x_1592_;
}
case 10:
{
uint8_t v___x_1593_; 
v___x_1593_ = 1;
return v___x_1593_;
}
case 11:
{
uint8_t v___x_1594_; 
v___x_1594_ = 1;
return v___x_1594_;
}
case 12:
{
uint8_t v___x_1595_; 
v___x_1595_ = 1;
return v___x_1595_;
}
case 13:
{
uint8_t v___x_1596_; 
v___x_1596_ = 1;
return v___x_1596_;
}
case 14:
{
uint8_t v___x_1597_; 
v___x_1597_ = 1;
return v___x_1597_;
}
case 15:
{
uint8_t v___x_1598_; 
v___x_1598_ = 1;
return v___x_1598_;
}
case 16:
{
uint8_t v___x_1599_; 
v___x_1599_ = 1;
return v___x_1599_;
}
case 17:
{
uint8_t v___x_1600_; 
v___x_1600_ = 1;
return v___x_1600_;
}
case 18:
{
uint8_t v___x_1601_; 
v___x_1601_ = 1;
return v___x_1601_;
}
default: 
{
uint8_t v___x_1602_; 
v___x_1602_ = 0;
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isVarDecl___boxed(lean_object* v_x_1603_){
_start:
{
uint8_t v_res_1604_; lean_object* v_r_1605_; 
v_res_1604_ = l_Lean_IR_FnBody_isVarDecl(v_x_1603_);
lean_dec(v_x_1603_);
v_r_1605_ = lean_box(v_res_1604_);
return v_r_1605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_targetVar_spec__0(lean_object* v_msg_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = lean_panic_fn_borrowed(v___x_1607_, v_msg_1606_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_targetVar___closed__3(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__2));
v___x_1613_ = lean_unsigned_to_nat(9u);
v___x_1614_ = lean_unsigned_to_nat(304u);
v___x_1615_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__1));
v___x_1616_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__0));
v___x_1617_ = l_mkPanicMessageWithDecl(v___x_1616_, v___x_1615_, v___x_1614_, v___x_1613_, v___x_1612_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetVar(lean_object* v_x_1618_){
_start:
{
switch(lean_obj_tag(v_x_1618_))
{
case 0:
{
lean_object* v_tgt_1619_; 
v_tgt_1619_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1619_);
return v_tgt_1619_;
}
case 1:
{
lean_object* v_tgt_1620_; 
v_tgt_1620_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1620_);
return v_tgt_1620_;
}
case 2:
{
lean_object* v_tgt_1621_; 
v_tgt_1621_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1621_);
return v_tgt_1621_;
}
case 3:
{
lean_object* v_tgt_1622_; 
v_tgt_1622_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1622_);
return v_tgt_1622_;
}
case 4:
{
lean_object* v_tgt_1623_; 
v_tgt_1623_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1623_);
return v_tgt_1623_;
}
case 5:
{
lean_object* v_tgt_1624_; 
v_tgt_1624_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1624_);
return v_tgt_1624_;
}
case 6:
{
lean_object* v_tgt_1625_; 
v_tgt_1625_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1625_);
return v_tgt_1625_;
}
case 7:
{
lean_object* v_tgt_1626_; 
v_tgt_1626_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1626_);
return v_tgt_1626_;
}
case 8:
{
lean_object* v_tgt_1627_; 
v_tgt_1627_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1627_);
return v_tgt_1627_;
}
case 9:
{
lean_object* v_tgt_1628_; 
v_tgt_1628_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1628_);
return v_tgt_1628_;
}
case 10:
{
lean_object* v_tgt_1629_; 
v_tgt_1629_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1629_);
return v_tgt_1629_;
}
case 11:
{
lean_object* v_tgt_1630_; 
v_tgt_1630_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1630_);
return v_tgt_1630_;
}
case 12:
{
lean_object* v_tgt_1631_; 
v_tgt_1631_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1631_);
return v_tgt_1631_;
}
case 13:
{
lean_object* v_tgt_1632_; 
v_tgt_1632_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1632_);
return v_tgt_1632_;
}
case 14:
{
lean_object* v_tgt_1633_; 
v_tgt_1633_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1633_);
return v_tgt_1633_;
}
case 15:
{
lean_object* v_tgt_1634_; 
v_tgt_1634_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1634_);
return v_tgt_1634_;
}
case 16:
{
lean_object* v_tgt_1635_; 
v_tgt_1635_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1635_);
return v_tgt_1635_;
}
case 17:
{
lean_object* v_tgt_1636_; 
v_tgt_1636_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1636_);
return v_tgt_1636_;
}
case 18:
{
lean_object* v_tgt_1637_; 
v_tgt_1637_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_tgt_1637_);
return v_tgt_1637_;
}
default: 
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_obj_once(&l_Lean_IR_FnBody_targetVar___closed__3, &l_Lean_IR_FnBody_targetVar___closed__3_once, _init_l_Lean_IR_FnBody_targetVar___closed__3);
v___x_1639_ = l_panic___at___00Lean_IR_FnBody_targetVar_spec__0(v___x_1638_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetVar___boxed(lean_object* v_x_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_IR_FnBody_targetVar(v_x_1640_);
lean_dec(v_x_1640_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_targetType_spec__0(lean_object* v_msg_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_panic_fn_borrowed(v___x_1643_, v_msg_1642_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_targetType___closed__1(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__2));
v___x_1647_ = lean_unsigned_to_nat(9u);
v___x_1648_ = lean_unsigned_to_nat(331u);
v___x_1649_ = ((lean_object*)(l_Lean_IR_FnBody_targetType___closed__0));
v___x_1650_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__0));
v___x_1651_ = l_mkPanicMessageWithDecl(v___x_1650_, v___x_1649_, v___x_1648_, v___x_1647_, v___x_1646_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetType(lean_object* v_x_1652_){
_start:
{
switch(lean_obj_tag(v_x_1652_))
{
case 0:
{
lean_object* v_i_1653_; lean_object* v___x_1654_; 
v_i_1653_ = lean_ctor_get(v_x_1652_, 2);
v___x_1654_ = l_Lean_IR_CtorInfo_type(v_i_1653_);
return v___x_1654_;
}
case 1:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_box(8);
return v___x_1655_;
}
case 2:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_box(7);
return v___x_1656_;
}
case 3:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_box(8);
return v___x_1657_;
}
case 4:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_box(5);
return v___x_1658_;
}
case 5:
{
lean_object* v_ty_1659_; 
v_ty_1659_ = lean_ctor_get(v_x_1652_, 2);
lean_inc(v_ty_1659_);
return v_ty_1659_;
}
case 6:
{
lean_object* v_ty_1660_; 
v_ty_1660_ = lean_ctor_get(v_x_1652_, 2);
lean_inc(v_ty_1660_);
return v_ty_1660_;
}
case 7:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_box(7);
return v___x_1661_;
}
case 8:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_box(8);
return v___x_1662_;
}
case 9:
{
lean_object* v_ty_1663_; 
v_ty_1663_ = lean_ctor_get(v_x_1652_, 2);
switch(lean_obj_tag(v_ty_1663_))
{
case 1:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_box(12);
return v___x_1664_;
}
case 2:
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_box(12);
return v___x_1665_;
}
case 4:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_box(7);
return v___x_1666_;
}
case 5:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_box(7);
return v___x_1667_;
}
case 0:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_box(7);
return v___x_1668_;
}
case 9:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_box(7);
return v___x_1669_;
}
default: 
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_box(8);
return v___x_1670_;
}
}
}
case 10:
{
lean_object* v_ty_1671_; 
v_ty_1671_ = lean_ctor_get(v_x_1652_, 2);
lean_inc(v_ty_1671_);
return v_ty_1671_;
}
case 11:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_box(1);
return v___x_1672_;
}
case 12:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_box(2);
return v___x_1673_;
}
case 13:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_box(3);
return v___x_1674_;
}
case 14:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_box(4);
return v___x_1675_;
}
case 15:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_box(5);
return v___x_1676_;
}
case 16:
{
lean_object* v_v_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_v_1677_ = lean_ctor_get(v_x_1652_, 2);
v___x_1678_ = lean_unsigned_to_nat(2147483648u);
v___x_1679_ = lean_nat_dec_lt(v_v_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_box(8);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_box(12);
return v___x_1681_;
}
}
case 17:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_box(7);
return v___x_1682_;
}
case 18:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_box(1);
return v___x_1683_;
}
default: 
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_obj_once(&l_Lean_IR_FnBody_targetType___closed__1, &l_Lean_IR_FnBody_targetType___closed__1_once, _init_l_Lean_IR_FnBody_targetType___closed__1);
v___x_1685_ = l_panic___at___00Lean_IR_FnBody_targetType_spec__0(v___x_1684_);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetType___boxed(lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_IR_FnBody_targetType(v_x_1686_);
lean_dec(v_x_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_setTargetVar_spec__0(lean_object* v_msg_1688_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_1690_ = lean_panic_fn_borrowed(v___x_1689_, v_msg_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_setTargetVar___closed__1(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1692_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__2));
v___x_1693_ = lean_unsigned_to_nat(12u);
v___x_1694_ = lean_unsigned_to_nat(353u);
v___x_1695_ = ((lean_object*)(l_Lean_IR_FnBody_setTargetVar___closed__0));
v___x_1696_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__0));
v___x_1697_ = l_mkPanicMessageWithDecl(v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_, v___x_1692_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTargetVar(lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
switch(lean_obj_tag(v_x_1698_))
{
case 0:
{
lean_object* v_b_1700_; lean_object* v_i_1701_; lean_object* v_ys_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_b_1700_ = lean_ctor_get(v_x_1698_, 1);
v_i_1701_ = lean_ctor_get(v_x_1698_, 2);
v_ys_1702_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1710_);
v___x_1704_ = v_x_1698_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_ys_1702_);
lean_inc(v_i_1701_);
lean_inc(v_b_1700_);
lean_dec(v_x_1698_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v_x_1699_);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_b_1700_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_i_1701_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_ys_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
case 1:
{
lean_object* v_b_1711_; lean_object* v_n_1712_; lean_object* v_x_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_b_1711_ = lean_ctor_get(v_x_1698_, 1);
v_n_1712_ = lean_ctor_get(v_x_1698_, 2);
v_x_1713_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1721_);
v___x_1715_ = v_x_1698_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_x_1713_);
lean_inc(v_n_1712_);
lean_inc(v_b_1711_);
lean_dec(v_x_1698_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v_x_1699_);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_b_1711_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_n_1712_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_x_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
case 2:
{
lean_object* v_b_1722_; lean_object* v_x_1723_; lean_object* v_i_1724_; uint8_t v_updtHeader_1725_; lean_object* v_ys_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_b_1722_ = lean_ctor_get(v_x_1698_, 1);
v_x_1723_ = lean_ctor_get(v_x_1698_, 2);
v_i_1724_ = lean_ctor_get(v_x_1698_, 3);
v_updtHeader_1725_ = lean_ctor_get_uint8(v_x_1698_, sizeof(void*)*5);
v_ys_1726_ = lean_ctor_get(v_x_1698_, 4);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1734_);
v___x_1728_ = v_x_1698_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_ys_1726_);
lean_inc(v_i_1724_);
lean_inc(v_x_1723_);
lean_inc(v_b_1722_);
lean_dec(v_x_1698_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_x_1699_);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_b_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_x_1723_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_i_1724_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_ys_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*5, v_updtHeader_1725_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
case 3:
{
lean_object* v_b_1735_; lean_object* v_i_1736_; lean_object* v_x_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_b_1735_ = lean_ctor_get(v_x_1698_, 1);
v_i_1736_ = lean_ctor_get(v_x_1698_, 2);
v_x_1737_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1745_);
v___x_1739_ = v_x_1698_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_x_1737_);
lean_inc(v_i_1736_);
lean_inc(v_b_1735_);
lean_dec(v_x_1698_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_x_1699_);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_b_1735_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_i_1736_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_x_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
case 4:
{
lean_object* v_b_1746_; lean_object* v_i_1747_; lean_object* v_x_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_b_1746_ = lean_ctor_get(v_x_1698_, 1);
v_i_1747_ = lean_ctor_get(v_x_1698_, 2);
v_x_1748_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1756_);
v___x_1750_ = v_x_1698_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_x_1748_);
lean_inc(v_i_1747_);
lean_inc(v_b_1746_);
lean_dec(v_x_1698_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v_x_1699_);
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_b_1746_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_i_1747_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_x_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
case 5:
{
lean_object* v_b_1757_; lean_object* v_ty_1758_; lean_object* v_n_1759_; lean_object* v_offset_1760_; lean_object* v_x_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_b_1757_ = lean_ctor_get(v_x_1698_, 1);
v_ty_1758_ = lean_ctor_get(v_x_1698_, 2);
v_n_1759_ = lean_ctor_get(v_x_1698_, 3);
v_offset_1760_ = lean_ctor_get(v_x_1698_, 4);
v_x_1761_ = lean_ctor_get(v_x_1698_, 5);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1769_);
v___x_1763_ = v_x_1698_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_x_1761_);
lean_inc(v_offset_1760_);
lean_inc(v_n_1759_);
lean_inc(v_ty_1758_);
lean_inc(v_b_1757_);
lean_dec(v_x_1698_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v_x_1699_);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_b_1757_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_ty_1758_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_n_1759_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_offset_1760_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v_x_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
case 6:
{
lean_object* v_b_1770_; lean_object* v_ty_1771_; lean_object* v_c_1772_; lean_object* v_ys_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_b_1770_ = lean_ctor_get(v_x_1698_, 1);
v_ty_1771_ = lean_ctor_get(v_x_1698_, 2);
v_c_1772_ = lean_ctor_get(v_x_1698_, 3);
v_ys_1773_ = lean_ctor_get(v_x_1698_, 4);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1781_);
v___x_1775_ = v_x_1698_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_ys_1773_);
lean_inc(v_c_1772_);
lean_inc(v_ty_1771_);
lean_inc(v_b_1770_);
lean_dec(v_x_1698_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v_x_1699_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_b_1770_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_ty_1771_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_c_1772_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_ys_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
case 7:
{
lean_object* v_b_1782_; lean_object* v_c_1783_; lean_object* v_ys_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_b_1782_ = lean_ctor_get(v_x_1698_, 1);
v_c_1783_ = lean_ctor_get(v_x_1698_, 2);
v_ys_1784_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1792_);
v___x_1786_ = v_x_1698_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_ys_1784_);
lean_inc(v_c_1783_);
lean_inc(v_b_1782_);
lean_dec(v_x_1698_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_x_1699_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_b_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_c_1783_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_ys_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
case 8:
{
lean_object* v_b_1793_; lean_object* v_x_1794_; lean_object* v_ys_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_b_1793_ = lean_ctor_get(v_x_1698_, 1);
v_x_1794_ = lean_ctor_get(v_x_1698_, 2);
v_ys_1795_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1803_);
v___x_1797_ = v_x_1698_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_ys_1795_);
lean_inc(v_x_1794_);
lean_inc(v_b_1793_);
lean_dec(v_x_1698_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v_x_1699_);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_b_1793_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_x_1794_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_ys_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
case 9:
{
lean_object* v_b_1804_; lean_object* v_ty_1805_; lean_object* v_x_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_b_1804_ = lean_ctor_get(v_x_1698_, 1);
v_ty_1805_ = lean_ctor_get(v_x_1698_, 2);
v_x_1806_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1814_);
v___x_1808_ = v_x_1698_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_x_1806_);
lean_inc(v_ty_1805_);
lean_inc(v_b_1804_);
lean_dec(v_x_1698_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_x_1699_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_b_1804_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_ty_1805_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_x_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
case 10:
{
lean_object* v_b_1815_; lean_object* v_ty_1816_; lean_object* v_x_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_b_1815_ = lean_ctor_get(v_x_1698_, 1);
v_ty_1816_ = lean_ctor_get(v_x_1698_, 2);
v_x_1817_ = lean_ctor_get(v_x_1698_, 3);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1825_);
v___x_1819_ = v_x_1698_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_x_1817_);
lean_inc(v_ty_1816_);
lean_inc(v_b_1815_);
lean_dec(v_x_1698_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v_x_1699_);
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_b_1815_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_ty_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_x_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
case 11:
{
lean_object* v_b_1826_; uint8_t v_v_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v_b_1826_ = lean_ctor_get(v_x_1698_, 1);
v_v_1827_ = lean_ctor_get_uint8(v_x_1698_, sizeof(void*)*2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1835_);
v___x_1829_ = v_x_1698_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_b_1826_);
lean_dec(v_x_1698_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v_x_1699_);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_b_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*2, v_v_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
case 12:
{
lean_object* v_b_1836_; uint16_t v_v_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_b_1836_ = lean_ctor_get(v_x_1698_, 1);
v_v_1837_ = lean_ctor_get_uint16(v_x_1698_, sizeof(void*)*2);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; 
v_unused_1845_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1845_);
v___x_1839_ = v_x_1698_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_b_1836_);
lean_dec(v_x_1698_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_x_1699_);
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_b_1836_);
lean_ctor_set_uint16(v_reuseFailAlloc_1843_, sizeof(void*)*2, v_v_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
case 13:
{
lean_object* v_b_1846_; uint32_t v_v_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_b_1846_ = lean_ctor_get(v_x_1698_, 1);
v_v_1847_ = lean_ctor_get_uint32(v_x_1698_, sizeof(void*)*2);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1855_);
v___x_1849_ = v_x_1698_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_b_1846_);
lean_dec(v_x_1698_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_x_1699_);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_b_1846_);
lean_ctor_set_uint32(v_reuseFailAlloc_1853_, sizeof(void*)*2, v_v_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
case 14:
{
lean_object* v_b_1856_; uint64_t v_v_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_b_1856_ = lean_ctor_get(v_x_1698_, 1);
v_v_1857_ = lean_ctor_get_uint64(v_x_1698_, sizeof(void*)*2);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1865_);
v___x_1859_ = v_x_1698_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_b_1856_);
lean_dec(v_x_1698_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_x_1699_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_b_1856_);
lean_ctor_set_uint64(v_reuseFailAlloc_1863_, sizeof(void*)*2, v_v_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
case 15:
{
lean_object* v_b_1866_; uint64_t v_v_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_b_1866_ = lean_ctor_get(v_x_1698_, 1);
v_v_1867_ = lean_ctor_get_uint64(v_x_1698_, sizeof(void*)*2);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1874_ == 0)
{
lean_object* v_unused_1875_; 
v_unused_1875_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1875_);
v___x_1869_ = v_x_1698_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_b_1866_);
lean_dec(v_x_1698_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v_x_1699_);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_b_1866_);
lean_ctor_set_uint64(v_reuseFailAlloc_1873_, sizeof(void*)*2, v_v_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
case 16:
{
lean_object* v_b_1876_; lean_object* v_v_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_b_1876_ = lean_ctor_get(v_x_1698_, 1);
v_v_1877_ = lean_ctor_get(v_x_1698_, 2);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1885_);
v___x_1879_ = v_x_1698_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_v_1877_);
lean_inc(v_b_1876_);
lean_dec(v_x_1698_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_x_1699_);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_b_1876_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_v_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
case 17:
{
lean_object* v_b_1886_; lean_object* v_v_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
v_b_1886_ = lean_ctor_get(v_x_1698_, 1);
v_v_1887_ = lean_ctor_get(v_x_1698_, 2);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1895_);
v___x_1889_ = v_x_1698_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_v_1887_);
lean_inc(v_b_1886_);
lean_dec(v_x_1698_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_x_1699_);
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_b_1886_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_v_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
case 18:
{
lean_object* v_b_1896_; lean_object* v_x_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_b_1896_ = lean_ctor_get(v_x_1698_, 1);
v_x_1897_ = lean_ctor_get(v_x_1698_, 2);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1905_);
v___x_1899_ = v_x_1698_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_x_1897_);
lean_inc(v_b_1896_);
lean_dec(v_x_1698_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_x_1699_);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_b_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_x_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
default: 
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_dec(v_x_1699_);
lean_dec(v_x_1698_);
v___x_1906_ = lean_obj_once(&l_Lean_IR_FnBody_setTargetVar___closed__1, &l_Lean_IR_FnBody_setTargetVar___closed__1_once, _init_l_Lean_IR_FnBody_setTargetVar___closed__1);
v___x_1907_ = l_panic___at___00Lean_IR_FnBody_setTargetVar_spec__0(v___x_1906_);
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object* v_x_1908_){
_start:
{
switch(lean_obj_tag(v_x_1908_))
{
case 0:
{
lean_object* v_b_1909_; 
v_b_1909_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1909_);
return v_b_1909_;
}
case 1:
{
lean_object* v_b_1910_; 
v_b_1910_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1910_);
return v_b_1910_;
}
case 2:
{
lean_object* v_b_1911_; 
v_b_1911_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1911_);
return v_b_1911_;
}
case 3:
{
lean_object* v_b_1912_; 
v_b_1912_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1912_);
return v_b_1912_;
}
case 4:
{
lean_object* v_b_1913_; 
v_b_1913_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1913_);
return v_b_1913_;
}
case 5:
{
lean_object* v_b_1914_; 
v_b_1914_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1914_);
return v_b_1914_;
}
case 6:
{
lean_object* v_b_1915_; 
v_b_1915_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1915_);
return v_b_1915_;
}
case 7:
{
lean_object* v_b_1916_; 
v_b_1916_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1916_);
return v_b_1916_;
}
case 8:
{
lean_object* v_b_1917_; 
v_b_1917_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1917_);
return v_b_1917_;
}
case 9:
{
lean_object* v_b_1918_; 
v_b_1918_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1918_);
return v_b_1918_;
}
case 10:
{
lean_object* v_b_1919_; 
v_b_1919_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1919_);
return v_b_1919_;
}
case 11:
{
lean_object* v_b_1920_; 
v_b_1920_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1920_);
return v_b_1920_;
}
case 12:
{
lean_object* v_b_1921_; 
v_b_1921_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1921_);
return v_b_1921_;
}
case 13:
{
lean_object* v_b_1922_; 
v_b_1922_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1922_);
return v_b_1922_;
}
case 14:
{
lean_object* v_b_1923_; 
v_b_1923_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1923_);
return v_b_1923_;
}
case 15:
{
lean_object* v_b_1924_; 
v_b_1924_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1924_);
return v_b_1924_;
}
case 16:
{
lean_object* v_b_1925_; 
v_b_1925_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1925_);
return v_b_1925_;
}
case 17:
{
lean_object* v_b_1926_; 
v_b_1926_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1926_);
return v_b_1926_;
}
case 18:
{
lean_object* v_b_1927_; 
v_b_1927_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1927_);
return v_b_1927_;
}
case 19:
{
lean_object* v_b_1928_; 
v_b_1928_ = lean_ctor_get(v_x_1908_, 3);
lean_inc(v_b_1928_);
return v_b_1928_;
}
case 20:
{
lean_object* v_b_1929_; 
v_b_1929_ = lean_ctor_get(v_x_1908_, 3);
lean_inc(v_b_1929_);
return v_b_1929_;
}
case 22:
{
lean_object* v_b_1930_; 
v_b_1930_ = lean_ctor_get(v_x_1908_, 3);
lean_inc(v_b_1930_);
return v_b_1930_;
}
case 23:
{
lean_object* v_b_1931_; 
v_b_1931_ = lean_ctor_get(v_x_1908_, 5);
lean_inc(v_b_1931_);
return v_b_1931_;
}
case 21:
{
lean_object* v_b_1932_; 
v_b_1932_ = lean_ctor_get(v_x_1908_, 2);
lean_inc(v_b_1932_);
return v_b_1932_;
}
case 24:
{
lean_object* v_b_1933_; 
v_b_1933_ = lean_ctor_get(v_x_1908_, 2);
lean_inc(v_b_1933_);
return v_b_1933_;
}
case 25:
{
lean_object* v_b_1934_; 
v_b_1934_ = lean_ctor_get(v_x_1908_, 2);
lean_inc(v_b_1934_);
return v_b_1934_;
}
case 26:
{
lean_object* v_b_1935_; 
v_b_1935_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_b_1935_);
return v_b_1935_;
}
default: 
{
lean_inc(v_x_1908_);
return v_x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* v_x_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_IR_FnBody_body(v_x_1936_);
lean_dec(v_x_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
switch(lean_obj_tag(v_x_1938_))
{
case 0:
{
lean_object* v_tgt_1940_; lean_object* v_i_1941_; lean_object* v_ys_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_tgt_1940_ = lean_ctor_get(v_x_1938_, 0);
v_i_1941_ = lean_ctor_get(v_x_1938_, 2);
v_ys_1942_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_1950_);
v___x_1944_ = v_x_1938_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_ys_1942_);
lean_inc(v_i_1941_);
lean_inc(v_tgt_1940_);
lean_dec(v_x_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_x_1939_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_tgt_1940_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_i_1941_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_ys_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
case 1:
{
lean_object* v_tgt_1951_; lean_object* v_n_1952_; lean_object* v_x_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_tgt_1951_ = lean_ctor_get(v_x_1938_, 0);
v_n_1952_ = lean_ctor_get(v_x_1938_, 2);
v_x_1953_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_1961_);
v___x_1955_ = v_x_1938_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_x_1953_);
lean_inc(v_n_1952_);
lean_inc(v_tgt_1951_);
lean_dec(v_x_1938_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 1, v_x_1939_);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_tgt_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_n_1952_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_x_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
case 2:
{
lean_object* v_tgt_1962_; lean_object* v_x_1963_; lean_object* v_i_1964_; uint8_t v_updtHeader_1965_; lean_object* v_ys_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_tgt_1962_ = lean_ctor_get(v_x_1938_, 0);
v_x_1963_ = lean_ctor_get(v_x_1938_, 2);
v_i_1964_ = lean_ctor_get(v_x_1938_, 3);
v_updtHeader_1965_ = lean_ctor_get_uint8(v_x_1938_, sizeof(void*)*5);
v_ys_1966_ = lean_ctor_get(v_x_1938_, 4);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_1974_);
v___x_1968_ = v_x_1938_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_ys_1966_);
lean_inc(v_i_1964_);
lean_inc(v_x_1963_);
lean_inc(v_tgt_1962_);
lean_dec(v_x_1938_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v_x_1939_);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_tgt_1962_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_x_1963_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_i_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_ys_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*5, v_updtHeader_1965_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
case 3:
{
lean_object* v_tgt_1975_; lean_object* v_i_1976_; lean_object* v_x_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v_tgt_1975_ = lean_ctor_get(v_x_1938_, 0);
v_i_1976_ = lean_ctor_get(v_x_1938_, 2);
v_x_1977_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_1985_);
v___x_1979_ = v_x_1938_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_x_1977_);
lean_inc(v_i_1976_);
lean_inc(v_tgt_1975_);
lean_dec(v_x_1938_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v_x_1939_);
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_tgt_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_i_1976_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_x_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
case 4:
{
lean_object* v_tgt_1986_; lean_object* v_i_1987_; lean_object* v_x_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_tgt_1986_ = lean_ctor_get(v_x_1938_, 0);
v_i_1987_ = lean_ctor_get(v_x_1938_, 2);
v_x_1988_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_1996_);
v___x_1990_ = v_x_1938_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_x_1988_);
lean_inc(v_i_1987_);
lean_inc(v_tgt_1986_);
lean_dec(v_x_1938_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v_x_1939_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_tgt_1986_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_i_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_x_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
case 5:
{
lean_object* v_tgt_1997_; lean_object* v_ty_1998_; lean_object* v_n_1999_; lean_object* v_offset_2000_; lean_object* v_x_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_tgt_1997_ = lean_ctor_get(v_x_1938_, 0);
v_ty_1998_ = lean_ctor_get(v_x_1938_, 2);
v_n_1999_ = lean_ctor_get(v_x_1938_, 3);
v_offset_2000_ = lean_ctor_get(v_x_1938_, 4);
v_x_2001_ = lean_ctor_get(v_x_1938_, 5);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2009_);
v___x_2003_ = v_x_1938_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_x_2001_);
lean_inc(v_offset_2000_);
lean_inc(v_n_1999_);
lean_inc(v_ty_1998_);
lean_inc(v_tgt_1997_);
lean_dec(v_x_1938_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_x_1939_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_tgt_1997_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_ty_1998_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_n_1999_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_offset_2000_);
lean_ctor_set(v_reuseFailAlloc_2007_, 5, v_x_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
case 6:
{
lean_object* v_tgt_2010_; lean_object* v_ty_2011_; lean_object* v_c_2012_; lean_object* v_ys_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_tgt_2010_ = lean_ctor_get(v_x_1938_, 0);
v_ty_2011_ = lean_ctor_get(v_x_1938_, 2);
v_c_2012_ = lean_ctor_get(v_x_1938_, 3);
v_ys_2013_ = lean_ctor_get(v_x_1938_, 4);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2021_);
v___x_2015_ = v_x_1938_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_ys_2013_);
lean_inc(v_c_2012_);
lean_inc(v_ty_2011_);
lean_inc(v_tgt_2010_);
lean_dec(v_x_1938_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_x_1939_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_tgt_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_ty_2011_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_c_2012_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_ys_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
case 7:
{
lean_object* v_tgt_2022_; lean_object* v_c_2023_; lean_object* v_ys_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_tgt_2022_ = lean_ctor_get(v_x_1938_, 0);
v_c_2023_ = lean_ctor_get(v_x_1938_, 2);
v_ys_2024_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2032_);
v___x_2026_ = v_x_1938_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_ys_2024_);
lean_inc(v_c_2023_);
lean_inc(v_tgt_2022_);
lean_dec(v_x_1938_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v_x_1939_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_tgt_2022_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_c_2023_);
lean_ctor_set(v_reuseFailAlloc_2030_, 3, v_ys_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
case 8:
{
lean_object* v_tgt_2033_; lean_object* v_x_2034_; lean_object* v_ys_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_tgt_2033_ = lean_ctor_get(v_x_1938_, 0);
v_x_2034_ = lean_ctor_get(v_x_1938_, 2);
v_ys_2035_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2043_);
v___x_2037_ = v_x_1938_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_ys_2035_);
lean_inc(v_x_2034_);
lean_inc(v_tgt_2033_);
lean_dec(v_x_1938_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v_x_1939_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_tgt_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_x_2034_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_ys_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
case 9:
{
lean_object* v_tgt_2044_; lean_object* v_ty_2045_; lean_object* v_x_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_tgt_2044_ = lean_ctor_get(v_x_1938_, 0);
v_ty_2045_ = lean_ctor_get(v_x_1938_, 2);
v_x_2046_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2054_);
v___x_2048_ = v_x_1938_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_x_2046_);
lean_inc(v_ty_2045_);
lean_inc(v_tgt_2044_);
lean_dec(v_x_1938_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v_x_1939_);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_tgt_2044_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_ty_2045_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_x_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
case 10:
{
lean_object* v_tgt_2055_; lean_object* v_ty_2056_; lean_object* v_x_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_tgt_2055_ = lean_ctor_get(v_x_1938_, 0);
v_ty_2056_ = lean_ctor_get(v_x_1938_, 2);
v_x_2057_ = lean_ctor_get(v_x_1938_, 3);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2065_);
v___x_2059_ = v_x_1938_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_x_2057_);
lean_inc(v_ty_2056_);
lean_inc(v_tgt_2055_);
lean_dec(v_x_1938_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v_x_1939_);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_tgt_2055_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_ty_2056_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_x_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
case 11:
{
lean_object* v_tgt_2066_; uint8_t v_v_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_tgt_2066_ = lean_ctor_get(v_x_1938_, 0);
v_v_2067_ = lean_ctor_get_uint8(v_x_1938_, sizeof(void*)*2);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2075_);
v___x_2069_ = v_x_1938_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_tgt_2066_);
lean_dec(v_x_1938_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 1, v_x_1939_);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_tgt_2066_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_x_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, sizeof(void*)*2, v_v_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
case 12:
{
lean_object* v_tgt_2076_; uint16_t v_v_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_tgt_2076_ = lean_ctor_get(v_x_1938_, 0);
v_v_2077_ = lean_ctor_get_uint16(v_x_1938_, sizeof(void*)*2);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2085_);
v___x_2079_ = v_x_1938_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_tgt_2076_);
lean_dec(v_x_1938_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v_x_1939_);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_tgt_2076_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_x_1939_);
lean_ctor_set_uint16(v_reuseFailAlloc_2083_, sizeof(void*)*2, v_v_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
case 13:
{
lean_object* v_tgt_2086_; uint32_t v_v_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_tgt_2086_ = lean_ctor_get(v_x_1938_, 0);
v_v_2087_ = lean_ctor_get_uint32(v_x_1938_, sizeof(void*)*2);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2095_);
v___x_2089_ = v_x_1938_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_tgt_2086_);
lean_dec(v_x_1938_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_x_1939_);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_tgt_2086_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_x_1939_);
lean_ctor_set_uint32(v_reuseFailAlloc_2093_, sizeof(void*)*2, v_v_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
case 14:
{
lean_object* v_tgt_2096_; uint64_t v_v_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_tgt_2096_ = lean_ctor_get(v_x_1938_, 0);
v_v_2097_ = lean_ctor_get_uint64(v_x_1938_, sizeof(void*)*2);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2105_);
v___x_2099_ = v_x_1938_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_tgt_2096_);
lean_dec(v_x_1938_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v_x_1939_);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_tgt_2096_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_x_1939_);
lean_ctor_set_uint64(v_reuseFailAlloc_2103_, sizeof(void*)*2, v_v_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
case 15:
{
lean_object* v_tgt_2106_; uint64_t v_v_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_tgt_2106_ = lean_ctor_get(v_x_1938_, 0);
v_v_2107_ = lean_ctor_get_uint64(v_x_1938_, sizeof(void*)*2);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2115_);
v___x_2109_ = v_x_1938_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_tgt_2106_);
lean_dec(v_x_1938_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v_x_1939_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_tgt_2106_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_x_1939_);
lean_ctor_set_uint64(v_reuseFailAlloc_2113_, sizeof(void*)*2, v_v_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
case 16:
{
lean_object* v_tgt_2116_; lean_object* v_v_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_tgt_2116_ = lean_ctor_get(v_x_1938_, 0);
v_v_2117_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2125_);
v___x_2119_ = v_x_1938_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_v_2117_);
lean_inc(v_tgt_2116_);
lean_dec(v_x_1938_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_x_1939_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_tgt_2116_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_v_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
case 17:
{
lean_object* v_tgt_2126_; lean_object* v_v_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
v_tgt_2126_ = lean_ctor_get(v_x_1938_, 0);
v_v_2127_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2135_);
v___x_2129_ = v_x_1938_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_v_2127_);
lean_inc(v_tgt_2126_);
lean_dec(v_x_1938_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_x_1939_);
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_tgt_2126_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_v_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
case 18:
{
lean_object* v_tgt_2136_; lean_object* v_x_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_tgt_2136_ = lean_ctor_get(v_x_1938_, 0);
v_x_2137_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2145_);
v___x_2139_ = v_x_1938_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_x_2137_);
lean_inc(v_tgt_2136_);
lean_dec(v_x_1938_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_x_1939_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_tgt_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_x_1939_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_x_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
case 19:
{
lean_object* v_j_2146_; lean_object* v_xs_2147_; lean_object* v_v_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_j_2146_ = lean_ctor_get(v_x_1938_, 0);
v_xs_2147_ = lean_ctor_get(v_x_1938_, 1);
v_v_2148_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v_x_1938_, 3);
lean_dec(v_unused_2156_);
v___x_2150_ = v_x_1938_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_v_2148_);
lean_inc(v_xs_2147_);
lean_inc(v_j_2146_);
lean_dec(v_x_1938_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 3, v_x_1939_);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_j_2146_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_xs_2147_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_x_1939_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
case 20:
{
lean_object* v_x_2157_; lean_object* v_i_2158_; lean_object* v_y_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
v_x_2157_ = lean_ctor_get(v_x_1938_, 0);
v_i_2158_ = lean_ctor_get(v_x_1938_, 1);
v_y_2159_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v_x_1938_, 3);
lean_dec(v_unused_2167_);
v___x_2161_ = v_x_1938_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_y_2159_);
lean_inc(v_i_2158_);
lean_inc(v_x_2157_);
lean_dec(v_x_1938_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 3, v_x_1939_);
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(20, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_x_2157_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_i_2158_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_y_2159_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_x_1939_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
case 21:
{
lean_object* v_x_2168_; lean_object* v_cidx_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_x_2168_ = lean_ctor_get(v_x_1938_, 0);
v_cidx_2169_ = lean_ctor_get(v_x_1938_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v_x_1938_, 2);
lean_dec(v_unused_2177_);
v___x_2171_ = v_x_1938_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_cidx_2169_);
lean_inc(v_x_2168_);
lean_dec(v_x_1938_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 2, v_x_1939_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_x_2168_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_cidx_2169_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_x_1939_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
case 22:
{
lean_object* v_x_2178_; lean_object* v_i_2179_; lean_object* v_y_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_x_2178_ = lean_ctor_get(v_x_1938_, 0);
v_i_2179_ = lean_ctor_get(v_x_1938_, 1);
v_y_2180_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_x_1938_, 3);
lean_dec(v_unused_2188_);
v___x_2182_ = v_x_1938_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_y_2180_);
lean_inc(v_i_2179_);
lean_inc(v_x_2178_);
lean_dec(v_x_1938_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 3, v_x_1939_);
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_x_2178_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_i_2179_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_y_2180_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_x_1939_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
case 23:
{
lean_object* v_x_2189_; lean_object* v_i_2190_; lean_object* v_offset_2191_; lean_object* v_y_2192_; lean_object* v_ty_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
v_x_2189_ = lean_ctor_get(v_x_1938_, 0);
v_i_2190_ = lean_ctor_get(v_x_1938_, 1);
v_offset_2191_ = lean_ctor_get(v_x_1938_, 2);
v_y_2192_ = lean_ctor_get(v_x_1938_, 3);
v_ty_2193_ = lean_ctor_get(v_x_1938_, 4);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v_x_1938_, 5);
lean_dec(v_unused_2201_);
v___x_2195_ = v_x_1938_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_ty_2193_);
lean_inc(v_y_2192_);
lean_inc(v_offset_2191_);
lean_inc(v_i_2190_);
lean_inc(v_x_2189_);
lean_dec(v_x_1938_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 5, v_x_1939_);
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_x_2189_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_i_2190_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_offset_2191_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_y_2192_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_ty_2193_);
lean_ctor_set(v_reuseFailAlloc_2199_, 5, v_x_1939_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
case 24:
{
lean_object* v_x_2202_; lean_object* v_n_2203_; uint8_t v_c_2204_; uint8_t v_persistent_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_x_2202_ = lean_ctor_get(v_x_1938_, 0);
v_n_2203_ = lean_ctor_get(v_x_1938_, 1);
v_c_2204_ = lean_ctor_get_uint8(v_x_1938_, sizeof(void*)*3);
v_persistent_2205_ = lean_ctor_get_uint8(v_x_1938_, sizeof(void*)*3 + 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v_x_1938_, 2);
lean_dec(v_unused_2213_);
v___x_2207_ = v_x_1938_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_n_2203_);
lean_inc(v_x_2202_);
lean_dec(v_x_1938_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 2, v_x_1939_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(24, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_x_2202_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_n_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_x_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*3, v_c_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*3 + 1, v_persistent_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
case 25:
{
lean_object* v_x_2214_; lean_object* v_n_2215_; uint8_t v_c_2216_; uint8_t v_persistent_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_x_2214_ = lean_ctor_get(v_x_1938_, 0);
v_n_2215_ = lean_ctor_get(v_x_1938_, 1);
v_c_2216_ = lean_ctor_get_uint8(v_x_1938_, sizeof(void*)*3);
v_persistent_2217_ = lean_ctor_get_uint8(v_x_1938_, sizeof(void*)*3 + 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v_x_1938_, 2);
lean_dec(v_unused_2225_);
v___x_2219_ = v_x_1938_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_n_2215_);
lean_inc(v_x_2214_);
lean_dec(v_x_1938_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 2, v_x_1939_);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(25, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_x_2214_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_n_2215_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_x_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*3, v_c_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*3 + 1, v_persistent_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
case 26:
{
lean_object* v_x_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
v_x_2226_ = lean_ctor_get(v_x_1938_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; 
v_unused_2234_ = lean_ctor_get(v_x_1938_, 1);
lean_dec(v_unused_2234_);
v___x_2228_ = v_x_1938_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_x_2226_);
lean_dec(v_x_1938_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v_x_1939_);
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(26, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_x_2226_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_x_1939_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
default: 
{
lean_dec(v_x_1939_);
return v_x_1938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object* v_b_2235_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_box(30);
v___x_2237_ = l_Lean_IR_FnBody_setBody(v_b_2235_, v___x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object* v_b_2238_){
_start:
{
lean_object* v___y_2240_; 
switch(lean_obj_tag(v_b_2238_))
{
case 0:
{
lean_object* v_b_2244_; 
v_b_2244_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2244_);
v___y_2240_ = v_b_2244_;
goto v___jp_2239_;
}
case 1:
{
lean_object* v_b_2245_; 
v_b_2245_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2245_);
v___y_2240_ = v_b_2245_;
goto v___jp_2239_;
}
case 2:
{
lean_object* v_b_2246_; 
v_b_2246_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2246_);
v___y_2240_ = v_b_2246_;
goto v___jp_2239_;
}
case 3:
{
lean_object* v_b_2247_; 
v_b_2247_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2247_);
v___y_2240_ = v_b_2247_;
goto v___jp_2239_;
}
case 4:
{
lean_object* v_b_2248_; 
v_b_2248_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2248_);
v___y_2240_ = v_b_2248_;
goto v___jp_2239_;
}
case 5:
{
lean_object* v_b_2249_; 
v_b_2249_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2249_);
v___y_2240_ = v_b_2249_;
goto v___jp_2239_;
}
case 6:
{
lean_object* v_b_2250_; 
v_b_2250_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2250_);
v___y_2240_ = v_b_2250_;
goto v___jp_2239_;
}
case 7:
{
lean_object* v_b_2251_; 
v_b_2251_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2251_);
v___y_2240_ = v_b_2251_;
goto v___jp_2239_;
}
case 8:
{
lean_object* v_b_2252_; 
v_b_2252_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2252_);
v___y_2240_ = v_b_2252_;
goto v___jp_2239_;
}
case 9:
{
lean_object* v_b_2253_; 
v_b_2253_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2253_);
v___y_2240_ = v_b_2253_;
goto v___jp_2239_;
}
case 10:
{
lean_object* v_b_2254_; 
v_b_2254_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2254_);
v___y_2240_ = v_b_2254_;
goto v___jp_2239_;
}
case 11:
{
lean_object* v_b_2255_; 
v_b_2255_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2255_);
v___y_2240_ = v_b_2255_;
goto v___jp_2239_;
}
case 12:
{
lean_object* v_b_2256_; 
v_b_2256_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2256_);
v___y_2240_ = v_b_2256_;
goto v___jp_2239_;
}
case 13:
{
lean_object* v_b_2257_; 
v_b_2257_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2257_);
v___y_2240_ = v_b_2257_;
goto v___jp_2239_;
}
case 14:
{
lean_object* v_b_2258_; 
v_b_2258_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2258_);
v___y_2240_ = v_b_2258_;
goto v___jp_2239_;
}
case 15:
{
lean_object* v_b_2259_; 
v_b_2259_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2259_);
v___y_2240_ = v_b_2259_;
goto v___jp_2239_;
}
case 16:
{
lean_object* v_b_2260_; 
v_b_2260_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2260_);
v___y_2240_ = v_b_2260_;
goto v___jp_2239_;
}
case 17:
{
lean_object* v_b_2261_; 
v_b_2261_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2261_);
v___y_2240_ = v_b_2261_;
goto v___jp_2239_;
}
case 18:
{
lean_object* v_b_2262_; 
v_b_2262_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2262_);
v___y_2240_ = v_b_2262_;
goto v___jp_2239_;
}
case 19:
{
lean_object* v_b_2263_; 
v_b_2263_ = lean_ctor_get(v_b_2238_, 3);
lean_inc(v_b_2263_);
v___y_2240_ = v_b_2263_;
goto v___jp_2239_;
}
case 20:
{
lean_object* v_b_2264_; 
v_b_2264_ = lean_ctor_get(v_b_2238_, 3);
lean_inc(v_b_2264_);
v___y_2240_ = v_b_2264_;
goto v___jp_2239_;
}
case 22:
{
lean_object* v_b_2265_; 
v_b_2265_ = lean_ctor_get(v_b_2238_, 3);
lean_inc(v_b_2265_);
v___y_2240_ = v_b_2265_;
goto v___jp_2239_;
}
case 23:
{
lean_object* v_b_2266_; 
v_b_2266_ = lean_ctor_get(v_b_2238_, 5);
lean_inc(v_b_2266_);
v___y_2240_ = v_b_2266_;
goto v___jp_2239_;
}
case 21:
{
lean_object* v_b_2267_; 
v_b_2267_ = lean_ctor_get(v_b_2238_, 2);
lean_inc(v_b_2267_);
v___y_2240_ = v_b_2267_;
goto v___jp_2239_;
}
case 24:
{
lean_object* v_b_2268_; 
v_b_2268_ = lean_ctor_get(v_b_2238_, 2);
lean_inc(v_b_2268_);
v___y_2240_ = v_b_2268_;
goto v___jp_2239_;
}
case 25:
{
lean_object* v_b_2269_; 
v_b_2269_ = lean_ctor_get(v_b_2238_, 2);
lean_inc(v_b_2269_);
v___y_2240_ = v_b_2269_;
goto v___jp_2239_;
}
case 26:
{
lean_object* v_b_2270_; 
v_b_2270_ = lean_ctor_get(v_b_2238_, 1);
lean_inc(v_b_2270_);
v___y_2240_ = v_b_2270_;
goto v___jp_2239_;
}
default: 
{
lean_inc(v_b_2238_);
v___y_2240_ = v_b_2238_;
goto v___jp_2239_;
}
}
v___jp_2239_:
{
lean_object* v___x_2241_; lean_object* v_c_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_box(30);
v_c_2242_ = l_Lean_IR_FnBody_setBody(v_b_2238_, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v_c_2242_);
lean_ctor_set(v___x_2243_, 1, v___y_2240_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v_b_2272_; 
v_b_2272_ = lean_ctor_get(v_x_2271_, 1);
lean_inc(v_b_2272_);
return v_b_2272_;
}
else
{
lean_object* v_b_2273_; 
v_b_2273_ = lean_ctor_get(v_x_2271_, 0);
lean_inc(v_b_2273_);
return v_b_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object* v_x_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_IR_Alt_body(v_x_2274_);
lean_dec_ref(v_x_2274_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 0)
{
lean_object* v_info_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_info_2278_ = lean_ctor_get(v_x_2276_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v_x_2276_, 1);
lean_dec(v_unused_2286_);
v___x_2280_ = v_x_2276_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_info_2278_);
lean_dec(v_x_2276_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 1, v_x_2277_);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_info_2278_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_x_2277_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; 
v_unused_2294_ = lean_ctor_get(v_x_2276_, 0);
lean_dec(v_unused_2294_);
v___x_2288_ = v_x_2276_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_dec(v_x_2276_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_x_2277_);
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_x_2277_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object* v_f_2295_, lean_object* v_x_2296_){
_start:
{
if (lean_obj_tag(v_x_2296_) == 0)
{
lean_object* v_info_2297_; lean_object* v_b_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_info_2297_ = lean_ctor_get(v_x_2296_, 0);
v_b_2298_ = lean_ctor_get(v_x_2296_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_x_2296_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2300_ = v_x_2296_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_b_2298_);
lean_inc(v_info_2297_);
lean_dec(v_x_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_apply_1(v_f_2295_, v_b_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_info_2297_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v___x_2302_);
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
lean_object* v_b_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_b_2307_ = lean_ctor_get(v_x_2296_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_x_2296_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v_x_2296_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_b_2307_);
lean_dec(v_x_2296_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_apply_1(v_f_2295_, v_b_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(lean_object* v_info_2316_, lean_object* v_b_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_info_2316_);
lean_ctor_set(v___x_2318_, 1, v_b_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(lean_object* v_b_2319_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_b_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg(lean_object* v_inst_2322_, lean_object* v_f_2323_, lean_object* v_x_2324_){
_start:
{
lean_object* v_toApplicative_2325_; 
v_toApplicative_2325_ = lean_ctor_get(v_inst_2322_, 0);
lean_inc_ref(v_toApplicative_2325_);
lean_dec_ref(v_inst_2322_);
if (lean_obj_tag(v_x_2324_) == 0)
{
lean_object* v_toFunctor_2326_; lean_object* v_info_2327_; lean_object* v_b_2328_; lean_object* v_map_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_toFunctor_2326_ = lean_ctor_get(v_toApplicative_2325_, 0);
lean_inc_ref(v_toFunctor_2326_);
lean_dec_ref(v_toApplicative_2325_);
v_info_2327_ = lean_ctor_get(v_x_2324_, 0);
lean_inc_ref(v_info_2327_);
v_b_2328_ = lean_ctor_get(v_x_2324_, 1);
lean_inc(v_b_2328_);
lean_dec_ref_known(v_x_2324_, 2);
v_map_2329_ = lean_ctor_get(v_toFunctor_2326_, 0);
lean_inc(v_map_2329_);
lean_dec_ref(v_toFunctor_2326_);
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2330_, 0, v_info_2327_);
v___x_2331_ = lean_apply_1(v_f_2323_, v_b_2328_);
v___x_2332_ = lean_apply_4(v_map_2329_, lean_box(0), lean_box(0), v___f_2330_, v___x_2331_);
return v___x_2332_;
}
else
{
lean_object* v_toFunctor_2333_; lean_object* v_b_2334_; lean_object* v_map_2335_; lean_object* v___f_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_toFunctor_2333_ = lean_ctor_get(v_toApplicative_2325_, 0);
lean_inc_ref(v_toFunctor_2333_);
lean_dec_ref(v_toApplicative_2325_);
v_b_2334_ = lean_ctor_get(v_x_2324_, 0);
lean_inc(v_b_2334_);
lean_dec_ref_known(v_x_2324_, 1);
v_map_2335_ = lean_ctor_get(v_toFunctor_2333_, 0);
lean_inc(v_map_2335_);
lean_dec_ref(v_toFunctor_2333_);
v___f_2336_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_2337_ = lean_apply_1(v_f_2323_, v_b_2334_);
v___x_2338_ = lean_apply_4(v_map_2335_, lean_box(0), lean_box(0), v___f_2336_, v___x_2337_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM(lean_object* v_m_2339_, lean_object* v_inst_2340_, lean_object* v_f_2341_, lean_object* v_x_2342_){
_start:
{
lean_object* v_toApplicative_2343_; 
v_toApplicative_2343_ = lean_ctor_get(v_inst_2340_, 0);
lean_inc_ref(v_toApplicative_2343_);
lean_dec_ref(v_inst_2340_);
if (lean_obj_tag(v_x_2342_) == 0)
{
lean_object* v_toFunctor_2344_; lean_object* v_info_2345_; lean_object* v_b_2346_; lean_object* v_map_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_toFunctor_2344_ = lean_ctor_get(v_toApplicative_2343_, 0);
lean_inc_ref(v_toFunctor_2344_);
lean_dec_ref(v_toApplicative_2343_);
v_info_2345_ = lean_ctor_get(v_x_2342_, 0);
lean_inc_ref(v_info_2345_);
v_b_2346_ = lean_ctor_get(v_x_2342_, 1);
lean_inc(v_b_2346_);
lean_dec_ref_known(v_x_2342_, 2);
v_map_2347_ = lean_ctor_get(v_toFunctor_2344_, 0);
lean_inc(v_map_2347_);
lean_dec_ref(v_toFunctor_2344_);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2348_, 0, v_info_2345_);
v___x_2349_ = lean_apply_1(v_f_2341_, v_b_2346_);
v___x_2350_ = lean_apply_4(v_map_2347_, lean_box(0), lean_box(0), v___f_2348_, v___x_2349_);
return v___x_2350_;
}
else
{
lean_object* v_toFunctor_2351_; lean_object* v_b_2352_; lean_object* v_map_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_toFunctor_2351_ = lean_ctor_get(v_toApplicative_2343_, 0);
lean_inc_ref(v_toFunctor_2351_);
lean_dec_ref(v_toApplicative_2343_);
v_b_2352_ = lean_ctor_get(v_x_2342_, 0);
lean_inc(v_b_2352_);
lean_dec_ref_known(v_x_2342_, 1);
v_map_2353_ = lean_ctor_get(v_toFunctor_2351_, 0);
lean_inc(v_map_2353_);
lean_dec_ref(v_toFunctor_2351_);
v___f_2354_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_2355_ = lean_apply_1(v_f_2341_, v_b_2352_);
v___x_2356_ = lean_apply_4(v_map_2353_, lean_box(0), lean_box(0), v___f_2354_, v___x_2355_);
return v___x_2356_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* v_x_2357_){
_start:
{
if (lean_obj_tag(v_x_2357_) == 0)
{
uint8_t v___x_2358_; 
v___x_2358_ = 0;
return v___x_2358_;
}
else
{
uint8_t v___x_2359_; 
v___x_2359_ = 1;
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* v_x_2360_){
_start:
{
uint8_t v_res_2361_; lean_object* v_r_2362_; 
v_res_2361_ = l_Lean_IR_Alt_isDefault(v_x_2360_);
lean_dec_ref(v_x_2360_);
v_r_2362_ = lean_box(v_res_2361_);
return v_r_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object* v_bs_2363_, lean_object* v_b_2364_){
_start:
{
lean_object* v___x_2365_; lean_object* v_b_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_box(30);
v_b_2366_ = l_Lean_IR_FnBody_setBody(v_b_2364_, v___x_2365_);
v___x_2367_ = lean_array_push(v_bs_2363_, v_b_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object* v_b_2368_, lean_object* v_r_2369_){
_start:
{
lean_object* v___y_2371_; uint8_t v___x_2374_; 
v___x_2374_ = l_Lean_IR_FnBody_isTerminal(v_b_2368_);
if (v___x_2374_ == 0)
{
switch(lean_obj_tag(v_b_2368_))
{
case 0:
{
lean_object* v_b_2375_; 
v_b_2375_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2375_);
v___y_2371_ = v_b_2375_;
goto v___jp_2370_;
}
case 1:
{
lean_object* v_b_2376_; 
v_b_2376_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2376_);
v___y_2371_ = v_b_2376_;
goto v___jp_2370_;
}
case 2:
{
lean_object* v_b_2377_; 
v_b_2377_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2377_);
v___y_2371_ = v_b_2377_;
goto v___jp_2370_;
}
case 3:
{
lean_object* v_b_2378_; 
v_b_2378_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2378_);
v___y_2371_ = v_b_2378_;
goto v___jp_2370_;
}
case 4:
{
lean_object* v_b_2379_; 
v_b_2379_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2379_);
v___y_2371_ = v_b_2379_;
goto v___jp_2370_;
}
case 5:
{
lean_object* v_b_2380_; 
v_b_2380_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2380_);
v___y_2371_ = v_b_2380_;
goto v___jp_2370_;
}
case 6:
{
lean_object* v_b_2381_; 
v_b_2381_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2381_);
v___y_2371_ = v_b_2381_;
goto v___jp_2370_;
}
case 7:
{
lean_object* v_b_2382_; 
v_b_2382_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2382_);
v___y_2371_ = v_b_2382_;
goto v___jp_2370_;
}
case 8:
{
lean_object* v_b_2383_; 
v_b_2383_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2383_);
v___y_2371_ = v_b_2383_;
goto v___jp_2370_;
}
case 9:
{
lean_object* v_b_2384_; 
v_b_2384_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2384_);
v___y_2371_ = v_b_2384_;
goto v___jp_2370_;
}
case 10:
{
lean_object* v_b_2385_; 
v_b_2385_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2385_);
v___y_2371_ = v_b_2385_;
goto v___jp_2370_;
}
case 11:
{
lean_object* v_b_2386_; 
v_b_2386_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2386_);
v___y_2371_ = v_b_2386_;
goto v___jp_2370_;
}
case 12:
{
lean_object* v_b_2387_; 
v_b_2387_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2387_);
v___y_2371_ = v_b_2387_;
goto v___jp_2370_;
}
case 13:
{
lean_object* v_b_2388_; 
v_b_2388_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2388_);
v___y_2371_ = v_b_2388_;
goto v___jp_2370_;
}
case 14:
{
lean_object* v_b_2389_; 
v_b_2389_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2389_);
v___y_2371_ = v_b_2389_;
goto v___jp_2370_;
}
case 15:
{
lean_object* v_b_2390_; 
v_b_2390_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2390_);
v___y_2371_ = v_b_2390_;
goto v___jp_2370_;
}
case 16:
{
lean_object* v_b_2391_; 
v_b_2391_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2391_);
v___y_2371_ = v_b_2391_;
goto v___jp_2370_;
}
case 17:
{
lean_object* v_b_2392_; 
v_b_2392_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2392_);
v___y_2371_ = v_b_2392_;
goto v___jp_2370_;
}
case 18:
{
lean_object* v_b_2393_; 
v_b_2393_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2393_);
v___y_2371_ = v_b_2393_;
goto v___jp_2370_;
}
case 19:
{
lean_object* v_b_2394_; 
v_b_2394_ = lean_ctor_get(v_b_2368_, 3);
lean_inc(v_b_2394_);
v___y_2371_ = v_b_2394_;
goto v___jp_2370_;
}
case 20:
{
lean_object* v_b_2395_; 
v_b_2395_ = lean_ctor_get(v_b_2368_, 3);
lean_inc(v_b_2395_);
v___y_2371_ = v_b_2395_;
goto v___jp_2370_;
}
case 22:
{
lean_object* v_b_2396_; 
v_b_2396_ = lean_ctor_get(v_b_2368_, 3);
lean_inc(v_b_2396_);
v___y_2371_ = v_b_2396_;
goto v___jp_2370_;
}
case 23:
{
lean_object* v_b_2397_; 
v_b_2397_ = lean_ctor_get(v_b_2368_, 5);
lean_inc(v_b_2397_);
v___y_2371_ = v_b_2397_;
goto v___jp_2370_;
}
case 21:
{
lean_object* v_b_2398_; 
v_b_2398_ = lean_ctor_get(v_b_2368_, 2);
lean_inc(v_b_2398_);
v___y_2371_ = v_b_2398_;
goto v___jp_2370_;
}
case 24:
{
lean_object* v_b_2399_; 
v_b_2399_ = lean_ctor_get(v_b_2368_, 2);
lean_inc(v_b_2399_);
v___y_2371_ = v_b_2399_;
goto v___jp_2370_;
}
case 25:
{
lean_object* v_b_2400_; 
v_b_2400_ = lean_ctor_get(v_b_2368_, 2);
lean_inc(v_b_2400_);
v___y_2371_ = v_b_2400_;
goto v___jp_2370_;
}
case 26:
{
lean_object* v_b_2401_; 
v_b_2401_ = lean_ctor_get(v_b_2368_, 1);
lean_inc(v_b_2401_);
v___y_2371_ = v_b_2401_;
goto v___jp_2370_;
}
default: 
{
lean_inc(v_b_2368_);
v___y_2371_ = v_b_2368_;
goto v___jp_2370_;
}
}
}
else
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_r_2369_);
lean_ctor_set(v___x_2402_, 1, v_b_2368_);
return v___x_2402_;
}
v___jp_2370_:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_IR_push(v_r_2369_, v_b_2368_);
v_b_2368_ = v___y_2371_;
v_r_2369_ = v___x_2372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object* v_b_2405_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_IR_FnBody_flatten___closed__0));
v___x_2407_ = l_Lean_IR_flattenAux(v_b_2405_, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0(lean_object* v___x_2408_, lean_object* v_msg_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_panic_fn_borrowed(v___x_2408_, v_msg_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(lean_object* v___x_2411_, lean_object* v_msg_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_2411_, v_msg_2412_);
lean_dec_ref(v___x_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object* v_a_2418_, lean_object* v_i_2419_, lean_object* v_b_2420_){
_start:
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_nat_dec_eq(v_i_2419_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v_i_2424_; lean_object* v_fst_2426_; lean_object* v_snd_2427_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2423_ = lean_unsigned_to_nat(1u);
v_i_2424_ = lean_nat_sub(v_i_2419_, v___x_2423_);
lean_dec(v_i_2419_);
v___x_2430_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_2431_ = lean_array_get_size(v_a_2418_);
v___x_2432_ = lean_nat_dec_lt(v_i_2424_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_fst_2445_; lean_object* v_snd_2446_; 
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2430_);
lean_ctor_set(v___x_2433_, 1, v_a_2418_);
v___x_2434_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__0));
v___x_2435_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__1));
v___x_2436_ = lean_unsigned_to_nat(463u);
v___x_2437_ = lean_unsigned_to_nat(4u);
v___x_2438_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__2));
lean_inc(v_i_2424_);
v___x_2439_ = l_Nat_reprFast(v_i_2424_);
v___x_2440_ = lean_string_append(v___x_2438_, v___x_2439_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__3));
v___x_2442_ = lean_string_append(v___x_2440_, v___x_2441_);
v___x_2443_ = l_mkPanicMessageWithDecl(v___x_2434_, v___x_2435_, v___x_2436_, v___x_2437_, v___x_2442_);
lean_dec_ref(v___x_2442_);
v___x_2444_ = lean_panic_fn_borrowed(v___x_2433_, v___x_2443_);
lean_dec_ref_known(v___x_2433_, 2);
v_fst_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_fst_2445_);
v_snd_2446_ = lean_ctor_get(v___x_2444_, 1);
lean_inc(v_snd_2446_);
lean_dec(v___x_2444_);
v_fst_2426_ = v_fst_2445_;
v_snd_2427_ = v_snd_2446_;
goto v___jp_2425_;
}
else
{
lean_object* v_e_2447_; lean_object* v_xs_x27_2448_; 
v_e_2447_ = lean_array_fget(v_a_2418_, v_i_2424_);
v_xs_x27_2448_ = lean_array_fset(v_a_2418_, v_i_2424_, v___x_2430_);
v_fst_2426_ = v_e_2447_;
v_snd_2427_ = v_xs_x27_2448_;
goto v___jp_2425_;
}
v___jp_2425_:
{
lean_object* v_b_2428_; 
v_b_2428_ = l_Lean_IR_FnBody_setBody(v_fst_2426_, v_b_2420_);
v_a_2418_ = v_snd_2427_;
v_i_2419_ = v_i_2424_;
v_b_2420_ = v_b_2428_;
goto _start;
}
}
else
{
lean_dec(v_i_2419_);
lean_dec_ref(v_a_2418_);
return v_b_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object* v_bs_2449_, lean_object* v_term_2450_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_array_get_size(v_bs_2449_);
v___x_2452_ = l_Lean_IR_reshapeAux(v_bs_2449_, v___x_2451_, v_term_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object* v_f_2453_, lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2454_) == 19)
{
lean_object* v_j_2455_; lean_object* v_xs_2456_; lean_object* v_v_2457_; lean_object* v_b_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_j_2455_ = lean_ctor_get(v_x_2454_, 0);
v_xs_2456_ = lean_ctor_get(v_x_2454_, 1);
v_v_2457_ = lean_ctor_get(v_x_2454_, 2);
v_b_2458_ = lean_ctor_get(v_x_2454_, 3);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2454_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2460_ = v_x_2454_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_b_2458_);
lean_inc(v_v_2457_);
lean_inc(v_xs_2456_);
lean_inc(v_j_2455_);
lean_dec(v_x_2454_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_apply_1(v_f_2453_, v_v_2457_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 2, v___x_2462_);
v___x_2464_ = v___x_2460_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_j_2455_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_xs_2456_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_b_2458_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_dec_ref(v_f_2453_);
return v_x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* v_bs_2486_, lean_object* v_f_2487_){
_start:
{
lean_object* v___f_2488_; lean_object* v___x_2489_; size_t v_sz_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPs___lam__0), 2, 1);
lean_closure_set(v___f_2488_, 0, v_f_2487_);
v___x_2489_ = ((lean_object*)(l_Lean_IR_modifyJPs___closed__9));
v_sz_2490_ = lean_array_size(v_bs_2486_);
v___x_2491_ = ((size_t)0ULL);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2489_, v___f_2488_, v_sz_2490_, v___x_2491_, v_bs_2486_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__0(lean_object* v_j_2493_, lean_object* v_xs_2494_, lean_object* v_b_2495_, lean_object* v_toPure_2496_, lean_object* v_____do__lift_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v___x_2498_, 0, v_j_2493_);
lean_ctor_set(v___x_2498_, 1, v_xs_2494_);
lean_ctor_set(v___x_2498_, 2, v_____do__lift_2497_);
lean_ctor_set(v___x_2498_, 3, v_b_2495_);
v___x_2499_ = lean_apply_2(v_toPure_2496_, lean_box(0), v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__1(lean_object* v_toPure_2500_, lean_object* v_f_2501_, lean_object* v_toBind_2502_, lean_object* v_b_2503_){
_start:
{
if (lean_obj_tag(v_b_2503_) == 19)
{
lean_object* v_j_2504_; lean_object* v_xs_2505_; lean_object* v_v_2506_; lean_object* v_b_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_j_2504_ = lean_ctor_get(v_b_2503_, 0);
lean_inc(v_j_2504_);
v_xs_2505_ = lean_ctor_get(v_b_2503_, 1);
lean_inc_ref(v_xs_2505_);
v_v_2506_ = lean_ctor_get(v_b_2503_, 2);
lean_inc(v_v_2506_);
v_b_2507_ = lean_ctor_get(v_b_2503_, 3);
lean_inc(v_b_2507_);
lean_dec_ref_known(v_b_2503_, 4);
v___f_2508_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2508_, 0, v_j_2504_);
lean_closure_set(v___f_2508_, 1, v_xs_2505_);
lean_closure_set(v___f_2508_, 2, v_b_2507_);
lean_closure_set(v___f_2508_, 3, v_toPure_2500_);
v___x_2509_ = lean_apply_1(v_f_2501_, v_v_2506_);
v___x_2510_ = lean_apply_4(v_toBind_2502_, lean_box(0), lean_box(0), v___x_2509_, v___f_2508_);
return v___x_2510_;
}
else
{
lean_object* v___x_2511_; 
lean_dec(v_toBind_2502_);
lean_dec(v_f_2501_);
v___x_2511_ = lean_apply_2(v_toPure_2500_, lean_box(0), v_b_2503_);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg(lean_object* v_inst_2512_, lean_object* v_bs_2513_, lean_object* v_f_2514_){
_start:
{
lean_object* v_toApplicative_2515_; lean_object* v_toBind_2516_; lean_object* v_toPure_2517_; lean_object* v___f_2518_; size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v_toApplicative_2515_ = lean_ctor_get(v_inst_2512_, 0);
v_toBind_2516_ = lean_ctor_get(v_inst_2512_, 1);
v_toPure_2517_ = lean_ctor_get(v_toApplicative_2515_, 1);
lean_inc(v_toBind_2516_);
lean_inc(v_toPure_2517_);
v___f_2518_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2518_, 0, v_toPure_2517_);
lean_closure_set(v___f_2518_, 1, v_f_2514_);
lean_closure_set(v___f_2518_, 2, v_toBind_2516_);
v_sz_2519_ = lean_array_size(v_bs_2513_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2512_, v___f_2518_, v_sz_2519_, v___x_2520_, v_bs_2513_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM(lean_object* v_m_2522_, lean_object* v_inst_2523_, lean_object* v_bs_2524_, lean_object* v_f_2525_){
_start:
{
lean_object* v_toApplicative_2526_; lean_object* v_toBind_2527_; lean_object* v_toPure_2528_; lean_object* v___f_2529_; size_t v_sz_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v_toApplicative_2526_ = lean_ctor_get(v_inst_2523_, 0);
v_toBind_2527_ = lean_ctor_get(v_inst_2523_, 1);
v_toPure_2528_ = lean_ctor_get(v_toApplicative_2526_, 1);
lean_inc(v_toBind_2527_);
lean_inc(v_toPure_2528_);
v___f_2529_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2529_, 0, v_toPure_2528_);
lean_closure_set(v___f_2529_, 1, v_f_2525_);
lean_closure_set(v___f_2529_, 2, v_toBind_2527_);
v_sz_2530_ = lean_array_size(v_bs_2524_);
v___x_2531_ = ((size_t)0ULL);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2523_, v___f_2529_, v_sz_2530_, v___x_2531_, v_bs_2524_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl(lean_object* v_x_2533_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_obj_tag_nat(v_x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl___boxed(lean_object* v_x_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_IR_Decl_ctorIdx___impl(v_x_2535_);
lean_dec_ref(v_x_2535_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___redArg(lean_object* v_t_2537_, lean_object* v_k_2538_){
_start:
{
if (lean_obj_tag(v_t_2537_) == 0)
{
lean_object* v_f_2539_; lean_object* v_xs_2540_; lean_object* v_type_2541_; lean_object* v_body_2542_; lean_object* v_info_2543_; lean_object* v___x_2544_; 
v_f_2539_ = lean_ctor_get(v_t_2537_, 0);
lean_inc(v_f_2539_);
v_xs_2540_ = lean_ctor_get(v_t_2537_, 1);
lean_inc_ref(v_xs_2540_);
v_type_2541_ = lean_ctor_get(v_t_2537_, 2);
lean_inc(v_type_2541_);
v_body_2542_ = lean_ctor_get(v_t_2537_, 3);
lean_inc(v_body_2542_);
v_info_2543_ = lean_ctor_get(v_t_2537_, 4);
lean_inc_ref(v_info_2543_);
lean_dec_ref_known(v_t_2537_, 5);
v___x_2544_ = lean_apply_5(v_k_2538_, v_f_2539_, v_xs_2540_, v_type_2541_, v_body_2542_, v_info_2543_);
return v___x_2544_;
}
else
{
lean_object* v_f_2545_; lean_object* v_xs_2546_; lean_object* v_type_2547_; lean_object* v_ext_2548_; lean_object* v___x_2549_; 
v_f_2545_ = lean_ctor_get(v_t_2537_, 0);
lean_inc(v_f_2545_);
v_xs_2546_ = lean_ctor_get(v_t_2537_, 1);
lean_inc_ref(v_xs_2546_);
v_type_2547_ = lean_ctor_get(v_t_2537_, 2);
lean_inc(v_type_2547_);
v_ext_2548_ = lean_ctor_get(v_t_2537_, 3);
lean_inc(v_ext_2548_);
lean_dec_ref_known(v_t_2537_, 4);
v___x_2549_ = lean_apply_4(v_k_2538_, v_f_2545_, v_xs_2546_, v_type_2547_, v_ext_2548_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim(lean_object* v_motive_2550_, lean_object* v_ctorIdx_2551_, lean_object* v_t_2552_, lean_object* v_h_2553_, lean_object* v_k_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2552_, v_k_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___boxed(lean_object* v_motive_2556_, lean_object* v_ctorIdx_2557_, lean_object* v_t_2558_, lean_object* v_h_2559_, lean_object* v_k_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_IR_Decl_ctorElim(v_motive_2556_, v_ctorIdx_2557_, v_t_2558_, v_h_2559_, v_k_2560_);
lean_dec(v_ctorIdx_2557_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim___redArg(lean_object* v_t_2562_, lean_object* v_fdecl_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2562_, v_fdecl_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim(lean_object* v_motive_2565_, lean_object* v_t_2566_, lean_object* v_h_2567_, lean_object* v_fdecl_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2566_, v_fdecl_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim___redArg(lean_object* v_t_2570_, lean_object* v_extern_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2570_, v_extern_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim(lean_object* v_motive_2573_, lean_object* v_t_2574_, lean_object* v_h_2575_, lean_object* v_extern_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2574_, v_extern_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object* v_x_2587_){
_start:
{
lean_object* v_f_2588_; 
v_f_2588_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_f_2588_);
return v_f_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object* v_x_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_IR_Decl_name(v_x_2589_);
lean_dec_ref(v_x_2589_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object* v_x_2591_){
_start:
{
lean_object* v_xs_2592_; 
v_xs_2592_ = lean_ctor_get(v_x_2591_, 1);
lean_inc_ref(v_xs_2592_);
return v_xs_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object* v_x_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_IR_Decl_params(v_x_2593_);
lean_dec_ref(v_x_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object* v_x_2595_){
_start:
{
lean_object* v_type_2596_; 
v_type_2596_ = lean_ctor_get(v_x_2595_, 2);
lean_inc(v_type_2596_);
return v_type_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* v_x_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_IR_Decl_resultType(v_x_2597_);
lean_dec_ref(v_x_2597_);
return v_res_2598_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object* v_x_2599_){
_start:
{
if (lean_obj_tag(v_x_2599_) == 1)
{
uint8_t v___x_2600_; 
v___x_2600_ = 1;
return v___x_2600_;
}
else
{
uint8_t v___x_2601_; 
v___x_2601_ = 0;
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* v_x_2602_){
_start:
{
uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_res_2603_ = l_Lean_IR_Decl_isExtern(v_x_2602_);
lean_dec_ref(v_x_2602_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* v_x_2608_){
_start:
{
if (lean_obj_tag(v_x_2608_) == 0)
{
lean_object* v_info_2609_; 
v_info_2609_ = lean_ctor_get(v_x_2608_, 4);
lean_inc_ref(v_info_2609_);
return v_info_2609_;
}
else
{
lean_object* v___x_2610_; 
v___x_2610_ = ((lean_object*)(l_Lean_IR_Decl_getInfo___closed__0));
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* v_x_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_IR_Decl_getInfo(v_x_2611_);
lean_dec_ref(v_x_2611_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object* v_msg_2613_){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_Lean_IR_instInhabitedDecl_default));
v___x_2615_ = lean_panic_fn_borrowed(v___x_2614_, v_msg_2613_);
return v___x_2615_;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__2(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2618_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__1));
v___x_2619_ = lean_unsigned_to_nat(9u);
v___x_2620_ = lean_unsigned_to_nat(515u);
v___x_2621_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__0));
v___x_2622_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__0));
v___x_2623_ = l_mkPanicMessageWithDecl(v___x_2622_, v___x_2621_, v___x_2620_, v___x_2619_, v___x_2618_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* v_d_2624_, lean_object* v_bNew_2625_){
_start:
{
if (lean_obj_tag(v_d_2624_) == 0)
{
lean_object* v_f_2626_; lean_object* v_xs_2627_; lean_object* v_type_2628_; lean_object* v_info_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
v_f_2626_ = lean_ctor_get(v_d_2624_, 0);
v_xs_2627_ = lean_ctor_get(v_d_2624_, 1);
v_type_2628_ = lean_ctor_get(v_d_2624_, 2);
v_info_2629_ = lean_ctor_get(v_d_2624_, 4);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_d_2624_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_d_2624_, 3);
lean_dec(v_unused_2637_);
v___x_2631_ = v_d_2624_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_info_2629_);
lean_inc(v_type_2628_);
lean_inc(v_xs_2627_);
lean_inc(v_f_2626_);
lean_dec(v_d_2624_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 3, v_bNew_2625_);
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_f_2626_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_xs_2627_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_type_2628_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v_bNew_2625_);
lean_ctor_set(v_reuseFailAlloc_2635_, 4, v_info_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec(v_bNew_2625_);
lean_dec_ref(v_d_2624_);
v___x_2638_ = lean_obj_once(&l_Lean_IR_Decl_updateBody_x21___closed__2, &l_Lean_IR_Decl_updateBody_x21___closed__2_once, _init_l_Lean_IR_Decl_updateBody_x21___closed__2);
v___x_2639_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_2638_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object* v_f_2640_, lean_object* v_xs_2641_, lean_object* v_ty_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_box(30);
v___x_2644_ = ((lean_object*)(l_Lean_IR_Decl_getInfo___closed__0));
v___x_2645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2645_, 0, v_f_2640_);
lean_ctor_set(v___x_2645_, 1, v_xs_2641_);
lean_ctor_set(v___x_2645_, 2, v_ty_2642_);
lean_ctor_set(v___x_2645_, 3, v___x_2643_);
lean_ctor_set(v___x_2645_, 4, v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object* v_k_2646_, lean_object* v_v_2647_, lean_object* v_t_2648_){
_start:
{
if (lean_obj_tag(v_t_2648_) == 0)
{
lean_object* v_size_2649_; lean_object* v_k_2650_; lean_object* v_v_2651_; lean_object* v_l_2652_; lean_object* v_r_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2934_; 
v_size_2649_ = lean_ctor_get(v_t_2648_, 0);
v_k_2650_ = lean_ctor_get(v_t_2648_, 1);
v_v_2651_ = lean_ctor_get(v_t_2648_, 2);
v_l_2652_ = lean_ctor_get(v_t_2648_, 3);
v_r_2653_ = lean_ctor_get(v_t_2648_, 4);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_t_2648_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2655_ = v_t_2648_;
v_isShared_2656_ = v_isSharedCheck_2934_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_r_2653_);
lean_inc(v_l_2652_);
lean_inc(v_v_2651_);
lean_inc(v_k_2650_);
lean_inc(v_size_2649_);
lean_dec(v_t_2648_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2934_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_lt(v_k_2646_, v_k_2650_);
if (v___x_2657_ == 0)
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_nat_dec_eq(v_k_2646_, v_k_2650_);
if (v___x_2658_ == 0)
{
lean_object* v_impl_2659_; lean_object* v___x_2660_; 
lean_dec(v_size_2649_);
v_impl_2659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2646_, v_v_2647_, v_r_2653_);
v___x_2660_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2652_) == 0)
{
lean_object* v_size_2661_; lean_object* v_size_2662_; lean_object* v_k_2663_; lean_object* v_v_2664_; lean_object* v_l_2665_; lean_object* v_r_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_size_2661_ = lean_ctor_get(v_l_2652_, 0);
v_size_2662_ = lean_ctor_get(v_impl_2659_, 0);
v_k_2663_ = lean_ctor_get(v_impl_2659_, 1);
v_v_2664_ = lean_ctor_get(v_impl_2659_, 2);
v_l_2665_ = lean_ctor_get(v_impl_2659_, 3);
lean_inc(v_l_2665_);
v_r_2666_ = lean_ctor_get(v_impl_2659_, 4);
v___x_2667_ = lean_unsigned_to_nat(3u);
v___x_2668_ = lean_nat_mul(v___x_2667_, v_size_2661_);
v___x_2669_ = lean_nat_dec_lt(v___x_2668_, v_size_2662_);
lean_dec(v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_dec(v_l_2665_);
v___x_2670_ = lean_nat_add(v___x_2660_, v_size_2661_);
v___x_2671_ = lean_nat_add(v___x_2670_, v_size_2662_);
lean_dec(v___x_2670_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_impl_2659_);
lean_ctor_set(v___x_2655_, 0, v___x_2671_);
v___x_2673_ = v___x_2655_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_l_2652_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v_impl_2659_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
else
{
lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2738_; 
lean_inc(v_r_2666_);
lean_inc(v_v_2664_);
lean_inc(v_k_2663_);
lean_inc(v_size_2662_);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_impl_2659_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; lean_object* v_unused_2743_; 
v_unused_2739_ = lean_ctor_get(v_impl_2659_, 4);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_impl_2659_, 3);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_impl_2659_, 2);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_impl_2659_, 1);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_impl_2659_, 0);
lean_dec(v_unused_2743_);
v___x_2676_ = v_impl_2659_;
v_isShared_2677_ = v_isSharedCheck_2738_;
goto v_resetjp_2675_;
}
else
{
lean_dec(v_impl_2659_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2738_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_size_2678_; lean_object* v_k_2679_; lean_object* v_v_2680_; lean_object* v_l_2681_; lean_object* v_r_2682_; lean_object* v_size_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_size_2678_ = lean_ctor_get(v_l_2665_, 0);
v_k_2679_ = lean_ctor_get(v_l_2665_, 1);
v_v_2680_ = lean_ctor_get(v_l_2665_, 2);
v_l_2681_ = lean_ctor_get(v_l_2665_, 3);
v_r_2682_ = lean_ctor_get(v_l_2665_, 4);
v_size_2683_ = lean_ctor_get(v_r_2666_, 0);
v___x_2684_ = lean_unsigned_to_nat(2u);
v___x_2685_ = lean_nat_mul(v___x_2684_, v_size_2683_);
v___x_2686_ = lean_nat_dec_lt(v_size_2678_, v___x_2685_);
lean_dec(v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2714_; 
lean_inc(v_r_2682_);
lean_inc(v_l_2681_);
lean_inc(v_v_2680_);
lean_inc(v_k_2679_);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_l_2665_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2715_ = lean_ctor_get(v_l_2665_, 4);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_l_2665_, 3);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_l_2665_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_l_2665_, 1);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_l_2665_, 0);
lean_dec(v_unused_2719_);
v___x_2688_ = v_l_2665_;
v_isShared_2689_ = v_isSharedCheck_2714_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_l_2665_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2714_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2704_; 
v___x_2690_ = lean_nat_add(v___x_2660_, v_size_2661_);
v___x_2691_ = lean_nat_add(v___x_2690_, v_size_2662_);
lean_dec(v_size_2662_);
if (lean_obj_tag(v_l_2681_) == 0)
{
lean_object* v_size_2712_; 
v_size_2712_ = lean_ctor_get(v_l_2681_, 0);
lean_inc(v_size_2712_);
v___y_2704_ = v_size_2712_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_unsigned_to_nat(0u);
v___y_2704_ = v___x_2713_;
goto v___jp_2703_;
}
v___jp_2692_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_nat_add(v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec(v___y_2694_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 4, v_r_2666_);
lean_ctor_set(v___x_2688_, 3, v_r_2682_);
lean_ctor_set(v___x_2688_, 2, v_v_2664_);
lean_ctor_set(v___x_2688_, 1, v_k_2663_);
lean_ctor_set(v___x_2688_, 0, v___x_2696_);
v___x_2698_ = v___x_2688_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_k_2663_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_v_2664_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_r_2682_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_r_2666_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 4, v___x_2698_);
lean_ctor_set(v___x_2676_, 3, v___y_2693_);
lean_ctor_set(v___x_2676_, 2, v_v_2680_);
lean_ctor_set(v___x_2676_, 1, v_k_2679_);
lean_ctor_set(v___x_2676_, 0, v___x_2691_);
v___x_2700_ = v___x_2676_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_k_2679_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_v_2680_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v___y_2693_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
v___jp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = lean_nat_add(v___x_2690_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec(v___x_2690_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_l_2681_);
lean_ctor_set(v___x_2655_, 0, v___x_2705_);
v___x_2707_ = v___x_2655_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_l_2652_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_l_2681_);
v___x_2707_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_nat_add(v___x_2660_, v_size_2683_);
if (lean_obj_tag(v_r_2682_) == 0)
{
lean_object* v_size_2709_; 
v_size_2709_ = lean_ctor_get(v_r_2682_, 0);
lean_inc(v_size_2709_);
v___y_2693_ = v___x_2707_;
v___y_2694_ = v___x_2708_;
v___y_2695_ = v_size_2709_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_unsigned_to_nat(0u);
v___y_2693_ = v___x_2707_;
v___y_2694_ = v___x_2708_;
v___y_2695_ = v___x_2710_;
goto v___jp_2692_;
}
}
}
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_del_object(v___x_2655_);
v___x_2720_ = lean_nat_add(v___x_2660_, v_size_2661_);
v___x_2721_ = lean_nat_add(v___x_2720_, v_size_2662_);
lean_dec(v_size_2662_);
v___x_2722_ = lean_nat_add(v___x_2720_, v_size_2678_);
lean_dec(v___x_2720_);
lean_inc_ref(v_l_2652_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 4, v_l_2665_);
lean_ctor_set(v___x_2676_, 3, v_l_2652_);
lean_ctor_set(v___x_2676_, 2, v_v_2651_);
lean_ctor_set(v___x_2676_, 1, v_k_2650_);
lean_ctor_set(v___x_2676_, 0, v___x_2722_);
v___x_2724_ = v___x_2676_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2737_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2737_, 3, v_l_2652_);
lean_ctor_set(v_reuseFailAlloc_2737_, 4, v_l_2665_);
v___x_2724_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_isSharedCheck_2731_ = !lean_is_exclusive(v_l_2652_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2732_ = lean_ctor_get(v_l_2652_, 4);
lean_dec(v_unused_2732_);
v_unused_2733_ = lean_ctor_get(v_l_2652_, 3);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_l_2652_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_l_2652_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_l_2652_, 0);
lean_dec(v_unused_2736_);
v___x_2726_ = v_l_2652_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v_l_2652_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 4, v_r_2666_);
lean_ctor_set(v___x_2726_, 3, v___x_2724_);
lean_ctor_set(v___x_2726_, 2, v_v_2664_);
lean_ctor_set(v___x_2726_, 1, v_k_2663_);
lean_ctor_set(v___x_2726_, 0, v___x_2721_);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_k_2663_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_v_2664_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_r_2666_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2744_; 
v_l_2744_ = lean_ctor_get(v_impl_2659_, 3);
lean_inc(v_l_2744_);
if (lean_obj_tag(v_l_2744_) == 0)
{
lean_object* v_r_2745_; lean_object* v_k_2746_; lean_object* v_v_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2770_; 
v_r_2745_ = lean_ctor_get(v_impl_2659_, 4);
v_k_2746_ = lean_ctor_get(v_impl_2659_, 1);
v_v_2747_ = lean_ctor_get(v_impl_2659_, 2);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_impl_2659_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; lean_object* v_unused_2772_; 
v_unused_2771_ = lean_ctor_get(v_impl_2659_, 3);
lean_dec(v_unused_2771_);
v_unused_2772_ = lean_ctor_get(v_impl_2659_, 0);
lean_dec(v_unused_2772_);
v___x_2749_ = v_impl_2659_;
v_isShared_2750_ = v_isSharedCheck_2770_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_r_2745_);
lean_inc(v_v_2747_);
lean_inc(v_k_2746_);
lean_dec(v_impl_2659_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2770_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_k_2751_; lean_object* v_v_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2766_; 
v_k_2751_ = lean_ctor_get(v_l_2744_, 1);
v_v_2752_ = lean_ctor_get(v_l_2744_, 2);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; lean_object* v_unused_2768_; lean_object* v_unused_2769_; 
v_unused_2767_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2767_);
v_unused_2768_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2768_);
v_unused_2769_ = lean_ctor_get(v_l_2744_, 0);
lean_dec(v_unused_2769_);
v___x_2754_ = v_l_2744_;
v_isShared_2755_ = v_isSharedCheck_2766_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_v_2752_);
lean_inc(v_k_2751_);
lean_dec(v_l_2744_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2766_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2745_, 2);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 4, v_r_2745_);
lean_ctor_set(v___x_2754_, 3, v_r_2745_);
lean_ctor_set(v___x_2754_, 2, v_v_2651_);
lean_ctor_set(v___x_2754_, 1, v_k_2650_);
lean_ctor_set(v___x_2754_, 0, v___x_2660_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_r_2745_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v_r_2745_);
v___x_2758_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2760_; 
lean_inc(v_r_2745_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 3, v_r_2745_);
lean_ctor_set(v___x_2749_, 0, v___x_2660_);
v___x_2760_ = v___x_2749_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2764_, 3, v_r_2745_);
lean_ctor_set(v_reuseFailAlloc_2764_, 4, v_r_2745_);
v___x_2760_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v___x_2760_);
lean_ctor_set(v___x_2655_, 3, v___x_2758_);
lean_ctor_set(v___x_2655_, 2, v_v_2752_);
lean_ctor_set(v___x_2655_, 1, v_k_2751_);
lean_ctor_set(v___x_2655_, 0, v___x_2756_);
v___x_2762_ = v___x_2655_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_k_2751_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_v_2752_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
}
else
{
lean_object* v_r_2773_; 
v_r_2773_ = lean_ctor_get(v_impl_2659_, 4);
lean_inc(v_r_2773_);
if (lean_obj_tag(v_r_2773_) == 0)
{
lean_object* v_k_2774_; lean_object* v_v_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2786_; 
v_k_2774_ = lean_ctor_get(v_impl_2659_, 1);
v_v_2775_ = lean_ctor_get(v_impl_2659_, 2);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_impl_2659_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; lean_object* v_unused_2788_; lean_object* v_unused_2789_; 
v_unused_2787_ = lean_ctor_get(v_impl_2659_, 4);
lean_dec(v_unused_2787_);
v_unused_2788_ = lean_ctor_get(v_impl_2659_, 3);
lean_dec(v_unused_2788_);
v_unused_2789_ = lean_ctor_get(v_impl_2659_, 0);
lean_dec(v_unused_2789_);
v___x_2777_ = v_impl_2659_;
v_isShared_2778_ = v_isSharedCheck_2786_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_v_2775_);
lean_inc(v_k_2774_);
lean_dec(v_impl_2659_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2786_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_unsigned_to_nat(3u);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 4, v_l_2744_);
lean_ctor_set(v___x_2777_, 2, v_v_2651_);
lean_ctor_set(v___x_2777_, 1, v_k_2650_);
lean_ctor_set(v___x_2777_, 0, v___x_2660_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_l_2744_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_l_2744_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_r_2773_);
lean_ctor_set(v___x_2655_, 3, v___x_2781_);
lean_ctor_set(v___x_2655_, 2, v_v_2775_);
lean_ctor_set(v___x_2655_, 1, v_k_2774_);
lean_ctor_set(v___x_2655_, 0, v___x_2779_);
v___x_2783_ = v___x_2655_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_k_2774_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v_v_2775_);
lean_ctor_set(v_reuseFailAlloc_2784_, 3, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2784_, 4, v_r_2773_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = lean_unsigned_to_nat(2u);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_impl_2659_);
lean_ctor_set(v___x_2655_, 3, v_r_2773_);
lean_ctor_set(v___x_2655_, 0, v___x_2790_);
v___x_2792_ = v___x_2655_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2793_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2793_, 3, v_r_2773_);
lean_ctor_set(v_reuseFailAlloc_2793_, 4, v_impl_2659_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
else
{
lean_object* v___x_2795_; 
lean_dec(v_v_2651_);
lean_dec(v_k_2650_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 2, v_v_2647_);
lean_ctor_set(v___x_2655_, 1, v_k_2646_);
v___x_2795_ = v___x_2655_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_size_2649_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_k_2646_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_v_2647_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_l_2652_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_r_2653_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_object* v_impl_2797_; lean_object* v___x_2798_; 
lean_dec(v_size_2649_);
v_impl_2797_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2646_, v_v_2647_, v_l_2652_);
v___x_2798_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2653_) == 0)
{
lean_object* v_size_2799_; lean_object* v_size_2800_; lean_object* v_k_2801_; lean_object* v_v_2802_; lean_object* v_l_2803_; lean_object* v_r_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v_size_2799_ = lean_ctor_get(v_r_2653_, 0);
v_size_2800_ = lean_ctor_get(v_impl_2797_, 0);
v_k_2801_ = lean_ctor_get(v_impl_2797_, 1);
v_v_2802_ = lean_ctor_get(v_impl_2797_, 2);
v_l_2803_ = lean_ctor_get(v_impl_2797_, 3);
v_r_2804_ = lean_ctor_get(v_impl_2797_, 4);
lean_inc(v_r_2804_);
v___x_2805_ = lean_unsigned_to_nat(3u);
v___x_2806_ = lean_nat_mul(v___x_2805_, v_size_2799_);
v___x_2807_ = lean_nat_dec_lt(v___x_2806_, v_size_2800_);
lean_dec(v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
lean_dec(v_r_2804_);
v___x_2808_ = lean_nat_add(v___x_2798_, v_size_2800_);
v___x_2809_ = lean_nat_add(v___x_2808_, v_size_2799_);
lean_dec(v___x_2808_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 3, v_impl_2797_);
lean_ctor_set(v___x_2655_, 0, v___x_2809_);
v___x_2811_ = v___x_2655_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_impl_2797_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_r_2653_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2878_; 
lean_inc(v_l_2803_);
lean_inc(v_v_2802_);
lean_inc(v_k_2801_);
lean_inc(v_size_2800_);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_impl_2797_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; lean_object* v_unused_2880_; lean_object* v_unused_2881_; lean_object* v_unused_2882_; lean_object* v_unused_2883_; 
v_unused_2879_ = lean_ctor_get(v_impl_2797_, 4);
lean_dec(v_unused_2879_);
v_unused_2880_ = lean_ctor_get(v_impl_2797_, 3);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_impl_2797_, 2);
lean_dec(v_unused_2881_);
v_unused_2882_ = lean_ctor_get(v_impl_2797_, 1);
lean_dec(v_unused_2882_);
v_unused_2883_ = lean_ctor_get(v_impl_2797_, 0);
lean_dec(v_unused_2883_);
v___x_2814_ = v_impl_2797_;
v_isShared_2815_ = v_isSharedCheck_2878_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v_impl_2797_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2878_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_size_2816_; lean_object* v_size_2817_; lean_object* v_k_2818_; lean_object* v_v_2819_; lean_object* v_l_2820_; lean_object* v_r_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_size_2816_ = lean_ctor_get(v_l_2803_, 0);
v_size_2817_ = lean_ctor_get(v_r_2804_, 0);
v_k_2818_ = lean_ctor_get(v_r_2804_, 1);
v_v_2819_ = lean_ctor_get(v_r_2804_, 2);
v_l_2820_ = lean_ctor_get(v_r_2804_, 3);
v_r_2821_ = lean_ctor_get(v_r_2804_, 4);
v___x_2822_ = lean_unsigned_to_nat(2u);
v___x_2823_ = lean_nat_mul(v___x_2822_, v_size_2816_);
v___x_2824_ = lean_nat_dec_lt(v_size_2817_, v___x_2823_);
lean_dec(v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2853_; 
lean_inc(v_r_2821_);
lean_inc(v_l_2820_);
lean_inc(v_v_2819_);
lean_inc(v_k_2818_);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_r_2804_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; lean_object* v_unused_2855_; lean_object* v_unused_2856_; lean_object* v_unused_2857_; lean_object* v_unused_2858_; 
v_unused_2854_ = lean_ctor_get(v_r_2804_, 4);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v_r_2804_, 3);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_r_2804_, 2);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_r_2804_, 1);
lean_dec(v_unused_2857_);
v_unused_2858_ = lean_ctor_get(v_r_2804_, 0);
lean_dec(v_unused_2858_);
v___x_2826_ = v_r_2804_;
v_isShared_2827_ = v_isSharedCheck_2853_;
goto v_resetjp_2825_;
}
else
{
lean_dec(v_r_2804_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2853_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___x_2841_; lean_object* v___y_2843_; 
v___x_2828_ = lean_nat_add(v___x_2798_, v_size_2800_);
lean_dec(v_size_2800_);
v___x_2829_ = lean_nat_add(v___x_2828_, v_size_2799_);
lean_dec(v___x_2828_);
v___x_2841_ = lean_nat_add(v___x_2798_, v_size_2816_);
if (lean_obj_tag(v_l_2820_) == 0)
{
lean_object* v_size_2851_; 
v_size_2851_ = lean_ctor_get(v_l_2820_, 0);
lean_inc(v_size_2851_);
v___y_2843_ = v_size_2851_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_unsigned_to_nat(0u);
v___y_2843_ = v___x_2852_;
goto v___jp_2842_;
}
v___jp_2830_:
{
lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2834_ = lean_nat_add(v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec(v___y_2832_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 4, v_r_2653_);
lean_ctor_set(v___x_2826_, 3, v_r_2821_);
lean_ctor_set(v___x_2826_, 2, v_v_2651_);
lean_ctor_set(v___x_2826_, 1, v_k_2650_);
lean_ctor_set(v___x_2826_, 0, v___x_2834_);
v___x_2836_ = v___x_2826_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_r_2821_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_r_2653_);
v___x_2836_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2838_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v___x_2836_);
lean_ctor_set(v___x_2814_, 3, v___y_2831_);
lean_ctor_set(v___x_2814_, 2, v_v_2819_);
lean_ctor_set(v___x_2814_, 1, v_k_2818_);
lean_ctor_set(v___x_2814_, 0, v___x_2829_);
v___x_2838_ = v___x_2814_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_k_2818_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_v_2819_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v___y_2831_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
v___jp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2844_ = lean_nat_add(v___x_2841_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec(v___x_2841_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_l_2820_);
lean_ctor_set(v___x_2655_, 3, v_l_2803_);
lean_ctor_set(v___x_2655_, 2, v_v_2802_);
lean_ctor_set(v___x_2655_, 1, v_k_2801_);
lean_ctor_set(v___x_2655_, 0, v___x_2844_);
v___x_2846_ = v___x_2655_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2801_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2802_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_l_2803_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_l_2820_);
v___x_2846_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_nat_add(v___x_2798_, v_size_2799_);
if (lean_obj_tag(v_r_2821_) == 0)
{
lean_object* v_size_2848_; 
v_size_2848_ = lean_ctor_get(v_r_2821_, 0);
lean_inc(v_size_2848_);
v___y_2831_ = v___x_2846_;
v___y_2832_ = v___x_2847_;
v___y_2833_ = v_size_2848_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_unsigned_to_nat(0u);
v___y_2831_ = v___x_2846_;
v___y_2832_ = v___x_2847_;
v___y_2833_ = v___x_2849_;
goto v___jp_2830_;
}
}
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_del_object(v___x_2655_);
v___x_2859_ = lean_nat_add(v___x_2798_, v_size_2800_);
lean_dec(v_size_2800_);
v___x_2860_ = lean_nat_add(v___x_2859_, v_size_2799_);
lean_dec(v___x_2859_);
v___x_2861_ = lean_nat_add(v___x_2798_, v_size_2799_);
v___x_2862_ = lean_nat_add(v___x_2861_, v_size_2817_);
lean_dec(v___x_2861_);
lean_inc_ref(v_r_2653_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v_r_2653_);
lean_ctor_set(v___x_2814_, 3, v_r_2804_);
lean_ctor_set(v___x_2814_, 2, v_v_2651_);
lean_ctor_set(v___x_2814_, 1, v_k_2650_);
lean_ctor_set(v___x_2814_, 0, v___x_2862_);
v___x_2864_ = v___x_2814_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_r_2804_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_r_2653_);
v___x_2864_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_isSharedCheck_2871_ = !lean_is_exclusive(v_r_2653_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; lean_object* v_unused_2873_; lean_object* v_unused_2874_; lean_object* v_unused_2875_; lean_object* v_unused_2876_; 
v_unused_2872_ = lean_ctor_get(v_r_2653_, 4);
lean_dec(v_unused_2872_);
v_unused_2873_ = lean_ctor_get(v_r_2653_, 3);
lean_dec(v_unused_2873_);
v_unused_2874_ = lean_ctor_get(v_r_2653_, 2);
lean_dec(v_unused_2874_);
v_unused_2875_ = lean_ctor_get(v_r_2653_, 1);
lean_dec(v_unused_2875_);
v_unused_2876_ = lean_ctor_get(v_r_2653_, 0);
lean_dec(v_unused_2876_);
v___x_2866_ = v_r_2653_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_dec(v_r_2653_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 4, v___x_2864_);
lean_ctor_set(v___x_2866_, 3, v_l_2803_);
lean_ctor_set(v___x_2866_, 2, v_v_2802_);
lean_ctor_set(v___x_2866_, 1, v_k_2801_);
lean_ctor_set(v___x_2866_, 0, v___x_2860_);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2801_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2802_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_l_2803_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v___x_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2884_; 
v_l_2884_ = lean_ctor_get(v_impl_2797_, 3);
if (lean_obj_tag(v_l_2884_) == 0)
{
lean_object* v_r_2885_; lean_object* v_k_2886_; lean_object* v_v_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2898_; 
lean_inc_ref(v_l_2884_);
v_r_2885_ = lean_ctor_get(v_impl_2797_, 4);
v_k_2886_ = lean_ctor_get(v_impl_2797_, 1);
v_v_2887_ = lean_ctor_get(v_impl_2797_, 2);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_impl_2797_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; lean_object* v_unused_2900_; 
v_unused_2899_ = lean_ctor_get(v_impl_2797_, 3);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_impl_2797_, 0);
lean_dec(v_unused_2900_);
v___x_2889_ = v_impl_2797_;
v_isShared_2890_ = v_isSharedCheck_2898_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_r_2885_);
lean_inc(v_v_2887_);
lean_inc(v_k_2886_);
lean_dec(v_impl_2797_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2898_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2891_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2885_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 3, v_r_2885_);
lean_ctor_set(v___x_2889_, 2, v_v_2651_);
lean_ctor_set(v___x_2889_, 1, v_k_2650_);
lean_ctor_set(v___x_2889_, 0, v___x_2798_);
v___x_2893_ = v___x_2889_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2897_, 3, v_r_2885_);
lean_ctor_set(v_reuseFailAlloc_2897_, 4, v_r_2885_);
v___x_2893_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2895_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v___x_2893_);
lean_ctor_set(v___x_2655_, 3, v_l_2884_);
lean_ctor_set(v___x_2655_, 2, v_v_2887_);
lean_ctor_set(v___x_2655_, 1, v_k_2886_);
lean_ctor_set(v___x_2655_, 0, v___x_2891_);
v___x_2895_ = v___x_2655_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_k_2886_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_v_2887_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_l_2884_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_r_2901_; 
v_r_2901_ = lean_ctor_get(v_impl_2797_, 4);
lean_inc(v_r_2901_);
if (lean_obj_tag(v_r_2901_) == 0)
{
lean_object* v_k_2902_; lean_object* v_v_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2926_; 
lean_inc(v_l_2884_);
v_k_2902_ = lean_ctor_get(v_impl_2797_, 1);
v_v_2903_ = lean_ctor_get(v_impl_2797_, 2);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_impl_2797_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; lean_object* v_unused_2928_; lean_object* v_unused_2929_; 
v_unused_2927_ = lean_ctor_get(v_impl_2797_, 4);
lean_dec(v_unused_2927_);
v_unused_2928_ = lean_ctor_get(v_impl_2797_, 3);
lean_dec(v_unused_2928_);
v_unused_2929_ = lean_ctor_get(v_impl_2797_, 0);
lean_dec(v_unused_2929_);
v___x_2905_ = v_impl_2797_;
v_isShared_2906_ = v_isSharedCheck_2926_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_v_2903_);
lean_inc(v_k_2902_);
lean_dec(v_impl_2797_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2926_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_k_2907_; lean_object* v_v_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2922_; 
v_k_2907_ = lean_ctor_get(v_r_2901_, 1);
v_v_2908_ = lean_ctor_get(v_r_2901_, 2);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_r_2901_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2923_ = lean_ctor_get(v_r_2901_, 4);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_r_2901_, 3);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_r_2901_, 0);
lean_dec(v_unused_2925_);
v___x_2910_ = v_r_2901_;
v_isShared_2911_ = v_isSharedCheck_2922_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_v_2908_);
lean_inc(v_k_2907_);
lean_dec(v_r_2901_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2922_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_unsigned_to_nat(3u);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 4, v_l_2884_);
lean_ctor_set(v___x_2910_, 3, v_l_2884_);
lean_ctor_set(v___x_2910_, 2, v_v_2903_);
lean_ctor_set(v___x_2910_, 1, v_k_2902_);
lean_ctor_set(v___x_2910_, 0, v___x_2798_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_k_2902_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v_v_2903_);
lean_ctor_set(v_reuseFailAlloc_2921_, 3, v_l_2884_);
lean_ctor_set(v_reuseFailAlloc_2921_, 4, v_l_2884_);
v___x_2914_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 4, v_l_2884_);
lean_ctor_set(v___x_2905_, 2, v_v_2651_);
lean_ctor_set(v___x_2905_, 1, v_k_2650_);
lean_ctor_set(v___x_2905_, 0, v___x_2798_);
v___x_2916_ = v___x_2905_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2920_, 3, v_l_2884_);
lean_ctor_set(v_reuseFailAlloc_2920_, 4, v_l_2884_);
v___x_2916_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v___x_2916_);
lean_ctor_set(v___x_2655_, 3, v___x_2914_);
lean_ctor_set(v___x_2655_, 2, v_v_2908_);
lean_ctor_set(v___x_2655_, 1, v_k_2907_);
lean_ctor_set(v___x_2655_, 0, v___x_2912_);
v___x_2918_ = v___x_2655_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_k_2907_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_v_2908_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2919_, 4, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_unsigned_to_nat(2u);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_r_2901_);
lean_ctor_set(v___x_2655_, 3, v_impl_2797_);
lean_ctor_set(v___x_2655_, 0, v___x_2930_);
v___x_2932_ = v___x_2655_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_impl_2797_);
lean_ctor_set(v_reuseFailAlloc_2933_, 4, v_r_2901_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set(v___x_2936_, 1, v_k_2646_);
lean_ctor_set(v___x_2936_, 2, v_v_2647_);
lean_ctor_set(v___x_2936_, 3, v_t_2648_);
lean_ctor_set(v___x_2936_, 4, v_t_2648_);
return v___x_2936_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object* v_k_2937_, lean_object* v_t_2938_){
_start:
{
if (lean_obj_tag(v_t_2938_) == 0)
{
lean_object* v_k_2939_; lean_object* v_l_2940_; lean_object* v_r_2941_; uint8_t v___x_2942_; 
v_k_2939_ = lean_ctor_get(v_t_2938_, 1);
v_l_2940_ = lean_ctor_get(v_t_2938_, 3);
v_r_2941_ = lean_ctor_get(v_t_2938_, 4);
v___x_2942_ = lean_nat_dec_lt(v_k_2937_, v_k_2939_);
if (v___x_2942_ == 0)
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_nat_dec_eq(v_k_2937_, v_k_2939_);
if (v___x_2943_ == 0)
{
v_t_2938_ = v_r_2941_;
goto _start;
}
else
{
return v___x_2943_;
}
}
else
{
v_t_2938_ = v_l_2940_;
goto _start;
}
}
else
{
uint8_t v___x_2946_; 
v___x_2946_ = 0;
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object* v_k_2947_, lean_object* v_t_2948_){
_start:
{
uint8_t v_res_2949_; lean_object* v_r_2950_; 
v_res_2949_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2947_, v_t_2948_);
lean_dec(v_t_2948_);
lean_dec(v_k_2947_);
v_r_2950_ = lean_box(v_res_2949_);
return v_r_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* v_idx_2951_){
_start:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = lean_box(1);
v___x_2953_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_box(0);
v___x_2955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_idx_2951_, v___x_2954_, v___x_2952_);
return v___x_2955_;
}
else
{
lean_dec(v_idx_2951_);
return v___x_2952_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object* v_00_u03b2_2956_, lean_object* v_k_2957_, lean_object* v_t_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2957_, v_t_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_k_2961_, lean_object* v_t_2962_){
_start:
{
uint8_t v_res_2963_; lean_object* v_r_2964_; 
v_res_2963_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(v_00_u03b2_2960_, v_k_2961_, v_t_2962_);
lean_dec(v_t_2962_);
lean_dec(v_k_2961_);
v_r_2964_ = lean_box(v_res_2963_);
return v_r_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object* v_00_u03b2_2965_, lean_object* v_k_2966_, lean_object* v_v_2967_, lean_object* v_t_2968_, lean_object* v_hl_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2966_, v_v_2967_, v_t_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl(lean_object* v_x_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_obj_tag_nat(v_x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl___boxed(lean_object* v_x_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_IR_LocalContextEntry_ctorIdx___impl(v_x_2973_);
lean_dec_ref(v_x_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object* v_t_2975_, lean_object* v_k_2976_){
_start:
{
if (lean_obj_tag(v_t_2975_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; 
v_a_2977_ = lean_ctor_get(v_t_2975_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v_t_2975_, 1);
v___x_2978_ = lean_apply_1(v_k_2976_, v_a_2977_);
return v___x_2978_;
}
else
{
lean_object* v_a_2979_; lean_object* v_a_2980_; lean_object* v___x_2981_; 
v_a_2979_ = lean_ctor_get(v_t_2975_, 0);
lean_inc(v_a_2979_);
v_a_2980_ = lean_ctor_get(v_t_2975_, 1);
lean_inc(v_a_2980_);
lean_dec_ref_known(v_t_2975_, 2);
v___x_2981_ = lean_apply_2(v_k_2976_, v_a_2979_, v_a_2980_);
return v___x_2981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object* v_motive_2982_, lean_object* v_ctorIdx_2983_, lean_object* v_t_2984_, lean_object* v_h_2985_, lean_object* v_k_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2984_, v_k_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object* v_motive_2988_, lean_object* v_ctorIdx_2989_, lean_object* v_t_2990_, lean_object* v_h_2991_, lean_object* v_k_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_IR_LocalContextEntry_ctorElim(v_motive_2988_, v_ctorIdx_2989_, v_t_2990_, v_h_2991_, v_k_2992_);
lean_dec(v_ctorIdx_2989_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object* v_t_2994_, lean_object* v_param_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2994_, v_param_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object* v_motive_2997_, lean_object* v_t_2998_, lean_object* v_h_2999_, lean_object* v_param_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2998_, v_param_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object* v_t_3002_, lean_object* v_localVar_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_3002_, v_localVar_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object* v_motive_3005_, lean_object* v_t_3006_, lean_object* v_h_3007_, lean_object* v_localVar_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_3006_, v_localVar_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* v_ctx_3010_, lean_object* v_x_3011_, lean_object* v_t_3012_, lean_object* v_v_3013_){
_start:
{
lean_object* v_vars_3014_; lean_object* v_jps_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3024_; 
v_vars_3014_ = lean_ctor_get(v_ctx_3010_, 0);
v_jps_3015_ = lean_ctor_get(v_ctx_3010_, 1);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_ctx_3010_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3017_ = v_ctx_3010_;
v_isShared_3018_ = v_isSharedCheck_3024_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_jps_3015_);
lean_inc(v_vars_3014_);
lean_dec(v_ctx_3010_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3024_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_t_3012_);
lean_ctor_set(v___x_3019_, 1, v_v_3013_);
v___x_3020_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_3011_, v___x_3019_, v_vars_3014_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3020_);
v___x_3022_ = v___x_3017_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_jps_3015_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* v_ctx_3025_, lean_object* v_j_3026_, lean_object* v_xs_3027_, lean_object* v_b_3028_){
_start:
{
lean_object* v_vars_3029_; lean_object* v_jps_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3039_; 
v_vars_3029_ = lean_ctor_get(v_ctx_3025_, 0);
v_jps_3030_ = lean_ctor_get(v_ctx_3025_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_ctx_3025_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3032_ = v_ctx_3025_;
v_isShared_3033_ = v_isSharedCheck_3039_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_jps_3030_);
lean_inc(v_vars_3029_);
lean_dec(v_ctx_3025_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3039_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_xs_3027_);
lean_ctor_set(v___x_3034_, 1, v_b_3028_);
v___x_3035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_j_3026_, v___x_3034_, v_jps_3030_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_3035_);
v___x_3037_ = v___x_3032_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_vars_3029_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* v_ctx_3040_, lean_object* v_p_3041_){
_start:
{
lean_object* v_vars_3042_; lean_object* v_jps_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3054_; 
v_vars_3042_ = lean_ctor_get(v_ctx_3040_, 0);
v_jps_3043_ = lean_ctor_get(v_ctx_3040_, 1);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_ctx_3040_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3045_ = v_ctx_3040_;
v_isShared_3046_ = v_isSharedCheck_3054_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_jps_3043_);
lean_inc(v_vars_3042_);
lean_dec(v_ctx_3040_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3054_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_x_3047_; lean_object* v_ty_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v_x_3047_ = lean_ctor_get(v_p_3041_, 0);
lean_inc(v_x_3047_);
v_ty_3048_ = lean_ctor_get(v_p_3041_, 1);
lean_inc(v_ty_3048_);
lean_dec_ref(v_p_3041_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_ty_3048_);
v___x_3050_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_3047_, v___x_3049_, v_vars_3042_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3050_);
v___x_3052_ = v___x_3045_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_jps_3043_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object* v_as_3055_, size_t v_i_3056_, size_t v_stop_3057_, lean_object* v_b_3058_){
_start:
{
uint8_t v___x_3059_; 
v___x_3059_ = lean_usize_dec_eq(v_i_3056_, v_stop_3057_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; 
v___x_3060_ = lean_array_uget_borrowed(v_as_3055_, v_i_3056_);
lean_inc(v___x_3060_);
v___x_3061_ = l_Lean_IR_LocalContext_addParam(v_b_3058_, v___x_3060_);
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_add(v_i_3056_, v___x_3062_);
v_i_3056_ = v___x_3063_;
v_b_3058_ = v___x_3061_;
goto _start;
}
else
{
return v_b_3058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* v_as_3065_, lean_object* v_i_3066_, lean_object* v_stop_3067_, lean_object* v_b_3068_){
_start:
{
size_t v_i_boxed_3069_; size_t v_stop_boxed_3070_; lean_object* v_res_3071_; 
v_i_boxed_3069_ = lean_unbox_usize(v_i_3066_);
lean_dec(v_i_3066_);
v_stop_boxed_3070_ = lean_unbox_usize(v_stop_3067_);
lean_dec(v_stop_3067_);
v_res_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_3065_, v_i_boxed_3069_, v_stop_boxed_3070_, v_b_3068_);
lean_dec_ref(v_as_3065_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* v_ctx_3072_, lean_object* v_ps_3073_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_array_get_size(v_ps_3073_);
v___x_3076_ = lean_nat_dec_lt(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
return v_ctx_3072_;
}
else
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((size_t)0ULL);
v___x_3078_ = lean_usize_of_nat(v___x_3075_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_3073_, v___x_3077_, v___x_3078_, v_ctx_3072_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_3080_, lean_object* v_ps_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_IR_LocalContext_addParams(v_ctx_3080_, v_ps_3081_);
lean_dec_ref(v_ps_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_3083_, lean_object* v_j_3084_){
_start:
{
lean_object* v_jps_3085_; uint8_t v___x_3086_; 
v_jps_3085_ = lean_ctor_get(v_ctx_3083_, 1);
v___x_3086_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_j_3084_, v_jps_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_3087_, lean_object* v_j_3088_){
_start:
{
uint8_t v_res_3089_; lean_object* v_r_3090_; 
v_res_3089_ = l_Lean_IR_LocalContext_isJP(v_ctx_3087_, v_j_3088_);
lean_dec(v_j_3088_);
lean_dec_ref(v_ctx_3087_);
v_r_3090_ = lean_box(v_res_3089_);
return v_r_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(lean_object* v_t_3091_, lean_object* v_k_3092_){
_start:
{
if (lean_obj_tag(v_t_3091_) == 0)
{
lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v_l_3095_; lean_object* v_r_3096_; uint8_t v___x_3097_; 
v_k_3093_ = lean_ctor_get(v_t_3091_, 1);
v_v_3094_ = lean_ctor_get(v_t_3091_, 2);
v_l_3095_ = lean_ctor_get(v_t_3091_, 3);
v_r_3096_ = lean_ctor_get(v_t_3091_, 4);
v___x_3097_ = lean_nat_dec_lt(v_k_3092_, v_k_3093_);
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_nat_dec_eq(v_k_3092_, v_k_3093_);
if (v___x_3098_ == 0)
{
v_t_3091_ = v_r_3096_;
goto _start;
}
else
{
lean_object* v___x_3100_; 
lean_inc(v_v_3094_);
v___x_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_v_3094_);
return v___x_3100_;
}
}
else
{
v_t_3091_ = v_l_3095_;
goto _start;
}
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = lean_box(0);
return v___x_3102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg___boxed(lean_object* v_t_3103_, lean_object* v_k_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_3103_, v_k_3104_);
lean_dec(v_k_3104_);
lean_dec(v_t_3103_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_3106_, lean_object* v_j_3107_){
_start:
{
lean_object* v_jps_3108_; lean_object* v___x_3109_; 
v_jps_3108_ = lean_ctor_get(v_ctx_3106_, 1);
v___x_3109_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_3108_, v_j_3107_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_box(0);
return v___x_3110_;
}
else
{
lean_object* v_val_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
v_val_3111_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v___x_3109_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_val_3111_);
lean_dec(v___x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_snd_3115_; lean_object* v___x_3117_; 
v_snd_3115_ = lean_ctor_get(v_val_3111_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_val_3111_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v_snd_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_snd_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_3120_, lean_object* v_j_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_3120_, v_j_3121_);
lean_dec(v_j_3121_);
lean_dec_ref(v_ctx_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(lean_object* v_00_u03b4_3123_, lean_object* v_t_3124_, lean_object* v_k_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_3124_, v_k_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___boxed(lean_object* v_00_u03b4_3127_, lean_object* v_t_3128_, lean_object* v_k_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(v_00_u03b4_3127_, v_t_3128_, v_k_3129_);
lean_dec(v_k_3129_);
lean_dec(v_t_3128_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_3131_, lean_object* v_j_3132_){
_start:
{
lean_object* v_jps_3133_; lean_object* v___x_3134_; 
v_jps_3133_ = lean_ctor_get(v_ctx_3131_, 1);
v___x_3134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_3133_, v_j_3132_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_box(0);
return v___x_3135_;
}
else
{
lean_object* v_val_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
v_val_3136_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v___x_3134_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_val_3136_);
lean_dec(v___x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_fst_3140_; lean_object* v___x_3142_; 
v_fst_3140_ = lean_ctor_get(v_val_3136_, 0);
lean_inc(v_fst_3140_);
lean_dec(v_val_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v_fst_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_fst_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_3145_, lean_object* v_j_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_3145_, v_j_3146_);
lean_dec(v_j_3146_);
lean_dec_ref(v_ctx_3145_);
return v_res_3147_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v_vars_3150_; lean_object* v___x_3151_; 
v_vars_3150_ = lean_ctor_get(v_ctx_3148_, 0);
v___x_3151_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3150_, v_x_3149_);
if (lean_obj_tag(v___x_3151_) == 1)
{
lean_object* v_val_3152_; 
v_val_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_val_3152_);
lean_dec_ref_known(v___x_3151_, 1);
if (lean_obj_tag(v_val_3152_) == 0)
{
uint8_t v___x_3153_; 
lean_dec_ref_known(v_val_3152_, 1);
v___x_3153_ = 1;
return v___x_3153_;
}
else
{
uint8_t v___x_3154_; 
lean_dec(v_val_3152_);
v___x_3154_ = 0;
return v___x_3154_;
}
}
else
{
uint8_t v___x_3155_; 
lean_dec(v___x_3151_);
v___x_3155_ = 0;
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_3156_, lean_object* v_x_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Lean_IR_LocalContext_isParam(v_ctx_3156_, v_x_3157_);
lean_dec(v_x_3157_);
lean_dec_ref(v_ctx_3156_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_3160_, lean_object* v_x_3161_){
_start:
{
lean_object* v_vars_3162_; lean_object* v___x_3163_; 
v_vars_3162_ = lean_ctor_get(v_ctx_3160_, 0);
v___x_3163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3162_, v_x_3161_);
if (lean_obj_tag(v___x_3163_) == 1)
{
lean_object* v_val_3164_; 
v_val_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_val_3164_);
lean_dec_ref_known(v___x_3163_, 1);
if (lean_obj_tag(v_val_3164_) == 1)
{
uint8_t v___x_3165_; 
lean_dec_ref_known(v_val_3164_, 2);
v___x_3165_ = 1;
return v___x_3165_;
}
else
{
uint8_t v___x_3166_; 
lean_dec(v_val_3164_);
v___x_3166_ = 0;
return v___x_3166_;
}
}
else
{
uint8_t v___x_3167_; 
lean_dec(v___x_3163_);
v___x_3167_ = 0;
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_3168_, lean_object* v_x_3169_){
_start:
{
uint8_t v_res_3170_; lean_object* v_r_3171_; 
v_res_3170_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_3168_, v_x_3169_);
lean_dec(v_x_3169_);
lean_dec_ref(v_ctx_3168_);
v_r_3171_ = lean_box(v_res_3170_);
return v_r_3171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_3172_, lean_object* v_t_3173_){
_start:
{
if (lean_obj_tag(v_t_3173_) == 0)
{
lean_object* v_k_3174_; lean_object* v_v_3175_; lean_object* v_l_3176_; lean_object* v_r_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3832_; 
v_k_3174_ = lean_ctor_get(v_t_3173_, 1);
v_v_3175_ = lean_ctor_get(v_t_3173_, 2);
v_l_3176_ = lean_ctor_get(v_t_3173_, 3);
v_r_3177_ = lean_ctor_get(v_t_3173_, 4);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_t_3173_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_t_3173_, 0);
lean_dec(v_unused_3833_);
v___x_3179_ = v_t_3173_;
v_isShared_3180_ = v_isSharedCheck_3832_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_r_3177_);
lean_inc(v_l_3176_);
lean_inc(v_v_3175_);
lean_inc(v_k_3174_);
lean_dec(v_t_3173_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3832_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_nat_dec_lt(v_k_3172_, v_k_3174_);
if (v___x_3181_ == 0)
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_nat_dec_eq(v_k_3172_, v_k_3174_);
if (v___x_3182_ == 0)
{
lean_object* v_impl_3183_; lean_object* v___x_3184_; 
v_impl_3183_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3172_, v_r_3177_);
v___x_3184_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3183_) == 0)
{
if (lean_obj_tag(v_l_3176_) == 0)
{
lean_object* v_size_3185_; lean_object* v_size_3186_; lean_object* v_k_3187_; lean_object* v_v_3188_; lean_object* v_l_3189_; lean_object* v_r_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
v_size_3185_ = lean_ctor_get(v_impl_3183_, 0);
v_size_3186_ = lean_ctor_get(v_l_3176_, 0);
v_k_3187_ = lean_ctor_get(v_l_3176_, 1);
v_v_3188_ = lean_ctor_get(v_l_3176_, 2);
v_l_3189_ = lean_ctor_get(v_l_3176_, 3);
v_r_3190_ = lean_ctor_get(v_l_3176_, 4);
lean_inc(v_r_3190_);
v___x_3191_ = lean_unsigned_to_nat(3u);
v___x_3192_ = lean_nat_mul(v___x_3191_, v_size_3185_);
v___x_3193_ = lean_nat_dec_lt(v___x_3192_, v_size_3186_);
lean_dec(v___x_3192_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_dec(v_r_3190_);
v___x_3194_ = lean_nat_add(v___x_3184_, v_size_3186_);
v___x_3195_ = lean_nat_add(v___x_3194_, v_size_3185_);
lean_dec(v___x_3194_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_impl_3183_);
lean_ctor_set(v___x_3179_, 0, v___x_3195_);
v___x_3197_ = v___x_3179_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_impl_3183_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
else
{
lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3264_; 
lean_inc(v_l_3189_);
lean_inc(v_v_3188_);
lean_inc(v_k_3187_);
lean_inc(v_size_3186_);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; lean_object* v_unused_3266_; lean_object* v_unused_3267_; lean_object* v_unused_3268_; lean_object* v_unused_3269_; 
v_unused_3265_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3266_);
v_unused_3267_ = lean_ctor_get(v_l_3176_, 2);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_l_3176_, 1);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3269_);
v___x_3200_ = v_l_3176_;
v_isShared_3201_ = v_isSharedCheck_3264_;
goto v_resetjp_3199_;
}
else
{
lean_dec(v_l_3176_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3264_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_size_3202_; lean_object* v_size_3203_; lean_object* v_k_3204_; lean_object* v_v_3205_; lean_object* v_l_3206_; lean_object* v_r_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; 
v_size_3202_ = lean_ctor_get(v_l_3189_, 0);
v_size_3203_ = lean_ctor_get(v_r_3190_, 0);
v_k_3204_ = lean_ctor_get(v_r_3190_, 1);
v_v_3205_ = lean_ctor_get(v_r_3190_, 2);
v_l_3206_ = lean_ctor_get(v_r_3190_, 3);
v_r_3207_ = lean_ctor_get(v_r_3190_, 4);
v___x_3208_ = lean_unsigned_to_nat(2u);
v___x_3209_ = lean_nat_mul(v___x_3208_, v_size_3202_);
v___x_3210_ = lean_nat_dec_lt(v_size_3203_, v___x_3209_);
lean_dec(v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3239_; 
lean_inc(v_r_3207_);
lean_inc(v_l_3206_);
lean_inc(v_v_3205_);
lean_inc(v_k_3204_);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_r_3190_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; lean_object* v_unused_3241_; lean_object* v_unused_3242_; lean_object* v_unused_3243_; lean_object* v_unused_3244_; 
v_unused_3240_ = lean_ctor_get(v_r_3190_, 4);
lean_dec(v_unused_3240_);
v_unused_3241_ = lean_ctor_get(v_r_3190_, 3);
lean_dec(v_unused_3241_);
v_unused_3242_ = lean_ctor_get(v_r_3190_, 2);
lean_dec(v_unused_3242_);
v_unused_3243_ = lean_ctor_get(v_r_3190_, 1);
lean_dec(v_unused_3243_);
v_unused_3244_ = lean_ctor_get(v_r_3190_, 0);
lean_dec(v_unused_3244_);
v___x_3212_ = v_r_3190_;
v_isShared_3213_ = v_isSharedCheck_3239_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v_r_3190_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3239_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___x_3227_; lean_object* v___y_3229_; 
v___x_3214_ = lean_nat_add(v___x_3184_, v_size_3186_);
lean_dec(v_size_3186_);
v___x_3215_ = lean_nat_add(v___x_3214_, v_size_3185_);
lean_dec(v___x_3214_);
v___x_3227_ = lean_nat_add(v___x_3184_, v_size_3202_);
if (lean_obj_tag(v_l_3206_) == 0)
{
lean_object* v_size_3237_; 
v_size_3237_ = lean_ctor_get(v_l_3206_, 0);
lean_inc(v_size_3237_);
v___y_3229_ = v_size_3237_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_unsigned_to_nat(0u);
v___y_3229_ = v___x_3238_;
goto v___jp_3228_;
}
v___jp_3216_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = lean_nat_add(v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 4, v_impl_3183_);
lean_ctor_set(v___x_3212_, 3, v_r_3207_);
lean_ctor_set(v___x_3212_, 2, v_v_3175_);
lean_ctor_set(v___x_3212_, 1, v_k_3174_);
lean_ctor_set(v___x_3212_, 0, v___x_3220_);
v___x_3222_ = v___x_3212_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_r_3207_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_impl_3183_);
v___x_3222_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 4, v___x_3222_);
lean_ctor_set(v___x_3200_, 3, v___y_3217_);
lean_ctor_set(v___x_3200_, 2, v_v_3205_);
lean_ctor_set(v___x_3200_, 1, v_k_3204_);
lean_ctor_set(v___x_3200_, 0, v___x_3215_);
v___x_3224_ = v___x_3200_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_k_3204_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_v_3205_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v___y_3217_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
v___jp_3228_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_nat_add(v___x_3227_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec(v___x_3227_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_l_3206_);
lean_ctor_set(v___x_3179_, 3, v_l_3189_);
lean_ctor_set(v___x_3179_, 2, v_v_3188_);
lean_ctor_set(v___x_3179_, 1, v_k_3187_);
lean_ctor_set(v___x_3179_, 0, v___x_3230_);
v___x_3232_ = v___x_3179_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_k_3187_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_v_3188_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_l_3189_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_l_3206_);
v___x_3232_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_nat_add(v___x_3184_, v_size_3185_);
if (lean_obj_tag(v_r_3207_) == 0)
{
lean_object* v_size_3234_; 
v_size_3234_ = lean_ctor_get(v_r_3207_, 0);
lean_inc(v_size_3234_);
v___y_3217_ = v___x_3232_;
v___y_3218_ = v___x_3233_;
v___y_3219_ = v_size_3234_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_unsigned_to_nat(0u);
v___y_3217_ = v___x_3232_;
v___y_3218_ = v___x_3233_;
v___y_3219_ = v___x_3235_;
goto v___jp_3216_;
}
}
}
}
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
lean_del_object(v___x_3179_);
v___x_3245_ = lean_nat_add(v___x_3184_, v_size_3186_);
lean_dec(v_size_3186_);
v___x_3246_ = lean_nat_add(v___x_3245_, v_size_3185_);
lean_dec(v___x_3245_);
v___x_3247_ = lean_nat_add(v___x_3184_, v_size_3185_);
v___x_3248_ = lean_nat_add(v___x_3247_, v_size_3203_);
lean_dec(v___x_3247_);
lean_inc_ref(v_impl_3183_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 4, v_impl_3183_);
lean_ctor_set(v___x_3200_, 3, v_r_3190_);
lean_ctor_set(v___x_3200_, 2, v_v_3175_);
lean_ctor_set(v___x_3200_, 1, v_k_3174_);
lean_ctor_set(v___x_3200_, 0, v___x_3248_);
v___x_3250_ = v___x_3200_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_r_3190_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_impl_3183_);
v___x_3250_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
v_isSharedCheck_3257_ = !lean_is_exclusive(v_impl_3183_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; lean_object* v_unused_3259_; lean_object* v_unused_3260_; lean_object* v_unused_3261_; lean_object* v_unused_3262_; 
v_unused_3258_ = lean_ctor_get(v_impl_3183_, 4);
lean_dec(v_unused_3258_);
v_unused_3259_ = lean_ctor_get(v_impl_3183_, 3);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_impl_3183_, 2);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_impl_3183_, 1);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_impl_3183_, 0);
lean_dec(v_unused_3262_);
v___x_3252_ = v_impl_3183_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_dec(v_impl_3183_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v___x_3250_);
lean_ctor_set(v___x_3252_, 3, v_l_3189_);
lean_ctor_set(v___x_3252_, 2, v_v_3188_);
lean_ctor_set(v___x_3252_, 1, v_k_3187_);
lean_ctor_set(v___x_3252_, 0, v___x_3246_);
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_3187_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_v_3188_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_l_3189_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v___x_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v_size_3270_ = lean_ctor_get(v_impl_3183_, 0);
v___x_3271_ = lean_nat_add(v___x_3184_, v_size_3270_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_impl_3183_);
lean_ctor_set(v___x_3179_, 0, v___x_3271_);
v___x_3273_ = v___x_3179_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3274_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3274_, 4, v_impl_3183_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
else
{
if (lean_obj_tag(v_l_3176_) == 0)
{
lean_object* v_l_3275_; 
v_l_3275_ = lean_ctor_get(v_l_3176_, 3);
if (lean_obj_tag(v_l_3275_) == 0)
{
lean_object* v_r_3276_; 
lean_inc_ref(v_l_3275_);
v_r_3276_ = lean_ctor_get(v_l_3176_, 4);
lean_inc(v_r_3276_);
if (lean_obj_tag(v_r_3276_) == 0)
{
lean_object* v_size_3277_; lean_object* v_k_3278_; lean_object* v_v_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3292_; 
v_size_3277_ = lean_ctor_get(v_l_3176_, 0);
v_k_3278_ = lean_ctor_get(v_l_3176_, 1);
v_v_3279_ = lean_ctor_get(v_l_3176_, 2);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; lean_object* v_unused_3294_; 
v_unused_3293_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3294_);
v___x_3281_ = v_l_3176_;
v_isShared_3282_ = v_isSharedCheck_3292_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_v_3279_);
lean_inc(v_k_3278_);
lean_inc(v_size_3277_);
lean_dec(v_l_3176_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3292_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_size_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v_size_3283_ = lean_ctor_get(v_r_3276_, 0);
v___x_3284_ = lean_nat_add(v___x_3184_, v_size_3277_);
lean_dec(v_size_3277_);
v___x_3285_ = lean_nat_add(v___x_3184_, v_size_3283_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 4, v_impl_3183_);
lean_ctor_set(v___x_3281_, 3, v_r_3276_);
lean_ctor_set(v___x_3281_, 2, v_v_3175_);
lean_ctor_set(v___x_3281_, 1, v_k_3174_);
lean_ctor_set(v___x_3281_, 0, v___x_3285_);
v___x_3287_ = v___x_3281_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3291_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3291_, 3, v_r_3276_);
lean_ctor_set(v_reuseFailAlloc_3291_, 4, v_impl_3183_);
v___x_3287_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3289_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___x_3287_);
lean_ctor_set(v___x_3179_, 3, v_l_3275_);
lean_ctor_set(v___x_3179_, 2, v_v_3279_);
lean_ctor_set(v___x_3179_, 1, v_k_3278_);
lean_ctor_set(v___x_3179_, 0, v___x_3284_);
v___x_3289_ = v___x_3179_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_k_3278_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_v_3279_);
lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_l_3275_);
lean_ctor_set(v_reuseFailAlloc_3290_, 4, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v_k_3295_; lean_object* v_v_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3307_; 
v_k_3295_ = lean_ctor_get(v_l_3176_, 1);
v_v_3296_ = lean_ctor_get(v_l_3176_, 2);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; 
v_unused_3308_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3310_);
v___x_3298_ = v_l_3176_;
v_isShared_3299_ = v_isSharedCheck_3307_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_v_3296_);
lean_inc(v_k_3295_);
lean_dec(v_l_3176_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3307_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_unsigned_to_nat(3u);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 3, v_r_3276_);
lean_ctor_set(v___x_3298_, 2, v_v_3175_);
lean_ctor_set(v___x_3298_, 1, v_k_3174_);
lean_ctor_set(v___x_3298_, 0, v___x_3184_);
v___x_3302_ = v___x_3298_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v_r_3276_);
lean_ctor_set(v_reuseFailAlloc_3306_, 4, v_r_3276_);
v___x_3302_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3304_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___x_3302_);
lean_ctor_set(v___x_3179_, 3, v_l_3275_);
lean_ctor_set(v___x_3179_, 2, v_v_3296_);
lean_ctor_set(v___x_3179_, 1, v_k_3295_);
lean_ctor_set(v___x_3179_, 0, v___x_3300_);
v___x_3304_ = v___x_3179_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_k_3295_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_v_3296_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_l_3275_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
else
{
lean_object* v_r_3311_; 
v_r_3311_ = lean_ctor_get(v_l_3176_, 4);
lean_inc(v_r_3311_);
if (lean_obj_tag(v_r_3311_) == 0)
{
lean_object* v_k_3312_; lean_object* v_v_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3336_; 
lean_inc(v_l_3275_);
v_k_3312_ = lean_ctor_get(v_l_3176_, 1);
v_v_3313_ = lean_ctor_get(v_l_3176_, 2);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; lean_object* v_unused_3338_; lean_object* v_unused_3339_; 
v_unused_3337_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3339_);
v___x_3315_ = v_l_3176_;
v_isShared_3316_ = v_isSharedCheck_3336_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_v_3313_);
lean_inc(v_k_3312_);
lean_dec(v_l_3176_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3336_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v_k_3317_; lean_object* v_v_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3332_; 
v_k_3317_ = lean_ctor_get(v_r_3311_, 1);
v_v_3318_ = lean_ctor_get(v_r_3311_, 2);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_r_3311_);
if (v_isSharedCheck_3332_ == 0)
{
lean_object* v_unused_3333_; lean_object* v_unused_3334_; lean_object* v_unused_3335_; 
v_unused_3333_ = lean_ctor_get(v_r_3311_, 4);
lean_dec(v_unused_3333_);
v_unused_3334_ = lean_ctor_get(v_r_3311_, 3);
lean_dec(v_unused_3334_);
v_unused_3335_ = lean_ctor_get(v_r_3311_, 0);
lean_dec(v_unused_3335_);
v___x_3320_ = v_r_3311_;
v_isShared_3321_ = v_isSharedCheck_3332_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_v_3318_);
lean_inc(v_k_3317_);
lean_dec(v_r_3311_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3332_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3322_ = lean_unsigned_to_nat(3u);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 4, v_l_3275_);
lean_ctor_set(v___x_3320_, 3, v_l_3275_);
lean_ctor_set(v___x_3320_, 2, v_v_3313_);
lean_ctor_set(v___x_3320_, 1, v_k_3312_);
lean_ctor_set(v___x_3320_, 0, v___x_3184_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3331_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3331_, 3, v_l_3275_);
lean_ctor_set(v_reuseFailAlloc_3331_, 4, v_l_3275_);
v___x_3324_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 4, v_l_3275_);
lean_ctor_set(v___x_3315_, 2, v_v_3175_);
lean_ctor_set(v___x_3315_, 1, v_k_3174_);
lean_ctor_set(v___x_3315_, 0, v___x_3184_);
v___x_3326_ = v___x_3315_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v_l_3275_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v_l_3275_);
v___x_3326_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3328_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___x_3326_);
lean_ctor_set(v___x_3179_, 3, v___x_3324_);
lean_ctor_set(v___x_3179_, 2, v_v_3318_);
lean_ctor_set(v___x_3179_, 1, v_k_3317_);
lean_ctor_set(v___x_3179_, 0, v___x_3322_);
v___x_3328_ = v___x_3179_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_k_3317_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_v_3318_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_unsigned_to_nat(2u);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_r_3311_);
lean_ctor_set(v___x_3179_, 0, v___x_3340_);
v___x_3342_ = v___x_3179_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_r_3311_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v___x_3345_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_l_3176_);
lean_ctor_set(v___x_3179_, 0, v___x_3184_);
v___x_3345_ = v___x_3179_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_l_3176_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_del_object(v___x_3179_);
lean_dec(v_v_3175_);
lean_dec(v_k_3174_);
if (lean_obj_tag(v_l_3176_) == 0)
{
if (lean_obj_tag(v_r_3177_) == 0)
{
lean_object* v_size_3347_; lean_object* v_k_3348_; lean_object* v_v_3349_; lean_object* v_l_3350_; lean_object* v_r_3351_; lean_object* v_size_3352_; lean_object* v_k_3353_; lean_object* v_v_3354_; lean_object* v_l_3355_; lean_object* v_r_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v_size_3347_ = lean_ctor_get(v_l_3176_, 0);
v_k_3348_ = lean_ctor_get(v_l_3176_, 1);
v_v_3349_ = lean_ctor_get(v_l_3176_, 2);
v_l_3350_ = lean_ctor_get(v_l_3176_, 3);
v_r_3351_ = lean_ctor_get(v_l_3176_, 4);
lean_inc(v_r_3351_);
v_size_3352_ = lean_ctor_get(v_r_3177_, 0);
v_k_3353_ = lean_ctor_get(v_r_3177_, 1);
v_v_3354_ = lean_ctor_get(v_r_3177_, 2);
v_l_3355_ = lean_ctor_get(v_r_3177_, 3);
lean_inc(v_l_3355_);
v_r_3356_ = lean_ctor_get(v_r_3177_, 4);
v___x_3357_ = lean_unsigned_to_nat(1u);
v___x_3358_ = lean_nat_dec_lt(v_size_3347_, v_size_3352_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3494_; 
lean_inc(v_l_3350_);
lean_inc(v_v_3349_);
lean_inc(v_k_3348_);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; lean_object* v_unused_3496_; lean_object* v_unused_3497_; lean_object* v_unused_3498_; lean_object* v_unused_3499_; 
v_unused_3495_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v_l_3176_, 2);
lean_dec(v_unused_3497_);
v_unused_3498_ = lean_ctor_get(v_l_3176_, 1);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3499_);
v___x_3360_ = v_l_3176_;
v_isShared_3361_ = v_isSharedCheck_3494_;
goto v_resetjp_3359_;
}
else
{
lean_dec(v_l_3176_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3494_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v_tree_3363_; 
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3348_, v_v_3349_, v_l_3350_, v_r_3351_);
v_tree_3363_ = lean_ctor_get(v___x_3362_, 2);
if (lean_obj_tag(v_tree_3363_) == 0)
{
lean_object* v_k_3364_; lean_object* v_v_3365_; lean_object* v_size_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
lean_inc_ref(v_tree_3363_);
v_k_3364_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_k_3364_);
v_v_3365_ = lean_ctor_get(v___x_3362_, 1);
lean_inc(v_v_3365_);
lean_dec_ref(v___x_3362_);
v_size_3366_ = lean_ctor_get(v_tree_3363_, 0);
v___x_3367_ = lean_unsigned_to_nat(3u);
v___x_3368_ = lean_nat_mul(v___x_3367_, v_size_3366_);
v___x_3369_ = lean_nat_dec_lt(v___x_3368_, v_size_3352_);
lean_dec(v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
lean_dec(v_l_3355_);
v___x_3370_ = lean_nat_add(v___x_3357_, v_size_3366_);
v___x_3371_ = lean_nat_add(v___x_3370_, v_size_3352_);
lean_dec(v___x_3370_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v_r_3177_);
lean_ctor_set(v___x_3360_, 3, v_tree_3363_);
lean_ctor_set(v___x_3360_, 2, v_v_3365_);
lean_ctor_set(v___x_3360_, 1, v_k_3364_);
lean_ctor_set(v___x_3360_, 0, v___x_3371_);
v___x_3373_ = v___x_3360_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_k_3364_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_v_3365_);
lean_ctor_set(v_reuseFailAlloc_3374_, 3, v_tree_3363_);
lean_ctor_set(v_reuseFailAlloc_3374_, 4, v_r_3177_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
else
{
lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3429_; 
lean_inc(v_r_3356_);
lean_inc(v_v_3354_);
lean_inc(v_k_3353_);
lean_inc(v_size_3352_);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; lean_object* v_unused_3431_; lean_object* v_unused_3432_; lean_object* v_unused_3433_; lean_object* v_unused_3434_; 
v_unused_3430_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3431_);
v_unused_3432_ = lean_ctor_get(v_r_3177_, 2);
lean_dec(v_unused_3432_);
v_unused_3433_ = lean_ctor_get(v_r_3177_, 1);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v_r_3177_, 0);
lean_dec(v_unused_3434_);
v___x_3376_ = v_r_3177_;
v_isShared_3377_ = v_isSharedCheck_3429_;
goto v_resetjp_3375_;
}
else
{
lean_dec(v_r_3177_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3429_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_size_3378_; lean_object* v_k_3379_; lean_object* v_v_3380_; lean_object* v_l_3381_; lean_object* v_r_3382_; lean_object* v_size_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_size_3378_ = lean_ctor_get(v_l_3355_, 0);
v_k_3379_ = lean_ctor_get(v_l_3355_, 1);
v_v_3380_ = lean_ctor_get(v_l_3355_, 2);
v_l_3381_ = lean_ctor_get(v_l_3355_, 3);
v_r_3382_ = lean_ctor_get(v_l_3355_, 4);
v_size_3383_ = lean_ctor_get(v_r_3356_, 0);
v___x_3384_ = lean_unsigned_to_nat(2u);
v___x_3385_ = lean_nat_mul(v___x_3384_, v_size_3383_);
v___x_3386_ = lean_nat_dec_lt(v_size_3378_, v___x_3385_);
lean_dec(v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3414_; 
lean_inc(v_r_3382_);
lean_inc(v_l_3381_);
lean_inc(v_v_3380_);
lean_inc(v_k_3379_);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_l_3355_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; lean_object* v_unused_3416_; lean_object* v_unused_3417_; lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3415_ = lean_ctor_get(v_l_3355_, 4);
lean_dec(v_unused_3415_);
v_unused_3416_ = lean_ctor_get(v_l_3355_, 3);
lean_dec(v_unused_3416_);
v_unused_3417_ = lean_ctor_get(v_l_3355_, 2);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_l_3355_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_l_3355_, 0);
lean_dec(v_unused_3419_);
v___x_3388_ = v_l_3355_;
v_isShared_3389_ = v_isSharedCheck_3414_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v_l_3355_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3414_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3404_; 
v___x_3390_ = lean_nat_add(v___x_3357_, v_size_3366_);
v___x_3391_ = lean_nat_add(v___x_3390_, v_size_3352_);
lean_dec(v_size_3352_);
if (lean_obj_tag(v_l_3381_) == 0)
{
lean_object* v_size_3412_; 
v_size_3412_ = lean_ctor_get(v_l_3381_, 0);
lean_inc(v_size_3412_);
v___y_3404_ = v_size_3412_;
goto v___jp_3403_;
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_unsigned_to_nat(0u);
v___y_3404_ = v___x_3413_;
goto v___jp_3403_;
}
v___jp_3392_:
{
lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3396_ = lean_nat_add(v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec(v___y_3394_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_r_3356_);
lean_ctor_set(v___x_3388_, 3, v_r_3382_);
lean_ctor_set(v___x_3388_, 2, v_v_3354_);
lean_ctor_set(v___x_3388_, 1, v_k_3353_);
lean_ctor_set(v___x_3388_, 0, v___x_3396_);
v___x_3398_ = v___x_3388_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_k_3353_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_v_3354_);
lean_ctor_set(v_reuseFailAlloc_3402_, 3, v_r_3382_);
lean_ctor_set(v_reuseFailAlloc_3402_, 4, v_r_3356_);
v___x_3398_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 4, v___x_3398_);
lean_ctor_set(v___x_3376_, 3, v___y_3393_);
lean_ctor_set(v___x_3376_, 2, v_v_3380_);
lean_ctor_set(v___x_3376_, 1, v_k_3379_);
lean_ctor_set(v___x_3376_, 0, v___x_3391_);
v___x_3400_ = v___x_3376_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_k_3379_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_v_3380_);
lean_ctor_set(v_reuseFailAlloc_3401_, 3, v___y_3393_);
lean_ctor_set(v_reuseFailAlloc_3401_, 4, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
v___jp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = lean_nat_add(v___x_3390_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec(v___x_3390_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v_l_3381_);
lean_ctor_set(v___x_3360_, 3, v_tree_3363_);
lean_ctor_set(v___x_3360_, 2, v_v_3365_);
lean_ctor_set(v___x_3360_, 1, v_k_3364_);
lean_ctor_set(v___x_3360_, 0, v___x_3405_);
v___x_3407_ = v___x_3360_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_k_3364_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_v_3365_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_tree_3363_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v_l_3381_);
v___x_3407_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_nat_add(v___x_3357_, v_size_3383_);
if (lean_obj_tag(v_r_3382_) == 0)
{
lean_object* v_size_3409_; 
v_size_3409_ = lean_ctor_get(v_r_3382_, 0);
lean_inc(v_size_3409_);
v___y_3393_ = v___x_3407_;
v___y_3394_ = v___x_3408_;
v___y_3395_ = v_size_3409_;
goto v___jp_3392_;
}
else
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
v___y_3393_ = v___x_3407_;
v___y_3394_ = v___x_3408_;
v___y_3395_ = v___x_3410_;
goto v___jp_3392_;
}
}
}
}
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3420_ = lean_nat_add(v___x_3357_, v_size_3366_);
v___x_3421_ = lean_nat_add(v___x_3420_, v_size_3352_);
lean_dec(v_size_3352_);
v___x_3422_ = lean_nat_add(v___x_3420_, v_size_3378_);
lean_dec(v___x_3420_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 4, v_l_3355_);
lean_ctor_set(v___x_3376_, 3, v_tree_3363_);
lean_ctor_set(v___x_3376_, 2, v_v_3365_);
lean_ctor_set(v___x_3376_, 1, v_k_3364_);
lean_ctor_set(v___x_3376_, 0, v___x_3422_);
v___x_3424_ = v___x_3376_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_k_3364_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_v_3365_);
lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_tree_3363_);
lean_ctor_set(v_reuseFailAlloc_3428_, 4, v_l_3355_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v_r_3356_);
lean_ctor_set(v___x_3360_, 3, v___x_3424_);
lean_ctor_set(v___x_3360_, 2, v_v_3354_);
lean_ctor_set(v___x_3360_, 1, v_k_3353_);
lean_ctor_set(v___x_3360_, 0, v___x_3421_);
v___x_3426_ = v___x_3360_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_k_3353_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_v_3354_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3427_, 4, v_r_3356_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
else
{
lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3488_; 
lean_inc(v_r_3356_);
lean_inc(v_v_3354_);
lean_inc(v_k_3353_);
lean_inc(v_size_3352_);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; lean_object* v_unused_3490_; lean_object* v_unused_3491_; lean_object* v_unused_3492_; lean_object* v_unused_3493_; 
v_unused_3489_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3490_);
v_unused_3491_ = lean_ctor_get(v_r_3177_, 2);
lean_dec(v_unused_3491_);
v_unused_3492_ = lean_ctor_get(v_r_3177_, 1);
lean_dec(v_unused_3492_);
v_unused_3493_ = lean_ctor_get(v_r_3177_, 0);
lean_dec(v_unused_3493_);
v___x_3436_ = v_r_3177_;
v_isShared_3437_ = v_isSharedCheck_3488_;
goto v_resetjp_3435_;
}
else
{
lean_dec(v_r_3177_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3488_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
if (lean_obj_tag(v_l_3355_) == 0)
{
if (lean_obj_tag(v_r_3356_) == 0)
{
lean_object* v_k_3438_; lean_object* v_v_3439_; lean_object* v_size_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_inc(v_tree_3363_);
v_k_3438_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_k_3438_);
v_v_3439_ = lean_ctor_get(v___x_3362_, 1);
lean_inc(v_v_3439_);
lean_dec_ref(v___x_3362_);
v_size_3440_ = lean_ctor_get(v_l_3355_, 0);
v___x_3441_ = lean_nat_add(v___x_3357_, v_size_3352_);
lean_dec(v_size_3352_);
v___x_3442_ = lean_nat_add(v___x_3357_, v_size_3440_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_l_3355_);
lean_ctor_set(v___x_3436_, 3, v_tree_3363_);
lean_ctor_set(v___x_3436_, 2, v_v_3439_);
lean_ctor_set(v___x_3436_, 1, v_k_3438_);
lean_ctor_set(v___x_3436_, 0, v___x_3442_);
v___x_3444_ = v___x_3436_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3438_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3439_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_tree_3363_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_l_3355_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v_r_3356_);
lean_ctor_set(v___x_3360_, 3, v___x_3444_);
lean_ctor_set(v___x_3360_, 2, v_v_3354_);
lean_ctor_set(v___x_3360_, 1, v_k_3353_);
lean_ctor_set(v___x_3360_, 0, v___x_3441_);
v___x_3446_ = v___x_3360_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_3353_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_3354_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_r_3356_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
else
{
lean_object* v_k_3449_; lean_object* v_v_3450_; lean_object* v_k_3451_; lean_object* v_v_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_size_3352_);
v_k_3449_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_k_3449_);
v_v_3450_ = lean_ctor_get(v___x_3362_, 1);
lean_inc(v_v_3450_);
lean_dec_ref(v___x_3362_);
v_k_3451_ = lean_ctor_get(v_l_3355_, 1);
v_v_3452_ = lean_ctor_get(v_l_3355_, 2);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_l_3355_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; lean_object* v_unused_3469_; 
v_unused_3467_ = lean_ctor_get(v_l_3355_, 4);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_l_3355_, 3);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v_l_3355_, 0);
lean_dec(v_unused_3469_);
v___x_3454_ = v_l_3355_;
v_isShared_3455_ = v_isSharedCheck_3466_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_v_3452_);
lean_inc(v_k_3451_);
lean_dec(v_l_3355_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3466_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = lean_unsigned_to_nat(3u);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 4, v_r_3356_);
lean_ctor_set(v___x_3454_, 3, v_r_3356_);
lean_ctor_set(v___x_3454_, 2, v_v_3450_);
lean_ctor_set(v___x_3454_, 1, v_k_3449_);
lean_ctor_set(v___x_3454_, 0, v___x_3357_);
v___x_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_k_3449_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_v_3450_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_r_3356_);
lean_ctor_set(v_reuseFailAlloc_3465_, 4, v_r_3356_);
v___x_3458_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 3, v_r_3356_);
lean_ctor_set(v___x_3436_, 0, v___x_3357_);
v___x_3460_ = v___x_3436_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_k_3353_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_v_3354_);
lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_r_3356_);
lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_r_3356_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v___x_3460_);
lean_ctor_set(v___x_3360_, 3, v___x_3458_);
lean_ctor_set(v___x_3360_, 2, v_v_3452_);
lean_ctor_set(v___x_3360_, 1, v_k_3451_);
lean_ctor_set(v___x_3360_, 0, v___x_3456_);
v___x_3462_ = v___x_3360_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_k_3451_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_v_3452_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3356_) == 0)
{
lean_object* v_k_3470_; lean_object* v_v_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
lean_dec(v_size_3352_);
v_k_3470_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_k_3470_);
v_v_3471_ = lean_ctor_get(v___x_3362_, 1);
lean_inc(v_v_3471_);
lean_dec_ref(v___x_3362_);
v___x_3472_ = lean_unsigned_to_nat(3u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_l_3355_);
lean_ctor_set(v___x_3436_, 2, v_v_3471_);
lean_ctor_set(v___x_3436_, 1, v_k_3470_);
lean_ctor_set(v___x_3436_, 0, v___x_3357_);
v___x_3474_ = v___x_3436_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3470_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3471_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_l_3355_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_l_3355_);
v___x_3474_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v_r_3356_);
lean_ctor_set(v___x_3360_, 3, v___x_3474_);
lean_ctor_set(v___x_3360_, 2, v_v_3354_);
lean_ctor_set(v___x_3360_, 1, v_k_3353_);
lean_ctor_set(v___x_3360_, 0, v___x_3472_);
v___x_3476_ = v___x_3360_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_k_3353_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_v_3354_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_r_3356_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
else
{
lean_object* v_k_3479_; lean_object* v_v_3480_; lean_object* v___x_3482_; 
v_k_3479_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_k_3479_);
v_v_3480_ = lean_ctor_get(v___x_3362_, 1);
lean_inc(v_v_3480_);
lean_dec_ref(v___x_3362_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 3, v_r_3356_);
v___x_3482_ = v___x_3436_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_size_3352_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_3353_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_3354_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_r_3356_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_r_3356_);
v___x_3482_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_unsigned_to_nat(2u);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v___x_3482_);
lean_ctor_set(v___x_3360_, 3, v_r_3356_);
lean_ctor_set(v___x_3360_, 2, v_v_3480_);
lean_ctor_set(v___x_3360_, 1, v_k_3479_);
lean_ctor_set(v___x_3360_, 0, v___x_3483_);
v___x_3485_ = v___x_3360_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_3479_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_3480_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_r_3356_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v___x_3482_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
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
lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3652_; 
lean_inc(v_r_3356_);
lean_inc(v_v_3354_);
lean_inc(v_k_3353_);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; lean_object* v_unused_3654_; lean_object* v_unused_3655_; lean_object* v_unused_3656_; lean_object* v_unused_3657_; 
v_unused_3653_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3654_);
v_unused_3655_ = lean_ctor_get(v_r_3177_, 2);
lean_dec(v_unused_3655_);
v_unused_3656_ = lean_ctor_get(v_r_3177_, 1);
lean_dec(v_unused_3656_);
v_unused_3657_ = lean_ctor_get(v_r_3177_, 0);
lean_dec(v_unused_3657_);
v___x_3501_ = v_r_3177_;
v_isShared_3502_ = v_isSharedCheck_3652_;
goto v_resetjp_3500_;
}
else
{
lean_dec(v_r_3177_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3652_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v_tree_3504_; 
v___x_3503_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3353_, v_v_3354_, v_l_3355_, v_r_3356_);
v_tree_3504_ = lean_ctor_get(v___x_3503_, 2);
lean_inc(v_tree_3504_);
if (lean_obj_tag(v_tree_3504_) == 0)
{
lean_object* v_k_3505_; lean_object* v_v_3506_; lean_object* v_size_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v_k_3505_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_k_3505_);
v_v_3506_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_v_3506_);
lean_dec_ref(v___x_3503_);
v_size_3507_ = lean_ctor_get(v_tree_3504_, 0);
v___x_3508_ = lean_unsigned_to_nat(3u);
v___x_3509_ = lean_nat_mul(v___x_3508_, v_size_3507_);
v___x_3510_ = lean_nat_dec_lt(v___x_3509_, v_size_3347_);
lean_dec(v___x_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
lean_dec(v_r_3351_);
v___x_3511_ = lean_nat_add(v___x_3357_, v_size_3347_);
v___x_3512_ = lean_nat_add(v___x_3511_, v_size_3507_);
lean_dec(v___x_3511_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_tree_3504_);
lean_ctor_set(v___x_3501_, 3, v_l_3176_);
lean_ctor_set(v___x_3501_, 2, v_v_3506_);
lean_ctor_set(v___x_3501_, 1, v_k_3505_);
lean_ctor_set(v___x_3501_, 0, v___x_3512_);
v___x_3514_ = v___x_3501_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3505_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3506_);
lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_tree_3504_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
else
{
lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3581_; 
lean_inc(v_l_3350_);
lean_inc(v_v_3349_);
lean_inc(v_k_3348_);
lean_inc(v_size_3347_);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; lean_object* v_unused_3583_; lean_object* v_unused_3584_; lean_object* v_unused_3585_; lean_object* v_unused_3586_; 
v_unused_3582_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3582_);
v_unused_3583_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3583_);
v_unused_3584_ = lean_ctor_get(v_l_3176_, 2);
lean_dec(v_unused_3584_);
v_unused_3585_ = lean_ctor_get(v_l_3176_, 1);
lean_dec(v_unused_3585_);
v_unused_3586_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3586_);
v___x_3517_ = v_l_3176_;
v_isShared_3518_ = v_isSharedCheck_3581_;
goto v_resetjp_3516_;
}
else
{
lean_dec(v_l_3176_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3581_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_size_3519_; lean_object* v_size_3520_; lean_object* v_k_3521_; lean_object* v_v_3522_; lean_object* v_l_3523_; lean_object* v_r_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_size_3519_ = lean_ctor_get(v_l_3350_, 0);
v_size_3520_ = lean_ctor_get(v_r_3351_, 0);
v_k_3521_ = lean_ctor_get(v_r_3351_, 1);
v_v_3522_ = lean_ctor_get(v_r_3351_, 2);
v_l_3523_ = lean_ctor_get(v_r_3351_, 3);
v_r_3524_ = lean_ctor_get(v_r_3351_, 4);
v___x_3525_ = lean_unsigned_to_nat(2u);
v___x_3526_ = lean_nat_mul(v___x_3525_, v_size_3519_);
v___x_3527_ = lean_nat_dec_lt(v_size_3520_, v___x_3526_);
lean_dec(v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3565_; 
lean_inc(v_r_3524_);
lean_inc(v_l_3523_);
lean_inc(v_v_3522_);
lean_inc(v_k_3521_);
lean_del_object(v___x_3517_);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_r_3351_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; lean_object* v_unused_3567_; lean_object* v_unused_3568_; lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3566_ = lean_ctor_get(v_r_3351_, 4);
lean_dec(v_unused_3566_);
v_unused_3567_ = lean_ctor_get(v_r_3351_, 3);
lean_dec(v_unused_3567_);
v_unused_3568_ = lean_ctor_get(v_r_3351_, 2);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v_r_3351_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_r_3351_, 0);
lean_dec(v_unused_3570_);
v___x_3529_ = v_r_3351_;
v_isShared_3530_ = v_isSharedCheck_3565_;
goto v_resetjp_3528_;
}
else
{
lean_dec(v_r_3351_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3565_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___x_3553_; lean_object* v___y_3555_; 
v___x_3531_ = lean_nat_add(v___x_3357_, v_size_3347_);
lean_dec(v_size_3347_);
v___x_3532_ = lean_nat_add(v___x_3531_, v_size_3507_);
lean_dec(v___x_3531_);
v___x_3553_ = lean_nat_add(v___x_3357_, v_size_3519_);
if (lean_obj_tag(v_l_3523_) == 0)
{
lean_object* v_size_3563_; 
v_size_3563_ = lean_ctor_get(v_l_3523_, 0);
lean_inc(v_size_3563_);
v___y_3555_ = v_size_3563_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_unsigned_to_nat(0u);
v___y_3555_ = v___x_3564_;
goto v___jp_3554_;
}
v___jp_3533_:
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3537_ = lean_nat_add(v___y_3534_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec(v___y_3534_);
lean_inc_ref(v_tree_3504_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 4, v_tree_3504_);
lean_ctor_set(v___x_3529_, 3, v_r_3524_);
lean_ctor_set(v___x_3529_, 2, v_v_3506_);
lean_ctor_set(v___x_3529_, 1, v_k_3505_);
lean_ctor_set(v___x_3529_, 0, v___x_3537_);
v___x_3539_ = v___x_3529_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_k_3505_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_v_3506_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_r_3524_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_tree_3504_);
v___x_3539_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
v_isSharedCheck_3546_ = !lean_is_exclusive(v_tree_3504_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; lean_object* v_unused_3550_; lean_object* v_unused_3551_; 
v_unused_3547_ = lean_ctor_get(v_tree_3504_, 4);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_tree_3504_, 3);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_tree_3504_, 2);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_tree_3504_, 1);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_tree_3504_, 0);
lean_dec(v_unused_3551_);
v___x_3541_ = v_tree_3504_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_dec(v_tree_3504_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v___x_3539_);
lean_ctor_set(v___x_3541_, 3, v___y_3535_);
lean_ctor_set(v___x_3541_, 2, v_v_3522_);
lean_ctor_set(v___x_3541_, 1, v_k_3521_);
lean_ctor_set(v___x_3541_, 0, v___x_3532_);
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_k_3521_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_v_3522_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v___y_3535_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v___x_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
v___jp_3554_:
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3556_ = lean_nat_add(v___x_3553_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec(v___x_3553_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_l_3523_);
lean_ctor_set(v___x_3501_, 3, v_l_3350_);
lean_ctor_set(v___x_3501_, 2, v_v_3349_);
lean_ctor_set(v___x_3501_, 1, v_k_3348_);
lean_ctor_set(v___x_3501_, 0, v___x_3556_);
v___x_3558_ = v___x_3501_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_k_3348_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_v_3349_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v_l_3350_);
lean_ctor_set(v_reuseFailAlloc_3562_, 4, v_l_3523_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_nat_add(v___x_3357_, v_size_3507_);
if (lean_obj_tag(v_r_3524_) == 0)
{
lean_object* v_size_3560_; 
v_size_3560_ = lean_ctor_get(v_r_3524_, 0);
lean_inc(v_size_3560_);
v___y_3534_ = v___x_3559_;
v___y_3535_ = v___x_3558_;
v___y_3536_ = v_size_3560_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_unsigned_to_nat(0u);
v___y_3534_ = v___x_3559_;
v___y_3535_ = v___x_3558_;
v___y_3536_ = v___x_3561_;
goto v___jp_3533_;
}
}
}
}
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3571_ = lean_nat_add(v___x_3357_, v_size_3347_);
lean_dec(v_size_3347_);
v___x_3572_ = lean_nat_add(v___x_3571_, v_size_3507_);
lean_dec(v___x_3571_);
v___x_3573_ = lean_nat_add(v___x_3357_, v_size_3507_);
v___x_3574_ = lean_nat_add(v___x_3573_, v_size_3520_);
lean_dec(v___x_3573_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_tree_3504_);
lean_ctor_set(v___x_3501_, 3, v_r_3351_);
lean_ctor_set(v___x_3501_, 2, v_v_3506_);
lean_ctor_set(v___x_3501_, 1, v_k_3505_);
lean_ctor_set(v___x_3501_, 0, v___x_3574_);
v___x_3576_ = v___x_3501_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_k_3505_);
lean_ctor_set(v_reuseFailAlloc_3580_, 2, v_v_3506_);
lean_ctor_set(v_reuseFailAlloc_3580_, 3, v_r_3351_);
lean_ctor_set(v_reuseFailAlloc_3580_, 4, v_tree_3504_);
v___x_3576_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 4, v___x_3576_);
lean_ctor_set(v___x_3517_, 0, v___x_3572_);
v___x_3578_ = v___x_3517_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_k_3348_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_v_3349_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_l_3350_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3350_) == 0)
{
lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3610_; 
lean_inc_ref(v_l_3350_);
lean_inc(v_v_3349_);
lean_inc(v_k_3348_);
lean_inc(v_size_3347_);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; lean_object* v_unused_3612_; lean_object* v_unused_3613_; lean_object* v_unused_3614_; lean_object* v_unused_3615_; 
v_unused_3611_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3611_);
v_unused_3612_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_l_3176_, 2);
lean_dec(v_unused_3613_);
v_unused_3614_ = lean_ctor_get(v_l_3176_, 1);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3615_);
v___x_3588_ = v_l_3176_;
v_isShared_3589_ = v_isSharedCheck_3610_;
goto v_resetjp_3587_;
}
else
{
lean_dec(v_l_3176_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3610_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
if (lean_obj_tag(v_r_3351_) == 0)
{
lean_object* v_k_3590_; lean_object* v_v_3591_; lean_object* v_size_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v_k_3590_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_k_3590_);
v_v_3591_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_v_3591_);
lean_dec_ref(v___x_3503_);
v_size_3592_ = lean_ctor_get(v_r_3351_, 0);
v___x_3593_ = lean_nat_add(v___x_3357_, v_size_3347_);
lean_dec(v_size_3347_);
v___x_3594_ = lean_nat_add(v___x_3357_, v_size_3592_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_tree_3504_);
lean_ctor_set(v___x_3501_, 3, v_r_3351_);
lean_ctor_set(v___x_3501_, 2, v_v_3591_);
lean_ctor_set(v___x_3501_, 1, v_k_3590_);
lean_ctor_set(v___x_3501_, 0, v___x_3594_);
v___x_3596_ = v___x_3501_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_k_3590_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_v_3591_);
lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_r_3351_);
lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_tree_3504_);
v___x_3596_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3598_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_3596_);
lean_ctor_set(v___x_3588_, 0, v___x_3593_);
v___x_3598_ = v___x_3588_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_k_3348_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_v_3349_);
lean_ctor_set(v_reuseFailAlloc_3599_, 3, v_l_3350_);
lean_ctor_set(v_reuseFailAlloc_3599_, 4, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
else
{
lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec(v_size_3347_);
v_k_3601_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_k_3601_);
v_v_3602_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_v_3602_);
lean_dec_ref(v___x_3503_);
v___x_3603_ = lean_unsigned_to_nat(3u);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_r_3351_);
lean_ctor_set(v___x_3501_, 3, v_r_3351_);
lean_ctor_set(v___x_3501_, 2, v_v_3602_);
lean_ctor_set(v___x_3501_, 1, v_k_3601_);
lean_ctor_set(v___x_3501_, 0, v___x_3357_);
v___x_3605_ = v___x_3501_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3601_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3602_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_r_3351_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v_r_3351_);
v___x_3605_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_3605_);
lean_ctor_set(v___x_3588_, 0, v___x_3603_);
v___x_3607_ = v___x_3588_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_k_3348_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v_v_3349_);
lean_ctor_set(v_reuseFailAlloc_3608_, 3, v_l_3350_);
lean_ctor_set(v_reuseFailAlloc_3608_, 4, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3351_) == 0)
{
lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3640_; 
lean_inc(v_l_3350_);
lean_inc(v_v_3349_);
lean_inc(v_k_3348_);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_l_3176_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; lean_object* v_unused_3642_; lean_object* v_unused_3643_; lean_object* v_unused_3644_; lean_object* v_unused_3645_; 
v_unused_3641_ = lean_ctor_get(v_l_3176_, 4);
lean_dec(v_unused_3641_);
v_unused_3642_ = lean_ctor_get(v_l_3176_, 3);
lean_dec(v_unused_3642_);
v_unused_3643_ = lean_ctor_get(v_l_3176_, 2);
lean_dec(v_unused_3643_);
v_unused_3644_ = lean_ctor_get(v_l_3176_, 1);
lean_dec(v_unused_3644_);
v_unused_3645_ = lean_ctor_get(v_l_3176_, 0);
lean_dec(v_unused_3645_);
v___x_3617_ = v_l_3176_;
v_isShared_3618_ = v_isSharedCheck_3640_;
goto v_resetjp_3616_;
}
else
{
lean_dec(v_l_3176_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3640_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v_k_3619_; lean_object* v_v_3620_; lean_object* v_k_3621_; lean_object* v_v_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3636_; 
v_k_3619_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_k_3619_);
v_v_3620_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_v_3620_);
lean_dec_ref(v___x_3503_);
v_k_3621_ = lean_ctor_get(v_r_3351_, 1);
v_v_3622_ = lean_ctor_get(v_r_3351_, 2);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_r_3351_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; lean_object* v_unused_3638_; lean_object* v_unused_3639_; 
v_unused_3637_ = lean_ctor_get(v_r_3351_, 4);
lean_dec(v_unused_3637_);
v_unused_3638_ = lean_ctor_get(v_r_3351_, 3);
lean_dec(v_unused_3638_);
v_unused_3639_ = lean_ctor_get(v_r_3351_, 0);
lean_dec(v_unused_3639_);
v___x_3624_ = v_r_3351_;
v_isShared_3625_ = v_isSharedCheck_3636_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_v_3622_);
lean_inc(v_k_3621_);
lean_dec(v_r_3351_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3636_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = lean_unsigned_to_nat(3u);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_l_3350_);
lean_ctor_set(v___x_3624_, 3, v_l_3350_);
lean_ctor_set(v___x_3624_, 2, v_v_3349_);
lean_ctor_set(v___x_3624_, 1, v_k_3348_);
lean_ctor_set(v___x_3624_, 0, v___x_3357_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_k_3348_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_v_3349_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_l_3350_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_l_3350_);
v___x_3628_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3630_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_l_3350_);
lean_ctor_set(v___x_3501_, 3, v_l_3350_);
lean_ctor_set(v___x_3501_, 2, v_v_3620_);
lean_ctor_set(v___x_3501_, 1, v_k_3619_);
lean_ctor_set(v___x_3501_, 0, v___x_3357_);
v___x_3630_ = v___x_3501_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_l_3350_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_l_3350_);
v___x_3630_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 4, v___x_3630_);
lean_ctor_set(v___x_3617_, 3, v___x_3628_);
lean_ctor_set(v___x_3617_, 2, v_v_3622_);
lean_ctor_set(v___x_3617_, 1, v_k_3621_);
lean_ctor_set(v___x_3617_, 0, v___x_3626_);
v___x_3632_ = v___x_3617_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_k_3621_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_v_3622_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
}
else
{
lean_object* v_k_3646_; lean_object* v_v_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v_k_3646_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_k_3646_);
v_v_3647_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_v_3647_);
lean_dec_ref(v___x_3503_);
v___x_3648_ = lean_unsigned_to_nat(2u);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_r_3351_);
lean_ctor_set(v___x_3501_, 3, v_l_3176_);
lean_ctor_set(v___x_3501_, 2, v_v_3647_);
lean_ctor_set(v___x_3501_, 1, v_k_3646_);
lean_ctor_set(v___x_3501_, 0, v___x_3648_);
v___x_3650_ = v___x_3501_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3646_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3647_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_r_3351_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
}
}
else
{
return v_l_3176_;
}
}
else
{
return v_r_3177_;
}
}
}
else
{
lean_object* v_impl_3658_; lean_object* v___x_3659_; 
v_impl_3658_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3172_, v_l_3176_);
v___x_3659_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3658_) == 0)
{
if (lean_obj_tag(v_r_3177_) == 0)
{
lean_object* v_size_3660_; lean_object* v_size_3661_; lean_object* v_k_3662_; lean_object* v_v_3663_; lean_object* v_l_3664_; lean_object* v_r_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; 
v_size_3660_ = lean_ctor_get(v_impl_3658_, 0);
v_size_3661_ = lean_ctor_get(v_r_3177_, 0);
v_k_3662_ = lean_ctor_get(v_r_3177_, 1);
v_v_3663_ = lean_ctor_get(v_r_3177_, 2);
v_l_3664_ = lean_ctor_get(v_r_3177_, 3);
lean_inc(v_l_3664_);
v_r_3665_ = lean_ctor_get(v_r_3177_, 4);
v___x_3666_ = lean_unsigned_to_nat(3u);
v___x_3667_ = lean_nat_mul(v___x_3666_, v_size_3660_);
v___x_3668_ = lean_nat_dec_lt(v___x_3667_, v_size_3661_);
lean_dec(v___x_3667_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
lean_dec(v_l_3664_);
v___x_3669_ = lean_nat_add(v___x_3659_, v_size_3660_);
v___x_3670_ = lean_nat_add(v___x_3669_, v_size_3661_);
lean_dec(v___x_3669_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 3, v_impl_3658_);
lean_ctor_set(v___x_3179_, 0, v___x_3670_);
v___x_3672_ = v___x_3179_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_impl_3658_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_r_3177_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
else
{
lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3737_; 
lean_inc(v_r_3665_);
lean_inc(v_v_3663_);
lean_inc(v_k_3662_);
lean_inc(v_size_3661_);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3738_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_r_3177_, 2);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_r_3177_, 1);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_r_3177_, 0);
lean_dec(v_unused_3742_);
v___x_3675_ = v_r_3177_;
v_isShared_3676_ = v_isSharedCheck_3737_;
goto v_resetjp_3674_;
}
else
{
lean_dec(v_r_3177_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3737_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v_size_3677_; lean_object* v_k_3678_; lean_object* v_v_3679_; lean_object* v_l_3680_; lean_object* v_r_3681_; lean_object* v_size_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_size_3677_ = lean_ctor_get(v_l_3664_, 0);
v_k_3678_ = lean_ctor_get(v_l_3664_, 1);
v_v_3679_ = lean_ctor_get(v_l_3664_, 2);
v_l_3680_ = lean_ctor_get(v_l_3664_, 3);
v_r_3681_ = lean_ctor_get(v_l_3664_, 4);
v_size_3682_ = lean_ctor_get(v_r_3665_, 0);
v___x_3683_ = lean_unsigned_to_nat(2u);
v___x_3684_ = lean_nat_mul(v___x_3683_, v_size_3682_);
v___x_3685_ = lean_nat_dec_lt(v_size_3677_, v___x_3684_);
lean_dec(v___x_3684_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3713_; 
lean_inc(v_r_3681_);
lean_inc(v_l_3680_);
lean_inc(v_v_3679_);
lean_inc(v_k_3678_);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_l_3664_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; 
v_unused_3714_ = lean_ctor_get(v_l_3664_, 4);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_l_3664_, 3);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_l_3664_, 2);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_l_3664_, 1);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_l_3664_, 0);
lean_dec(v_unused_3718_);
v___x_3687_ = v_l_3664_;
v_isShared_3688_ = v_isSharedCheck_3713_;
goto v_resetjp_3686_;
}
else
{
lean_dec(v_l_3664_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3713_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3703_; 
v___x_3689_ = lean_nat_add(v___x_3659_, v_size_3660_);
v___x_3690_ = lean_nat_add(v___x_3689_, v_size_3661_);
lean_dec(v_size_3661_);
if (lean_obj_tag(v_l_3680_) == 0)
{
lean_object* v_size_3711_; 
v_size_3711_ = lean_ctor_get(v_l_3680_, 0);
lean_inc(v_size_3711_);
v___y_3703_ = v_size_3711_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___y_3703_ = v___x_3712_;
goto v___jp_3702_;
}
v___jp_3691_:
{
lean_object* v___x_3695_; lean_object* v___x_3697_; 
v___x_3695_ = lean_nat_add(v___y_3692_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec(v___y_3692_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 4, v_r_3665_);
lean_ctor_set(v___x_3687_, 3, v_r_3681_);
lean_ctor_set(v___x_3687_, 2, v_v_3663_);
lean_ctor_set(v___x_3687_, 1, v_k_3662_);
lean_ctor_set(v___x_3687_, 0, v___x_3695_);
v___x_3697_ = v___x_3687_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_k_3662_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v_v_3663_);
lean_ctor_set(v_reuseFailAlloc_3701_, 3, v_r_3681_);
lean_ctor_set(v_reuseFailAlloc_3701_, 4, v_r_3665_);
v___x_3697_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3699_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 4, v___x_3697_);
lean_ctor_set(v___x_3675_, 3, v___y_3693_);
lean_ctor_set(v___x_3675_, 2, v_v_3679_);
lean_ctor_set(v___x_3675_, 1, v_k_3678_);
lean_ctor_set(v___x_3675_, 0, v___x_3690_);
v___x_3699_ = v___x_3675_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v___y_3693_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
v___jp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_nat_add(v___x_3689_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec(v___x_3689_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_l_3680_);
lean_ctor_set(v___x_3179_, 3, v_impl_3658_);
lean_ctor_set(v___x_3179_, 0, v___x_3704_);
v___x_3706_ = v___x_3179_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_impl_3658_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_l_3680_);
v___x_3706_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_nat_add(v___x_3659_, v_size_3682_);
if (lean_obj_tag(v_r_3681_) == 0)
{
lean_object* v_size_3708_; 
v_size_3708_ = lean_ctor_get(v_r_3681_, 0);
lean_inc(v_size_3708_);
v___y_3692_ = v___x_3707_;
v___y_3693_ = v___x_3706_;
v___y_3694_ = v_size_3708_;
goto v___jp_3691_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v___y_3692_ = v___x_3707_;
v___y_3693_ = v___x_3706_;
v___y_3694_ = v___x_3709_;
goto v___jp_3691_;
}
}
}
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
lean_del_object(v___x_3179_);
v___x_3719_ = lean_nat_add(v___x_3659_, v_size_3660_);
v___x_3720_ = lean_nat_add(v___x_3719_, v_size_3661_);
lean_dec(v_size_3661_);
v___x_3721_ = lean_nat_add(v___x_3719_, v_size_3677_);
lean_dec(v___x_3719_);
lean_inc_ref(v_impl_3658_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 4, v_l_3664_);
lean_ctor_set(v___x_3675_, 3, v_impl_3658_);
lean_ctor_set(v___x_3675_, 2, v_v_3175_);
lean_ctor_set(v___x_3675_, 1, v_k_3174_);
lean_ctor_set(v___x_3675_, 0, v___x_3721_);
v___x_3723_ = v___x_3675_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_impl_3658_);
lean_ctor_set(v_reuseFailAlloc_3736_, 4, v_l_3664_);
v___x_3723_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
v_isSharedCheck_3730_ = !lean_is_exclusive(v_impl_3658_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; 
v_unused_3731_ = lean_ctor_get(v_impl_3658_, 4);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_impl_3658_, 3);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_impl_3658_, 2);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_impl_3658_, 1);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_impl_3658_, 0);
lean_dec(v_unused_3735_);
v___x_3725_ = v_impl_3658_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_dec(v_impl_3658_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 4, v_r_3665_);
lean_ctor_set(v___x_3725_, 3, v___x_3723_);
lean_ctor_set(v___x_3725_, 2, v_v_3663_);
lean_ctor_set(v___x_3725_, 1, v_k_3662_);
lean_ctor_set(v___x_3725_, 0, v___x_3720_);
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3662_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3663_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_r_3665_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v_size_3743_ = lean_ctor_get(v_impl_3658_, 0);
v___x_3744_ = lean_nat_add(v___x_3659_, v_size_3743_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 3, v_impl_3658_);
lean_ctor_set(v___x_3179_, 0, v___x_3744_);
v___x_3746_ = v___x_3179_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_impl_3658_);
lean_ctor_set(v_reuseFailAlloc_3747_, 4, v_r_3177_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
else
{
if (lean_obj_tag(v_r_3177_) == 0)
{
lean_object* v_l_3748_; 
v_l_3748_ = lean_ctor_get(v_r_3177_, 3);
lean_inc(v_l_3748_);
if (lean_obj_tag(v_l_3748_) == 0)
{
lean_object* v_r_3749_; 
v_r_3749_ = lean_ctor_get(v_r_3177_, 4);
lean_inc(v_r_3749_);
if (lean_obj_tag(v_r_3749_) == 0)
{
lean_object* v_size_3750_; lean_object* v_k_3751_; lean_object* v_v_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3765_; 
v_size_3750_ = lean_ctor_get(v_r_3177_, 0);
v_k_3751_ = lean_ctor_get(v_r_3177_, 1);
v_v_3752_ = lean_ctor_get(v_r_3177_, 2);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; lean_object* v_unused_3767_; 
v_unused_3766_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3767_);
v___x_3754_ = v_r_3177_;
v_isShared_3755_ = v_isSharedCheck_3765_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_v_3752_);
lean_inc(v_k_3751_);
lean_inc(v_size_3750_);
lean_dec(v_r_3177_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3765_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_size_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v_size_3756_ = lean_ctor_get(v_l_3748_, 0);
v___x_3757_ = lean_nat_add(v___x_3659_, v_size_3750_);
lean_dec(v_size_3750_);
v___x_3758_ = lean_nat_add(v___x_3659_, v_size_3756_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 4, v_l_3748_);
lean_ctor_set(v___x_3754_, 3, v_impl_3658_);
lean_ctor_set(v___x_3754_, 2, v_v_3175_);
lean_ctor_set(v___x_3754_, 1, v_k_3174_);
lean_ctor_set(v___x_3754_, 0, v___x_3758_);
v___x_3760_ = v___x_3754_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_impl_3658_);
lean_ctor_set(v_reuseFailAlloc_3764_, 4, v_l_3748_);
v___x_3760_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_r_3749_);
lean_ctor_set(v___x_3179_, 3, v___x_3760_);
lean_ctor_set(v___x_3179_, 2, v_v_3752_);
lean_ctor_set(v___x_3179_, 1, v_k_3751_);
lean_ctor_set(v___x_3179_, 0, v___x_3757_);
v___x_3762_ = v___x_3179_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_k_3751_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_v_3752_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_r_3749_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v_k_3768_; lean_object* v_v_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3792_; 
v_k_3768_ = lean_ctor_get(v_r_3177_, 1);
v_v_3769_ = lean_ctor_get(v_r_3177_, 2);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; lean_object* v_unused_3794_; lean_object* v_unused_3795_; 
v_unused_3793_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3794_);
v_unused_3795_ = lean_ctor_get(v_r_3177_, 0);
lean_dec(v_unused_3795_);
v___x_3771_ = v_r_3177_;
v_isShared_3772_ = v_isSharedCheck_3792_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_v_3769_);
lean_inc(v_k_3768_);
lean_dec(v_r_3177_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3792_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_k_3773_; lean_object* v_v_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3788_; 
v_k_3773_ = lean_ctor_get(v_l_3748_, 1);
v_v_3774_ = lean_ctor_get(v_l_3748_, 2);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_l_3748_);
if (v_isSharedCheck_3788_ == 0)
{
lean_object* v_unused_3789_; lean_object* v_unused_3790_; lean_object* v_unused_3791_; 
v_unused_3789_ = lean_ctor_get(v_l_3748_, 4);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_l_3748_, 3);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_l_3748_, 0);
lean_dec(v_unused_3791_);
v___x_3776_ = v_l_3748_;
v_isShared_3777_ = v_isSharedCheck_3788_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_v_3774_);
lean_inc(v_k_3773_);
lean_dec(v_l_3748_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3788_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
v___x_3778_ = lean_unsigned_to_nat(3u);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 4, v_r_3749_);
lean_ctor_set(v___x_3776_, 3, v_r_3749_);
lean_ctor_set(v___x_3776_, 2, v_v_3175_);
lean_ctor_set(v___x_3776_, 1, v_k_3174_);
lean_ctor_set(v___x_3776_, 0, v___x_3659_);
v___x_3780_ = v___x_3776_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3787_, 3, v_r_3749_);
lean_ctor_set(v_reuseFailAlloc_3787_, 4, v_r_3749_);
v___x_3780_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3782_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 3, v_r_3749_);
lean_ctor_set(v___x_3771_, 0, v___x_3659_);
v___x_3782_ = v___x_3771_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_k_3768_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_v_3769_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_r_3749_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_r_3749_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___x_3782_);
lean_ctor_set(v___x_3179_, 3, v___x_3780_);
lean_ctor_set(v___x_3179_, 2, v_v_3774_);
lean_ctor_set(v___x_3179_, 1, v_k_3773_);
lean_ctor_set(v___x_3179_, 0, v___x_3778_);
v___x_3784_ = v___x_3179_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3785_, 4, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3796_; 
v_r_3796_ = lean_ctor_get(v_r_3177_, 4);
lean_inc(v_r_3796_);
if (lean_obj_tag(v_r_3796_) == 0)
{
lean_object* v_k_3797_; lean_object* v_v_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3809_; 
v_k_3797_ = lean_ctor_get(v_r_3177_, 1);
v_v_3798_ = lean_ctor_get(v_r_3177_, 2);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; 
v_unused_3810_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_r_3177_, 0);
lean_dec(v_unused_3812_);
v___x_3800_ = v_r_3177_;
v_isShared_3801_ = v_isSharedCheck_3809_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_v_3798_);
lean_inc(v_k_3797_);
lean_dec(v_r_3177_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3809_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3802_ = lean_unsigned_to_nat(3u);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 4, v_l_3748_);
lean_ctor_set(v___x_3800_, 2, v_v_3175_);
lean_ctor_set(v___x_3800_, 1, v_k_3174_);
lean_ctor_set(v___x_3800_, 0, v___x_3659_);
v___x_3804_ = v___x_3800_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3808_, 3, v_l_3748_);
lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_l_3748_);
v___x_3804_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3806_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v_r_3796_);
lean_ctor_set(v___x_3179_, 3, v___x_3804_);
lean_ctor_set(v___x_3179_, 2, v_v_3798_);
lean_ctor_set(v___x_3179_, 1, v_k_3797_);
lean_ctor_set(v___x_3179_, 0, v___x_3802_);
v___x_3806_ = v___x_3179_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_k_3797_);
lean_ctor_set(v_reuseFailAlloc_3807_, 2, v_v_3798_);
lean_ctor_set(v_reuseFailAlloc_3807_, 3, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3807_, 4, v_r_3796_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v_size_3813_; lean_object* v_k_3814_; lean_object* v_v_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3826_; 
v_size_3813_ = lean_ctor_get(v_r_3177_, 0);
v_k_3814_ = lean_ctor_get(v_r_3177_, 1);
v_v_3815_ = lean_ctor_get(v_r_3177_, 2);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_r_3177_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; lean_object* v_unused_3828_; 
v_unused_3827_ = lean_ctor_get(v_r_3177_, 4);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_r_3177_, 3);
lean_dec(v_unused_3828_);
v___x_3817_ = v_r_3177_;
v_isShared_3818_ = v_isSharedCheck_3826_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_v_3815_);
lean_inc(v_k_3814_);
lean_inc(v_size_3813_);
lean_dec(v_r_3177_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3826_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 3, v_r_3796_);
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_size_3813_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_k_3814_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_v_3815_);
lean_ctor_set(v_reuseFailAlloc_3825_, 3, v_r_3796_);
lean_ctor_set(v_reuseFailAlloc_3825_, 4, v_r_3796_);
v___x_3820_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3821_ = lean_unsigned_to_nat(2u);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 4, v___x_3820_);
lean_ctor_set(v___x_3179_, 3, v_r_3796_);
lean_ctor_set(v___x_3179_, 0, v___x_3821_);
v___x_3823_ = v___x_3179_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_r_3796_);
lean_ctor_set(v_reuseFailAlloc_3824_, 4, v___x_3820_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
}
else
{
lean_object* v___x_3830_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 3, v_r_3177_);
lean_ctor_set(v___x_3179_, 0, v___x_3659_);
v___x_3830_ = v___x_3179_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_r_3177_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v_r_3177_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
else
{
return v_t_3173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3834_, lean_object* v_t_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3834_, v_t_3835_);
lean_dec(v_k_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3837_, lean_object* v_j_3838_){
_start:
{
lean_object* v_vars_3839_; lean_object* v_jps_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3848_; 
v_vars_3839_ = lean_ctor_get(v_ctx_3837_, 0);
v_jps_3840_ = lean_ctor_get(v_ctx_3837_, 1);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_ctx_3837_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3842_ = v_ctx_3837_;
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_jps_3840_);
lean_inc(v_vars_3839_);
lean_dec(v_ctx_3837_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3848_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3844_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3838_, v_jps_3840_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 1, v___x_3844_);
v___x_3846_ = v___x_3842_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_vars_3839_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3849_, lean_object* v_j_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3849_, v_j_3850_);
lean_dec(v_j_3850_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3852_, lean_object* v_k_3853_, lean_object* v_t_3854_, lean_object* v_h_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3853_, v_t_3854_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3857_, lean_object* v_k_3858_, lean_object* v_t_3859_, lean_object* v_h_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3857_, v_k_3858_, v_t_3859_, v_h_3860_);
lean_dec(v_k_3858_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3862_, lean_object* v_x_3863_){
_start:
{
lean_object* v_vars_3864_; lean_object* v___x_3865_; 
v_vars_3864_ = lean_ctor_get(v_ctx_3862_, 0);
v___x_3865_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3864_, v_x_3863_);
if (lean_obj_tag(v___x_3865_) == 1)
{
lean_object* v_val_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3874_; 
v_val_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_val_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_a_3870_; lean_object* v___x_3872_; 
v_a_3870_ = lean_ctor_get(v_val_3866_, 0);
lean_inc(v_a_3870_);
lean_dec(v_val_3866_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v_a_3870_);
v___x_3872_ = v___x_3868_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
else
{
lean_object* v___x_3875_; 
lean_dec(v___x_3865_);
v___x_3875_ = lean_box(0);
return v___x_3875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3876_, lean_object* v_x_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_IR_LocalContext_getType(v_ctx_3876_, v_x_3877_);
lean_dec(v_x_3877_);
lean_dec_ref(v_ctx_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3879_, lean_object* v_x_3880_){
_start:
{
lean_object* v_vars_3881_; lean_object* v___x_3882_; 
v_vars_3881_ = lean_ctor_get(v_ctx_3879_, 0);
v___x_3882_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3881_, v_x_3880_);
if (lean_obj_tag(v___x_3882_) == 1)
{
lean_object* v_val_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3892_; 
v_val_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3892_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_val_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3892_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
if (lean_obj_tag(v_val_3883_) == 1)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; 
v_a_3887_ = lean_ctor_get(v_val_3883_, 1);
lean_inc(v_a_3887_);
lean_dec_ref_known(v_val_3883_, 2);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v_a_3887_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
else
{
lean_object* v___x_3891_; 
lean_del_object(v___x_3885_);
lean_dec(v_val_3883_);
v___x_3891_ = lean_box(0);
return v___x_3891_;
}
}
}
else
{
lean_object* v___x_3893_; 
lean_dec(v___x_3882_);
v___x_3893_ = lean_box(0);
return v___x_3893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_IR_LocalContext_getValue(v_ctx_3894_, v_x_3895_);
lean_dec(v_x_3895_);
lean_dec_ref(v_ctx_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3897_, lean_object* v_v_u2081_3898_, lean_object* v_v_u2082_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_00_u03c1_3897_, v_v_u2081_3898_);
if (lean_obj_tag(v___x_3900_) == 0)
{
uint8_t v___x_3901_; 
v___x_3901_ = lean_nat_dec_eq(v_v_u2081_3898_, v_v_u2082_3899_);
return v___x_3901_;
}
else
{
lean_object* v_val_3902_; uint8_t v___x_3903_; 
v_val_3902_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3903_ = lean_nat_dec_eq(v_val_3902_, v_v_u2082_3899_);
lean_dec(v_val_3902_);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3904_, lean_object* v_v_u2081_3905_, lean_object* v_v_u2082_3906_){
_start:
{
uint8_t v_res_3907_; lean_object* v_r_3908_; 
v_res_3907_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3904_, v_v_u2081_3905_, v_v_u2082_3906_);
lean_dec(v_v_u2082_3906_);
lean_dec(v_v_u2081_3905_);
lean_dec(v_00_u03c1_3904_);
v_r_3908_ = lean_box(v_res_3907_);
return v_r_3908_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3911_, lean_object* v_x_3912_, lean_object* v_x_3913_){
_start:
{
if (lean_obj_tag(v_x_3912_) == 0)
{
if (lean_obj_tag(v_x_3913_) == 0)
{
lean_object* v_id_3914_; lean_object* v_id_3915_; uint8_t v___x_3916_; 
v_id_3914_ = lean_ctor_get(v_x_3912_, 0);
v_id_3915_ = lean_ctor_get(v_x_3913_, 0);
v___x_3916_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3911_, v_id_3914_, v_id_3915_);
return v___x_3916_;
}
else
{
uint8_t v___x_3917_; 
v___x_3917_ = 0;
return v___x_3917_;
}
}
else
{
if (lean_obj_tag(v_x_3913_) == 1)
{
uint8_t v___x_3918_; 
v___x_3918_ = 1;
return v___x_3918_;
}
else
{
uint8_t v___x_3919_; 
v___x_3919_ = 0;
return v___x_3919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_){
_start:
{
uint8_t v_res_3923_; lean_object* v_r_3924_; 
v_res_3923_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3920_, v_x_3921_, v_x_3922_);
lean_dec(v_x_3922_);
lean_dec(v_x_3921_);
lean_dec(v_00_u03c1_3920_);
v_r_3924_ = lean_box(v_res_3923_);
return v_r_3924_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3927_, lean_object* v_xs_3928_, lean_object* v_ys_3929_, lean_object* v_x_3930_){
_start:
{
lean_object* v_zero_3931_; uint8_t v_isZero_3932_; 
v_zero_3931_ = lean_unsigned_to_nat(0u);
v_isZero_3932_ = lean_nat_dec_eq(v_x_3930_, v_zero_3931_);
if (v_isZero_3932_ == 1)
{
lean_dec(v_x_3930_);
return v_isZero_3932_;
}
else
{
lean_object* v_one_3933_; lean_object* v_n_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v_one_3933_ = lean_unsigned_to_nat(1u);
v_n_3934_ = lean_nat_sub(v_x_3930_, v_one_3933_);
lean_dec(v_x_3930_);
v___x_3935_ = lean_array_fget_borrowed(v_xs_3928_, v_n_3934_);
v___x_3936_ = lean_array_fget_borrowed(v_ys_3929_, v_n_3934_);
v___x_3937_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3927_, v___x_3935_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_dec(v_n_3934_);
return v___x_3937_;
}
else
{
v_x_3930_ = v_n_3934_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3939_, lean_object* v_xs_3940_, lean_object* v_ys_3941_, lean_object* v_x_3942_){
_start:
{
uint8_t v_res_3943_; lean_object* v_r_3944_; 
v_res_3943_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3939_, v_xs_3940_, v_ys_3941_, v_x_3942_);
lean_dec_ref(v_ys_3941_);
lean_dec_ref(v_xs_3940_);
lean_dec(v_00_u03c1_3939_);
v_r_3944_ = lean_box(v_res_3943_);
return v_r_3944_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3945_, lean_object* v_args_u2081_3946_, lean_object* v_args_u2082_3947_){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3948_ = lean_array_get_size(v_args_u2081_3946_);
v___x_3949_ = lean_array_get_size(v_args_u2082_3947_);
v___x_3950_ = lean_nat_dec_eq(v___x_3948_, v___x_3949_);
if (v___x_3950_ == 0)
{
return v___x_3950_;
}
else
{
uint8_t v___x_3951_; 
v___x_3951_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3945_, v_args_u2081_3946_, v_args_u2082_3947_, v___x_3948_);
return v___x_3951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3952_, lean_object* v_args_u2081_3953_, lean_object* v_args_u2082_3954_){
_start:
{
uint8_t v_res_3955_; lean_object* v_r_3956_; 
v_res_3955_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3952_, v_args_u2081_3953_, v_args_u2082_3954_);
lean_dec_ref(v_args_u2082_3954_);
lean_dec_ref(v_args_u2081_3953_);
lean_dec(v_00_u03c1_3952_);
v_r_3956_ = lean_box(v_res_3955_);
return v_r_3956_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3957_, lean_object* v_xs_3958_, lean_object* v_ys_3959_, lean_object* v_hsz_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_){
_start:
{
uint8_t v___x_3963_; 
v___x_3963_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3957_, v_xs_3958_, v_ys_3959_, v_x_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3964_, lean_object* v_xs_3965_, lean_object* v_ys_3966_, lean_object* v_hsz_3967_, lean_object* v_x_3968_, lean_object* v_x_3969_){
_start:
{
uint8_t v_res_3970_; lean_object* v_r_3971_; 
v_res_3970_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3964_, v_xs_3965_, v_ys_3966_, v_hsz_3967_, v_x_3968_, v_x_3969_);
lean_dec_ref(v_ys_3966_);
lean_dec_ref(v_xs_3965_);
lean_dec(v_00_u03c1_3964_);
v_r_3971_ = lean_box(v_res_3970_);
return v_r_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3974_, lean_object* v_x_u2081_3975_, lean_object* v_x_u2082_3976_){
_start:
{
uint8_t v___x_3977_; 
v___x_3977_ = lean_nat_dec_eq(v_x_u2081_3975_, v_x_u2082_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3975_, v_x_u2082_3976_, v_00_u03c1_3974_);
return v___x_3978_;
}
else
{
lean_dec(v_x_u2082_3976_);
lean_dec(v_x_u2081_3975_);
return v_00_u03c1_3974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3979_, lean_object* v_p_u2081_3980_, lean_object* v_p_u2082_3981_){
_start:
{
lean_object* v_x_3982_; uint8_t v_borrow_3983_; lean_object* v_ty_3984_; lean_object* v_x_3985_; uint8_t v_borrow_3986_; lean_object* v_ty_3987_; uint8_t v___x_3991_; 
v_x_3982_ = lean_ctor_get(v_p_u2081_3980_, 0);
lean_inc(v_x_3982_);
v_borrow_3983_ = lean_ctor_get_uint8(v_p_u2081_3980_, sizeof(void*)*2);
v_ty_3984_ = lean_ctor_get(v_p_u2081_3980_, 1);
lean_inc(v_ty_3984_);
lean_dec_ref(v_p_u2081_3980_);
v_x_3985_ = lean_ctor_get(v_p_u2082_3981_, 0);
lean_inc(v_x_3985_);
v_borrow_3986_ = lean_ctor_get_uint8(v_p_u2082_3981_, sizeof(void*)*2);
v_ty_3987_ = lean_ctor_get(v_p_u2082_3981_, 1);
lean_inc(v_ty_3987_);
lean_dec_ref(v_p_u2082_3981_);
v___x_3991_ = l_Lean_IR_instBEqIRType_beq(v_ty_3984_, v_ty_3987_);
lean_dec(v_ty_3987_);
lean_dec(v_ty_3984_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
lean_dec(v_x_3985_);
lean_dec(v_x_3982_);
lean_dec(v_00_u03c1_3979_);
v___x_3992_ = lean_box(0);
return v___x_3992_;
}
else
{
if (v_borrow_3986_ == 0)
{
if (v_borrow_3983_ == 0)
{
goto v___jp_3988_;
}
else
{
lean_object* v___x_3993_; 
lean_dec(v_x_3985_);
lean_dec(v_x_3982_);
lean_dec(v_00_u03c1_3979_);
v___x_3993_ = lean_box(0);
return v___x_3993_;
}
}
else
{
if (v_borrow_3983_ == 0)
{
lean_object* v___x_3994_; 
lean_dec(v_x_3985_);
lean_dec(v_x_3982_);
lean_dec(v_00_u03c1_3979_);
v___x_3994_ = lean_box(0);
return v___x_3994_;
}
else
{
goto v___jp_3988_;
}
}
}
v___jp_3988_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = l_Lean_IR_addVarRename(v_00_u03c1_3979_, v_x_3982_, v_x_3985_);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3995_, lean_object* v_ps_u2081_3996_, lean_object* v_ps_u2082_3997_, lean_object* v_a_3998_, lean_object* v_b_3999_){
_start:
{
uint8_t v___x_4000_; 
v___x_4000_ = lean_nat_dec_lt(v_a_3998_, v_upperBound_3995_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
lean_dec(v_a_3998_);
v___x_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4001_, 0, v_b_3999_);
return v___x_4001_;
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4002_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_4003_ = lean_array_get_borrowed(v___x_4002_, v_ps_u2081_3996_, v_a_3998_);
v___x_4004_ = lean_array_get_borrowed(v___x_4002_, v_ps_u2082_3997_, v_a_3998_);
lean_inc(v___x_4004_);
lean_inc(v___x_4003_);
v___x_4005_ = l_Lean_IR_addParamRename(v_b_3999_, v___x_4003_, v___x_4004_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_dec(v_a_3998_);
return v___x_4005_;
}
else
{
lean_object* v_val_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_val_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_val_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v___x_4007_ = lean_unsigned_to_nat(1u);
v___x_4008_ = lean_nat_add(v_a_3998_, v___x_4007_);
lean_dec(v_a_3998_);
v_a_3998_ = v___x_4008_;
v_b_3999_ = v_val_4006_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_4010_, lean_object* v_ps_u2081_4011_, lean_object* v_ps_u2082_4012_, lean_object* v_a_4013_, lean_object* v_b_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_4010_, v_ps_u2081_4011_, v_ps_u2082_4012_, v_a_4013_, v_b_4014_);
lean_dec_ref(v_ps_u2082_4012_);
lean_dec_ref(v_ps_u2081_4011_);
lean_dec(v_upperBound_4010_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_4016_, lean_object* v_ps_u2081_4017_, lean_object* v_ps_u2082_4018_){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4019_ = lean_array_get_size(v_ps_u2081_4017_);
v___x_4020_ = lean_array_get_size(v_ps_u2082_4018_);
v___x_4021_ = lean_nat_dec_eq(v___x_4019_, v___x_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_dec(v_00_u03c1_4016_);
v___x_4022_ = lean_box(0);
return v___x_4022_;
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_unsigned_to_nat(0u);
v___x_4024_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_4019_, v_ps_u2081_4017_, v_ps_u2082_4018_, v___x_4023_, v_00_u03c1_4016_);
return v___x_4024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* v_00_u03c1_4025_, lean_object* v_ps_u2081_4026_, lean_object* v_ps_u2082_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_IR_addParamsRename(v_00_u03c1_4025_, v_ps_u2081_4026_, v_ps_u2082_4027_);
lean_dec_ref(v_ps_u2082_4027_);
lean_dec_ref(v_ps_u2081_4026_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object* v_upperBound_4029_, lean_object* v_ps_u2081_4030_, lean_object* v_ps_u2082_4031_, lean_object* v_inst_4032_, lean_object* v_R_4033_, lean_object* v_a_4034_, lean_object* v_b_4035_, lean_object* v_c_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_4029_, v_ps_u2081_4030_, v_ps_u2082_4031_, v_a_4034_, v_b_4035_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object* v_upperBound_4038_, lean_object* v_ps_u2081_4039_, lean_object* v_ps_u2082_4040_, lean_object* v_inst_4041_, lean_object* v_R_4042_, lean_object* v_a_4043_, lean_object* v_b_4044_, lean_object* v_c_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(v_upperBound_4038_, v_ps_u2081_4039_, v_ps_u2082_4040_, v_inst_4041_, v_R_4042_, v_a_4043_, v_b_4044_, v_c_4045_);
lean_dec_ref(v_ps_u2082_4040_);
lean_dec_ref(v_ps_u2081_4039_);
lean_dec(v_upperBound_4038_);
return v_res_4046_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* v_x_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_){
_start:
{
lean_object* v___y_4051_; lean_object* v___y_4052_; uint8_t v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4055_; lean_object* v_00_u03c1_4059_; lean_object* v_x_u2081_4060_; lean_object* v_n_u2081_4061_; uint8_t v_c_u2081_4062_; uint8_t v_p_u2081_4063_; lean_object* v_b_u2081_4064_; lean_object* v_x_u2082_4065_; lean_object* v_n_u2082_4066_; uint8_t v_c_u2082_4067_; uint8_t v_p_u2082_4068_; lean_object* v_b_u2082_4069_; lean_object* v_00_u03c1_4073_; lean_object* v_tgt_u2081_4074_; lean_object* v_b_u2081_4075_; uint64_t v_v_u2081_4076_; lean_object* v_tgt_u2082_4077_; lean_object* v_b_u2082_4078_; uint64_t v_v_u2082_4079_; lean_object* v_00_u03c1_4084_; lean_object* v_tgt_u2081_4085_; lean_object* v_b_u2081_4086_; lean_object* v_ty_u2081_4087_; lean_object* v_x_u2081_4088_; lean_object* v_tgt_u2082_4089_; lean_object* v_b_u2082_4090_; lean_object* v_ty_u2082_4091_; lean_object* v_x_u2082_4092_; lean_object* v_00_u03c1_4098_; lean_object* v_tgt_u2081_4099_; lean_object* v_b_u2081_4100_; lean_object* v_n_u2081_4101_; lean_object* v_x_u2081_4102_; lean_object* v_tgt_u2082_4103_; lean_object* v_b_u2082_4104_; lean_object* v_n_u2082_4105_; lean_object* v_x_u2082_4106_; 
switch(lean_obj_tag(v_x_4048_))
{
case 0:
{
if (lean_obj_tag(v_x_4049_) == 0)
{
lean_object* v_tgt_4111_; lean_object* v_b_4112_; lean_object* v_i_4113_; lean_object* v_ys_4114_; lean_object* v_tgt_4115_; lean_object* v_b_4116_; lean_object* v_i_4117_; lean_object* v_ys_4118_; uint8_t v___x_4119_; 
v_tgt_4111_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4111_);
v_b_4112_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4112_);
v_i_4113_ = lean_ctor_get(v_x_4048_, 2);
lean_inc_ref(v_i_4113_);
v_ys_4114_ = lean_ctor_get(v_x_4048_, 3);
lean_inc_ref(v_ys_4114_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4115_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4115_);
v_b_4116_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4116_);
v_i_4117_ = lean_ctor_get(v_x_4049_, 2);
lean_inc_ref(v_i_4117_);
v_ys_4118_ = lean_ctor_get(v_x_4049_, 3);
lean_inc_ref(v_ys_4118_);
lean_dec_ref_known(v_x_4049_, 4);
v___x_4119_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_4113_, v_i_4117_);
lean_dec_ref(v_i_4117_);
lean_dec_ref(v_i_4113_);
if (v___x_4119_ == 0)
{
lean_dec_ref(v_ys_4118_);
lean_dec(v_b_4116_);
lean_dec(v_tgt_4115_);
lean_dec_ref(v_ys_4114_);
lean_dec(v_b_4112_);
lean_dec(v_tgt_4111_);
lean_dec(v_x_4047_);
return v___x_4119_;
}
else
{
uint8_t v___x_4120_; 
v___x_4120_ = l_Lean_IR_args_alphaEqv(v_x_4047_, v_ys_4114_, v_ys_4118_);
lean_dec_ref(v_ys_4118_);
lean_dec_ref(v_ys_4114_);
if (v___x_4120_ == 0)
{
lean_dec(v_b_4116_);
lean_dec(v_tgt_4115_);
lean_dec(v_b_4112_);
lean_dec(v_tgt_4111_);
lean_dec(v_x_4047_);
return v___x_4120_;
}
else
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4111_, v_tgt_4115_);
v_x_4047_ = v___x_4121_;
v_x_4048_ = v_b_4112_;
v_x_4049_ = v_b_4116_;
goto _start;
}
}
}
else
{
uint8_t v___x_4123_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4123_ = 0;
return v___x_4123_;
}
}
case 1:
{
if (lean_obj_tag(v_x_4049_) == 1)
{
lean_object* v_tgt_4124_; lean_object* v_b_4125_; lean_object* v_n_4126_; lean_object* v_x_4127_; lean_object* v_tgt_4128_; lean_object* v_b_4129_; lean_object* v_n_4130_; lean_object* v_x_4131_; 
v_tgt_4124_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4124_);
v_b_4125_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4125_);
v_n_4126_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_n_4126_);
v_x_4127_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_x_4127_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4128_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4128_);
v_b_4129_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4129_);
v_n_4130_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_n_4130_);
v_x_4131_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_x_4131_);
lean_dec_ref_known(v_x_4049_, 4);
v_00_u03c1_4098_ = v_x_4047_;
v_tgt_u2081_4099_ = v_tgt_4124_;
v_b_u2081_4100_ = v_b_4125_;
v_n_u2081_4101_ = v_n_4126_;
v_x_u2081_4102_ = v_x_4127_;
v_tgt_u2082_4103_ = v_tgt_4128_;
v_b_u2082_4104_ = v_b_4129_;
v_n_u2082_4105_ = v_n_4130_;
v_x_u2082_4106_ = v_x_4131_;
goto v___jp_4097_;
}
else
{
uint8_t v___x_4132_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4132_ = 0;
return v___x_4132_;
}
}
case 2:
{
if (lean_obj_tag(v_x_4049_) == 2)
{
lean_object* v_tgt_4133_; lean_object* v_b_4134_; lean_object* v_x_4135_; lean_object* v_i_4136_; uint8_t v_updtHeader_4137_; lean_object* v_ys_4138_; lean_object* v_tgt_4139_; lean_object* v_b_4140_; lean_object* v_x_4141_; lean_object* v_i_4142_; uint8_t v_updtHeader_4143_; lean_object* v_ys_4144_; uint8_t v___x_4149_; 
v_tgt_4133_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4133_);
v_b_4134_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4134_);
v_x_4135_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_x_4135_);
v_i_4136_ = lean_ctor_get(v_x_4048_, 3);
lean_inc_ref(v_i_4136_);
v_updtHeader_4137_ = lean_ctor_get_uint8(v_x_4048_, sizeof(void*)*5);
v_ys_4138_ = lean_ctor_get(v_x_4048_, 4);
lean_inc_ref(v_ys_4138_);
lean_dec_ref_known(v_x_4048_, 5);
v_tgt_4139_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4139_);
v_b_4140_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4140_);
v_x_4141_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_x_4141_);
v_i_4142_ = lean_ctor_get(v_x_4049_, 3);
lean_inc_ref(v_i_4142_);
v_updtHeader_4143_ = lean_ctor_get_uint8(v_x_4049_, sizeof(void*)*5);
v_ys_4144_ = lean_ctor_get(v_x_4049_, 4);
lean_inc_ref(v_ys_4144_);
lean_dec_ref_known(v_x_4049_, 5);
v___x_4149_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4135_, v_x_4141_);
lean_dec(v_x_4141_);
lean_dec(v_x_4135_);
if (v___x_4149_ == 0)
{
lean_dec_ref(v_ys_4144_);
lean_dec_ref(v_i_4142_);
lean_dec(v_b_4140_);
lean_dec(v_tgt_4139_);
lean_dec_ref(v_ys_4138_);
lean_dec_ref(v_i_4136_);
lean_dec(v_b_4134_);
lean_dec(v_tgt_4133_);
lean_dec(v_x_4047_);
return v___x_4149_;
}
else
{
uint8_t v___x_4150_; 
v___x_4150_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_4136_, v_i_4142_);
lean_dec_ref(v_i_4142_);
lean_dec_ref(v_i_4136_);
if (v___x_4150_ == 0)
{
lean_dec_ref(v_ys_4144_);
lean_dec(v_b_4140_);
lean_dec(v_tgt_4139_);
lean_dec_ref(v_ys_4138_);
lean_dec(v_b_4134_);
lean_dec(v_tgt_4133_);
lean_dec(v_x_4047_);
return v___x_4150_;
}
else
{
if (v_updtHeader_4143_ == 0)
{
if (v_updtHeader_4137_ == 0)
{
goto v___jp_4145_;
}
else
{
lean_dec_ref(v_ys_4144_);
lean_dec(v_b_4140_);
lean_dec(v_tgt_4139_);
lean_dec_ref(v_ys_4138_);
lean_dec(v_b_4134_);
lean_dec(v_tgt_4133_);
lean_dec(v_x_4047_);
return v_updtHeader_4143_;
}
}
else
{
if (v_updtHeader_4137_ == 0)
{
lean_dec_ref(v_ys_4144_);
lean_dec(v_b_4140_);
lean_dec(v_tgt_4139_);
lean_dec_ref(v_ys_4138_);
lean_dec(v_b_4134_);
lean_dec(v_tgt_4133_);
lean_dec(v_x_4047_);
return v_updtHeader_4137_;
}
else
{
goto v___jp_4145_;
}
}
}
}
v___jp_4145_:
{
uint8_t v___x_4146_; 
v___x_4146_ = l_Lean_IR_args_alphaEqv(v_x_4047_, v_ys_4138_, v_ys_4144_);
lean_dec_ref(v_ys_4144_);
lean_dec_ref(v_ys_4138_);
if (v___x_4146_ == 0)
{
lean_dec(v_b_4140_);
lean_dec(v_tgt_4139_);
lean_dec(v_b_4134_);
lean_dec(v_tgt_4133_);
lean_dec(v_x_4047_);
return v___x_4146_;
}
else
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4133_, v_tgt_4139_);
v_x_4047_ = v___x_4147_;
v_x_4048_ = v_b_4134_;
v_x_4049_ = v_b_4140_;
goto _start;
}
}
}
else
{
uint8_t v___x_4151_; 
lean_dec_ref_known(v_x_4048_, 5);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4151_ = 0;
return v___x_4151_;
}
}
case 3:
{
if (lean_obj_tag(v_x_4049_) == 3)
{
lean_object* v_tgt_4152_; lean_object* v_b_4153_; lean_object* v_i_4154_; lean_object* v_x_4155_; lean_object* v_tgt_4156_; lean_object* v_b_4157_; lean_object* v_i_4158_; lean_object* v_x_4159_; 
v_tgt_4152_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4152_);
v_b_4153_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4153_);
v_i_4154_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_i_4154_);
v_x_4155_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_x_4155_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4156_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4156_);
v_b_4157_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4157_);
v_i_4158_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_i_4158_);
v_x_4159_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_x_4159_);
lean_dec_ref_known(v_x_4049_, 4);
v_00_u03c1_4098_ = v_x_4047_;
v_tgt_u2081_4099_ = v_tgt_4152_;
v_b_u2081_4100_ = v_b_4153_;
v_n_u2081_4101_ = v_i_4154_;
v_x_u2081_4102_ = v_x_4155_;
v_tgt_u2082_4103_ = v_tgt_4156_;
v_b_u2082_4104_ = v_b_4157_;
v_n_u2082_4105_ = v_i_4158_;
v_x_u2082_4106_ = v_x_4159_;
goto v___jp_4097_;
}
else
{
uint8_t v___x_4160_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4160_ = 0;
return v___x_4160_;
}
}
case 4:
{
if (lean_obj_tag(v_x_4049_) == 4)
{
lean_object* v_tgt_4161_; lean_object* v_b_4162_; lean_object* v_i_4163_; lean_object* v_x_4164_; lean_object* v_tgt_4165_; lean_object* v_b_4166_; lean_object* v_i_4167_; lean_object* v_x_4168_; 
v_tgt_4161_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4161_);
v_b_4162_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4162_);
v_i_4163_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_i_4163_);
v_x_4164_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_x_4164_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4165_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4165_);
v_b_4166_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4166_);
v_i_4167_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_i_4167_);
v_x_4168_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_x_4168_);
lean_dec_ref_known(v_x_4049_, 4);
v_00_u03c1_4098_ = v_x_4047_;
v_tgt_u2081_4099_ = v_tgt_4161_;
v_b_u2081_4100_ = v_b_4162_;
v_n_u2081_4101_ = v_i_4163_;
v_x_u2081_4102_ = v_x_4164_;
v_tgt_u2082_4103_ = v_tgt_4165_;
v_b_u2082_4104_ = v_b_4166_;
v_n_u2082_4105_ = v_i_4167_;
v_x_u2082_4106_ = v_x_4168_;
goto v___jp_4097_;
}
else
{
uint8_t v___x_4169_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4169_ = 0;
return v___x_4169_;
}
}
case 5:
{
if (lean_obj_tag(v_x_4049_) == 5)
{
lean_object* v_tgt_4170_; lean_object* v_b_4171_; lean_object* v_ty_4172_; lean_object* v_n_4173_; lean_object* v_offset_4174_; lean_object* v_x_4175_; lean_object* v_tgt_4176_; lean_object* v_b_4177_; lean_object* v_ty_4178_; lean_object* v_n_4179_; lean_object* v_offset_4180_; lean_object* v_x_4181_; uint8_t v___x_4182_; 
v_tgt_4170_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4170_);
v_b_4171_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4171_);
v_ty_4172_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_ty_4172_);
v_n_4173_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_n_4173_);
v_offset_4174_ = lean_ctor_get(v_x_4048_, 4);
lean_inc(v_offset_4174_);
v_x_4175_ = lean_ctor_get(v_x_4048_, 5);
lean_inc(v_x_4175_);
lean_dec_ref_known(v_x_4048_, 6);
v_tgt_4176_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4176_);
v_b_4177_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4177_);
v_ty_4178_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_ty_4178_);
v_n_4179_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_n_4179_);
v_offset_4180_ = lean_ctor_get(v_x_4049_, 4);
lean_inc(v_offset_4180_);
v_x_4181_ = lean_ctor_get(v_x_4049_, 5);
lean_inc(v_x_4181_);
lean_dec_ref_known(v_x_4049_, 6);
v___x_4182_ = l_Lean_IR_instBEqIRType_beq(v_ty_4172_, v_ty_4178_);
lean_dec(v_ty_4178_);
lean_dec(v_ty_4172_);
if (v___x_4182_ == 0)
{
lean_dec(v_x_4181_);
lean_dec(v_offset_4180_);
lean_dec(v_n_4179_);
lean_dec(v_b_4177_);
lean_dec(v_tgt_4176_);
lean_dec(v_x_4175_);
lean_dec(v_offset_4174_);
lean_dec(v_n_4173_);
lean_dec(v_b_4171_);
lean_dec(v_tgt_4170_);
lean_dec(v_x_4047_);
return v___x_4182_;
}
else
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_nat_dec_eq(v_n_4173_, v_n_4179_);
lean_dec(v_n_4179_);
lean_dec(v_n_4173_);
if (v___x_4183_ == 0)
{
lean_dec(v_x_4181_);
lean_dec(v_offset_4180_);
lean_dec(v_b_4177_);
lean_dec(v_tgt_4176_);
lean_dec(v_x_4175_);
lean_dec(v_offset_4174_);
lean_dec(v_b_4171_);
lean_dec(v_tgt_4170_);
lean_dec(v_x_4047_);
return v___x_4183_;
}
else
{
uint8_t v___x_4184_; 
v___x_4184_ = lean_nat_dec_eq(v_offset_4174_, v_offset_4180_);
lean_dec(v_offset_4180_);
lean_dec(v_offset_4174_);
if (v___x_4184_ == 0)
{
lean_dec(v_x_4181_);
lean_dec(v_b_4177_);
lean_dec(v_tgt_4176_);
lean_dec(v_x_4175_);
lean_dec(v_b_4171_);
lean_dec(v_tgt_4170_);
lean_dec(v_x_4047_);
return v___x_4184_;
}
else
{
uint8_t v___x_4185_; 
v___x_4185_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4175_, v_x_4181_);
lean_dec(v_x_4181_);
lean_dec(v_x_4175_);
if (v___x_4185_ == 0)
{
lean_dec(v_b_4177_);
lean_dec(v_tgt_4176_);
lean_dec(v_b_4171_);
lean_dec(v_tgt_4170_);
lean_dec(v_x_4047_);
return v___x_4185_;
}
else
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4170_, v_tgt_4176_);
v_x_4047_ = v___x_4186_;
v_x_4048_ = v_b_4171_;
v_x_4049_ = v_b_4177_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_4188_; 
lean_dec_ref_known(v_x_4048_, 6);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4188_ = 0;
return v___x_4188_;
}
}
case 6:
{
if (lean_obj_tag(v_x_4049_) == 6)
{
lean_object* v_tgt_4189_; lean_object* v_b_4190_; lean_object* v_ty_4191_; lean_object* v_c_4192_; lean_object* v_ys_4193_; lean_object* v_tgt_4194_; lean_object* v_b_4195_; lean_object* v_ty_4196_; lean_object* v_c_4197_; lean_object* v_ys_4198_; uint8_t v___x_4199_; 
v_tgt_4189_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4189_);
v_b_4190_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4190_);
v_ty_4191_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_ty_4191_);
v_c_4192_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_c_4192_);
v_ys_4193_ = lean_ctor_get(v_x_4048_, 4);
lean_inc_ref(v_ys_4193_);
lean_dec_ref_known(v_x_4048_, 5);
v_tgt_4194_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4194_);
v_b_4195_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4195_);
v_ty_4196_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_ty_4196_);
v_c_4197_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_c_4197_);
v_ys_4198_ = lean_ctor_get(v_x_4049_, 4);
lean_inc_ref(v_ys_4198_);
lean_dec_ref_known(v_x_4049_, 5);
v___x_4199_ = l_Lean_IR_instBEqIRType_beq(v_ty_4191_, v_ty_4196_);
lean_dec(v_ty_4196_);
lean_dec(v_ty_4191_);
if (v___x_4199_ == 0)
{
lean_dec_ref(v_ys_4198_);
lean_dec(v_c_4197_);
lean_dec(v_b_4195_);
lean_dec(v_tgt_4194_);
lean_dec_ref(v_ys_4193_);
lean_dec(v_c_4192_);
lean_dec(v_b_4190_);
lean_dec(v_tgt_4189_);
lean_dec(v_x_4047_);
return v___x_4199_;
}
else
{
uint8_t v___x_4200_; 
v___x_4200_ = lean_name_eq(v_c_4192_, v_c_4197_);
lean_dec(v_c_4197_);
lean_dec(v_c_4192_);
if (v___x_4200_ == 0)
{
lean_dec_ref(v_ys_4198_);
lean_dec(v_b_4195_);
lean_dec(v_tgt_4194_);
lean_dec_ref(v_ys_4193_);
lean_dec(v_b_4190_);
lean_dec(v_tgt_4189_);
lean_dec(v_x_4047_);
return v___x_4200_;
}
else
{
uint8_t v___x_4201_; 
v___x_4201_ = l_Lean_IR_args_alphaEqv(v_x_4047_, v_ys_4193_, v_ys_4198_);
lean_dec_ref(v_ys_4198_);
lean_dec_ref(v_ys_4193_);
if (v___x_4201_ == 0)
{
lean_dec(v_b_4195_);
lean_dec(v_tgt_4194_);
lean_dec(v_b_4190_);
lean_dec(v_tgt_4189_);
lean_dec(v_x_4047_);
return v___x_4201_;
}
else
{
lean_object* v___x_4202_; 
v___x_4202_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4189_, v_tgt_4194_);
v_x_4047_ = v___x_4202_;
v_x_4048_ = v_b_4190_;
v_x_4049_ = v_b_4195_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_4204_; 
lean_dec_ref_known(v_x_4048_, 5);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4204_ = 0;
return v___x_4204_;
}
}
case 7:
{
if (lean_obj_tag(v_x_4049_) == 7)
{
lean_object* v_tgt_4205_; lean_object* v_b_4206_; lean_object* v_c_4207_; lean_object* v_ys_4208_; lean_object* v_tgt_4209_; lean_object* v_b_4210_; lean_object* v_c_4211_; lean_object* v_ys_4212_; uint8_t v___x_4213_; 
v_tgt_4205_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4205_);
v_b_4206_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4206_);
v_c_4207_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_c_4207_);
v_ys_4208_ = lean_ctor_get(v_x_4048_, 3);
lean_inc_ref(v_ys_4208_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4209_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4209_);
v_b_4210_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4210_);
v_c_4211_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_c_4211_);
v_ys_4212_ = lean_ctor_get(v_x_4049_, 3);
lean_inc_ref(v_ys_4212_);
lean_dec_ref_known(v_x_4049_, 4);
v___x_4213_ = lean_name_eq(v_c_4207_, v_c_4211_);
lean_dec(v_c_4211_);
lean_dec(v_c_4207_);
if (v___x_4213_ == 0)
{
lean_dec_ref(v_ys_4212_);
lean_dec(v_b_4210_);
lean_dec(v_tgt_4209_);
lean_dec_ref(v_ys_4208_);
lean_dec(v_b_4206_);
lean_dec(v_tgt_4205_);
lean_dec(v_x_4047_);
return v___x_4213_;
}
else
{
uint8_t v___x_4214_; 
v___x_4214_ = l_Lean_IR_args_alphaEqv(v_x_4047_, v_ys_4208_, v_ys_4212_);
lean_dec_ref(v_ys_4212_);
lean_dec_ref(v_ys_4208_);
if (v___x_4214_ == 0)
{
lean_dec(v_b_4210_);
lean_dec(v_tgt_4209_);
lean_dec(v_b_4206_);
lean_dec(v_tgt_4205_);
lean_dec(v_x_4047_);
return v___x_4214_;
}
else
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4205_, v_tgt_4209_);
v_x_4047_ = v___x_4215_;
v_x_4048_ = v_b_4206_;
v_x_4049_ = v_b_4210_;
goto _start;
}
}
}
else
{
uint8_t v___x_4217_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4217_ = 0;
return v___x_4217_;
}
}
case 8:
{
if (lean_obj_tag(v_x_4049_) == 8)
{
lean_object* v_tgt_4218_; lean_object* v_b_4219_; lean_object* v_x_4220_; lean_object* v_ys_4221_; lean_object* v_tgt_4222_; lean_object* v_b_4223_; lean_object* v_x_4224_; lean_object* v_ys_4225_; uint8_t v___x_4226_; 
v_tgt_4218_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4218_);
v_b_4219_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4219_);
v_x_4220_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_x_4220_);
v_ys_4221_ = lean_ctor_get(v_x_4048_, 3);
lean_inc_ref(v_ys_4221_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4222_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4222_);
v_b_4223_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4223_);
v_x_4224_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_x_4224_);
v_ys_4225_ = lean_ctor_get(v_x_4049_, 3);
lean_inc_ref(v_ys_4225_);
lean_dec_ref_known(v_x_4049_, 4);
v___x_4226_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4220_, v_x_4224_);
lean_dec(v_x_4224_);
lean_dec(v_x_4220_);
if (v___x_4226_ == 0)
{
lean_dec_ref(v_ys_4225_);
lean_dec(v_b_4223_);
lean_dec(v_tgt_4222_);
lean_dec_ref(v_ys_4221_);
lean_dec(v_b_4219_);
lean_dec(v_tgt_4218_);
lean_dec(v_x_4047_);
return v___x_4226_;
}
else
{
uint8_t v___x_4227_; 
v___x_4227_ = l_Lean_IR_args_alphaEqv(v_x_4047_, v_ys_4221_, v_ys_4225_);
lean_dec_ref(v_ys_4225_);
lean_dec_ref(v_ys_4221_);
if (v___x_4227_ == 0)
{
lean_dec(v_b_4223_);
lean_dec(v_tgt_4222_);
lean_dec(v_b_4219_);
lean_dec(v_tgt_4218_);
lean_dec(v_x_4047_);
return v___x_4227_;
}
else
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4218_, v_tgt_4222_);
v_x_4047_ = v___x_4228_;
v_x_4048_ = v_b_4219_;
v_x_4049_ = v_b_4223_;
goto _start;
}
}
}
else
{
uint8_t v___x_4230_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4230_ = 0;
return v___x_4230_;
}
}
case 9:
{
if (lean_obj_tag(v_x_4049_) == 9)
{
lean_object* v_tgt_4231_; lean_object* v_b_4232_; lean_object* v_ty_4233_; lean_object* v_x_4234_; lean_object* v_tgt_4235_; lean_object* v_b_4236_; lean_object* v_ty_4237_; lean_object* v_x_4238_; 
v_tgt_4231_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4231_);
v_b_4232_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4232_);
v_ty_4233_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_ty_4233_);
v_x_4234_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_x_4234_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4235_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4235_);
v_b_4236_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4236_);
v_ty_4237_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_ty_4237_);
v_x_4238_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_x_4238_);
lean_dec_ref_known(v_x_4049_, 4);
v_00_u03c1_4084_ = v_x_4047_;
v_tgt_u2081_4085_ = v_tgt_4231_;
v_b_u2081_4086_ = v_b_4232_;
v_ty_u2081_4087_ = v_ty_4233_;
v_x_u2081_4088_ = v_x_4234_;
v_tgt_u2082_4089_ = v_tgt_4235_;
v_b_u2082_4090_ = v_b_4236_;
v_ty_u2082_4091_ = v_ty_4237_;
v_x_u2082_4092_ = v_x_4238_;
goto v___jp_4083_;
}
else
{
uint8_t v___x_4239_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4239_ = 0;
return v___x_4239_;
}
}
case 10:
{
if (lean_obj_tag(v_x_4049_) == 10)
{
lean_object* v_tgt_4240_; lean_object* v_b_4241_; lean_object* v_ty_4242_; lean_object* v_x_4243_; lean_object* v_tgt_4244_; lean_object* v_b_4245_; lean_object* v_ty_4246_; lean_object* v_x_4247_; 
v_tgt_4240_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4240_);
v_b_4241_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4241_);
v_ty_4242_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_ty_4242_);
v_x_4243_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_x_4243_);
lean_dec_ref_known(v_x_4048_, 4);
v_tgt_4244_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4244_);
v_b_4245_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4245_);
v_ty_4246_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_ty_4246_);
v_x_4247_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_x_4247_);
lean_dec_ref_known(v_x_4049_, 4);
v_00_u03c1_4084_ = v_x_4047_;
v_tgt_u2081_4085_ = v_tgt_4240_;
v_b_u2081_4086_ = v_b_4241_;
v_ty_u2081_4087_ = v_ty_4242_;
v_x_u2081_4088_ = v_x_4243_;
v_tgt_u2082_4089_ = v_tgt_4244_;
v_b_u2082_4090_ = v_b_4245_;
v_ty_u2082_4091_ = v_ty_4246_;
v_x_u2082_4092_ = v_x_4247_;
goto v___jp_4083_;
}
else
{
uint8_t v___x_4248_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4248_ = 0;
return v___x_4248_;
}
}
case 11:
{
if (lean_obj_tag(v_x_4049_) == 11)
{
lean_object* v_tgt_4249_; lean_object* v_b_4250_; uint8_t v_v_4251_; lean_object* v_tgt_4252_; lean_object* v_b_4253_; uint8_t v_v_4254_; uint8_t v___x_4255_; 
v_tgt_4249_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4249_);
v_b_4250_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4250_);
v_v_4251_ = lean_ctor_get_uint8(v_x_4048_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4048_, 2);
v_tgt_4252_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4252_);
v_b_4253_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4253_);
v_v_4254_ = lean_ctor_get_uint8(v_x_4049_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4049_, 2);
v___x_4255_ = lean_uint8_dec_eq(v_v_4251_, v_v_4254_);
if (v___x_4255_ == 0)
{
lean_dec(v_b_4253_);
lean_dec(v_tgt_4252_);
lean_dec(v_b_4250_);
lean_dec(v_tgt_4249_);
lean_dec(v_x_4047_);
return v___x_4255_;
}
else
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4249_, v_tgt_4252_);
v_x_4047_ = v___x_4256_;
v_x_4048_ = v_b_4250_;
v_x_4049_ = v_b_4253_;
goto _start;
}
}
else
{
uint8_t v___x_4258_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4258_ = 0;
return v___x_4258_;
}
}
case 12:
{
if (lean_obj_tag(v_x_4049_) == 12)
{
lean_object* v_tgt_4259_; lean_object* v_b_4260_; uint16_t v_v_4261_; lean_object* v_tgt_4262_; lean_object* v_b_4263_; uint16_t v_v_4264_; uint8_t v___x_4265_; 
v_tgt_4259_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4259_);
v_b_4260_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4260_);
v_v_4261_ = lean_ctor_get_uint16(v_x_4048_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4048_, 2);
v_tgt_4262_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4262_);
v_b_4263_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4263_);
v_v_4264_ = lean_ctor_get_uint16(v_x_4049_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4049_, 2);
v___x_4265_ = lean_uint16_dec_eq(v_v_4261_, v_v_4264_);
if (v___x_4265_ == 0)
{
lean_dec(v_b_4263_);
lean_dec(v_tgt_4262_);
lean_dec(v_b_4260_);
lean_dec(v_tgt_4259_);
lean_dec(v_x_4047_);
return v___x_4265_;
}
else
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4259_, v_tgt_4262_);
v_x_4047_ = v___x_4266_;
v_x_4048_ = v_b_4260_;
v_x_4049_ = v_b_4263_;
goto _start;
}
}
else
{
uint8_t v___x_4268_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4268_ = 0;
return v___x_4268_;
}
}
case 13:
{
if (lean_obj_tag(v_x_4049_) == 13)
{
lean_object* v_tgt_4269_; lean_object* v_b_4270_; uint32_t v_v_4271_; lean_object* v_tgt_4272_; lean_object* v_b_4273_; uint32_t v_v_4274_; uint8_t v___x_4275_; 
v_tgt_4269_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4269_);
v_b_4270_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4270_);
v_v_4271_ = lean_ctor_get_uint32(v_x_4048_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4048_, 2);
v_tgt_4272_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4272_);
v_b_4273_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4273_);
v_v_4274_ = lean_ctor_get_uint32(v_x_4049_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4049_, 2);
v___x_4275_ = lean_uint32_dec_eq(v_v_4271_, v_v_4274_);
if (v___x_4275_ == 0)
{
lean_dec(v_b_4273_);
lean_dec(v_tgt_4272_);
lean_dec(v_b_4270_);
lean_dec(v_tgt_4269_);
lean_dec(v_x_4047_);
return v___x_4275_;
}
else
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4269_, v_tgt_4272_);
v_x_4047_ = v___x_4276_;
v_x_4048_ = v_b_4270_;
v_x_4049_ = v_b_4273_;
goto _start;
}
}
else
{
uint8_t v___x_4278_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4278_ = 0;
return v___x_4278_;
}
}
case 14:
{
if (lean_obj_tag(v_x_4049_) == 14)
{
lean_object* v_tgt_4279_; lean_object* v_b_4280_; uint64_t v_v_4281_; lean_object* v_tgt_4282_; lean_object* v_b_4283_; uint64_t v_v_4284_; 
v_tgt_4279_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4279_);
v_b_4280_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4280_);
v_v_4281_ = lean_ctor_get_uint64(v_x_4048_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4048_, 2);
v_tgt_4282_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4282_);
v_b_4283_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4283_);
v_v_4284_ = lean_ctor_get_uint64(v_x_4049_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4049_, 2);
v_00_u03c1_4073_ = v_x_4047_;
v_tgt_u2081_4074_ = v_tgt_4279_;
v_b_u2081_4075_ = v_b_4280_;
v_v_u2081_4076_ = v_v_4281_;
v_tgt_u2082_4077_ = v_tgt_4282_;
v_b_u2082_4078_ = v_b_4283_;
v_v_u2082_4079_ = v_v_4284_;
goto v___jp_4072_;
}
else
{
uint8_t v___x_4285_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4285_ = 0;
return v___x_4285_;
}
}
case 15:
{
if (lean_obj_tag(v_x_4049_) == 15)
{
lean_object* v_tgt_4286_; lean_object* v_b_4287_; uint64_t v_v_4288_; lean_object* v_tgt_4289_; lean_object* v_b_4290_; uint64_t v_v_4291_; 
v_tgt_4286_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4286_);
v_b_4287_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4287_);
v_v_4288_ = lean_ctor_get_uint64(v_x_4048_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4048_, 2);
v_tgt_4289_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4289_);
v_b_4290_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4290_);
v_v_4291_ = lean_ctor_get_uint64(v_x_4049_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4049_, 2);
v_00_u03c1_4073_ = v_x_4047_;
v_tgt_u2081_4074_ = v_tgt_4286_;
v_b_u2081_4075_ = v_b_4287_;
v_v_u2081_4076_ = v_v_4288_;
v_tgt_u2082_4077_ = v_tgt_4289_;
v_b_u2082_4078_ = v_b_4290_;
v_v_u2082_4079_ = v_v_4291_;
goto v___jp_4072_;
}
else
{
uint8_t v___x_4292_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4292_ = 0;
return v___x_4292_;
}
}
case 16:
{
if (lean_obj_tag(v_x_4049_) == 16)
{
lean_object* v_tgt_4293_; lean_object* v_b_4294_; lean_object* v_v_4295_; lean_object* v_tgt_4296_; lean_object* v_b_4297_; lean_object* v_v_4298_; uint8_t v___x_4299_; 
v_tgt_4293_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4293_);
v_b_4294_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4294_);
v_v_4295_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_v_4295_);
lean_dec_ref_known(v_x_4048_, 3);
v_tgt_4296_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4296_);
v_b_4297_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4297_);
v_v_4298_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_v_4298_);
lean_dec_ref_known(v_x_4049_, 3);
v___x_4299_ = lean_nat_dec_eq(v_v_4295_, v_v_4298_);
lean_dec(v_v_4298_);
lean_dec(v_v_4295_);
if (v___x_4299_ == 0)
{
lean_dec(v_b_4297_);
lean_dec(v_tgt_4296_);
lean_dec(v_b_4294_);
lean_dec(v_tgt_4293_);
lean_dec(v_x_4047_);
return v___x_4299_;
}
else
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4293_, v_tgt_4296_);
v_x_4047_ = v___x_4300_;
v_x_4048_ = v_b_4294_;
v_x_4049_ = v_b_4297_;
goto _start;
}
}
else
{
uint8_t v___x_4302_; 
lean_dec_ref_known(v_x_4048_, 3);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4302_ = 0;
return v___x_4302_;
}
}
case 17:
{
if (lean_obj_tag(v_x_4049_) == 17)
{
lean_object* v_tgt_4303_; lean_object* v_b_4304_; lean_object* v_v_4305_; lean_object* v_tgt_4306_; lean_object* v_b_4307_; lean_object* v_v_4308_; uint8_t v___x_4309_; 
v_tgt_4303_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4303_);
v_b_4304_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4304_);
v_v_4305_ = lean_ctor_get(v_x_4048_, 2);
lean_inc_ref(v_v_4305_);
lean_dec_ref_known(v_x_4048_, 3);
v_tgt_4306_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4306_);
v_b_4307_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4307_);
v_v_4308_ = lean_ctor_get(v_x_4049_, 2);
lean_inc_ref(v_v_4308_);
lean_dec_ref_known(v_x_4049_, 3);
v___x_4309_ = lean_string_dec_eq(v_v_4305_, v_v_4308_);
lean_dec_ref(v_v_4308_);
lean_dec_ref(v_v_4305_);
if (v___x_4309_ == 0)
{
lean_dec(v_b_4307_);
lean_dec(v_tgt_4306_);
lean_dec(v_b_4304_);
lean_dec(v_tgt_4303_);
lean_dec(v_x_4047_);
return v___x_4309_;
}
else
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4303_, v_tgt_4306_);
v_x_4047_ = v___x_4310_;
v_x_4048_ = v_b_4304_;
v_x_4049_ = v_b_4307_;
goto _start;
}
}
else
{
uint8_t v___x_4312_; 
lean_dec_ref_known(v_x_4048_, 3);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4312_ = 0;
return v___x_4312_;
}
}
case 18:
{
if (lean_obj_tag(v_x_4049_) == 18)
{
lean_object* v_tgt_4313_; lean_object* v_b_4314_; lean_object* v_x_4315_; lean_object* v_tgt_4316_; lean_object* v_b_4317_; lean_object* v_x_4318_; uint8_t v___x_4319_; 
v_tgt_4313_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tgt_4313_);
v_b_4314_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4314_);
v_x_4315_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_x_4315_);
lean_dec_ref_known(v_x_4048_, 3);
v_tgt_4316_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tgt_4316_);
v_b_4317_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4317_);
v_x_4318_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_x_4318_);
lean_dec_ref_known(v_x_4049_, 3);
v___x_4319_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4315_, v_x_4318_);
lean_dec(v_x_4318_);
lean_dec(v_x_4315_);
if (v___x_4319_ == 0)
{
lean_dec(v_b_4317_);
lean_dec(v_tgt_4316_);
lean_dec(v_b_4314_);
lean_dec(v_tgt_4313_);
lean_dec(v_x_4047_);
return v___x_4319_;
}
else
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_IR_addVarRename(v_x_4047_, v_tgt_4313_, v_tgt_4316_);
v_x_4047_ = v___x_4320_;
v_x_4048_ = v_b_4314_;
v_x_4049_ = v_b_4317_;
goto _start;
}
}
else
{
uint8_t v___x_4322_; 
lean_dec_ref_known(v_x_4048_, 3);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4322_ = 0;
return v___x_4322_;
}
}
case 19:
{
if (lean_obj_tag(v_x_4049_) == 19)
{
lean_object* v_j_4323_; lean_object* v_xs_4324_; lean_object* v_v_4325_; lean_object* v_b_4326_; lean_object* v_j_4327_; lean_object* v_xs_4328_; lean_object* v_v_4329_; lean_object* v_b_4330_; lean_object* v___x_4331_; 
v_j_4323_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_j_4323_);
v_xs_4324_ = lean_ctor_get(v_x_4048_, 1);
lean_inc_ref(v_xs_4324_);
v_v_4325_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_v_4325_);
v_b_4326_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_b_4326_);
lean_dec_ref_known(v_x_4048_, 4);
v_j_4327_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_j_4327_);
v_xs_4328_ = lean_ctor_get(v_x_4049_, 1);
lean_inc_ref(v_xs_4328_);
v_v_4329_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_v_4329_);
v_b_4330_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_b_4330_);
lean_dec_ref_known(v_x_4049_, 4);
lean_inc(v_x_4047_);
v___x_4331_ = l_Lean_IR_addParamsRename(v_x_4047_, v_xs_4324_, v_xs_4328_);
lean_dec_ref(v_xs_4328_);
lean_dec_ref(v_xs_4324_);
if (lean_obj_tag(v___x_4331_) == 0)
{
uint8_t v___x_4332_; 
lean_dec(v_b_4330_);
lean_dec(v_v_4329_);
lean_dec(v_j_4327_);
lean_dec(v_b_4326_);
lean_dec(v_v_4325_);
lean_dec(v_j_4323_);
lean_dec(v_x_4047_);
v___x_4332_ = 0;
return v___x_4332_;
}
else
{
lean_object* v_val_4333_; uint8_t v___x_4334_; 
v_val_4333_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_val_4333_);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4334_ = l_Lean_IR_FnBody_alphaEqv(v_val_4333_, v_v_4325_, v_v_4329_);
if (v___x_4334_ == 0)
{
lean_dec(v_b_4330_);
lean_dec(v_j_4327_);
lean_dec(v_b_4326_);
lean_dec(v_j_4323_);
lean_dec(v_x_4047_);
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_IR_addVarRename(v_x_4047_, v_j_4323_, v_j_4327_);
v_x_4047_ = v___x_4335_;
v_x_4048_ = v_b_4326_;
v_x_4049_ = v_b_4330_;
goto _start;
}
}
}
else
{
uint8_t v___x_4337_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4337_ = 0;
return v___x_4337_;
}
}
case 20:
{
if (lean_obj_tag(v_x_4049_) == 20)
{
lean_object* v_x_4338_; lean_object* v_i_4339_; lean_object* v_y_4340_; lean_object* v_b_4341_; lean_object* v_x_4342_; lean_object* v_i_4343_; lean_object* v_y_4344_; lean_object* v_b_4345_; uint8_t v___x_4346_; 
v_x_4338_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4338_);
v_i_4339_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_i_4339_);
v_y_4340_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_y_4340_);
v_b_4341_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_b_4341_);
lean_dec_ref_known(v_x_4048_, 4);
v_x_4342_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4342_);
v_i_4343_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_i_4343_);
v_y_4344_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_y_4344_);
v_b_4345_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_b_4345_);
lean_dec_ref_known(v_x_4049_, 4);
v___x_4346_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4338_, v_x_4342_);
lean_dec(v_x_4342_);
lean_dec(v_x_4338_);
if (v___x_4346_ == 0)
{
lean_dec(v_b_4345_);
lean_dec(v_y_4344_);
lean_dec(v_i_4343_);
lean_dec(v_b_4341_);
lean_dec(v_y_4340_);
lean_dec(v_i_4339_);
lean_dec(v_x_4047_);
return v___x_4346_;
}
else
{
uint8_t v___x_4347_; 
v___x_4347_ = lean_nat_dec_eq(v_i_4339_, v_i_4343_);
lean_dec(v_i_4343_);
lean_dec(v_i_4339_);
if (v___x_4347_ == 0)
{
lean_dec(v_b_4345_);
lean_dec(v_y_4344_);
lean_dec(v_b_4341_);
lean_dec(v_y_4340_);
lean_dec(v_x_4047_);
return v___x_4347_;
}
else
{
uint8_t v___x_4348_; 
v___x_4348_ = l_Lean_IR_Arg_alphaEqv(v_x_4047_, v_y_4340_, v_y_4344_);
lean_dec(v_y_4344_);
lean_dec(v_y_4340_);
if (v___x_4348_ == 0)
{
lean_dec(v_b_4345_);
lean_dec(v_b_4341_);
lean_dec(v_x_4047_);
return v___x_4348_;
}
else
{
v_x_4048_ = v_b_4341_;
v_x_4049_ = v_b_4345_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_4350_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4350_ = 0;
return v___x_4350_;
}
}
case 21:
{
if (lean_obj_tag(v_x_4049_) == 21)
{
lean_object* v_x_4351_; lean_object* v_cidx_4352_; lean_object* v_b_4353_; lean_object* v_x_4354_; lean_object* v_cidx_4355_; lean_object* v_b_4356_; uint8_t v___x_4357_; 
v_x_4351_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4351_);
v_cidx_4352_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_cidx_4352_);
v_b_4353_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_b_4353_);
lean_dec_ref_known(v_x_4048_, 3);
v_x_4354_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4354_);
v_cidx_4355_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_cidx_4355_);
v_b_4356_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_b_4356_);
lean_dec_ref_known(v_x_4049_, 3);
v___x_4357_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4351_, v_x_4354_);
lean_dec(v_x_4354_);
lean_dec(v_x_4351_);
if (v___x_4357_ == 0)
{
lean_dec(v_b_4356_);
lean_dec(v_cidx_4355_);
lean_dec(v_b_4353_);
lean_dec(v_cidx_4352_);
lean_dec(v_x_4047_);
return v___x_4357_;
}
else
{
uint8_t v___x_4358_; 
v___x_4358_ = lean_nat_dec_eq(v_cidx_4352_, v_cidx_4355_);
lean_dec(v_cidx_4355_);
lean_dec(v_cidx_4352_);
if (v___x_4358_ == 0)
{
lean_dec(v_b_4356_);
lean_dec(v_b_4353_);
lean_dec(v_x_4047_);
return v___x_4358_;
}
else
{
v_x_4048_ = v_b_4353_;
v_x_4049_ = v_b_4356_;
goto _start;
}
}
}
else
{
uint8_t v___x_4360_; 
lean_dec_ref_known(v_x_4048_, 3);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4360_ = 0;
return v___x_4360_;
}
}
case 22:
{
if (lean_obj_tag(v_x_4049_) == 22)
{
lean_object* v_x_4361_; lean_object* v_i_4362_; lean_object* v_y_4363_; lean_object* v_b_4364_; lean_object* v_x_4365_; lean_object* v_i_4366_; lean_object* v_y_4367_; lean_object* v_b_4368_; uint8_t v___x_4369_; 
v_x_4361_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4361_);
v_i_4362_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_i_4362_);
v_y_4363_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_y_4363_);
v_b_4364_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_b_4364_);
lean_dec_ref_known(v_x_4048_, 4);
v_x_4365_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4365_);
v_i_4366_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_i_4366_);
v_y_4367_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_y_4367_);
v_b_4368_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_b_4368_);
lean_dec_ref_known(v_x_4049_, 4);
v___x_4369_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4361_, v_x_4365_);
lean_dec(v_x_4365_);
lean_dec(v_x_4361_);
if (v___x_4369_ == 0)
{
lean_dec(v_b_4368_);
lean_dec(v_y_4367_);
lean_dec(v_i_4366_);
lean_dec(v_b_4364_);
lean_dec(v_y_4363_);
lean_dec(v_i_4362_);
lean_dec(v_x_4047_);
return v___x_4369_;
}
else
{
uint8_t v___x_4370_; 
v___x_4370_ = lean_nat_dec_eq(v_i_4362_, v_i_4366_);
lean_dec(v_i_4366_);
lean_dec(v_i_4362_);
if (v___x_4370_ == 0)
{
lean_dec(v_b_4368_);
lean_dec(v_y_4367_);
lean_dec(v_b_4364_);
lean_dec(v_y_4363_);
lean_dec(v_x_4047_);
return v___x_4370_;
}
else
{
uint8_t v___x_4371_; 
v___x_4371_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_y_4363_, v_y_4367_);
lean_dec(v_y_4367_);
lean_dec(v_y_4363_);
if (v___x_4371_ == 0)
{
lean_dec(v_b_4368_);
lean_dec(v_b_4364_);
lean_dec(v_x_4047_);
return v___x_4371_;
}
else
{
v_x_4048_ = v_b_4364_;
v_x_4049_ = v_b_4368_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_4373_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4373_ = 0;
return v___x_4373_;
}
}
case 23:
{
if (lean_obj_tag(v_x_4049_) == 23)
{
lean_object* v_x_4374_; lean_object* v_i_4375_; lean_object* v_offset_4376_; lean_object* v_y_4377_; lean_object* v_ty_4378_; lean_object* v_b_4379_; lean_object* v_x_4380_; lean_object* v_i_4381_; lean_object* v_offset_4382_; lean_object* v_y_4383_; lean_object* v_ty_4384_; lean_object* v_b_4385_; uint8_t v___x_4386_; 
v_x_4374_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4374_);
v_i_4375_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_i_4375_);
v_offset_4376_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_offset_4376_);
v_y_4377_ = lean_ctor_get(v_x_4048_, 3);
lean_inc(v_y_4377_);
v_ty_4378_ = lean_ctor_get(v_x_4048_, 4);
lean_inc(v_ty_4378_);
v_b_4379_ = lean_ctor_get(v_x_4048_, 5);
lean_inc(v_b_4379_);
lean_dec_ref_known(v_x_4048_, 6);
v_x_4380_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4380_);
v_i_4381_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_i_4381_);
v_offset_4382_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_offset_4382_);
v_y_4383_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_y_4383_);
v_ty_4384_ = lean_ctor_get(v_x_4049_, 4);
lean_inc(v_ty_4384_);
v_b_4385_ = lean_ctor_get(v_x_4049_, 5);
lean_inc(v_b_4385_);
lean_dec_ref_known(v_x_4049_, 6);
v___x_4386_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4374_, v_x_4380_);
lean_dec(v_x_4380_);
lean_dec(v_x_4374_);
if (v___x_4386_ == 0)
{
lean_dec(v_b_4385_);
lean_dec(v_ty_4384_);
lean_dec(v_y_4383_);
lean_dec(v_offset_4382_);
lean_dec(v_i_4381_);
lean_dec(v_b_4379_);
lean_dec(v_ty_4378_);
lean_dec(v_y_4377_);
lean_dec(v_offset_4376_);
lean_dec(v_i_4375_);
lean_dec(v_x_4047_);
return v___x_4386_;
}
else
{
uint8_t v___x_4387_; 
v___x_4387_ = lean_nat_dec_eq(v_i_4375_, v_i_4381_);
lean_dec(v_i_4381_);
lean_dec(v_i_4375_);
if (v___x_4387_ == 0)
{
lean_dec(v_b_4385_);
lean_dec(v_ty_4384_);
lean_dec(v_y_4383_);
lean_dec(v_offset_4382_);
lean_dec(v_b_4379_);
lean_dec(v_ty_4378_);
lean_dec(v_y_4377_);
lean_dec(v_offset_4376_);
lean_dec(v_x_4047_);
return v___x_4387_;
}
else
{
uint8_t v___x_4388_; 
v___x_4388_ = lean_nat_dec_eq(v_offset_4376_, v_offset_4382_);
lean_dec(v_offset_4382_);
lean_dec(v_offset_4376_);
if (v___x_4388_ == 0)
{
lean_dec(v_b_4385_);
lean_dec(v_ty_4384_);
lean_dec(v_y_4383_);
lean_dec(v_b_4379_);
lean_dec(v_ty_4378_);
lean_dec(v_y_4377_);
lean_dec(v_x_4047_);
return v___x_4388_;
}
else
{
uint8_t v___x_4389_; 
v___x_4389_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_y_4377_, v_y_4383_);
lean_dec(v_y_4383_);
lean_dec(v_y_4377_);
if (v___x_4389_ == 0)
{
lean_dec(v_b_4385_);
lean_dec(v_ty_4384_);
lean_dec(v_b_4379_);
lean_dec(v_ty_4378_);
lean_dec(v_x_4047_);
return v___x_4389_;
}
else
{
uint8_t v___x_4390_; 
v___x_4390_ = l_Lean_IR_instBEqIRType_beq(v_ty_4378_, v_ty_4384_);
lean_dec(v_ty_4384_);
lean_dec(v_ty_4378_);
if (v___x_4390_ == 0)
{
lean_dec(v_b_4385_);
lean_dec(v_b_4379_);
lean_dec(v_x_4047_);
return v___x_4390_;
}
else
{
v_x_4048_ = v_b_4379_;
v_x_4049_ = v_b_4385_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_4392_; 
lean_dec_ref_known(v_x_4048_, 6);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4392_ = 0;
return v___x_4392_;
}
}
case 24:
{
if (lean_obj_tag(v_x_4049_) == 24)
{
lean_object* v_x_4393_; lean_object* v_n_4394_; uint8_t v_c_4395_; uint8_t v_persistent_4396_; lean_object* v_b_4397_; lean_object* v_x_4398_; lean_object* v_n_4399_; uint8_t v_c_4400_; uint8_t v_persistent_4401_; lean_object* v_b_4402_; 
v_x_4393_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4393_);
v_n_4394_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_n_4394_);
v_c_4395_ = lean_ctor_get_uint8(v_x_4048_, sizeof(void*)*3);
v_persistent_4396_ = lean_ctor_get_uint8(v_x_4048_, sizeof(void*)*3 + 1);
v_b_4397_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_b_4397_);
lean_dec_ref_known(v_x_4048_, 3);
v_x_4398_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4398_);
v_n_4399_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_n_4399_);
v_c_4400_ = lean_ctor_get_uint8(v_x_4049_, sizeof(void*)*3);
v_persistent_4401_ = lean_ctor_get_uint8(v_x_4049_, sizeof(void*)*3 + 1);
v_b_4402_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_b_4402_);
lean_dec_ref_known(v_x_4049_, 3);
v_00_u03c1_4059_ = v_x_4047_;
v_x_u2081_4060_ = v_x_4393_;
v_n_u2081_4061_ = v_n_4394_;
v_c_u2081_4062_ = v_c_4395_;
v_p_u2081_4063_ = v_persistent_4396_;
v_b_u2081_4064_ = v_b_4397_;
v_x_u2082_4065_ = v_x_4398_;
v_n_u2082_4066_ = v_n_4399_;
v_c_u2082_4067_ = v_c_4400_;
v_p_u2082_4068_ = v_persistent_4401_;
v_b_u2082_4069_ = v_b_4402_;
goto v___jp_4058_;
}
else
{
uint8_t v___x_4403_; 
lean_dec_ref_known(v_x_4048_, 3);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4403_ = 0;
return v___x_4403_;
}
}
case 25:
{
if (lean_obj_tag(v_x_4049_) == 25)
{
lean_object* v_x_4404_; lean_object* v_n_4405_; uint8_t v_c_4406_; uint8_t v_persistent_4407_; lean_object* v_b_4408_; lean_object* v_x_4409_; lean_object* v_n_4410_; uint8_t v_c_4411_; uint8_t v_persistent_4412_; lean_object* v_b_4413_; 
v_x_4404_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4404_);
v_n_4405_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_n_4405_);
v_c_4406_ = lean_ctor_get_uint8(v_x_4048_, sizeof(void*)*3);
v_persistent_4407_ = lean_ctor_get_uint8(v_x_4048_, sizeof(void*)*3 + 1);
v_b_4408_ = lean_ctor_get(v_x_4048_, 2);
lean_inc(v_b_4408_);
lean_dec_ref_known(v_x_4048_, 3);
v_x_4409_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4409_);
v_n_4410_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_n_4410_);
v_c_4411_ = lean_ctor_get_uint8(v_x_4049_, sizeof(void*)*3);
v_persistent_4412_ = lean_ctor_get_uint8(v_x_4049_, sizeof(void*)*3 + 1);
v_b_4413_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_b_4413_);
lean_dec_ref_known(v_x_4049_, 3);
v_00_u03c1_4059_ = v_x_4047_;
v_x_u2081_4060_ = v_x_4404_;
v_n_u2081_4061_ = v_n_4405_;
v_c_u2081_4062_ = v_c_4406_;
v_p_u2081_4063_ = v_persistent_4407_;
v_b_u2081_4064_ = v_b_4408_;
v_x_u2082_4065_ = v_x_4409_;
v_n_u2082_4066_ = v_n_4410_;
v_c_u2082_4067_ = v_c_4411_;
v_p_u2082_4068_ = v_persistent_4412_;
v_b_u2082_4069_ = v_b_4413_;
goto v___jp_4058_;
}
else
{
uint8_t v___x_4414_; 
lean_dec_ref_known(v_x_4048_, 3);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4414_ = 0;
return v___x_4414_;
}
}
case 26:
{
if (lean_obj_tag(v_x_4049_) == 26)
{
lean_object* v_x_4415_; lean_object* v_b_4416_; lean_object* v_x_4417_; lean_object* v_b_4418_; uint8_t v___x_4419_; 
v_x_4415_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4415_);
v_b_4416_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_b_4416_);
lean_dec_ref_known(v_x_4048_, 2);
v_x_4417_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4417_);
v_b_4418_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_b_4418_);
lean_dec_ref_known(v_x_4049_, 2);
v___x_4419_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4415_, v_x_4417_);
lean_dec(v_x_4417_);
lean_dec(v_x_4415_);
if (v___x_4419_ == 0)
{
lean_dec(v_b_4418_);
lean_dec(v_b_4416_);
lean_dec(v_x_4047_);
return v___x_4419_;
}
else
{
v_x_4048_ = v_b_4416_;
v_x_4049_ = v_b_4418_;
goto _start;
}
}
else
{
uint8_t v___x_4421_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4421_ = 0;
return v___x_4421_;
}
}
case 27:
{
if (lean_obj_tag(v_x_4049_) == 27)
{
lean_object* v_tid_4422_; lean_object* v_x_4423_; lean_object* v_cs_4424_; lean_object* v_tid_4425_; lean_object* v_x_4426_; lean_object* v_cs_4427_; uint8_t v___x_4428_; 
v_tid_4422_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_tid_4422_);
v_x_4423_ = lean_ctor_get(v_x_4048_, 1);
lean_inc(v_x_4423_);
v_cs_4424_ = lean_ctor_get(v_x_4048_, 3);
lean_inc_ref(v_cs_4424_);
lean_dec_ref_known(v_x_4048_, 4);
v_tid_4425_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_tid_4425_);
v_x_4426_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_x_4426_);
v_cs_4427_ = lean_ctor_get(v_x_4049_, 3);
lean_inc_ref(v_cs_4427_);
lean_dec_ref_known(v_x_4049_, 4);
v___x_4428_ = lean_name_eq(v_tid_4422_, v_tid_4425_);
lean_dec(v_tid_4425_);
lean_dec(v_tid_4422_);
if (v___x_4428_ == 0)
{
lean_dec_ref(v_cs_4427_);
lean_dec(v_x_4426_);
lean_dec_ref(v_cs_4424_);
lean_dec(v_x_4423_);
lean_dec(v_x_4047_);
return v___x_4428_;
}
else
{
uint8_t v___x_4429_; 
v___x_4429_ = l_Lean_IR_VarId_alphaEqv(v_x_4047_, v_x_4423_, v_x_4426_);
lean_dec(v_x_4426_);
lean_dec(v_x_4423_);
if (v___x_4429_ == 0)
{
lean_dec_ref(v_cs_4427_);
lean_dec_ref(v_cs_4424_);
lean_dec(v_x_4047_);
return v___x_4429_;
}
else
{
lean_object* v___x_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4430_ = lean_array_get_size(v_cs_4424_);
v___x_4431_ = lean_array_get_size(v_cs_4427_);
v___x_4432_ = lean_nat_dec_eq(v___x_4430_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_dec_ref(v_cs_4427_);
lean_dec_ref(v_cs_4424_);
lean_dec(v_x_4047_);
return v___x_4432_;
}
else
{
uint8_t v___x_4433_; 
v___x_4433_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_4047_, v_cs_4424_, v_cs_4427_, v___x_4430_);
lean_dec_ref(v_cs_4427_);
lean_dec_ref(v_cs_4424_);
return v___x_4433_;
}
}
}
}
else
{
uint8_t v___x_4434_; 
lean_dec_ref_known(v_x_4048_, 4);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4434_ = 0;
return v___x_4434_;
}
}
case 28:
{
if (lean_obj_tag(v_x_4049_) == 28)
{
lean_object* v_x_4435_; lean_object* v_x_4436_; uint8_t v___x_4437_; 
v_x_4435_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_x_4435_);
lean_dec_ref_known(v_x_4048_, 1);
v_x_4436_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_x_4436_);
lean_dec_ref_known(v_x_4049_, 1);
v___x_4437_ = l_Lean_IR_Arg_alphaEqv(v_x_4047_, v_x_4435_, v_x_4436_);
lean_dec(v_x_4436_);
lean_dec(v_x_4435_);
lean_dec(v_x_4047_);
return v___x_4437_;
}
else
{
uint8_t v___x_4438_; 
lean_dec_ref_known(v_x_4048_, 1);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4438_ = 0;
return v___x_4438_;
}
}
case 29:
{
if (lean_obj_tag(v_x_4049_) == 29)
{
lean_object* v_j_4439_; lean_object* v_ys_4440_; lean_object* v_j_4441_; lean_object* v_ys_4442_; uint8_t v___x_4443_; 
v_j_4439_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_j_4439_);
v_ys_4440_ = lean_ctor_get(v_x_4048_, 1);
lean_inc_ref(v_ys_4440_);
lean_dec_ref_known(v_x_4048_, 2);
v_j_4441_ = lean_ctor_get(v_x_4049_, 0);
lean_inc(v_j_4441_);
v_ys_4442_ = lean_ctor_get(v_x_4049_, 1);
lean_inc_ref(v_ys_4442_);
lean_dec_ref_known(v_x_4049_, 2);
v___x_4443_ = lean_nat_dec_eq(v_j_4439_, v_j_4441_);
lean_dec(v_j_4441_);
lean_dec(v_j_4439_);
if (v___x_4443_ == 0)
{
lean_dec_ref(v_ys_4442_);
lean_dec_ref(v_ys_4440_);
lean_dec(v_x_4047_);
return v___x_4443_;
}
else
{
uint8_t v___x_4444_; 
v___x_4444_ = l_Lean_IR_args_alphaEqv(v_x_4047_, v_ys_4440_, v_ys_4442_);
lean_dec_ref(v_ys_4442_);
lean_dec_ref(v_ys_4440_);
lean_dec(v_x_4047_);
return v___x_4444_;
}
}
else
{
uint8_t v___x_4445_; 
lean_dec_ref_known(v_x_4048_, 2);
lean_dec(v_x_4049_);
lean_dec(v_x_4047_);
v___x_4445_ = 0;
return v___x_4445_;
}
}
default: 
{
lean_dec(v_x_4047_);
if (lean_obj_tag(v_x_4049_) == 30)
{
uint8_t v___x_4446_; 
v___x_4446_ = 1;
return v___x_4446_;
}
else
{
uint8_t v___x_4447_; 
lean_dec(v_x_4049_);
v___x_4447_ = 0;
return v___x_4447_;
}
}
}
v___jp_4050_:
{
if (v___y_4053_ == 0)
{
if (v___y_4055_ == 0)
{
v_x_4047_ = v___y_4052_;
v_x_4048_ = v___y_4051_;
v_x_4049_ = v___y_4054_;
goto _start;
}
else
{
lean_dec(v___y_4054_);
lean_dec(v___y_4052_);
lean_dec(v___y_4051_);
return v___y_4053_;
}
}
else
{
if (v___y_4055_ == 0)
{
lean_dec(v___y_4054_);
lean_dec(v___y_4052_);
lean_dec(v___y_4051_);
return v___y_4055_;
}
else
{
v_x_4047_ = v___y_4052_;
v_x_4048_ = v___y_4051_;
v_x_4049_ = v___y_4054_;
goto _start;
}
}
}
v___jp_4058_:
{
uint8_t v___x_4070_; 
v___x_4070_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_4059_, v_x_u2081_4060_, v_x_u2082_4065_);
lean_dec(v_x_u2082_4065_);
lean_dec(v_x_u2081_4060_);
if (v___x_4070_ == 0)
{
lean_dec(v_b_u2082_4069_);
lean_dec(v_n_u2082_4066_);
lean_dec(v_b_u2081_4064_);
lean_dec(v_n_u2081_4061_);
lean_dec(v_00_u03c1_4059_);
return v___x_4070_;
}
else
{
uint8_t v___x_4071_; 
v___x_4071_ = lean_nat_dec_eq(v_n_u2081_4061_, v_n_u2082_4066_);
lean_dec(v_n_u2082_4066_);
lean_dec(v_n_u2081_4061_);
if (v___x_4071_ == 0)
{
lean_dec(v_b_u2082_4069_);
lean_dec(v_b_u2081_4064_);
lean_dec(v_00_u03c1_4059_);
return v___x_4071_;
}
else
{
if (v_c_u2082_4067_ == 0)
{
if (v_c_u2081_4062_ == 0)
{
v___y_4051_ = v_b_u2081_4064_;
v___y_4052_ = v_00_u03c1_4059_;
v___y_4053_ = v_p_u2082_4068_;
v___y_4054_ = v_b_u2082_4069_;
v___y_4055_ = v_p_u2081_4063_;
goto v___jp_4050_;
}
else
{
lean_dec(v_b_u2082_4069_);
lean_dec(v_b_u2081_4064_);
lean_dec(v_00_u03c1_4059_);
return v_c_u2082_4067_;
}
}
else
{
if (v_c_u2081_4062_ == 0)
{
lean_dec(v_b_u2082_4069_);
lean_dec(v_b_u2081_4064_);
lean_dec(v_00_u03c1_4059_);
return v_c_u2081_4062_;
}
else
{
v___y_4051_ = v_b_u2081_4064_;
v___y_4052_ = v_00_u03c1_4059_;
v___y_4053_ = v_p_u2082_4068_;
v___y_4054_ = v_b_u2082_4069_;
v___y_4055_ = v_p_u2081_4063_;
goto v___jp_4050_;
}
}
}
}
}
v___jp_4072_:
{
uint8_t v___x_4080_; 
v___x_4080_ = lean_uint64_dec_eq(v_v_u2081_4076_, v_v_u2082_4079_);
if (v___x_4080_ == 0)
{
lean_dec(v_b_u2082_4078_);
lean_dec(v_tgt_u2082_4077_);
lean_dec(v_b_u2081_4075_);
lean_dec(v_tgt_u2081_4074_);
lean_dec(v_00_u03c1_4073_);
return v___x_4080_;
}
else
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_IR_addVarRename(v_00_u03c1_4073_, v_tgt_u2081_4074_, v_tgt_u2082_4077_);
v_x_4047_ = v___x_4081_;
v_x_4048_ = v_b_u2081_4075_;
v_x_4049_ = v_b_u2082_4078_;
goto _start;
}
}
v___jp_4083_:
{
uint8_t v___x_4093_; 
v___x_4093_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_4087_, v_ty_u2082_4091_);
lean_dec(v_ty_u2082_4091_);
lean_dec(v_ty_u2081_4087_);
if (v___x_4093_ == 0)
{
lean_dec(v_x_u2082_4092_);
lean_dec(v_b_u2082_4090_);
lean_dec(v_tgt_u2082_4089_);
lean_dec(v_x_u2081_4088_);
lean_dec(v_b_u2081_4086_);
lean_dec(v_tgt_u2081_4085_);
lean_dec(v_00_u03c1_4084_);
return v___x_4093_;
}
else
{
uint8_t v___x_4094_; 
v___x_4094_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_4084_, v_x_u2081_4088_, v_x_u2082_4092_);
lean_dec(v_x_u2082_4092_);
lean_dec(v_x_u2081_4088_);
if (v___x_4094_ == 0)
{
lean_dec(v_b_u2082_4090_);
lean_dec(v_tgt_u2082_4089_);
lean_dec(v_b_u2081_4086_);
lean_dec(v_tgt_u2081_4085_);
lean_dec(v_00_u03c1_4084_);
return v___x_4094_;
}
else
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_IR_addVarRename(v_00_u03c1_4084_, v_tgt_u2081_4085_, v_tgt_u2082_4089_);
v_x_4047_ = v___x_4095_;
v_x_4048_ = v_b_u2081_4086_;
v_x_4049_ = v_b_u2082_4090_;
goto _start;
}
}
}
v___jp_4097_:
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_nat_dec_eq(v_n_u2081_4101_, v_n_u2082_4105_);
lean_dec(v_n_u2082_4105_);
lean_dec(v_n_u2081_4101_);
if (v___x_4107_ == 0)
{
lean_dec(v_x_u2082_4106_);
lean_dec(v_b_u2082_4104_);
lean_dec(v_tgt_u2082_4103_);
lean_dec(v_x_u2081_4102_);
lean_dec(v_b_u2081_4100_);
lean_dec(v_tgt_u2081_4099_);
lean_dec(v_00_u03c1_4098_);
return v___x_4107_;
}
else
{
uint8_t v___x_4108_; 
v___x_4108_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_4098_, v_x_u2081_4102_, v_x_u2082_4106_);
lean_dec(v_x_u2082_4106_);
lean_dec(v_x_u2081_4102_);
if (v___x_4108_ == 0)
{
lean_dec(v_b_u2082_4104_);
lean_dec(v_tgt_u2082_4103_);
lean_dec(v_b_u2081_4100_);
lean_dec(v_tgt_u2081_4099_);
lean_dec(v_00_u03c1_4098_);
return v___x_4108_;
}
else
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_IR_addVarRename(v_00_u03c1_4098_, v_tgt_u2081_4099_, v_tgt_u2082_4103_);
v_x_4047_ = v___x_4109_;
v_x_4048_ = v_b_u2081_4100_;
v_x_4049_ = v_b_u2082_4104_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* v_x_4448_, lean_object* v_xs_4449_, lean_object* v_ys_4450_, lean_object* v_x_4451_){
_start:
{
lean_object* v_zero_4452_; uint8_t v_isZero_4453_; 
v_zero_4452_ = lean_unsigned_to_nat(0u);
v_isZero_4453_ = lean_nat_dec_eq(v_x_4451_, v_zero_4452_);
if (v_isZero_4453_ == 1)
{
lean_dec(v_x_4451_);
lean_dec(v_x_4448_);
return v_isZero_4453_;
}
else
{
lean_object* v_one_4454_; lean_object* v_n_4455_; uint8_t v___y_4457_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v_one_4454_ = lean_unsigned_to_nat(1u);
v_n_4455_ = lean_nat_sub(v_x_4451_, v_one_4454_);
lean_dec(v_x_4451_);
v___x_4459_ = lean_array_fget_borrowed(v_xs_4449_, v_n_4455_);
v___x_4460_ = lean_array_fget_borrowed(v_ys_4450_, v_n_4455_);
if (lean_obj_tag(v___x_4459_) == 0)
{
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_info_4461_; lean_object* v_b_4462_; lean_object* v_info_4463_; lean_object* v_b_4464_; uint8_t v___x_4465_; 
v_info_4461_ = lean_ctor_get(v___x_4459_, 0);
v_b_4462_ = lean_ctor_get(v___x_4459_, 1);
v_info_4463_ = lean_ctor_get(v___x_4460_, 0);
v_b_4464_ = lean_ctor_get(v___x_4460_, 1);
v___x_4465_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_4461_, v_info_4463_);
if (v___x_4465_ == 0)
{
lean_dec(v_n_4455_);
lean_dec(v_x_4448_);
return v___x_4465_;
}
else
{
uint8_t v___x_4466_; 
lean_inc(v_b_4464_);
lean_inc(v_b_4462_);
lean_inc(v_x_4448_);
v___x_4466_ = l_Lean_IR_FnBody_alphaEqv(v_x_4448_, v_b_4462_, v_b_4464_);
v___y_4457_ = v___x_4466_;
goto v___jp_4456_;
}
}
else
{
lean_dec(v_n_4455_);
lean_dec(v_x_4448_);
return v_isZero_4453_;
}
}
else
{
if (lean_obj_tag(v___x_4460_) == 1)
{
lean_object* v_b_4467_; lean_object* v_b_4468_; uint8_t v___x_4469_; 
v_b_4467_ = lean_ctor_get(v___x_4459_, 0);
v_b_4468_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_b_4468_);
lean_inc(v_b_4467_);
lean_inc(v_x_4448_);
v___x_4469_ = l_Lean_IR_FnBody_alphaEqv(v_x_4448_, v_b_4467_, v_b_4468_);
v___y_4457_ = v___x_4469_;
goto v___jp_4456_;
}
else
{
lean_dec(v_n_4455_);
lean_dec(v_x_4448_);
return v_isZero_4453_;
}
}
v___jp_4456_:
{
if (v___y_4457_ == 0)
{
lean_dec(v_n_4455_);
lean_dec(v_x_4448_);
return v___y_4457_;
}
else
{
v_x_4451_ = v_n_4455_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* v_x_4470_, lean_object* v_xs_4471_, lean_object* v_ys_4472_, lean_object* v_x_4473_){
_start:
{
uint8_t v_res_4474_; lean_object* v_r_4475_; 
v_res_4474_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_4470_, v_xs_4471_, v_ys_4472_, v_x_4473_);
lean_dec_ref(v_ys_4472_);
lean_dec_ref(v_xs_4471_);
v_r_4475_ = lean_box(v_res_4474_);
return v_r_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* v_x_4476_, lean_object* v_x_4477_, lean_object* v_x_4478_){
_start:
{
uint8_t v_res_4479_; lean_object* v_r_4480_; 
v_res_4479_ = l_Lean_IR_FnBody_alphaEqv(v_x_4476_, v_x_4477_, v_x_4478_);
v_r_4480_ = lean_box(v_res_4479_);
return v_r_4480_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object* v_x_4481_, lean_object* v_xs_4482_, lean_object* v_ys_4483_, lean_object* v_hsz_4484_, lean_object* v_x_4485_, lean_object* v_x_4486_){
_start:
{
uint8_t v___x_4487_; 
v___x_4487_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_4481_, v_xs_4482_, v_ys_4483_, v_x_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* v_x_4488_, lean_object* v_xs_4489_, lean_object* v_ys_4490_, lean_object* v_hsz_4491_, lean_object* v_x_4492_, lean_object* v_x_4493_){
_start:
{
uint8_t v_res_4494_; lean_object* v_r_4495_; 
v_res_4494_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(v_x_4488_, v_xs_4489_, v_ys_4490_, v_hsz_4491_, v_x_4492_, v_x_4493_);
lean_dec_ref(v_ys_4490_);
lean_dec_ref(v_xs_4489_);
v_r_4495_ = lean_box(v_res_4494_);
return v_r_4495_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* v_b_u2081_4496_, lean_object* v_b_u2082_4497_){
_start:
{
lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4498_ = lean_box(1);
v___x_4499_ = l_Lean_IR_FnBody_alphaEqv(v___x_4498_, v_b_u2081_4496_, v_b_u2082_4497_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* v_b_u2081_4500_, lean_object* v_b_u2082_4501_){
_start:
{
uint8_t v_res_4502_; lean_object* v_r_4503_; 
v_res_4502_ = l_Lean_IR_FnBody_beq(v_b_u2081_4500_, v_b_u2082_4501_);
v_r_4503_ = lean_box(v_res_4502_);
return v_r_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* v_x_4524_, lean_object* v_t_4525_, lean_object* v_e_4526_){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4527_ = ((lean_object*)(l_Lean_IR_mkIf___closed__1));
v___x_4528_ = lean_box(1);
v___x_4529_ = ((lean_object*)(l_Lean_IR_mkIf___closed__4));
v___x_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
lean_ctor_set(v___x_4530_, 1, v_e_4526_);
v___x_4531_ = ((lean_object*)(l_Lean_IR_mkIf___closed__7));
v___x_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
lean_ctor_set(v___x_4532_, 1, v_t_4525_);
v___x_4533_ = lean_unsigned_to_nat(2u);
v___x_4534_ = lean_mk_empty_array_with_capacity(v___x_4533_);
v___x_4535_ = lean_array_push(v___x_4534_, v___x_4530_);
v___x_4536_ = lean_array_push(v___x_4535_, v___x_4532_);
v___x_4537_ = lean_alloc_ctor(27, 4, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4527_);
lean_ctor_set(v___x_4537_, 1, v_x_4524_);
lean_ctor_set(v___x_4537_, 2, v___x_4528_);
lean_ctor_set(v___x_4537_, 3, v___x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* v_t_4544_){
_start:
{
switch(lean_obj_tag(v_t_4544_))
{
case 5:
{
lean_object* v___x_4545_; 
v___x_4545_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__0));
return v___x_4545_;
}
case 3:
{
lean_object* v___x_4546_; 
v___x_4546_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__1));
return v___x_4546_;
}
case 4:
{
lean_object* v___x_4547_; 
v___x_4547_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__2));
return v___x_4547_;
}
case 0:
{
lean_object* v___x_4548_; 
v___x_4548_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__3));
return v___x_4548_;
}
case 9:
{
lean_object* v___x_4549_; 
v___x_4549_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__4));
return v___x_4549_;
}
default: 
{
lean_object* v___x_4550_; 
v___x_4550_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__5));
return v___x_4550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* v_t_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_IR_getUnboxOpName(v_t_4551_);
lean_dec(v_t_4551_);
return v_res_4552_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
