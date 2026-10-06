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
v___x_1648_ = lean_unsigned_to_nat(326u);
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
lean_object* v___x_1663_; 
v___x_1663_ = lean_box(8);
return v___x_1663_;
}
case 10:
{
lean_object* v_ty_1664_; 
v_ty_1664_ = lean_ctor_get(v_x_1652_, 2);
lean_inc(v_ty_1664_);
return v_ty_1664_;
}
case 11:
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_box(1);
return v___x_1665_;
}
case 12:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_box(2);
return v___x_1666_;
}
case 13:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_box(3);
return v___x_1667_;
}
case 14:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_box(4);
return v___x_1668_;
}
case 15:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_box(5);
return v___x_1669_;
}
case 16:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_box(8);
return v___x_1670_;
}
case 17:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_box(7);
return v___x_1671_;
}
case 18:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_box(1);
return v___x_1672_;
}
default: 
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_obj_once(&l_Lean_IR_FnBody_targetType___closed__1, &l_Lean_IR_FnBody_targetType___closed__1_once, _init_l_Lean_IR_FnBody_targetType___closed__1);
v___x_1674_ = l_panic___at___00Lean_IR_FnBody_targetType_spec__0(v___x_1673_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_targetType___boxed(lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_IR_FnBody_targetType(v_x_1675_);
lean_dec(v_x_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_FnBody_setTargetVar_spec__0(lean_object* v_msg_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_1679_ = lean_panic_fn_borrowed(v___x_1678_, v_msg_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_setTargetVar___closed__1(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1681_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__2));
v___x_1682_ = lean_unsigned_to_nat(12u);
v___x_1683_ = lean_unsigned_to_nat(348u);
v___x_1684_ = ((lean_object*)(l_Lean_IR_FnBody_setTargetVar___closed__0));
v___x_1685_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__0));
v___x_1686_ = l_mkPanicMessageWithDecl(v___x_1685_, v___x_1684_, v___x_1683_, v___x_1682_, v___x_1681_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTargetVar(lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
switch(lean_obj_tag(v_x_1687_))
{
case 0:
{
lean_object* v_b_1689_; lean_object* v_i_1690_; lean_object* v_ys_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_b_1689_ = lean_ctor_get(v_x_1687_, 1);
v_i_1690_ = lean_ctor_get(v_x_1687_, 2);
v_ys_1691_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1699_);
v___x_1693_ = v_x_1687_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_ys_1691_);
lean_inc(v_i_1690_);
lean_inc(v_b_1689_);
lean_dec(v_x_1687_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v_x_1688_);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_b_1689_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_i_1690_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_ys_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
case 1:
{
lean_object* v_b_1700_; lean_object* v_n_1701_; lean_object* v_x_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_b_1700_ = lean_ctor_get(v_x_1687_, 1);
v_n_1701_ = lean_ctor_get(v_x_1687_, 2);
v_x_1702_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1710_);
v___x_1704_ = v_x_1687_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_x_1702_);
lean_inc(v_n_1701_);
lean_inc(v_b_1700_);
lean_dec(v_x_1687_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v_x_1688_);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_b_1700_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_n_1701_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_x_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
case 2:
{
lean_object* v_b_1711_; lean_object* v_x_1712_; lean_object* v_i_1713_; uint8_t v_updtHeader_1714_; lean_object* v_ys_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_b_1711_ = lean_ctor_get(v_x_1687_, 1);
v_x_1712_ = lean_ctor_get(v_x_1687_, 2);
v_i_1713_ = lean_ctor_get(v_x_1687_, 3);
v_updtHeader_1714_ = lean_ctor_get_uint8(v_x_1687_, sizeof(void*)*5);
v_ys_1715_ = lean_ctor_get(v_x_1687_, 4);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1723_);
v___x_1717_ = v_x_1687_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_ys_1715_);
lean_inc(v_i_1713_);
lean_inc(v_x_1712_);
lean_inc(v_b_1711_);
lean_dec(v_x_1687_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_x_1688_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_b_1711_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_x_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_i_1713_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_ys_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*5, v_updtHeader_1714_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
case 3:
{
lean_object* v_b_1724_; lean_object* v_i_1725_; lean_object* v_x_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_b_1724_ = lean_ctor_get(v_x_1687_, 1);
v_i_1725_ = lean_ctor_get(v_x_1687_, 2);
v_x_1726_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1734_);
v___x_1728_ = v_x_1687_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_x_1726_);
lean_inc(v_i_1725_);
lean_inc(v_b_1724_);
lean_dec(v_x_1687_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_x_1688_);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_b_1724_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_i_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_x_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
case 4:
{
lean_object* v_b_1735_; lean_object* v_i_1736_; lean_object* v_x_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_b_1735_ = lean_ctor_get(v_x_1687_, 1);
v_i_1736_ = lean_ctor_get(v_x_1687_, 2);
v_x_1737_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1745_);
v___x_1739_ = v_x_1687_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_x_1737_);
lean_inc(v_i_1736_);
lean_inc(v_b_1735_);
lean_dec(v_x_1687_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_x_1688_);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_x_1688_);
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
case 5:
{
lean_object* v_b_1746_; lean_object* v_ty_1747_; lean_object* v_n_1748_; lean_object* v_offset_1749_; lean_object* v_x_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_b_1746_ = lean_ctor_get(v_x_1687_, 1);
v_ty_1747_ = lean_ctor_get(v_x_1687_, 2);
v_n_1748_ = lean_ctor_get(v_x_1687_, 3);
v_offset_1749_ = lean_ctor_get(v_x_1687_, 4);
v_x_1750_ = lean_ctor_get(v_x_1687_, 5);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1758_);
v___x_1752_ = v_x_1687_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_x_1750_);
lean_inc(v_offset_1749_);
lean_inc(v_n_1748_);
lean_inc(v_ty_1747_);
lean_inc(v_b_1746_);
lean_dec(v_x_1687_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v_x_1688_);
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_b_1746_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_ty_1747_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_n_1748_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_offset_1749_);
lean_ctor_set(v_reuseFailAlloc_1756_, 5, v_x_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
case 6:
{
lean_object* v_b_1759_; lean_object* v_ty_1760_; lean_object* v_c_1761_; lean_object* v_ys_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_b_1759_ = lean_ctor_get(v_x_1687_, 1);
v_ty_1760_ = lean_ctor_get(v_x_1687_, 2);
v_c_1761_ = lean_ctor_get(v_x_1687_, 3);
v_ys_1762_ = lean_ctor_get(v_x_1687_, 4);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1770_);
v___x_1764_ = v_x_1687_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_ys_1762_);
lean_inc(v_c_1761_);
lean_inc(v_ty_1760_);
lean_inc(v_b_1759_);
lean_dec(v_x_1687_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v_x_1688_);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_b_1759_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_ty_1760_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_c_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_ys_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
case 7:
{
lean_object* v_b_1771_; lean_object* v_c_1772_; lean_object* v_ys_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_b_1771_ = lean_ctor_get(v_x_1687_, 1);
v_c_1772_ = lean_ctor_get(v_x_1687_, 2);
v_ys_1773_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1781_);
v___x_1775_ = v_x_1687_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_ys_1773_);
lean_inc(v_c_1772_);
lean_inc(v_b_1771_);
lean_dec(v_x_1687_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v_x_1688_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_b_1771_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_c_1772_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_ys_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
case 8:
{
lean_object* v_b_1782_; lean_object* v_x_1783_; lean_object* v_ys_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_b_1782_ = lean_ctor_get(v_x_1687_, 1);
v_x_1783_ = lean_ctor_get(v_x_1687_, 2);
v_ys_1784_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1792_);
v___x_1786_ = v_x_1687_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_ys_1784_);
lean_inc(v_x_1783_);
lean_inc(v_b_1782_);
lean_dec(v_x_1687_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_x_1688_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_b_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_x_1783_);
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
case 9:
{
lean_object* v_b_1793_; lean_object* v_ty_1794_; lean_object* v_x_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_b_1793_ = lean_ctor_get(v_x_1687_, 1);
v_ty_1794_ = lean_ctor_get(v_x_1687_, 2);
v_x_1795_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1803_);
v___x_1797_ = v_x_1687_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_x_1795_);
lean_inc(v_ty_1794_);
lean_inc(v_b_1793_);
lean_dec(v_x_1687_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v_x_1688_);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_b_1793_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_ty_1794_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_x_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
case 10:
{
lean_object* v_b_1804_; lean_object* v_ty_1805_; lean_object* v_x_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_b_1804_ = lean_ctor_get(v_x_1687_, 1);
v_ty_1805_ = lean_ctor_get(v_x_1687_, 2);
v_x_1806_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1814_);
v___x_1808_ = v_x_1687_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_x_1806_);
lean_inc(v_ty_1805_);
lean_inc(v_b_1804_);
lean_dec(v_x_1687_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_x_1688_);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_x_1688_);
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
case 11:
{
lean_object* v_b_1815_; uint8_t v_v_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_b_1815_ = lean_ctor_get(v_x_1687_, 1);
v_v_1816_ = lean_ctor_get_uint8(v_x_1687_, sizeof(void*)*2);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1824_);
v___x_1818_ = v_x_1687_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_b_1815_);
lean_dec(v_x_1687_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_x_1688_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_b_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, sizeof(void*)*2, v_v_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
case 12:
{
lean_object* v_b_1825_; uint16_t v_v_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_b_1825_ = lean_ctor_get(v_x_1687_, 1);
v_v_1826_ = lean_ctor_get_uint16(v_x_1687_, sizeof(void*)*2);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1834_);
v___x_1828_ = v_x_1687_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_b_1825_);
lean_dec(v_x_1687_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v_x_1688_);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_b_1825_);
lean_ctor_set_uint16(v_reuseFailAlloc_1832_, sizeof(void*)*2, v_v_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
case 13:
{
lean_object* v_b_1835_; uint32_t v_v_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_b_1835_ = lean_ctor_get(v_x_1687_, 1);
v_v_1836_ = lean_ctor_get_uint32(v_x_1687_, sizeof(void*)*2);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1844_);
v___x_1838_ = v_x_1687_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_b_1835_);
lean_dec(v_x_1687_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_x_1688_);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_b_1835_);
lean_ctor_set_uint32(v_reuseFailAlloc_1842_, sizeof(void*)*2, v_v_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
case 14:
{
lean_object* v_b_1845_; uint64_t v_v_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_b_1845_ = lean_ctor_get(v_x_1687_, 1);
v_v_1846_ = lean_ctor_get_uint64(v_x_1687_, sizeof(void*)*2);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1854_);
v___x_1848_ = v_x_1687_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_b_1845_);
lean_dec(v_x_1687_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_x_1688_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_b_1845_);
lean_ctor_set_uint64(v_reuseFailAlloc_1852_, sizeof(void*)*2, v_v_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
case 15:
{
lean_object* v_b_1855_; uint64_t v_v_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_b_1855_ = lean_ctor_get(v_x_1687_, 1);
v_v_1856_ = lean_ctor_get_uint64(v_x_1687_, sizeof(void*)*2);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1864_);
v___x_1858_ = v_x_1687_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_b_1855_);
lean_dec(v_x_1687_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_x_1688_);
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_b_1855_);
lean_ctor_set_uint64(v_reuseFailAlloc_1862_, sizeof(void*)*2, v_v_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
case 16:
{
lean_object* v_b_1865_; lean_object* v_v_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_b_1865_ = lean_ctor_get(v_x_1687_, 1);
v_v_1866_ = lean_ctor_get(v_x_1687_, 2);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1874_);
v___x_1868_ = v_x_1687_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_v_1866_);
lean_inc(v_b_1865_);
lean_dec(v_x_1687_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v_x_1688_);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_b_1865_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_v_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
case 17:
{
lean_object* v_b_1875_; lean_object* v_v_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_b_1875_ = lean_ctor_get(v_x_1687_, 1);
v_v_1876_ = lean_ctor_get(v_x_1687_, 2);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; 
v_unused_1884_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1884_);
v___x_1878_ = v_x_1687_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_v_1876_);
lean_inc(v_b_1875_);
lean_dec(v_x_1687_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_x_1688_);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_b_1875_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_v_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
case 18:
{
lean_object* v_b_1885_; lean_object* v_x_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_b_1885_ = lean_ctor_get(v_x_1687_, 1);
v_x_1886_ = lean_ctor_get(v_x_1687_, 2);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v_x_1687_, 0);
lean_dec(v_unused_1894_);
v___x_1888_ = v_x_1687_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_x_1886_);
lean_inc(v_b_1885_);
lean_dec(v_x_1687_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v_x_1688_);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_x_1688_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_b_1885_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_x_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
default: 
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_x_1688_);
lean_dec(v_x_1687_);
v___x_1895_ = lean_obj_once(&l_Lean_IR_FnBody_setTargetVar___closed__1, &l_Lean_IR_FnBody_setTargetVar___closed__1_once, _init_l_Lean_IR_FnBody_setTargetVar___closed__1);
v___x_1896_ = l_panic___at___00Lean_IR_FnBody_setTargetVar_spec__0(v___x_1895_);
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object* v_x_1897_){
_start:
{
switch(lean_obj_tag(v_x_1897_))
{
case 0:
{
lean_object* v_b_1898_; 
v_b_1898_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1898_);
return v_b_1898_;
}
case 1:
{
lean_object* v_b_1899_; 
v_b_1899_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1899_);
return v_b_1899_;
}
case 2:
{
lean_object* v_b_1900_; 
v_b_1900_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1900_);
return v_b_1900_;
}
case 3:
{
lean_object* v_b_1901_; 
v_b_1901_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1901_);
return v_b_1901_;
}
case 4:
{
lean_object* v_b_1902_; 
v_b_1902_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1902_);
return v_b_1902_;
}
case 5:
{
lean_object* v_b_1903_; 
v_b_1903_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1903_);
return v_b_1903_;
}
case 6:
{
lean_object* v_b_1904_; 
v_b_1904_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1904_);
return v_b_1904_;
}
case 7:
{
lean_object* v_b_1905_; 
v_b_1905_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1905_);
return v_b_1905_;
}
case 8:
{
lean_object* v_b_1906_; 
v_b_1906_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1906_);
return v_b_1906_;
}
case 9:
{
lean_object* v_b_1907_; 
v_b_1907_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1907_);
return v_b_1907_;
}
case 10:
{
lean_object* v_b_1908_; 
v_b_1908_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1908_);
return v_b_1908_;
}
case 11:
{
lean_object* v_b_1909_; 
v_b_1909_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1909_);
return v_b_1909_;
}
case 12:
{
lean_object* v_b_1910_; 
v_b_1910_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1910_);
return v_b_1910_;
}
case 13:
{
lean_object* v_b_1911_; 
v_b_1911_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1911_);
return v_b_1911_;
}
case 14:
{
lean_object* v_b_1912_; 
v_b_1912_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1912_);
return v_b_1912_;
}
case 15:
{
lean_object* v_b_1913_; 
v_b_1913_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1913_);
return v_b_1913_;
}
case 16:
{
lean_object* v_b_1914_; 
v_b_1914_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1914_);
return v_b_1914_;
}
case 17:
{
lean_object* v_b_1915_; 
v_b_1915_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1915_);
return v_b_1915_;
}
case 18:
{
lean_object* v_b_1916_; 
v_b_1916_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1916_);
return v_b_1916_;
}
case 19:
{
lean_object* v_b_1917_; 
v_b_1917_ = lean_ctor_get(v_x_1897_, 3);
lean_inc(v_b_1917_);
return v_b_1917_;
}
case 20:
{
lean_object* v_b_1918_; 
v_b_1918_ = lean_ctor_get(v_x_1897_, 3);
lean_inc(v_b_1918_);
return v_b_1918_;
}
case 22:
{
lean_object* v_b_1919_; 
v_b_1919_ = lean_ctor_get(v_x_1897_, 3);
lean_inc(v_b_1919_);
return v_b_1919_;
}
case 23:
{
lean_object* v_b_1920_; 
v_b_1920_ = lean_ctor_get(v_x_1897_, 5);
lean_inc(v_b_1920_);
return v_b_1920_;
}
case 21:
{
lean_object* v_b_1921_; 
v_b_1921_ = lean_ctor_get(v_x_1897_, 2);
lean_inc(v_b_1921_);
return v_b_1921_;
}
case 24:
{
lean_object* v_b_1922_; 
v_b_1922_ = lean_ctor_get(v_x_1897_, 2);
lean_inc(v_b_1922_);
return v_b_1922_;
}
case 25:
{
lean_object* v_b_1923_; 
v_b_1923_ = lean_ctor_get(v_x_1897_, 2);
lean_inc(v_b_1923_);
return v_b_1923_;
}
case 26:
{
lean_object* v_b_1924_; 
v_b_1924_ = lean_ctor_get(v_x_1897_, 1);
lean_inc(v_b_1924_);
return v_b_1924_;
}
default: 
{
lean_inc(v_x_1897_);
return v_x_1897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* v_x_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_IR_FnBody_body(v_x_1925_);
lean_dec(v_x_1925_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
switch(lean_obj_tag(v_x_1927_))
{
case 0:
{
lean_object* v_tgt_1929_; lean_object* v_i_1930_; lean_object* v_ys_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_tgt_1929_ = lean_ctor_get(v_x_1927_, 0);
v_i_1930_ = lean_ctor_get(v_x_1927_, 2);
v_ys_1931_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_1939_);
v___x_1933_ = v_x_1927_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_ys_1931_);
lean_inc(v_i_1930_);
lean_inc(v_tgt_1929_);
lean_dec(v_x_1927_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_x_1928_);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_tgt_1929_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_i_1930_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_ys_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
case 1:
{
lean_object* v_tgt_1940_; lean_object* v_n_1941_; lean_object* v_x_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_tgt_1940_ = lean_ctor_get(v_x_1927_, 0);
v_n_1941_ = lean_ctor_get(v_x_1927_, 2);
v_x_1942_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_1950_);
v___x_1944_ = v_x_1927_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_x_1942_);
lean_inc(v_n_1941_);
lean_inc(v_tgt_1940_);
lean_dec(v_x_1927_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_x_1928_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_tgt_1940_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_n_1941_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_x_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
case 2:
{
lean_object* v_tgt_1951_; lean_object* v_x_1952_; lean_object* v_i_1953_; uint8_t v_updtHeader_1954_; lean_object* v_ys_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_tgt_1951_ = lean_ctor_get(v_x_1927_, 0);
v_x_1952_ = lean_ctor_get(v_x_1927_, 2);
v_i_1953_ = lean_ctor_get(v_x_1927_, 3);
v_updtHeader_1954_ = lean_ctor_get_uint8(v_x_1927_, sizeof(void*)*5);
v_ys_1955_ = lean_ctor_get(v_x_1927_, 4);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_1963_);
v___x_1957_ = v_x_1927_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_ys_1955_);
lean_inc(v_i_1953_);
lean_inc(v_x_1952_);
lean_inc(v_tgt_1951_);
lean_dec(v_x_1927_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_x_1928_);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(2, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_tgt_1951_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_x_1952_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_i_1953_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_ys_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*5, v_updtHeader_1954_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
case 3:
{
lean_object* v_tgt_1964_; lean_object* v_i_1965_; lean_object* v_x_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_tgt_1964_ = lean_ctor_get(v_x_1927_, 0);
v_i_1965_ = lean_ctor_get(v_x_1927_, 2);
v_x_1966_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_1974_);
v___x_1968_ = v_x_1927_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_x_1966_);
lean_inc(v_i_1965_);
lean_inc(v_tgt_1964_);
lean_dec(v_x_1927_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v_x_1928_);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_tgt_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_i_1965_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_x_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
case 4:
{
lean_object* v_tgt_1975_; lean_object* v_i_1976_; lean_object* v_x_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v_tgt_1975_ = lean_ctor_get(v_x_1927_, 0);
v_i_1976_ = lean_ctor_get(v_x_1927_, 2);
v_x_1977_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_1985_);
v___x_1979_ = v_x_1927_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_x_1977_);
lean_inc(v_i_1976_);
lean_inc(v_tgt_1975_);
lean_dec(v_x_1927_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v_x_1928_);
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_tgt_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_x_1928_);
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
case 5:
{
lean_object* v_tgt_1986_; lean_object* v_ty_1987_; lean_object* v_n_1988_; lean_object* v_offset_1989_; lean_object* v_x_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_tgt_1986_ = lean_ctor_get(v_x_1927_, 0);
v_ty_1987_ = lean_ctor_get(v_x_1927_, 2);
v_n_1988_ = lean_ctor_get(v_x_1927_, 3);
v_offset_1989_ = lean_ctor_get(v_x_1927_, 4);
v_x_1990_ = lean_ctor_get(v_x_1927_, 5);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_1998_);
v___x_1992_ = v_x_1927_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_x_1990_);
lean_inc(v_offset_1989_);
lean_inc(v_n_1988_);
lean_inc(v_ty_1987_);
lean_inc(v_tgt_1986_);
lean_dec(v_x_1927_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_x_1928_);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_tgt_1986_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_ty_1987_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_n_1988_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_offset_1989_);
lean_ctor_set(v_reuseFailAlloc_1996_, 5, v_x_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
case 6:
{
lean_object* v_tgt_1999_; lean_object* v_ty_2000_; lean_object* v_c_2001_; lean_object* v_ys_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_tgt_1999_ = lean_ctor_get(v_x_1927_, 0);
v_ty_2000_ = lean_ctor_get(v_x_1927_, 2);
v_c_2001_ = lean_ctor_get(v_x_1927_, 3);
v_ys_2002_ = lean_ctor_get(v_x_1927_, 4);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2010_);
v___x_2004_ = v_x_1927_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_ys_2002_);
lean_inc(v_c_2001_);
lean_inc(v_ty_2000_);
lean_inc(v_tgt_1999_);
lean_dec(v_x_1927_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v_x_1928_);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_tgt_1999_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_ty_2000_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_c_2001_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_ys_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
case 7:
{
lean_object* v_tgt_2011_; lean_object* v_c_2012_; lean_object* v_ys_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_tgt_2011_ = lean_ctor_get(v_x_1927_, 0);
v_c_2012_ = lean_ctor_get(v_x_1927_, 2);
v_ys_2013_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2021_);
v___x_2015_ = v_x_1927_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_ys_2013_);
lean_inc(v_c_2012_);
lean_inc(v_tgt_2011_);
lean_dec(v_x_1927_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_x_1928_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_tgt_2011_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_c_2012_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_ys_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
case 8:
{
lean_object* v_tgt_2022_; lean_object* v_x_2023_; lean_object* v_ys_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_tgt_2022_ = lean_ctor_get(v_x_1927_, 0);
v_x_2023_ = lean_ctor_get(v_x_1927_, 2);
v_ys_2024_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2032_);
v___x_2026_ = v_x_1927_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_ys_2024_);
lean_inc(v_x_2023_);
lean_inc(v_tgt_2022_);
lean_dec(v_x_1927_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v_x_1928_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_tgt_2022_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_x_2023_);
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
case 9:
{
lean_object* v_tgt_2033_; lean_object* v_ty_2034_; lean_object* v_x_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_tgt_2033_ = lean_ctor_get(v_x_1927_, 0);
v_ty_2034_ = lean_ctor_get(v_x_1927_, 2);
v_x_2035_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2043_);
v___x_2037_ = v_x_1927_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_x_2035_);
lean_inc(v_ty_2034_);
lean_inc(v_tgt_2033_);
lean_dec(v_x_1927_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 1, v_x_1928_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_tgt_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_ty_2034_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_x_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
case 10:
{
lean_object* v_tgt_2044_; lean_object* v_ty_2045_; lean_object* v_x_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_tgt_2044_ = lean_ctor_get(v_x_1927_, 0);
v_ty_2045_ = lean_ctor_get(v_x_1927_, 2);
v_x_2046_ = lean_ctor_get(v_x_1927_, 3);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2054_);
v___x_2048_ = v_x_1927_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_x_2046_);
lean_inc(v_ty_2045_);
lean_inc(v_tgt_2044_);
lean_dec(v_x_1927_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v_x_1928_);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_tgt_2044_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_x_1928_);
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
case 11:
{
lean_object* v_tgt_2055_; uint8_t v_v_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_tgt_2055_ = lean_ctor_get(v_x_1927_, 0);
v_v_2056_ = lean_ctor_get_uint8(v_x_1927_, sizeof(void*)*2);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2064_);
v___x_2058_ = v_x_1927_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_tgt_2055_);
lean_dec(v_x_1927_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v_x_1928_);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(11, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_tgt_2055_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_x_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2062_, sizeof(void*)*2, v_v_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
case 12:
{
lean_object* v_tgt_2065_; uint16_t v_v_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_tgt_2065_ = lean_ctor_get(v_x_1927_, 0);
v_v_2066_ = lean_ctor_get_uint16(v_x_1927_, sizeof(void*)*2);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2074_);
v___x_2068_ = v_x_1927_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_tgt_2065_);
lean_dec(v_x_1927_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v_x_1928_);
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(12, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_tgt_2065_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_x_1928_);
lean_ctor_set_uint16(v_reuseFailAlloc_2072_, sizeof(void*)*2, v_v_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
case 13:
{
lean_object* v_tgt_2075_; uint32_t v_v_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_tgt_2075_ = lean_ctor_get(v_x_1927_, 0);
v_v_2076_ = lean_ctor_get_uint32(v_x_1927_, sizeof(void*)*2);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2084_);
v___x_2078_ = v_x_1927_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_tgt_2075_);
lean_dec(v_x_1927_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v_x_1928_);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(13, 2, 4);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_tgt_2075_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_x_1928_);
lean_ctor_set_uint32(v_reuseFailAlloc_2082_, sizeof(void*)*2, v_v_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
case 14:
{
lean_object* v_tgt_2085_; uint64_t v_v_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_tgt_2085_ = lean_ctor_get(v_x_1927_, 0);
v_v_2086_ = lean_ctor_get_uint64(v_x_1927_, sizeof(void*)*2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2094_);
v___x_2088_ = v_x_1927_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_tgt_2085_);
lean_dec(v_x_1927_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v_x_1928_);
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(14, 2, 8);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_tgt_2085_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_x_1928_);
lean_ctor_set_uint64(v_reuseFailAlloc_2092_, sizeof(void*)*2, v_v_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
case 15:
{
lean_object* v_tgt_2095_; uint64_t v_v_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_tgt_2095_ = lean_ctor_get(v_x_1927_, 0);
v_v_2096_ = lean_ctor_get_uint64(v_x_1927_, sizeof(void*)*2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2104_);
v___x_2098_ = v_x_1927_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_tgt_2095_);
lean_dec(v_x_1927_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v_x_1928_);
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(15, 2, 8);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_tgt_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_x_1928_);
lean_ctor_set_uint64(v_reuseFailAlloc_2102_, sizeof(void*)*2, v_v_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
case 16:
{
lean_object* v_tgt_2105_; lean_object* v_v_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_tgt_2105_ = lean_ctor_get(v_x_1927_, 0);
v_v_2106_ = lean_ctor_get(v_x_1927_, 2);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2114_);
v___x_2108_ = v_x_1927_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_v_2106_);
lean_inc(v_tgt_2105_);
lean_dec(v_x_1927_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v_x_1928_);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_tgt_2105_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
case 17:
{
lean_object* v_tgt_2115_; lean_object* v_v_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_tgt_2115_ = lean_ctor_get(v_x_1927_, 0);
v_v_2116_ = lean_ctor_get(v_x_1927_, 2);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2124_);
v___x_2118_ = v_x_1927_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_v_2116_);
lean_inc(v_tgt_2115_);
lean_dec(v_x_1927_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v_x_1928_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_tgt_2115_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_v_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
case 18:
{
lean_object* v_tgt_2125_; lean_object* v_x_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_tgt_2125_ = lean_ctor_get(v_x_1927_, 0);
v_x_2126_ = lean_ctor_get(v_x_1927_, 2);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2134_);
v___x_2128_ = v_x_1927_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_x_2126_);
lean_inc(v_tgt_2125_);
lean_dec(v_x_1927_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_x_1928_);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(18, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_tgt_2125_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_x_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
case 19:
{
lean_object* v_j_2135_; lean_object* v_xs_2136_; lean_object* v_v_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_j_2135_ = lean_ctor_get(v_x_1927_, 0);
v_xs_2136_ = lean_ctor_get(v_x_1927_, 1);
v_v_2137_ = lean_ctor_get(v_x_1927_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v_x_1927_, 3);
lean_dec(v_unused_2145_);
v___x_2139_ = v_x_1927_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_v_2137_);
lean_inc(v_xs_2136_);
lean_inc(v_j_2135_);
lean_dec(v_x_1927_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 3, v_x_1928_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_j_2135_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_xs_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_v_2137_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_x_1928_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
case 20:
{
lean_object* v_x_2146_; lean_object* v_i_2147_; lean_object* v_y_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_x_2146_ = lean_ctor_get(v_x_1927_, 0);
v_i_2147_ = lean_ctor_get(v_x_1927_, 1);
v_y_2148_ = lean_ctor_get(v_x_1927_, 2);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v_x_1927_, 3);
lean_dec(v_unused_2156_);
v___x_2150_ = v_x_1927_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_y_2148_);
lean_inc(v_i_2147_);
lean_inc(v_x_2146_);
lean_dec(v_x_1927_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 3, v_x_1928_);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(20, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_x_2146_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_i_2147_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_y_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_x_1928_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
case 21:
{
lean_object* v_x_2157_; lean_object* v_cidx_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v_x_2157_ = lean_ctor_get(v_x_1927_, 0);
v_cidx_2158_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_x_1927_, 2);
lean_dec(v_unused_2166_);
v___x_2160_ = v_x_1927_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_cidx_2158_);
lean_inc(v_x_2157_);
lean_dec(v_x_1927_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 2, v_x_1928_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(21, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_x_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_cidx_2158_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_x_1928_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
case 22:
{
lean_object* v_x_2167_; lean_object* v_i_2168_; lean_object* v_y_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_x_2167_ = lean_ctor_get(v_x_1927_, 0);
v_i_2168_ = lean_ctor_get(v_x_1927_, 1);
v_y_2169_ = lean_ctor_get(v_x_1927_, 2);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v_x_1927_, 3);
lean_dec(v_unused_2177_);
v___x_2171_ = v_x_1927_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_y_2169_);
lean_inc(v_i_2168_);
lean_inc(v_x_2167_);
lean_dec(v_x_1927_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 3, v_x_1928_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(22, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_x_2167_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_i_2168_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_y_2169_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_x_1928_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
case 23:
{
lean_object* v_x_2178_; lean_object* v_i_2179_; lean_object* v_offset_2180_; lean_object* v_y_2181_; lean_object* v_ty_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_x_2178_ = lean_ctor_get(v_x_1927_, 0);
v_i_2179_ = lean_ctor_get(v_x_1927_, 1);
v_offset_2180_ = lean_ctor_get(v_x_1927_, 2);
v_y_2181_ = lean_ctor_get(v_x_1927_, 3);
v_ty_2182_ = lean_ctor_get(v_x_1927_, 4);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v_x_1927_, 5);
lean_dec(v_unused_2190_);
v___x_2184_ = v_x_1927_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_ty_2182_);
lean_inc(v_y_2181_);
lean_inc(v_offset_2180_);
lean_inc(v_i_2179_);
lean_inc(v_x_2178_);
lean_dec(v_x_1927_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 5, v_x_1928_);
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(23, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_x_2178_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_i_2179_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_offset_2180_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_y_2181_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_ty_2182_);
lean_ctor_set(v_reuseFailAlloc_2188_, 5, v_x_1928_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
case 24:
{
lean_object* v_x_2191_; lean_object* v_n_2192_; uint8_t v_c_2193_; uint8_t v_persistent_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_x_2191_ = lean_ctor_get(v_x_1927_, 0);
v_n_2192_ = lean_ctor_get(v_x_1927_, 1);
v_c_2193_ = lean_ctor_get_uint8(v_x_1927_, sizeof(void*)*3);
v_persistent_2194_ = lean_ctor_get_uint8(v_x_1927_, sizeof(void*)*3 + 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v_x_1927_, 2);
lean_dec(v_unused_2202_);
v___x_2196_ = v_x_1927_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_n_2192_);
lean_inc(v_x_2191_);
lean_dec(v_x_1927_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 2, v_x_1928_);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(24, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_x_2191_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_n_2192_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_x_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*3, v_c_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2200_, sizeof(void*)*3 + 1, v_persistent_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
case 25:
{
lean_object* v_x_2203_; lean_object* v_n_2204_; uint8_t v_c_2205_; uint8_t v_persistent_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
v_x_2203_ = lean_ctor_get(v_x_1927_, 0);
v_n_2204_ = lean_ctor_get(v_x_1927_, 1);
v_c_2205_ = lean_ctor_get_uint8(v_x_1927_, sizeof(void*)*3);
v_persistent_2206_ = lean_ctor_get_uint8(v_x_1927_, sizeof(void*)*3 + 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v_x_1927_, 2);
lean_dec(v_unused_2214_);
v___x_2208_ = v_x_1927_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_n_2204_);
lean_inc(v_x_2203_);
lean_dec(v_x_1927_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 2, v_x_1928_);
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(25, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_x_2203_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_n_2204_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_x_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2212_, sizeof(void*)*3, v_c_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2212_, sizeof(void*)*3 + 1, v_persistent_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
case 26:
{
lean_object* v_x_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_x_2215_ = lean_ctor_get(v_x_1927_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v_x_1927_, 1);
lean_dec(v_unused_2223_);
v___x_2217_ = v_x_1927_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_x_2215_);
lean_dec(v_x_1927_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_x_1928_);
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(26, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_x_2215_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_x_1928_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
default: 
{
lean_dec(v_x_1928_);
return v_x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object* v_b_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_box(30);
v___x_2226_ = l_Lean_IR_FnBody_setBody(v_b_2224_, v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object* v_b_2227_){
_start:
{
lean_object* v___y_2229_; 
switch(lean_obj_tag(v_b_2227_))
{
case 0:
{
lean_object* v_b_2233_; 
v_b_2233_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2233_);
v___y_2229_ = v_b_2233_;
goto v___jp_2228_;
}
case 1:
{
lean_object* v_b_2234_; 
v_b_2234_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2234_);
v___y_2229_ = v_b_2234_;
goto v___jp_2228_;
}
case 2:
{
lean_object* v_b_2235_; 
v_b_2235_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2235_);
v___y_2229_ = v_b_2235_;
goto v___jp_2228_;
}
case 3:
{
lean_object* v_b_2236_; 
v_b_2236_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2236_);
v___y_2229_ = v_b_2236_;
goto v___jp_2228_;
}
case 4:
{
lean_object* v_b_2237_; 
v_b_2237_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2237_);
v___y_2229_ = v_b_2237_;
goto v___jp_2228_;
}
case 5:
{
lean_object* v_b_2238_; 
v_b_2238_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2238_);
v___y_2229_ = v_b_2238_;
goto v___jp_2228_;
}
case 6:
{
lean_object* v_b_2239_; 
v_b_2239_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2239_);
v___y_2229_ = v_b_2239_;
goto v___jp_2228_;
}
case 7:
{
lean_object* v_b_2240_; 
v_b_2240_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2240_);
v___y_2229_ = v_b_2240_;
goto v___jp_2228_;
}
case 8:
{
lean_object* v_b_2241_; 
v_b_2241_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2241_);
v___y_2229_ = v_b_2241_;
goto v___jp_2228_;
}
case 9:
{
lean_object* v_b_2242_; 
v_b_2242_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2242_);
v___y_2229_ = v_b_2242_;
goto v___jp_2228_;
}
case 10:
{
lean_object* v_b_2243_; 
v_b_2243_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2243_);
v___y_2229_ = v_b_2243_;
goto v___jp_2228_;
}
case 11:
{
lean_object* v_b_2244_; 
v_b_2244_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2244_);
v___y_2229_ = v_b_2244_;
goto v___jp_2228_;
}
case 12:
{
lean_object* v_b_2245_; 
v_b_2245_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2245_);
v___y_2229_ = v_b_2245_;
goto v___jp_2228_;
}
case 13:
{
lean_object* v_b_2246_; 
v_b_2246_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2246_);
v___y_2229_ = v_b_2246_;
goto v___jp_2228_;
}
case 14:
{
lean_object* v_b_2247_; 
v_b_2247_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2247_);
v___y_2229_ = v_b_2247_;
goto v___jp_2228_;
}
case 15:
{
lean_object* v_b_2248_; 
v_b_2248_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2248_);
v___y_2229_ = v_b_2248_;
goto v___jp_2228_;
}
case 16:
{
lean_object* v_b_2249_; 
v_b_2249_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2249_);
v___y_2229_ = v_b_2249_;
goto v___jp_2228_;
}
case 17:
{
lean_object* v_b_2250_; 
v_b_2250_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2250_);
v___y_2229_ = v_b_2250_;
goto v___jp_2228_;
}
case 18:
{
lean_object* v_b_2251_; 
v_b_2251_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2251_);
v___y_2229_ = v_b_2251_;
goto v___jp_2228_;
}
case 19:
{
lean_object* v_b_2252_; 
v_b_2252_ = lean_ctor_get(v_b_2227_, 3);
lean_inc(v_b_2252_);
v___y_2229_ = v_b_2252_;
goto v___jp_2228_;
}
case 20:
{
lean_object* v_b_2253_; 
v_b_2253_ = lean_ctor_get(v_b_2227_, 3);
lean_inc(v_b_2253_);
v___y_2229_ = v_b_2253_;
goto v___jp_2228_;
}
case 22:
{
lean_object* v_b_2254_; 
v_b_2254_ = lean_ctor_get(v_b_2227_, 3);
lean_inc(v_b_2254_);
v___y_2229_ = v_b_2254_;
goto v___jp_2228_;
}
case 23:
{
lean_object* v_b_2255_; 
v_b_2255_ = lean_ctor_get(v_b_2227_, 5);
lean_inc(v_b_2255_);
v___y_2229_ = v_b_2255_;
goto v___jp_2228_;
}
case 21:
{
lean_object* v_b_2256_; 
v_b_2256_ = lean_ctor_get(v_b_2227_, 2);
lean_inc(v_b_2256_);
v___y_2229_ = v_b_2256_;
goto v___jp_2228_;
}
case 24:
{
lean_object* v_b_2257_; 
v_b_2257_ = lean_ctor_get(v_b_2227_, 2);
lean_inc(v_b_2257_);
v___y_2229_ = v_b_2257_;
goto v___jp_2228_;
}
case 25:
{
lean_object* v_b_2258_; 
v_b_2258_ = lean_ctor_get(v_b_2227_, 2);
lean_inc(v_b_2258_);
v___y_2229_ = v_b_2258_;
goto v___jp_2228_;
}
case 26:
{
lean_object* v_b_2259_; 
v_b_2259_ = lean_ctor_get(v_b_2227_, 1);
lean_inc(v_b_2259_);
v___y_2229_ = v_b_2259_;
goto v___jp_2228_;
}
default: 
{
lean_inc(v_b_2227_);
v___y_2229_ = v_b_2227_;
goto v___jp_2228_;
}
}
v___jp_2228_:
{
lean_object* v___x_2230_; lean_object* v_c_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_box(30);
v_c_2231_ = l_Lean_IR_FnBody_setBody(v_b_2227_, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v_c_2231_);
lean_ctor_set(v___x_2232_, 1, v___y_2229_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object* v_x_2260_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
lean_object* v_b_2261_; 
v_b_2261_ = lean_ctor_get(v_x_2260_, 1);
lean_inc(v_b_2261_);
return v_b_2261_;
}
else
{
lean_object* v_b_2262_; 
v_b_2262_ = lean_ctor_get(v_x_2260_, 0);
lean_inc(v_b_2262_);
return v_b_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object* v_x_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_IR_Alt_body(v_x_2263_);
lean_dec_ref(v_x_2263_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object* v_x_2265_, lean_object* v_x_2266_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 0)
{
lean_object* v_info_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_info_2267_ = lean_ctor_get(v_x_2265_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2274_ == 0)
{
lean_object* v_unused_2275_; 
v_unused_2275_ = lean_ctor_get(v_x_2265_, 1);
lean_dec(v_unused_2275_);
v___x_2269_ = v_x_2265_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_info_2267_);
lean_dec(v_x_2265_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v_x_2266_);
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_info_2267_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_x_2266_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_isSharedCheck_2282_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v_x_2265_, 0);
lean_dec(v_unused_2283_);
v___x_2277_ = v_x_2265_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_x_2265_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v_x_2266_);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_x_2266_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object* v_f_2284_, lean_object* v_x_2285_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 0)
{
lean_object* v_info_2286_; lean_object* v_b_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2295_; 
v_info_2286_ = lean_ctor_get(v_x_2285_, 0);
v_b_2287_ = lean_ctor_get(v_x_2285_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_x_2285_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2289_ = v_x_2285_;
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_b_2287_);
lean_inc(v_info_2286_);
lean_dec(v_x_2285_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_apply_1(v_f_2284_, v_b_2287_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_info_2286_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
else
{
lean_object* v_b_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_b_2296_ = lean_ctor_get(v_x_2285_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_x_2285_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2298_ = v_x_2285_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_b_2296_);
lean_dec(v_x_2285_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_apply_1(v_f_2284_, v_b_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(lean_object* v_info_2305_, lean_object* v_b_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_info_2305_);
lean_ctor_set(v___x_2307_, 1, v_b_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(lean_object* v_b_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_b_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg(lean_object* v_inst_2311_, lean_object* v_f_2312_, lean_object* v_x_2313_){
_start:
{
lean_object* v_toApplicative_2314_; 
v_toApplicative_2314_ = lean_ctor_get(v_inst_2311_, 0);
lean_inc_ref(v_toApplicative_2314_);
lean_dec_ref(v_inst_2311_);
if (lean_obj_tag(v_x_2313_) == 0)
{
lean_object* v_toFunctor_2315_; lean_object* v_info_2316_; lean_object* v_b_2317_; lean_object* v_map_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_toFunctor_2315_ = lean_ctor_get(v_toApplicative_2314_, 0);
lean_inc_ref(v_toFunctor_2315_);
lean_dec_ref(v_toApplicative_2314_);
v_info_2316_ = lean_ctor_get(v_x_2313_, 0);
lean_inc_ref(v_info_2316_);
v_b_2317_ = lean_ctor_get(v_x_2313_, 1);
lean_inc(v_b_2317_);
lean_dec_ref_known(v_x_2313_, 2);
v_map_2318_ = lean_ctor_get(v_toFunctor_2315_, 0);
lean_inc(v_map_2318_);
lean_dec_ref(v_toFunctor_2315_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2319_, 0, v_info_2316_);
v___x_2320_ = lean_apply_1(v_f_2312_, v_b_2317_);
v___x_2321_ = lean_apply_4(v_map_2318_, lean_box(0), lean_box(0), v___f_2319_, v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v_toFunctor_2322_; lean_object* v_b_2323_; lean_object* v_map_2324_; lean_object* v___f_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_toFunctor_2322_ = lean_ctor_get(v_toApplicative_2314_, 0);
lean_inc_ref(v_toFunctor_2322_);
lean_dec_ref(v_toApplicative_2314_);
v_b_2323_ = lean_ctor_get(v_x_2313_, 0);
lean_inc(v_b_2323_);
lean_dec_ref_known(v_x_2313_, 1);
v_map_2324_ = lean_ctor_get(v_toFunctor_2322_, 0);
lean_inc(v_map_2324_);
lean_dec_ref(v_toFunctor_2322_);
v___f_2325_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_2326_ = lean_apply_1(v_f_2312_, v_b_2323_);
v___x_2327_ = lean_apply_4(v_map_2324_, lean_box(0), lean_box(0), v___f_2325_, v___x_2326_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM(lean_object* v_m_2328_, lean_object* v_inst_2329_, lean_object* v_f_2330_, lean_object* v_x_2331_){
_start:
{
lean_object* v_toApplicative_2332_; 
v_toApplicative_2332_ = lean_ctor_get(v_inst_2329_, 0);
lean_inc_ref(v_toApplicative_2332_);
lean_dec_ref(v_inst_2329_);
if (lean_obj_tag(v_x_2331_) == 0)
{
lean_object* v_toFunctor_2333_; lean_object* v_info_2334_; lean_object* v_b_2335_; lean_object* v_map_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_toFunctor_2333_ = lean_ctor_get(v_toApplicative_2332_, 0);
lean_inc_ref(v_toFunctor_2333_);
lean_dec_ref(v_toApplicative_2332_);
v_info_2334_ = lean_ctor_get(v_x_2331_, 0);
lean_inc_ref(v_info_2334_);
v_b_2335_ = lean_ctor_get(v_x_2331_, 1);
lean_inc(v_b_2335_);
lean_dec_ref_known(v_x_2331_, 2);
v_map_2336_ = lean_ctor_get(v_toFunctor_2333_, 0);
lean_inc(v_map_2336_);
lean_dec_ref(v_toFunctor_2333_);
v___f_2337_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2337_, 0, v_info_2334_);
v___x_2338_ = lean_apply_1(v_f_2330_, v_b_2335_);
v___x_2339_ = lean_apply_4(v_map_2336_, lean_box(0), lean_box(0), v___f_2337_, v___x_2338_);
return v___x_2339_;
}
else
{
lean_object* v_toFunctor_2340_; lean_object* v_b_2341_; lean_object* v_map_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_toFunctor_2340_ = lean_ctor_get(v_toApplicative_2332_, 0);
lean_inc_ref(v_toFunctor_2340_);
lean_dec_ref(v_toApplicative_2332_);
v_b_2341_ = lean_ctor_get(v_x_2331_, 0);
lean_inc(v_b_2341_);
lean_dec_ref_known(v_x_2331_, 1);
v_map_2342_ = lean_ctor_get(v_toFunctor_2340_, 0);
lean_inc(v_map_2342_);
lean_dec_ref(v_toFunctor_2340_);
v___f_2343_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_2344_ = lean_apply_1(v_f_2330_, v_b_2341_);
v___x_2345_ = lean_apply_4(v_map_2342_, lean_box(0), lean_box(0), v___f_2343_, v___x_2344_);
return v___x_2345_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* v_x_2346_){
_start:
{
if (lean_obj_tag(v_x_2346_) == 0)
{
uint8_t v___x_2347_; 
v___x_2347_ = 0;
return v___x_2347_;
}
else
{
uint8_t v___x_2348_; 
v___x_2348_ = 1;
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* v_x_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = l_Lean_IR_Alt_isDefault(v_x_2349_);
lean_dec_ref(v_x_2349_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object* v_bs_2352_, lean_object* v_b_2353_){
_start:
{
lean_object* v___x_2354_; lean_object* v_b_2355_; lean_object* v___x_2356_; 
v___x_2354_ = lean_box(30);
v_b_2355_ = l_Lean_IR_FnBody_setBody(v_b_2353_, v___x_2354_);
v___x_2356_ = lean_array_push(v_bs_2352_, v_b_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object* v_b_2357_, lean_object* v_r_2358_){
_start:
{
lean_object* v___y_2360_; uint8_t v___x_2363_; 
v___x_2363_ = l_Lean_IR_FnBody_isTerminal(v_b_2357_);
if (v___x_2363_ == 0)
{
switch(lean_obj_tag(v_b_2357_))
{
case 0:
{
lean_object* v_b_2364_; 
v_b_2364_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2364_);
v___y_2360_ = v_b_2364_;
goto v___jp_2359_;
}
case 1:
{
lean_object* v_b_2365_; 
v_b_2365_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2365_);
v___y_2360_ = v_b_2365_;
goto v___jp_2359_;
}
case 2:
{
lean_object* v_b_2366_; 
v_b_2366_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2366_);
v___y_2360_ = v_b_2366_;
goto v___jp_2359_;
}
case 3:
{
lean_object* v_b_2367_; 
v_b_2367_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2367_);
v___y_2360_ = v_b_2367_;
goto v___jp_2359_;
}
case 4:
{
lean_object* v_b_2368_; 
v_b_2368_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2368_);
v___y_2360_ = v_b_2368_;
goto v___jp_2359_;
}
case 5:
{
lean_object* v_b_2369_; 
v_b_2369_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2369_);
v___y_2360_ = v_b_2369_;
goto v___jp_2359_;
}
case 6:
{
lean_object* v_b_2370_; 
v_b_2370_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2370_);
v___y_2360_ = v_b_2370_;
goto v___jp_2359_;
}
case 7:
{
lean_object* v_b_2371_; 
v_b_2371_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2371_);
v___y_2360_ = v_b_2371_;
goto v___jp_2359_;
}
case 8:
{
lean_object* v_b_2372_; 
v_b_2372_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2372_);
v___y_2360_ = v_b_2372_;
goto v___jp_2359_;
}
case 9:
{
lean_object* v_b_2373_; 
v_b_2373_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2373_);
v___y_2360_ = v_b_2373_;
goto v___jp_2359_;
}
case 10:
{
lean_object* v_b_2374_; 
v_b_2374_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2374_);
v___y_2360_ = v_b_2374_;
goto v___jp_2359_;
}
case 11:
{
lean_object* v_b_2375_; 
v_b_2375_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2375_);
v___y_2360_ = v_b_2375_;
goto v___jp_2359_;
}
case 12:
{
lean_object* v_b_2376_; 
v_b_2376_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2376_);
v___y_2360_ = v_b_2376_;
goto v___jp_2359_;
}
case 13:
{
lean_object* v_b_2377_; 
v_b_2377_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2377_);
v___y_2360_ = v_b_2377_;
goto v___jp_2359_;
}
case 14:
{
lean_object* v_b_2378_; 
v_b_2378_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2378_);
v___y_2360_ = v_b_2378_;
goto v___jp_2359_;
}
case 15:
{
lean_object* v_b_2379_; 
v_b_2379_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2379_);
v___y_2360_ = v_b_2379_;
goto v___jp_2359_;
}
case 16:
{
lean_object* v_b_2380_; 
v_b_2380_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2380_);
v___y_2360_ = v_b_2380_;
goto v___jp_2359_;
}
case 17:
{
lean_object* v_b_2381_; 
v_b_2381_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2381_);
v___y_2360_ = v_b_2381_;
goto v___jp_2359_;
}
case 18:
{
lean_object* v_b_2382_; 
v_b_2382_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2382_);
v___y_2360_ = v_b_2382_;
goto v___jp_2359_;
}
case 19:
{
lean_object* v_b_2383_; 
v_b_2383_ = lean_ctor_get(v_b_2357_, 3);
lean_inc(v_b_2383_);
v___y_2360_ = v_b_2383_;
goto v___jp_2359_;
}
case 20:
{
lean_object* v_b_2384_; 
v_b_2384_ = lean_ctor_get(v_b_2357_, 3);
lean_inc(v_b_2384_);
v___y_2360_ = v_b_2384_;
goto v___jp_2359_;
}
case 22:
{
lean_object* v_b_2385_; 
v_b_2385_ = lean_ctor_get(v_b_2357_, 3);
lean_inc(v_b_2385_);
v___y_2360_ = v_b_2385_;
goto v___jp_2359_;
}
case 23:
{
lean_object* v_b_2386_; 
v_b_2386_ = lean_ctor_get(v_b_2357_, 5);
lean_inc(v_b_2386_);
v___y_2360_ = v_b_2386_;
goto v___jp_2359_;
}
case 21:
{
lean_object* v_b_2387_; 
v_b_2387_ = lean_ctor_get(v_b_2357_, 2);
lean_inc(v_b_2387_);
v___y_2360_ = v_b_2387_;
goto v___jp_2359_;
}
case 24:
{
lean_object* v_b_2388_; 
v_b_2388_ = lean_ctor_get(v_b_2357_, 2);
lean_inc(v_b_2388_);
v___y_2360_ = v_b_2388_;
goto v___jp_2359_;
}
case 25:
{
lean_object* v_b_2389_; 
v_b_2389_ = lean_ctor_get(v_b_2357_, 2);
lean_inc(v_b_2389_);
v___y_2360_ = v_b_2389_;
goto v___jp_2359_;
}
case 26:
{
lean_object* v_b_2390_; 
v_b_2390_ = lean_ctor_get(v_b_2357_, 1);
lean_inc(v_b_2390_);
v___y_2360_ = v_b_2390_;
goto v___jp_2359_;
}
default: 
{
lean_inc(v_b_2357_);
v___y_2360_ = v_b_2357_;
goto v___jp_2359_;
}
}
}
else
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_r_2358_);
lean_ctor_set(v___x_2391_, 1, v_b_2357_);
return v___x_2391_;
}
v___jp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_IR_push(v_r_2358_, v_b_2357_);
v_b_2357_ = v___y_2360_;
v_r_2358_ = v___x_2361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object* v_b_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_IR_FnBody_flatten___closed__0));
v___x_2396_ = l_Lean_IR_flattenAux(v_b_2394_, v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0(lean_object* v___x_2397_, lean_object* v_msg_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_panic_fn_borrowed(v___x_2397_, v_msg_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(lean_object* v___x_2400_, lean_object* v_msg_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_2400_, v_msg_2401_);
lean_dec_ref(v___x_2400_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object* v_a_2407_, lean_object* v_i_2408_, lean_object* v_b_2409_){
_start:
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = lean_nat_dec_eq(v_i_2408_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v_i_2413_; lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2412_ = lean_unsigned_to_nat(1u);
v_i_2413_ = lean_nat_sub(v_i_2408_, v___x_2412_);
lean_dec(v_i_2408_);
v___x_2419_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_2420_ = lean_array_get_size(v_a_2407_);
v___x_2421_ = lean_nat_dec_lt(v_i_2413_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_fst_2434_; lean_object* v_snd_2435_; 
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2419_);
lean_ctor_set(v___x_2422_, 1, v_a_2407_);
v___x_2423_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__0));
v___x_2424_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__1));
v___x_2425_ = lean_unsigned_to_nat(463u);
v___x_2426_ = lean_unsigned_to_nat(4u);
v___x_2427_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__2));
lean_inc(v_i_2413_);
v___x_2428_ = l_Nat_reprFast(v_i_2413_);
v___x_2429_ = lean_string_append(v___x_2427_, v___x_2428_);
lean_dec_ref(v___x_2428_);
v___x_2430_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__3));
v___x_2431_ = lean_string_append(v___x_2429_, v___x_2430_);
v___x_2432_ = l_mkPanicMessageWithDecl(v___x_2423_, v___x_2424_, v___x_2425_, v___x_2426_, v___x_2431_);
lean_dec_ref(v___x_2431_);
v___x_2433_ = lean_panic_fn_borrowed(v___x_2422_, v___x_2432_);
lean_dec_ref_known(v___x_2422_, 2);
v_fst_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_fst_2434_);
v_snd_2435_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_snd_2435_);
lean_dec(v___x_2433_);
v_fst_2415_ = v_fst_2434_;
v_snd_2416_ = v_snd_2435_;
goto v___jp_2414_;
}
else
{
lean_object* v_e_2436_; lean_object* v_xs_x27_2437_; 
v_e_2436_ = lean_array_fget(v_a_2407_, v_i_2413_);
v_xs_x27_2437_ = lean_array_fset(v_a_2407_, v_i_2413_, v___x_2419_);
v_fst_2415_ = v_e_2436_;
v_snd_2416_ = v_xs_x27_2437_;
goto v___jp_2414_;
}
v___jp_2414_:
{
lean_object* v_b_2417_; 
v_b_2417_ = l_Lean_IR_FnBody_setBody(v_fst_2415_, v_b_2409_);
v_a_2407_ = v_snd_2416_;
v_i_2408_ = v_i_2413_;
v_b_2409_ = v_b_2417_;
goto _start;
}
}
else
{
lean_dec(v_i_2408_);
lean_dec_ref(v_a_2407_);
return v_b_2409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object* v_bs_2438_, lean_object* v_term_2439_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_array_get_size(v_bs_2438_);
v___x_2441_ = l_Lean_IR_reshapeAux(v_bs_2438_, v___x_2440_, v_term_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object* v_f_2442_, lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 19)
{
lean_object* v_j_2444_; lean_object* v_xs_2445_; lean_object* v_v_2446_; lean_object* v_b_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2455_; 
v_j_2444_ = lean_ctor_get(v_x_2443_, 0);
v_xs_2445_ = lean_ctor_get(v_x_2443_, 1);
v_v_2446_ = lean_ctor_get(v_x_2443_, 2);
v_b_2447_ = lean_ctor_get(v_x_2443_, 3);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2443_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2449_ = v_x_2443_;
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_b_2447_);
lean_inc(v_v_2446_);
lean_inc(v_xs_2445_);
lean_inc(v_j_2444_);
lean_dec(v_x_2443_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2455_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2451_ = lean_apply_1(v_f_2442_, v_v_2446_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 2, v___x_2451_);
v___x_2453_ = v___x_2449_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_j_2444_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_xs_2445_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_b_2447_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_dec_ref(v_f_2442_);
return v_x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* v_bs_2475_, lean_object* v_f_2476_){
_start:
{
lean_object* v___f_2477_; lean_object* v___x_2478_; size_t v_sz_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPs___lam__0), 2, 1);
lean_closure_set(v___f_2477_, 0, v_f_2476_);
v___x_2478_ = ((lean_object*)(l_Lean_IR_modifyJPs___closed__9));
v_sz_2479_ = lean_array_size(v_bs_2475_);
v___x_2480_ = ((size_t)0ULL);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2478_, v___f_2477_, v_sz_2479_, v___x_2480_, v_bs_2475_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__0(lean_object* v_j_2482_, lean_object* v_xs_2483_, lean_object* v_b_2484_, lean_object* v_toPure_2485_, lean_object* v_____do__lift_2486_){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_alloc_ctor(19, 4, 0);
lean_ctor_set(v___x_2487_, 0, v_j_2482_);
lean_ctor_set(v___x_2487_, 1, v_xs_2483_);
lean_ctor_set(v___x_2487_, 2, v_____do__lift_2486_);
lean_ctor_set(v___x_2487_, 3, v_b_2484_);
v___x_2488_ = lean_apply_2(v_toPure_2485_, lean_box(0), v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__1(lean_object* v_toPure_2489_, lean_object* v_f_2490_, lean_object* v_toBind_2491_, lean_object* v_b_2492_){
_start:
{
if (lean_obj_tag(v_b_2492_) == 19)
{
lean_object* v_j_2493_; lean_object* v_xs_2494_; lean_object* v_v_2495_; lean_object* v_b_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_j_2493_ = lean_ctor_get(v_b_2492_, 0);
lean_inc(v_j_2493_);
v_xs_2494_ = lean_ctor_get(v_b_2492_, 1);
lean_inc_ref(v_xs_2494_);
v_v_2495_ = lean_ctor_get(v_b_2492_, 2);
lean_inc(v_v_2495_);
v_b_2496_ = lean_ctor_get(v_b_2492_, 3);
lean_inc(v_b_2496_);
lean_dec_ref_known(v_b_2492_, 4);
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2497_, 0, v_j_2493_);
lean_closure_set(v___f_2497_, 1, v_xs_2494_);
lean_closure_set(v___f_2497_, 2, v_b_2496_);
lean_closure_set(v___f_2497_, 3, v_toPure_2489_);
v___x_2498_ = lean_apply_1(v_f_2490_, v_v_2495_);
v___x_2499_ = lean_apply_4(v_toBind_2491_, lean_box(0), lean_box(0), v___x_2498_, v___f_2497_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; 
lean_dec(v_toBind_2491_);
lean_dec(v_f_2490_);
v___x_2500_ = lean_apply_2(v_toPure_2489_, lean_box(0), v_b_2492_);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg(lean_object* v_inst_2501_, lean_object* v_bs_2502_, lean_object* v_f_2503_){
_start:
{
lean_object* v_toApplicative_2504_; lean_object* v_toBind_2505_; lean_object* v_toPure_2506_; lean_object* v___f_2507_; size_t v_sz_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v_toApplicative_2504_ = lean_ctor_get(v_inst_2501_, 0);
v_toBind_2505_ = lean_ctor_get(v_inst_2501_, 1);
v_toPure_2506_ = lean_ctor_get(v_toApplicative_2504_, 1);
lean_inc(v_toBind_2505_);
lean_inc(v_toPure_2506_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2507_, 0, v_toPure_2506_);
lean_closure_set(v___f_2507_, 1, v_f_2503_);
lean_closure_set(v___f_2507_, 2, v_toBind_2505_);
v_sz_2508_ = lean_array_size(v_bs_2502_);
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2501_, v___f_2507_, v_sz_2508_, v___x_2509_, v_bs_2502_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM(lean_object* v_m_2511_, lean_object* v_inst_2512_, lean_object* v_bs_2513_, lean_object* v_f_2514_){
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
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl(lean_object* v_x_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_obj_tag_nat(v_x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl___boxed(lean_object* v_x_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_IR_Decl_ctorIdx___impl(v_x_2524_);
lean_dec_ref(v_x_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___redArg(lean_object* v_t_2526_, lean_object* v_k_2527_){
_start:
{
if (lean_obj_tag(v_t_2526_) == 0)
{
lean_object* v_f_2528_; lean_object* v_xs_2529_; lean_object* v_type_2530_; lean_object* v_body_2531_; lean_object* v_info_2532_; lean_object* v___x_2533_; 
v_f_2528_ = lean_ctor_get(v_t_2526_, 0);
lean_inc(v_f_2528_);
v_xs_2529_ = lean_ctor_get(v_t_2526_, 1);
lean_inc_ref(v_xs_2529_);
v_type_2530_ = lean_ctor_get(v_t_2526_, 2);
lean_inc(v_type_2530_);
v_body_2531_ = lean_ctor_get(v_t_2526_, 3);
lean_inc(v_body_2531_);
v_info_2532_ = lean_ctor_get(v_t_2526_, 4);
lean_inc_ref(v_info_2532_);
lean_dec_ref_known(v_t_2526_, 5);
v___x_2533_ = lean_apply_5(v_k_2527_, v_f_2528_, v_xs_2529_, v_type_2530_, v_body_2531_, v_info_2532_);
return v___x_2533_;
}
else
{
lean_object* v_f_2534_; lean_object* v_xs_2535_; lean_object* v_type_2536_; lean_object* v_ext_2537_; lean_object* v___x_2538_; 
v_f_2534_ = lean_ctor_get(v_t_2526_, 0);
lean_inc(v_f_2534_);
v_xs_2535_ = lean_ctor_get(v_t_2526_, 1);
lean_inc_ref(v_xs_2535_);
v_type_2536_ = lean_ctor_get(v_t_2526_, 2);
lean_inc(v_type_2536_);
v_ext_2537_ = lean_ctor_get(v_t_2526_, 3);
lean_inc(v_ext_2537_);
lean_dec_ref_known(v_t_2526_, 4);
v___x_2538_ = lean_apply_4(v_k_2527_, v_f_2534_, v_xs_2535_, v_type_2536_, v_ext_2537_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim(lean_object* v_motive_2539_, lean_object* v_ctorIdx_2540_, lean_object* v_t_2541_, lean_object* v_h_2542_, lean_object* v_k_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2541_, v_k_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___boxed(lean_object* v_motive_2545_, lean_object* v_ctorIdx_2546_, lean_object* v_t_2547_, lean_object* v_h_2548_, lean_object* v_k_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_IR_Decl_ctorElim(v_motive_2545_, v_ctorIdx_2546_, v_t_2547_, v_h_2548_, v_k_2549_);
lean_dec(v_ctorIdx_2546_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim___redArg(lean_object* v_t_2551_, lean_object* v_fdecl_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2551_, v_fdecl_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim(lean_object* v_motive_2554_, lean_object* v_t_2555_, lean_object* v_h_2556_, lean_object* v_fdecl_2557_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2555_, v_fdecl_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim___redArg(lean_object* v_t_2559_, lean_object* v_extern_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2559_, v_extern_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim(lean_object* v_motive_2562_, lean_object* v_t_2563_, lean_object* v_h_2564_, lean_object* v_extern_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_2563_, v_extern_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object* v_x_2576_){
_start:
{
lean_object* v_f_2577_; 
v_f_2577_ = lean_ctor_get(v_x_2576_, 0);
lean_inc(v_f_2577_);
return v_f_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object* v_x_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_IR_Decl_name(v_x_2578_);
lean_dec_ref(v_x_2578_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object* v_x_2580_){
_start:
{
lean_object* v_xs_2581_; 
v_xs_2581_ = lean_ctor_get(v_x_2580_, 1);
lean_inc_ref(v_xs_2581_);
return v_xs_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object* v_x_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_IR_Decl_params(v_x_2582_);
lean_dec_ref(v_x_2582_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object* v_x_2584_){
_start:
{
lean_object* v_type_2585_; 
v_type_2585_ = lean_ctor_get(v_x_2584_, 2);
lean_inc(v_type_2585_);
return v_type_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* v_x_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_IR_Decl_resultType(v_x_2586_);
lean_dec_ref(v_x_2586_);
return v_res_2587_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object* v_x_2588_){
_start:
{
if (lean_obj_tag(v_x_2588_) == 1)
{
uint8_t v___x_2589_; 
v___x_2589_ = 1;
return v___x_2589_;
}
else
{
uint8_t v___x_2590_; 
v___x_2590_ = 0;
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* v_x_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = l_Lean_IR_Decl_isExtern(v_x_2591_);
lean_dec_ref(v_x_2591_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* v_x_2597_){
_start:
{
if (lean_obj_tag(v_x_2597_) == 0)
{
lean_object* v_info_2598_; 
v_info_2598_ = lean_ctor_get(v_x_2597_, 4);
lean_inc_ref(v_info_2598_);
return v_info_2598_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = ((lean_object*)(l_Lean_IR_Decl_getInfo___closed__0));
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* v_x_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_IR_Decl_getInfo(v_x_2600_);
lean_dec_ref(v_x_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object* v_msg_2602_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l_Lean_IR_instInhabitedDecl_default));
v___x_2604_ = lean_panic_fn_borrowed(v___x_2603_, v_msg_2602_);
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__2(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2607_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__1));
v___x_2608_ = lean_unsigned_to_nat(9u);
v___x_2609_ = lean_unsigned_to_nat(510u);
v___x_2610_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__0));
v___x_2611_ = ((lean_object*)(l_Lean_IR_FnBody_targetVar___closed__0));
v___x_2612_ = l_mkPanicMessageWithDecl(v___x_2611_, v___x_2610_, v___x_2609_, v___x_2608_, v___x_2607_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* v_d_2613_, lean_object* v_bNew_2614_){
_start:
{
if (lean_obj_tag(v_d_2613_) == 0)
{
lean_object* v_f_2615_; lean_object* v_xs_2616_; lean_object* v_type_2617_; lean_object* v_info_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
v_f_2615_ = lean_ctor_get(v_d_2613_, 0);
v_xs_2616_ = lean_ctor_get(v_d_2613_, 1);
v_type_2617_ = lean_ctor_get(v_d_2613_, 2);
v_info_2618_ = lean_ctor_get(v_d_2613_, 4);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_d_2613_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_d_2613_, 3);
lean_dec(v_unused_2626_);
v___x_2620_ = v_d_2613_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_info_2618_);
lean_inc(v_type_2617_);
lean_inc(v_xs_2616_);
lean_inc(v_f_2615_);
lean_dec(v_d_2613_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 3, v_bNew_2614_);
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_f_2615_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_xs_2616_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_type_2617_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_bNew_2614_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_info_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec(v_bNew_2614_);
lean_dec_ref(v_d_2613_);
v___x_2627_ = lean_obj_once(&l_Lean_IR_Decl_updateBody_x21___closed__2, &l_Lean_IR_Decl_updateBody_x21___closed__2_once, _init_l_Lean_IR_Decl_updateBody_x21___closed__2);
v___x_2628_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_2627_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object* v_f_2629_, lean_object* v_xs_2630_, lean_object* v_ty_2631_){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_box(30);
v___x_2633_ = ((lean_object*)(l_Lean_IR_Decl_getInfo___closed__0));
v___x_2634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2634_, 0, v_f_2629_);
lean_ctor_set(v___x_2634_, 1, v_xs_2630_);
lean_ctor_set(v___x_2634_, 2, v_ty_2631_);
lean_ctor_set(v___x_2634_, 3, v___x_2632_);
lean_ctor_set(v___x_2634_, 4, v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object* v_k_2635_, lean_object* v_v_2636_, lean_object* v_t_2637_){
_start:
{
if (lean_obj_tag(v_t_2637_) == 0)
{
lean_object* v_size_2638_; lean_object* v_k_2639_; lean_object* v_v_2640_; lean_object* v_l_2641_; lean_object* v_r_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2923_; 
v_size_2638_ = lean_ctor_get(v_t_2637_, 0);
v_k_2639_ = lean_ctor_get(v_t_2637_, 1);
v_v_2640_ = lean_ctor_get(v_t_2637_, 2);
v_l_2641_ = lean_ctor_get(v_t_2637_, 3);
v_r_2642_ = lean_ctor_get(v_t_2637_, 4);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_t_2637_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2644_ = v_t_2637_;
v_isShared_2645_ = v_isSharedCheck_2923_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_r_2642_);
lean_inc(v_l_2641_);
lean_inc(v_v_2640_);
lean_inc(v_k_2639_);
lean_inc(v_size_2638_);
lean_dec(v_t_2637_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2923_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_lt(v_k_2635_, v_k_2639_);
if (v___x_2646_ == 0)
{
uint8_t v___x_2647_; 
v___x_2647_ = lean_nat_dec_eq(v_k_2635_, v_k_2639_);
if (v___x_2647_ == 0)
{
lean_object* v_impl_2648_; lean_object* v___x_2649_; 
lean_dec(v_size_2638_);
v_impl_2648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2635_, v_v_2636_, v_r_2642_);
v___x_2649_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2641_) == 0)
{
lean_object* v_size_2650_; lean_object* v_size_2651_; lean_object* v_k_2652_; lean_object* v_v_2653_; lean_object* v_l_2654_; lean_object* v_r_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_size_2650_ = lean_ctor_get(v_l_2641_, 0);
v_size_2651_ = lean_ctor_get(v_impl_2648_, 0);
v_k_2652_ = lean_ctor_get(v_impl_2648_, 1);
v_v_2653_ = lean_ctor_get(v_impl_2648_, 2);
v_l_2654_ = lean_ctor_get(v_impl_2648_, 3);
lean_inc(v_l_2654_);
v_r_2655_ = lean_ctor_get(v_impl_2648_, 4);
v___x_2656_ = lean_unsigned_to_nat(3u);
v___x_2657_ = lean_nat_mul(v___x_2656_, v_size_2650_);
v___x_2658_ = lean_nat_dec_lt(v___x_2657_, v_size_2651_);
lean_dec(v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_dec(v_l_2654_);
v___x_2659_ = lean_nat_add(v___x_2649_, v_size_2650_);
v___x_2660_ = lean_nat_add(v___x_2659_, v_size_2651_);
lean_dec(v___x_2659_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v_impl_2648_);
lean_ctor_set(v___x_2644_, 0, v___x_2660_);
v___x_2662_ = v___x_2644_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_l_2641_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_impl_2648_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2727_; 
lean_inc(v_r_2655_);
lean_inc(v_v_2653_);
lean_inc(v_k_2652_);
lean_inc(v_size_2651_);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_impl_2648_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2728_ = lean_ctor_get(v_impl_2648_, 4);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_impl_2648_, 3);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_impl_2648_, 2);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_impl_2648_, 1);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_impl_2648_, 0);
lean_dec(v_unused_2732_);
v___x_2665_ = v_impl_2648_;
v_isShared_2666_ = v_isSharedCheck_2727_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v_impl_2648_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2727_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_size_2667_; lean_object* v_k_2668_; lean_object* v_v_2669_; lean_object* v_l_2670_; lean_object* v_r_2671_; lean_object* v_size_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_size_2667_ = lean_ctor_get(v_l_2654_, 0);
v_k_2668_ = lean_ctor_get(v_l_2654_, 1);
v_v_2669_ = lean_ctor_get(v_l_2654_, 2);
v_l_2670_ = lean_ctor_get(v_l_2654_, 3);
v_r_2671_ = lean_ctor_get(v_l_2654_, 4);
v_size_2672_ = lean_ctor_get(v_r_2655_, 0);
v___x_2673_ = lean_unsigned_to_nat(2u);
v___x_2674_ = lean_nat_mul(v___x_2673_, v_size_2672_);
v___x_2675_ = lean_nat_dec_lt(v_size_2667_, v___x_2674_);
lean_dec(v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2703_; 
lean_inc(v_r_2671_);
lean_inc(v_l_2670_);
lean_inc(v_v_2669_);
lean_inc(v_k_2668_);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_l_2654_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; lean_object* v_unused_2708_; 
v_unused_2704_ = lean_ctor_get(v_l_2654_, 4);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_l_2654_, 3);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_l_2654_, 2);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_l_2654_, 1);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_l_2654_, 0);
lean_dec(v_unused_2708_);
v___x_2677_ = v_l_2654_;
v_isShared_2678_ = v_isSharedCheck_2703_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v_l_2654_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2703_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2693_; 
v___x_2679_ = lean_nat_add(v___x_2649_, v_size_2650_);
v___x_2680_ = lean_nat_add(v___x_2679_, v_size_2651_);
lean_dec(v_size_2651_);
if (lean_obj_tag(v_l_2670_) == 0)
{
lean_object* v_size_2701_; 
v_size_2701_ = lean_ctor_get(v_l_2670_, 0);
lean_inc(v_size_2701_);
v___y_2693_ = v_size_2701_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_unsigned_to_nat(0u);
v___y_2693_ = v___x_2702_;
goto v___jp_2692_;
}
v___jp_2681_:
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2685_ = lean_nat_add(v___y_2682_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec(v___y_2682_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 4, v_r_2655_);
lean_ctor_set(v___x_2677_, 3, v_r_2671_);
lean_ctor_set(v___x_2677_, 2, v_v_2653_);
lean_ctor_set(v___x_2677_, 1, v_k_2652_);
lean_ctor_set(v___x_2677_, 0, v___x_2685_);
v___x_2687_ = v___x_2677_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_k_2652_);
lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_v_2653_);
lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_r_2671_);
lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_r_2655_);
v___x_2687_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 4, v___x_2687_);
lean_ctor_set(v___x_2665_, 3, v___y_2683_);
lean_ctor_set(v___x_2665_, 2, v_v_2669_);
lean_ctor_set(v___x_2665_, 1, v_k_2668_);
lean_ctor_set(v___x_2665_, 0, v___x_2680_);
v___x_2689_ = v___x_2665_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_k_2668_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_v_2669_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v___y_2683_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
v___jp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = lean_nat_add(v___x_2679_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec(v___x_2679_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v_l_2670_);
lean_ctor_set(v___x_2644_, 0, v___x_2694_);
v___x_2696_ = v___x_2644_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_l_2641_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_l_2670_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_nat_add(v___x_2649_, v_size_2672_);
if (lean_obj_tag(v_r_2671_) == 0)
{
lean_object* v_size_2698_; 
v_size_2698_ = lean_ctor_get(v_r_2671_, 0);
lean_inc(v_size_2698_);
v___y_2682_ = v___x_2697_;
v___y_2683_ = v___x_2696_;
v___y_2684_ = v_size_2698_;
goto v___jp_2681_;
}
else
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
v___y_2682_ = v___x_2697_;
v___y_2683_ = v___x_2696_;
v___y_2684_ = v___x_2699_;
goto v___jp_2681_;
}
}
}
}
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_del_object(v___x_2644_);
v___x_2709_ = lean_nat_add(v___x_2649_, v_size_2650_);
v___x_2710_ = lean_nat_add(v___x_2709_, v_size_2651_);
lean_dec(v_size_2651_);
v___x_2711_ = lean_nat_add(v___x_2709_, v_size_2667_);
lean_dec(v___x_2709_);
lean_inc_ref(v_l_2641_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 4, v_l_2654_);
lean_ctor_set(v___x_2665_, 3, v_l_2641_);
lean_ctor_set(v___x_2665_, 2, v_v_2640_);
lean_ctor_set(v___x_2665_, 1, v_k_2639_);
lean_ctor_set(v___x_2665_, 0, v___x_2711_);
v___x_2713_ = v___x_2665_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_l_2641_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_l_2654_);
v___x_2713_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_isSharedCheck_2720_ = !lean_is_exclusive(v_l_2641_);
if (v_isSharedCheck_2720_ == 0)
{
lean_object* v_unused_2721_; lean_object* v_unused_2722_; lean_object* v_unused_2723_; lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2721_ = lean_ctor_get(v_l_2641_, 4);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_l_2641_, 3);
lean_dec(v_unused_2722_);
v_unused_2723_ = lean_ctor_get(v_l_2641_, 2);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_l_2641_, 1);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_l_2641_, 0);
lean_dec(v_unused_2725_);
v___x_2715_ = v_l_2641_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_dec(v_l_2641_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 4, v_r_2655_);
lean_ctor_set(v___x_2715_, 3, v___x_2713_);
lean_ctor_set(v___x_2715_, 2, v_v_2653_);
lean_ctor_set(v___x_2715_, 1, v_k_2652_);
lean_ctor_set(v___x_2715_, 0, v___x_2710_);
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_k_2652_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_v_2653_);
lean_ctor_set(v_reuseFailAlloc_2719_, 3, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2719_, 4, v_r_2655_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2733_; 
v_l_2733_ = lean_ctor_get(v_impl_2648_, 3);
lean_inc(v_l_2733_);
if (lean_obj_tag(v_l_2733_) == 0)
{
lean_object* v_r_2734_; lean_object* v_k_2735_; lean_object* v_v_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2759_; 
v_r_2734_ = lean_ctor_get(v_impl_2648_, 4);
v_k_2735_ = lean_ctor_get(v_impl_2648_, 1);
v_v_2736_ = lean_ctor_get(v_impl_2648_, 2);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_impl_2648_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; lean_object* v_unused_2761_; 
v_unused_2760_ = lean_ctor_get(v_impl_2648_, 3);
lean_dec(v_unused_2760_);
v_unused_2761_ = lean_ctor_get(v_impl_2648_, 0);
lean_dec(v_unused_2761_);
v___x_2738_ = v_impl_2648_;
v_isShared_2739_ = v_isSharedCheck_2759_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_r_2734_);
lean_inc(v_v_2736_);
lean_inc(v_k_2735_);
lean_dec(v_impl_2648_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2759_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_k_2740_; lean_object* v_v_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2755_; 
v_k_2740_ = lean_ctor_get(v_l_2733_, 1);
v_v_2741_ = lean_ctor_get(v_l_2733_, 2);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_l_2733_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; lean_object* v_unused_2757_; lean_object* v_unused_2758_; 
v_unused_2756_ = lean_ctor_get(v_l_2733_, 4);
lean_dec(v_unused_2756_);
v_unused_2757_ = lean_ctor_get(v_l_2733_, 3);
lean_dec(v_unused_2757_);
v_unused_2758_ = lean_ctor_get(v_l_2733_, 0);
lean_dec(v_unused_2758_);
v___x_2743_ = v_l_2733_;
v_isShared_2744_ = v_isSharedCheck_2755_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_v_2741_);
lean_inc(v_k_2740_);
lean_dec(v_l_2733_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2755_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2734_, 2);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_r_2734_);
lean_ctor_set(v___x_2743_, 3, v_r_2734_);
lean_ctor_set(v___x_2743_, 2, v_v_2640_);
lean_ctor_set(v___x_2743_, 1, v_k_2639_);
lean_ctor_set(v___x_2743_, 0, v___x_2649_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_r_2734_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v_r_2734_);
v___x_2747_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
lean_inc(v_r_2734_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 3, v_r_2734_);
lean_ctor_set(v___x_2738_, 0, v___x_2649_);
v___x_2749_ = v___x_2738_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_k_2735_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_v_2736_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v_r_2734_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v_r_2734_);
v___x_2749_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2751_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v___x_2749_);
lean_ctor_set(v___x_2644_, 3, v___x_2747_);
lean_ctor_set(v___x_2644_, 2, v_v_2741_);
lean_ctor_set(v___x_2644_, 1, v_k_2740_);
lean_ctor_set(v___x_2644_, 0, v___x_2745_);
v___x_2751_ = v___x_2644_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2752_, 3, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2752_, 4, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
else
{
lean_object* v_r_2762_; 
v_r_2762_ = lean_ctor_get(v_impl_2648_, 4);
lean_inc(v_r_2762_);
if (lean_obj_tag(v_r_2762_) == 0)
{
lean_object* v_k_2763_; lean_object* v_v_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2775_; 
v_k_2763_ = lean_ctor_get(v_impl_2648_, 1);
v_v_2764_ = lean_ctor_get(v_impl_2648_, 2);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_impl_2648_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; lean_object* v_unused_2777_; lean_object* v_unused_2778_; 
v_unused_2776_ = lean_ctor_get(v_impl_2648_, 4);
lean_dec(v_unused_2776_);
v_unused_2777_ = lean_ctor_get(v_impl_2648_, 3);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_impl_2648_, 0);
lean_dec(v_unused_2778_);
v___x_2766_ = v_impl_2648_;
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_v_2764_);
lean_inc(v_k_2763_);
lean_dec(v_impl_2648_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2768_ = lean_unsigned_to_nat(3u);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_l_2733_);
lean_ctor_set(v___x_2766_, 2, v_v_2640_);
lean_ctor_set(v___x_2766_, 1, v_k_2639_);
lean_ctor_set(v___x_2766_, 0, v___x_2649_);
v___x_2770_ = v___x_2766_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2774_, 3, v_l_2733_);
lean_ctor_set(v_reuseFailAlloc_2774_, 4, v_l_2733_);
v___x_2770_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2772_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v_r_2762_);
lean_ctor_set(v___x_2644_, 3, v___x_2770_);
lean_ctor_set(v___x_2644_, 2, v_v_2764_);
lean_ctor_set(v___x_2644_, 1, v_k_2763_);
lean_ctor_set(v___x_2644_, 0, v___x_2768_);
v___x_2772_ = v___x_2644_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_k_2763_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_v_2764_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2773_, 4, v_r_2762_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_unsigned_to_nat(2u);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v_impl_2648_);
lean_ctor_set(v___x_2644_, 3, v_r_2762_);
lean_ctor_set(v___x_2644_, 0, v___x_2779_);
v___x_2781_ = v___x_2644_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2782_, 3, v_r_2762_);
lean_ctor_set(v_reuseFailAlloc_2782_, 4, v_impl_2648_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
else
{
lean_object* v___x_2784_; 
lean_dec(v_v_2640_);
lean_dec(v_k_2639_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 2, v_v_2636_);
lean_ctor_set(v___x_2644_, 1, v_k_2635_);
v___x_2784_ = v___x_2644_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_size_2638_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_k_2635_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_v_2636_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_l_2641_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_r_2642_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_impl_2786_; lean_object* v___x_2787_; 
lean_dec(v_size_2638_);
v_impl_2786_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2635_, v_v_2636_, v_l_2641_);
v___x_2787_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2642_) == 0)
{
lean_object* v_size_2788_; lean_object* v_size_2789_; lean_object* v_k_2790_; lean_object* v_v_2791_; lean_object* v_l_2792_; lean_object* v_r_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_size_2788_ = lean_ctor_get(v_r_2642_, 0);
v_size_2789_ = lean_ctor_get(v_impl_2786_, 0);
v_k_2790_ = lean_ctor_get(v_impl_2786_, 1);
v_v_2791_ = lean_ctor_get(v_impl_2786_, 2);
v_l_2792_ = lean_ctor_get(v_impl_2786_, 3);
v_r_2793_ = lean_ctor_get(v_impl_2786_, 4);
lean_inc(v_r_2793_);
v___x_2794_ = lean_unsigned_to_nat(3u);
v___x_2795_ = lean_nat_mul(v___x_2794_, v_size_2788_);
v___x_2796_ = lean_nat_dec_lt(v___x_2795_, v_size_2789_);
lean_dec(v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_dec(v_r_2793_);
v___x_2797_ = lean_nat_add(v___x_2787_, v_size_2789_);
v___x_2798_ = lean_nat_add(v___x_2797_, v_size_2788_);
lean_dec(v___x_2797_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 3, v_impl_2786_);
lean_ctor_set(v___x_2644_, 0, v___x_2798_);
v___x_2800_ = v___x_2644_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_impl_2786_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_r_2642_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
else
{
lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2867_; 
lean_inc(v_l_2792_);
lean_inc(v_v_2791_);
lean_inc(v_k_2790_);
lean_inc(v_size_2789_);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_impl_2786_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; lean_object* v_unused_2869_; lean_object* v_unused_2870_; lean_object* v_unused_2871_; lean_object* v_unused_2872_; 
v_unused_2868_ = lean_ctor_get(v_impl_2786_, 4);
lean_dec(v_unused_2868_);
v_unused_2869_ = lean_ctor_get(v_impl_2786_, 3);
lean_dec(v_unused_2869_);
v_unused_2870_ = lean_ctor_get(v_impl_2786_, 2);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_impl_2786_, 1);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_impl_2786_, 0);
lean_dec(v_unused_2872_);
v___x_2803_ = v_impl_2786_;
v_isShared_2804_ = v_isSharedCheck_2867_;
goto v_resetjp_2802_;
}
else
{
lean_dec(v_impl_2786_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2867_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v_size_2805_; lean_object* v_size_2806_; lean_object* v_k_2807_; lean_object* v_v_2808_; lean_object* v_l_2809_; lean_object* v_r_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_size_2805_ = lean_ctor_get(v_l_2792_, 0);
v_size_2806_ = lean_ctor_get(v_r_2793_, 0);
v_k_2807_ = lean_ctor_get(v_r_2793_, 1);
v_v_2808_ = lean_ctor_get(v_r_2793_, 2);
v_l_2809_ = lean_ctor_get(v_r_2793_, 3);
v_r_2810_ = lean_ctor_get(v_r_2793_, 4);
v___x_2811_ = lean_unsigned_to_nat(2u);
v___x_2812_ = lean_nat_mul(v___x_2811_, v_size_2805_);
v___x_2813_ = lean_nat_dec_lt(v_size_2806_, v___x_2812_);
lean_dec(v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2842_; 
lean_inc(v_r_2810_);
lean_inc(v_l_2809_);
lean_inc(v_v_2808_);
lean_inc(v_k_2807_);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_r_2793_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; lean_object* v_unused_2844_; lean_object* v_unused_2845_; lean_object* v_unused_2846_; lean_object* v_unused_2847_; 
v_unused_2843_ = lean_ctor_get(v_r_2793_, 4);
lean_dec(v_unused_2843_);
v_unused_2844_ = lean_ctor_get(v_r_2793_, 3);
lean_dec(v_unused_2844_);
v_unused_2845_ = lean_ctor_get(v_r_2793_, 2);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_r_2793_, 1);
lean_dec(v_unused_2846_);
v_unused_2847_ = lean_ctor_get(v_r_2793_, 0);
lean_dec(v_unused_2847_);
v___x_2815_ = v_r_2793_;
v_isShared_2816_ = v_isSharedCheck_2842_;
goto v_resetjp_2814_;
}
else
{
lean_dec(v_r_2793_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2842_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___x_2830_; lean_object* v___y_2832_; 
v___x_2817_ = lean_nat_add(v___x_2787_, v_size_2789_);
lean_dec(v_size_2789_);
v___x_2818_ = lean_nat_add(v___x_2817_, v_size_2788_);
lean_dec(v___x_2817_);
v___x_2830_ = lean_nat_add(v___x_2787_, v_size_2805_);
if (lean_obj_tag(v_l_2809_) == 0)
{
lean_object* v_size_2840_; 
v_size_2840_ = lean_ctor_get(v_l_2809_, 0);
lean_inc(v_size_2840_);
v___y_2832_ = v_size_2840_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_unsigned_to_nat(0u);
v___y_2832_ = v___x_2841_;
goto v___jp_2831_;
}
v___jp_2819_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_nat_add(v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec(v___y_2821_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 4, v_r_2642_);
lean_ctor_set(v___x_2815_, 3, v_r_2810_);
lean_ctor_set(v___x_2815_, 2, v_v_2640_);
lean_ctor_set(v___x_2815_, 1, v_k_2639_);
lean_ctor_set(v___x_2815_, 0, v___x_2823_);
v___x_2825_ = v___x_2815_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_r_2810_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_r_2642_);
v___x_2825_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 4, v___x_2825_);
lean_ctor_set(v___x_2803_, 3, v___y_2820_);
lean_ctor_set(v___x_2803_, 2, v_v_2808_);
lean_ctor_set(v___x_2803_, 1, v_k_2807_);
lean_ctor_set(v___x_2803_, 0, v___x_2818_);
v___x_2827_ = v___x_2803_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_k_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_v_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v___y_2820_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_nat_add(v___x_2830_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec(v___x_2830_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v_l_2809_);
lean_ctor_set(v___x_2644_, 3, v_l_2792_);
lean_ctor_set(v___x_2644_, 2, v_v_2791_);
lean_ctor_set(v___x_2644_, 1, v_k_2790_);
lean_ctor_set(v___x_2644_, 0, v___x_2833_);
v___x_2835_ = v___x_2644_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_k_2790_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_v_2791_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_l_2792_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_l_2809_);
v___x_2835_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_nat_add(v___x_2787_, v_size_2788_);
if (lean_obj_tag(v_r_2810_) == 0)
{
lean_object* v_size_2837_; 
v_size_2837_ = lean_ctor_get(v_r_2810_, 0);
lean_inc(v_size_2837_);
v___y_2820_ = v___x_2835_;
v___y_2821_ = v___x_2836_;
v___y_2822_ = v_size_2837_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_unsigned_to_nat(0u);
v___y_2820_ = v___x_2835_;
v___y_2821_ = v___x_2836_;
v___y_2822_ = v___x_2838_;
goto v___jp_2819_;
}
}
}
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_del_object(v___x_2644_);
v___x_2848_ = lean_nat_add(v___x_2787_, v_size_2789_);
lean_dec(v_size_2789_);
v___x_2849_ = lean_nat_add(v___x_2848_, v_size_2788_);
lean_dec(v___x_2848_);
v___x_2850_ = lean_nat_add(v___x_2787_, v_size_2788_);
v___x_2851_ = lean_nat_add(v___x_2850_, v_size_2806_);
lean_dec(v___x_2850_);
lean_inc_ref(v_r_2642_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 4, v_r_2642_);
lean_ctor_set(v___x_2803_, 3, v_r_2793_);
lean_ctor_set(v___x_2803_, 2, v_v_2640_);
lean_ctor_set(v___x_2803_, 1, v_k_2639_);
lean_ctor_set(v___x_2803_, 0, v___x_2851_);
v___x_2853_ = v___x_2803_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_r_2793_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v_r_2642_);
v___x_2853_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v_isSharedCheck_2860_ = !lean_is_exclusive(v_r_2642_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; lean_object* v_unused_2862_; lean_object* v_unused_2863_; lean_object* v_unused_2864_; lean_object* v_unused_2865_; 
v_unused_2861_ = lean_ctor_get(v_r_2642_, 4);
lean_dec(v_unused_2861_);
v_unused_2862_ = lean_ctor_get(v_r_2642_, 3);
lean_dec(v_unused_2862_);
v_unused_2863_ = lean_ctor_get(v_r_2642_, 2);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_r_2642_, 1);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_r_2642_, 0);
lean_dec(v_unused_2865_);
v___x_2855_ = v_r_2642_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v_r_2642_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 4, v___x_2853_);
lean_ctor_set(v___x_2855_, 3, v_l_2792_);
lean_ctor_set(v___x_2855_, 2, v_v_2791_);
lean_ctor_set(v___x_2855_, 1, v_k_2790_);
lean_ctor_set(v___x_2855_, 0, v___x_2849_);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_k_2790_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_v_2791_);
lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_l_2792_);
lean_ctor_set(v_reuseFailAlloc_2859_, 4, v___x_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2873_; 
v_l_2873_ = lean_ctor_get(v_impl_2786_, 3);
if (lean_obj_tag(v_l_2873_) == 0)
{
lean_object* v_r_2874_; lean_object* v_k_2875_; lean_object* v_v_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
lean_inc_ref(v_l_2873_);
v_r_2874_ = lean_ctor_get(v_impl_2786_, 4);
v_k_2875_ = lean_ctor_get(v_impl_2786_, 1);
v_v_2876_ = lean_ctor_get(v_impl_2786_, 2);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_impl_2786_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; lean_object* v_unused_2889_; 
v_unused_2888_ = lean_ctor_get(v_impl_2786_, 3);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_impl_2786_, 0);
lean_dec(v_unused_2889_);
v___x_2878_ = v_impl_2786_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_r_2874_);
lean_inc(v_v_2876_);
lean_inc(v_k_2875_);
lean_dec(v_impl_2786_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2874_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 3, v_r_2874_);
lean_ctor_set(v___x_2878_, 2, v_v_2640_);
lean_ctor_set(v___x_2878_, 1, v_k_2639_);
lean_ctor_set(v___x_2878_, 0, v___x_2787_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_r_2874_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_r_2874_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v___x_2882_);
lean_ctor_set(v___x_2644_, 3, v_l_2873_);
lean_ctor_set(v___x_2644_, 2, v_v_2876_);
lean_ctor_set(v___x_2644_, 1, v_k_2875_);
lean_ctor_set(v___x_2644_, 0, v___x_2880_);
v___x_2884_ = v___x_2644_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_k_2875_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_v_2876_);
lean_ctor_set(v_reuseFailAlloc_2885_, 3, v_l_2873_);
lean_ctor_set(v_reuseFailAlloc_2885_, 4, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_r_2890_; 
v_r_2890_ = lean_ctor_get(v_impl_2786_, 4);
lean_inc(v_r_2890_);
if (lean_obj_tag(v_r_2890_) == 0)
{
lean_object* v_k_2891_; lean_object* v_v_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2915_; 
lean_inc(v_l_2873_);
v_k_2891_ = lean_ctor_get(v_impl_2786_, 1);
v_v_2892_ = lean_ctor_get(v_impl_2786_, 2);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_impl_2786_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2916_ = lean_ctor_get(v_impl_2786_, 4);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_impl_2786_, 3);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_impl_2786_, 0);
lean_dec(v_unused_2918_);
v___x_2894_ = v_impl_2786_;
v_isShared_2895_ = v_isSharedCheck_2915_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_v_2892_);
lean_inc(v_k_2891_);
lean_dec(v_impl_2786_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2915_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_k_2896_; lean_object* v_v_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2911_; 
v_k_2896_ = lean_ctor_get(v_r_2890_, 1);
v_v_2897_ = lean_ctor_get(v_r_2890_, 2);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_r_2890_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; lean_object* v_unused_2913_; lean_object* v_unused_2914_; 
v_unused_2912_ = lean_ctor_get(v_r_2890_, 4);
lean_dec(v_unused_2912_);
v_unused_2913_ = lean_ctor_get(v_r_2890_, 3);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v_r_2890_, 0);
lean_dec(v_unused_2914_);
v___x_2899_ = v_r_2890_;
v_isShared_2900_ = v_isSharedCheck_2911_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_v_2897_);
lean_inc(v_k_2896_);
lean_dec(v_r_2890_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2911_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2901_ = lean_unsigned_to_nat(3u);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 4, v_l_2873_);
lean_ctor_set(v___x_2899_, 3, v_l_2873_);
lean_ctor_set(v___x_2899_, 2, v_v_2892_);
lean_ctor_set(v___x_2899_, 1, v_k_2891_);
lean_ctor_set(v___x_2899_, 0, v___x_2787_);
v___x_2903_ = v___x_2899_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_k_2891_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_v_2892_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_l_2873_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_l_2873_);
v___x_2903_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2905_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 4, v_l_2873_);
lean_ctor_set(v___x_2894_, 2, v_v_2640_);
lean_ctor_set(v___x_2894_, 1, v_k_2639_);
lean_ctor_set(v___x_2894_, 0, v___x_2787_);
v___x_2905_ = v___x_2894_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_l_2873_);
lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_l_2873_);
v___x_2905_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2907_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v___x_2905_);
lean_ctor_set(v___x_2644_, 3, v___x_2903_);
lean_ctor_set(v___x_2644_, 2, v_v_2897_);
lean_ctor_set(v___x_2644_, 1, v_k_2896_);
lean_ctor_set(v___x_2644_, 0, v___x_2901_);
v___x_2907_ = v___x_2644_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_k_2896_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_v_2897_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2919_ = lean_unsigned_to_nat(2u);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 4, v_r_2890_);
lean_ctor_set(v___x_2644_, 3, v_impl_2786_);
lean_ctor_set(v___x_2644_, 0, v___x_2919_);
v___x_2921_ = v___x_2644_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2922_, 3, v_impl_2786_);
lean_ctor_set(v_reuseFailAlloc_2922_, 4, v_r_2890_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v_k_2635_);
lean_ctor_set(v___x_2925_, 2, v_v_2636_);
lean_ctor_set(v___x_2925_, 3, v_t_2637_);
lean_ctor_set(v___x_2925_, 4, v_t_2637_);
return v___x_2925_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object* v_k_2926_, lean_object* v_t_2927_){
_start:
{
if (lean_obj_tag(v_t_2927_) == 0)
{
lean_object* v_k_2928_; lean_object* v_l_2929_; lean_object* v_r_2930_; uint8_t v___x_2931_; 
v_k_2928_ = lean_ctor_get(v_t_2927_, 1);
v_l_2929_ = lean_ctor_get(v_t_2927_, 3);
v_r_2930_ = lean_ctor_get(v_t_2927_, 4);
v___x_2931_ = lean_nat_dec_lt(v_k_2926_, v_k_2928_);
if (v___x_2931_ == 0)
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_nat_dec_eq(v_k_2926_, v_k_2928_);
if (v___x_2932_ == 0)
{
v_t_2927_ = v_r_2930_;
goto _start;
}
else
{
return v___x_2932_;
}
}
else
{
v_t_2927_ = v_l_2929_;
goto _start;
}
}
else
{
uint8_t v___x_2935_; 
v___x_2935_ = 0;
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object* v_k_2936_, lean_object* v_t_2937_){
_start:
{
uint8_t v_res_2938_; lean_object* v_r_2939_; 
v_res_2938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2936_, v_t_2937_);
lean_dec(v_t_2937_);
lean_dec(v_k_2936_);
v_r_2939_ = lean_box(v_res_2938_);
return v_r_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* v_idx_2940_){
_start:
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = lean_box(1);
v___x_2942_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_box(0);
v___x_2944_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_idx_2940_, v___x_2943_, v___x_2941_);
return v___x_2944_;
}
else
{
lean_dec(v_idx_2940_);
return v___x_2941_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object* v_00_u03b2_2945_, lean_object* v_k_2946_, lean_object* v_t_2947_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2946_, v_t_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object* v_00_u03b2_2949_, lean_object* v_k_2950_, lean_object* v_t_2951_){
_start:
{
uint8_t v_res_2952_; lean_object* v_r_2953_; 
v_res_2952_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(v_00_u03b2_2949_, v_k_2950_, v_t_2951_);
lean_dec(v_t_2951_);
lean_dec(v_k_2950_);
v_r_2953_ = lean_box(v_res_2952_);
return v_r_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object* v_00_u03b2_2954_, lean_object* v_k_2955_, lean_object* v_v_2956_, lean_object* v_t_2957_, lean_object* v_hl_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2955_, v_v_2956_, v_t_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl(lean_object* v_x_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_obj_tag_nat(v_x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl___boxed(lean_object* v_x_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_IR_LocalContextEntry_ctorIdx___impl(v_x_2962_);
lean_dec_ref(v_x_2962_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object* v_t_2964_, lean_object* v_k_2965_){
_start:
{
if (lean_obj_tag(v_t_2964_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2966_ = lean_ctor_get(v_t_2964_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v_t_2964_, 1);
v___x_2967_ = lean_apply_1(v_k_2965_, v_a_2966_);
return v___x_2967_;
}
else
{
lean_object* v_a_2968_; lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2968_ = lean_ctor_get(v_t_2964_, 0);
lean_inc(v_a_2968_);
v_a_2969_ = lean_ctor_get(v_t_2964_, 1);
lean_inc(v_a_2969_);
lean_dec_ref_known(v_t_2964_, 2);
v___x_2970_ = lean_apply_2(v_k_2965_, v_a_2968_, v_a_2969_);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object* v_motive_2971_, lean_object* v_ctorIdx_2972_, lean_object* v_t_2973_, lean_object* v_h_2974_, lean_object* v_k_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2973_, v_k_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object* v_motive_2977_, lean_object* v_ctorIdx_2978_, lean_object* v_t_2979_, lean_object* v_h_2980_, lean_object* v_k_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_IR_LocalContextEntry_ctorElim(v_motive_2977_, v_ctorIdx_2978_, v_t_2979_, v_h_2980_, v_k_2981_);
lean_dec(v_ctorIdx_2978_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object* v_t_2983_, lean_object* v_param_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2983_, v_param_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object* v_motive_2986_, lean_object* v_t_2987_, lean_object* v_h_2988_, lean_object* v_param_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2987_, v_param_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object* v_t_2991_, lean_object* v_localVar_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2991_, v_localVar_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object* v_motive_2994_, lean_object* v_t_2995_, lean_object* v_h_2996_, lean_object* v_localVar_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2995_, v_localVar_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* v_ctx_2999_, lean_object* v_x_3000_, lean_object* v_t_3001_, lean_object* v_v_3002_){
_start:
{
lean_object* v_vars_3003_; lean_object* v_jps_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3013_; 
v_vars_3003_ = lean_ctor_get(v_ctx_2999_, 0);
v_jps_3004_ = lean_ctor_get(v_ctx_2999_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_ctx_2999_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3006_ = v_ctx_2999_;
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_jps_3004_);
lean_inc(v_vars_3003_);
lean_dec(v_ctx_2999_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_t_3001_);
lean_ctor_set(v___x_3008_, 1, v_v_3002_);
v___x_3009_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_3000_, v___x_3008_, v_vars_3003_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3009_);
v___x_3011_ = v___x_3006_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_jps_3004_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* v_ctx_3014_, lean_object* v_j_3015_, lean_object* v_xs_3016_, lean_object* v_b_3017_){
_start:
{
lean_object* v_vars_3018_; lean_object* v_jps_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3028_; 
v_vars_3018_ = lean_ctor_get(v_ctx_3014_, 0);
v_jps_3019_ = lean_ctor_get(v_ctx_3014_, 1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_ctx_3014_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3021_ = v_ctx_3014_;
v_isShared_3022_ = v_isSharedCheck_3028_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_jps_3019_);
lean_inc(v_vars_3018_);
lean_dec(v_ctx_3014_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3028_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_xs_3016_);
lean_ctor_set(v___x_3023_, 1, v_b_3017_);
v___x_3024_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_j_3015_, v___x_3023_, v_jps_3019_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3024_);
v___x_3026_ = v___x_3021_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_vars_3018_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* v_ctx_3029_, lean_object* v_p_3030_){
_start:
{
lean_object* v_vars_3031_; lean_object* v_jps_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3043_; 
v_vars_3031_ = lean_ctor_get(v_ctx_3029_, 0);
v_jps_3032_ = lean_ctor_get(v_ctx_3029_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_ctx_3029_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3034_ = v_ctx_3029_;
v_isShared_3035_ = v_isSharedCheck_3043_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_jps_3032_);
lean_inc(v_vars_3031_);
lean_dec(v_ctx_3029_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3043_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v_x_3036_; lean_object* v_ty_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v_x_3036_ = lean_ctor_get(v_p_3030_, 0);
lean_inc(v_x_3036_);
v_ty_3037_ = lean_ctor_get(v_p_3030_, 1);
lean_inc(v_ty_3037_);
lean_dec_ref(v_p_3030_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_ty_3037_);
v___x_3039_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_3036_, v___x_3038_, v_vars_3031_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3039_);
v___x_3041_ = v___x_3034_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_jps_3032_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object* v_as_3044_, size_t v_i_3045_, size_t v_stop_3046_, lean_object* v_b_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_usize_dec_eq(v_i_3045_, v_stop_3046_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; size_t v___x_3051_; size_t v___x_3052_; 
v___x_3049_ = lean_array_uget_borrowed(v_as_3044_, v_i_3045_);
lean_inc(v___x_3049_);
v___x_3050_ = l_Lean_IR_LocalContext_addParam(v_b_3047_, v___x_3049_);
v___x_3051_ = ((size_t)1ULL);
v___x_3052_ = lean_usize_add(v_i_3045_, v___x_3051_);
v_i_3045_ = v___x_3052_;
v_b_3047_ = v___x_3050_;
goto _start;
}
else
{
return v_b_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* v_as_3054_, lean_object* v_i_3055_, lean_object* v_stop_3056_, lean_object* v_b_3057_){
_start:
{
size_t v_i_boxed_3058_; size_t v_stop_boxed_3059_; lean_object* v_res_3060_; 
v_i_boxed_3058_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_stop_boxed_3059_ = lean_unbox_usize(v_stop_3056_);
lean_dec(v_stop_3056_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_3054_, v_i_boxed_3058_, v_stop_boxed_3059_, v_b_3057_);
lean_dec_ref(v_as_3054_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* v_ctx_3061_, lean_object* v_ps_3062_){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_array_get_size(v_ps_3062_);
v___x_3065_ = lean_nat_dec_lt(v___x_3063_, v___x_3064_);
if (v___x_3065_ == 0)
{
return v_ctx_3061_;
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = lean_nat_dec_le(v___x_3064_, v___x_3064_);
if (v___x_3066_ == 0)
{
if (v___x_3065_ == 0)
{
return v_ctx_3061_;
}
else
{
size_t v___x_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = ((size_t)0ULL);
v___x_3068_ = lean_usize_of_nat(v___x_3064_);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_3062_, v___x_3067_, v___x_3068_, v_ctx_3061_);
return v___x_3069_;
}
}
else
{
size_t v___x_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = ((size_t)0ULL);
v___x_3071_ = lean_usize_of_nat(v___x_3064_);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_3062_, v___x_3070_, v___x_3071_, v_ctx_3061_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_3073_, lean_object* v_ps_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_IR_LocalContext_addParams(v_ctx_3073_, v_ps_3074_);
lean_dec_ref(v_ps_3074_);
return v_res_3075_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_3076_, lean_object* v_j_3077_){
_start:
{
lean_object* v_jps_3078_; uint8_t v___x_3079_; 
v_jps_3078_ = lean_ctor_get(v_ctx_3076_, 1);
v___x_3079_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_j_3077_, v_jps_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_3080_, lean_object* v_j_3081_){
_start:
{
uint8_t v_res_3082_; lean_object* v_r_3083_; 
v_res_3082_ = l_Lean_IR_LocalContext_isJP(v_ctx_3080_, v_j_3081_);
lean_dec(v_j_3081_);
lean_dec_ref(v_ctx_3080_);
v_r_3083_ = lean_box(v_res_3082_);
return v_r_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(lean_object* v_t_3084_, lean_object* v_k_3085_){
_start:
{
if (lean_obj_tag(v_t_3084_) == 0)
{
lean_object* v_k_3086_; lean_object* v_v_3087_; lean_object* v_l_3088_; lean_object* v_r_3089_; uint8_t v___x_3090_; 
v_k_3086_ = lean_ctor_get(v_t_3084_, 1);
v_v_3087_ = lean_ctor_get(v_t_3084_, 2);
v_l_3088_ = lean_ctor_get(v_t_3084_, 3);
v_r_3089_ = lean_ctor_get(v_t_3084_, 4);
v___x_3090_ = lean_nat_dec_lt(v_k_3085_, v_k_3086_);
if (v___x_3090_ == 0)
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_nat_dec_eq(v_k_3085_, v_k_3086_);
if (v___x_3091_ == 0)
{
v_t_3084_ = v_r_3089_;
goto _start;
}
else
{
lean_object* v___x_3093_; 
lean_inc(v_v_3087_);
v___x_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_v_3087_);
return v___x_3093_;
}
}
else
{
v_t_3084_ = v_l_3088_;
goto _start;
}
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg___boxed(lean_object* v_t_3096_, lean_object* v_k_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_3096_, v_k_3097_);
lean_dec(v_k_3097_);
lean_dec(v_t_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_3099_, lean_object* v_j_3100_){
_start:
{
lean_object* v_jps_3101_; lean_object* v___x_3102_; 
v_jps_3101_ = lean_ctor_get(v_ctx_3099_, 1);
v___x_3102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_3101_, v_j_3100_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_box(0);
return v___x_3103_;
}
else
{
lean_object* v_val_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3112_; 
v_val_3104_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3106_ = v___x_3102_;
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_val_3104_);
lean_dec(v___x_3102_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_snd_3108_; lean_object* v___x_3110_; 
v_snd_3108_ = lean_ctor_get(v_val_3104_, 1);
lean_inc(v_snd_3108_);
lean_dec(v_val_3104_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v_snd_3108_);
v___x_3110_ = v___x_3106_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_snd_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_3113_, lean_object* v_j_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_3113_, v_j_3114_);
lean_dec(v_j_3114_);
lean_dec_ref(v_ctx_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(lean_object* v_00_u03b4_3116_, lean_object* v_t_3117_, lean_object* v_k_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_3117_, v_k_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___boxed(lean_object* v_00_u03b4_3120_, lean_object* v_t_3121_, lean_object* v_k_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(v_00_u03b4_3120_, v_t_3121_, v_k_3122_);
lean_dec(v_k_3122_);
lean_dec(v_t_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_3124_, lean_object* v_j_3125_){
_start:
{
lean_object* v_jps_3126_; lean_object* v___x_3127_; 
v_jps_3126_ = lean_ctor_get(v_ctx_3124_, 1);
v___x_3127_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_3126_, v_j_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_box(0);
return v___x_3128_;
}
else
{
lean_object* v_val_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3137_; 
v_val_3129_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3131_ = v___x_3127_;
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_val_3129_);
lean_dec(v___x_3127_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v_fst_3133_; lean_object* v___x_3135_; 
v_fst_3133_ = lean_ctor_get(v_val_3129_, 0);
lean_inc(v_fst_3133_);
lean_dec(v_val_3129_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_fst_3133_);
v___x_3135_ = v___x_3131_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_fst_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_3138_, lean_object* v_j_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_3138_, v_j_3139_);
lean_dec(v_j_3139_);
lean_dec_ref(v_ctx_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_3141_, lean_object* v_x_3142_){
_start:
{
lean_object* v_vars_3143_; lean_object* v___x_3144_; 
v_vars_3143_ = lean_ctor_get(v_ctx_3141_, 0);
v___x_3144_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3143_, v_x_3142_);
if (lean_obj_tag(v___x_3144_) == 1)
{
lean_object* v_val_3145_; 
v_val_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_val_3145_);
lean_dec_ref_known(v___x_3144_, 1);
if (lean_obj_tag(v_val_3145_) == 0)
{
uint8_t v___x_3146_; 
lean_dec_ref_known(v_val_3145_, 1);
v___x_3146_ = 1;
return v___x_3146_;
}
else
{
uint8_t v___x_3147_; 
lean_dec(v_val_3145_);
v___x_3147_ = 0;
return v___x_3147_;
}
}
else
{
uint8_t v___x_3148_; 
lean_dec(v___x_3144_);
v___x_3148_ = 0;
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_3149_, lean_object* v_x_3150_){
_start:
{
uint8_t v_res_3151_; lean_object* v_r_3152_; 
v_res_3151_ = l_Lean_IR_LocalContext_isParam(v_ctx_3149_, v_x_3150_);
lean_dec(v_x_3150_);
lean_dec_ref(v_ctx_3149_);
v_r_3152_ = lean_box(v_res_3151_);
return v_r_3152_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v_vars_3155_; lean_object* v___x_3156_; 
v_vars_3155_ = lean_ctor_get(v_ctx_3153_, 0);
v___x_3156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3155_, v_x_3154_);
if (lean_obj_tag(v___x_3156_) == 1)
{
lean_object* v_val_3157_; 
v_val_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_val_3157_);
lean_dec_ref_known(v___x_3156_, 1);
if (lean_obj_tag(v_val_3157_) == 1)
{
uint8_t v___x_3158_; 
lean_dec_ref_known(v_val_3157_, 2);
v___x_3158_ = 1;
return v___x_3158_;
}
else
{
uint8_t v___x_3159_; 
lean_dec(v_val_3157_);
v___x_3159_ = 0;
return v___x_3159_;
}
}
else
{
uint8_t v___x_3160_; 
lean_dec(v___x_3156_);
v___x_3160_ = 0;
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_3161_, lean_object* v_x_3162_){
_start:
{
uint8_t v_res_3163_; lean_object* v_r_3164_; 
v_res_3163_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_3161_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec_ref(v_ctx_3161_);
v_r_3164_ = lean_box(v_res_3163_);
return v_r_3164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_3165_, lean_object* v_t_3166_){
_start:
{
if (lean_obj_tag(v_t_3166_) == 0)
{
lean_object* v_k_3167_; lean_object* v_v_3168_; lean_object* v_l_3169_; lean_object* v_r_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3825_; 
v_k_3167_ = lean_ctor_get(v_t_3166_, 1);
v_v_3168_ = lean_ctor_get(v_t_3166_, 2);
v_l_3169_ = lean_ctor_get(v_t_3166_, 3);
v_r_3170_ = lean_ctor_get(v_t_3166_, 4);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_t_3166_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v_t_3166_, 0);
lean_dec(v_unused_3826_);
v___x_3172_ = v_t_3166_;
v_isShared_3173_ = v_isSharedCheck_3825_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_r_3170_);
lean_inc(v_l_3169_);
lean_inc(v_v_3168_);
lean_inc(v_k_3167_);
lean_dec(v_t_3166_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3825_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_nat_dec_lt(v_k_3165_, v_k_3167_);
if (v___x_3174_ == 0)
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_nat_dec_eq(v_k_3165_, v_k_3167_);
if (v___x_3175_ == 0)
{
lean_object* v_impl_3176_; lean_object* v___x_3177_; 
v_impl_3176_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3165_, v_r_3170_);
v___x_3177_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3176_) == 0)
{
if (lean_obj_tag(v_l_3169_) == 0)
{
lean_object* v_size_3178_; lean_object* v_size_3179_; lean_object* v_k_3180_; lean_object* v_v_3181_; lean_object* v_l_3182_; lean_object* v_r_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v_size_3178_ = lean_ctor_get(v_impl_3176_, 0);
v_size_3179_ = lean_ctor_get(v_l_3169_, 0);
v_k_3180_ = lean_ctor_get(v_l_3169_, 1);
v_v_3181_ = lean_ctor_get(v_l_3169_, 2);
v_l_3182_ = lean_ctor_get(v_l_3169_, 3);
v_r_3183_ = lean_ctor_get(v_l_3169_, 4);
lean_inc(v_r_3183_);
v___x_3184_ = lean_unsigned_to_nat(3u);
v___x_3185_ = lean_nat_mul(v___x_3184_, v_size_3178_);
v___x_3186_ = lean_nat_dec_lt(v___x_3185_, v_size_3179_);
lean_dec(v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
lean_dec(v_r_3183_);
v___x_3187_ = lean_nat_add(v___x_3177_, v_size_3179_);
v___x_3188_ = lean_nat_add(v___x_3187_, v_size_3178_);
lean_dec(v___x_3187_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_impl_3176_);
lean_ctor_set(v___x_3172_, 0, v___x_3188_);
v___x_3190_ = v___x_3172_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v_impl_3176_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
else
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3257_; 
lean_inc(v_l_3182_);
lean_inc(v_v_3181_);
lean_inc(v_k_3180_);
lean_inc(v_size_3179_);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; lean_object* v_unused_3259_; lean_object* v_unused_3260_; lean_object* v_unused_3261_; lean_object* v_unused_3262_; 
v_unused_3258_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3258_);
v_unused_3259_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_l_3169_, 2);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_l_3169_, 1);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3262_);
v___x_3193_ = v_l_3169_;
v_isShared_3194_ = v_isSharedCheck_3257_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_l_3169_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3257_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v_size_3195_; lean_object* v_size_3196_; lean_object* v_k_3197_; lean_object* v_v_3198_; lean_object* v_l_3199_; lean_object* v_r_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
v_size_3195_ = lean_ctor_get(v_l_3182_, 0);
v_size_3196_ = lean_ctor_get(v_r_3183_, 0);
v_k_3197_ = lean_ctor_get(v_r_3183_, 1);
v_v_3198_ = lean_ctor_get(v_r_3183_, 2);
v_l_3199_ = lean_ctor_get(v_r_3183_, 3);
v_r_3200_ = lean_ctor_get(v_r_3183_, 4);
v___x_3201_ = lean_unsigned_to_nat(2u);
v___x_3202_ = lean_nat_mul(v___x_3201_, v_size_3195_);
v___x_3203_ = lean_nat_dec_lt(v_size_3196_, v___x_3202_);
lean_dec(v___x_3202_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3232_; 
lean_inc(v_r_3200_);
lean_inc(v_l_3199_);
lean_inc(v_v_3198_);
lean_inc(v_k_3197_);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_r_3183_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; lean_object* v_unused_3235_; lean_object* v_unused_3236_; lean_object* v_unused_3237_; 
v_unused_3233_ = lean_ctor_get(v_r_3183_, 4);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_r_3183_, 3);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_r_3183_, 2);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_r_3183_, 1);
lean_dec(v_unused_3236_);
v_unused_3237_ = lean_ctor_get(v_r_3183_, 0);
lean_dec(v_unused_3237_);
v___x_3205_ = v_r_3183_;
v_isShared_3206_ = v_isSharedCheck_3232_;
goto v_resetjp_3204_;
}
else
{
lean_dec(v_r_3183_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3232_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___x_3220_; lean_object* v___y_3222_; 
v___x_3207_ = lean_nat_add(v___x_3177_, v_size_3179_);
lean_dec(v_size_3179_);
v___x_3208_ = lean_nat_add(v___x_3207_, v_size_3178_);
lean_dec(v___x_3207_);
v___x_3220_ = lean_nat_add(v___x_3177_, v_size_3195_);
if (lean_obj_tag(v_l_3199_) == 0)
{
lean_object* v_size_3230_; 
v_size_3230_ = lean_ctor_get(v_l_3199_, 0);
lean_inc(v_size_3230_);
v___y_3222_ = v_size_3230_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___y_3222_ = v___x_3231_;
goto v___jp_3221_;
}
v___jp_3209_:
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3213_ = lean_nat_add(v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec(v___y_3211_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 4, v_impl_3176_);
lean_ctor_set(v___x_3205_, 3, v_r_3200_);
lean_ctor_set(v___x_3205_, 2, v_v_3168_);
lean_ctor_set(v___x_3205_, 1, v_k_3167_);
lean_ctor_set(v___x_3205_, 0, v___x_3213_);
v___x_3215_ = v___x_3205_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v_r_3200_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v_impl_3176_);
v___x_3215_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3217_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 4, v___x_3215_);
lean_ctor_set(v___x_3193_, 3, v___y_3210_);
lean_ctor_set(v___x_3193_, 2, v_v_3198_);
lean_ctor_set(v___x_3193_, 1, v_k_3197_);
lean_ctor_set(v___x_3193_, 0, v___x_3208_);
v___x_3217_ = v___x_3193_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_k_3197_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_v_3198_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v___y_3210_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_nat_add(v___x_3220_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec(v___x_3220_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_l_3199_);
lean_ctor_set(v___x_3172_, 3, v_l_3182_);
lean_ctor_set(v___x_3172_, 2, v_v_3181_);
lean_ctor_set(v___x_3172_, 1, v_k_3180_);
lean_ctor_set(v___x_3172_, 0, v___x_3223_);
v___x_3225_ = v___x_3172_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_k_3180_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_v_3181_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_l_3182_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_l_3199_);
v___x_3225_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_nat_add(v___x_3177_, v_size_3178_);
if (lean_obj_tag(v_r_3200_) == 0)
{
lean_object* v_size_3227_; 
v_size_3227_ = lean_ctor_get(v_r_3200_, 0);
lean_inc(v_size_3227_);
v___y_3210_ = v___x_3225_;
v___y_3211_ = v___x_3226_;
v___y_3212_ = v_size_3227_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_unsigned_to_nat(0u);
v___y_3210_ = v___x_3225_;
v___y_3211_ = v___x_3226_;
v___y_3212_ = v___x_3228_;
goto v___jp_3209_;
}
}
}
}
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
lean_del_object(v___x_3172_);
v___x_3238_ = lean_nat_add(v___x_3177_, v_size_3179_);
lean_dec(v_size_3179_);
v___x_3239_ = lean_nat_add(v___x_3238_, v_size_3178_);
lean_dec(v___x_3238_);
v___x_3240_ = lean_nat_add(v___x_3177_, v_size_3178_);
v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3196_);
lean_dec(v___x_3240_);
lean_inc_ref(v_impl_3176_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 4, v_impl_3176_);
lean_ctor_set(v___x_3193_, 3, v_r_3183_);
lean_ctor_set(v___x_3193_, 2, v_v_3168_);
lean_ctor_set(v___x_3193_, 1, v_k_3167_);
lean_ctor_set(v___x_3193_, 0, v___x_3241_);
v___x_3243_ = v___x_3193_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_r_3183_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v_impl_3176_);
v___x_3243_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
v_isSharedCheck_3250_ = !lean_is_exclusive(v_impl_3176_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; lean_object* v_unused_3252_; lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; 
v_unused_3251_ = lean_ctor_get(v_impl_3176_, 4);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v_impl_3176_, 3);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_impl_3176_, 2);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_impl_3176_, 1);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v_impl_3176_, 0);
lean_dec(v_unused_3255_);
v___x_3245_ = v_impl_3176_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_dec(v_impl_3176_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 4, v___x_3243_);
lean_ctor_set(v___x_3245_, 3, v_l_3182_);
lean_ctor_set(v___x_3245_, 2, v_v_3181_);
lean_ctor_set(v___x_3245_, 1, v_k_3180_);
lean_ctor_set(v___x_3245_, 0, v___x_3239_);
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_k_3180_);
lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_v_3181_);
lean_ctor_set(v_reuseFailAlloc_3249_, 3, v_l_3182_);
lean_ctor_set(v_reuseFailAlloc_3249_, 4, v___x_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
v_size_3263_ = lean_ctor_get(v_impl_3176_, 0);
v___x_3264_ = lean_nat_add(v___x_3177_, v_size_3263_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_impl_3176_);
lean_ctor_set(v___x_3172_, 0, v___x_3264_);
v___x_3266_ = v___x_3172_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3267_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3267_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3267_, 4, v_impl_3176_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
if (lean_obj_tag(v_l_3169_) == 0)
{
lean_object* v_l_3268_; 
v_l_3268_ = lean_ctor_get(v_l_3169_, 3);
if (lean_obj_tag(v_l_3268_) == 0)
{
lean_object* v_r_3269_; 
lean_inc_ref(v_l_3268_);
v_r_3269_ = lean_ctor_get(v_l_3169_, 4);
lean_inc(v_r_3269_);
if (lean_obj_tag(v_r_3269_) == 0)
{
lean_object* v_size_3270_; lean_object* v_k_3271_; lean_object* v_v_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3285_; 
v_size_3270_ = lean_ctor_get(v_l_3169_, 0);
v_k_3271_ = lean_ctor_get(v_l_3169_, 1);
v_v_3272_ = lean_ctor_get(v_l_3169_, 2);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3285_ == 0)
{
lean_object* v_unused_3286_; lean_object* v_unused_3287_; 
v_unused_3286_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3287_);
v___x_3274_ = v_l_3169_;
v_isShared_3275_ = v_isSharedCheck_3285_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_v_3272_);
lean_inc(v_k_3271_);
lean_inc(v_size_3270_);
lean_dec(v_l_3169_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3285_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_size_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v_size_3276_ = lean_ctor_get(v_r_3269_, 0);
v___x_3277_ = lean_nat_add(v___x_3177_, v_size_3270_);
lean_dec(v_size_3270_);
v___x_3278_ = lean_nat_add(v___x_3177_, v_size_3276_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 4, v_impl_3176_);
lean_ctor_set(v___x_3274_, 3, v_r_3269_);
lean_ctor_set(v___x_3274_, 2, v_v_3168_);
lean_ctor_set(v___x_3274_, 1, v_k_3167_);
lean_ctor_set(v___x_3274_, 0, v___x_3278_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_r_3269_);
lean_ctor_set(v_reuseFailAlloc_3284_, 4, v_impl_3176_);
v___x_3280_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3282_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3280_);
lean_ctor_set(v___x_3172_, 3, v_l_3268_);
lean_ctor_set(v___x_3172_, 2, v_v_3272_);
lean_ctor_set(v___x_3172_, 1, v_k_3271_);
lean_ctor_set(v___x_3172_, 0, v___x_3277_);
v___x_3282_ = v___x_3172_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3283_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3283_, 3, v_l_3268_);
lean_ctor_set(v_reuseFailAlloc_3283_, 4, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
else
{
lean_object* v_k_3288_; lean_object* v_v_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3300_; 
v_k_3288_ = lean_ctor_get(v_l_3169_, 1);
v_v_3289_ = lean_ctor_get(v_l_3169_, 2);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; lean_object* v_unused_3302_; lean_object* v_unused_3303_; 
v_unused_3301_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3303_);
v___x_3291_ = v_l_3169_;
v_isShared_3292_ = v_isSharedCheck_3300_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_v_3289_);
lean_inc(v_k_3288_);
lean_dec(v_l_3169_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3300_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_unsigned_to_nat(3u);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 3, v_r_3269_);
lean_ctor_set(v___x_3291_, 2, v_v_3168_);
lean_ctor_set(v___x_3291_, 1, v_k_3167_);
lean_ctor_set(v___x_3291_, 0, v___x_3177_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3299_, 3, v_r_3269_);
lean_ctor_set(v_reuseFailAlloc_3299_, 4, v_r_3269_);
v___x_3295_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3295_);
lean_ctor_set(v___x_3172_, 3, v_l_3268_);
lean_ctor_set(v___x_3172_, 2, v_v_3289_);
lean_ctor_set(v___x_3172_, 1, v_k_3288_);
lean_ctor_set(v___x_3172_, 0, v___x_3293_);
v___x_3297_ = v___x_3172_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_l_3268_);
lean_ctor_set(v_reuseFailAlloc_3298_, 4, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
else
{
lean_object* v_r_3304_; 
v_r_3304_ = lean_ctor_get(v_l_3169_, 4);
lean_inc(v_r_3304_);
if (lean_obj_tag(v_r_3304_) == 0)
{
lean_object* v_k_3305_; lean_object* v_v_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3329_; 
lean_inc(v_l_3268_);
v_k_3305_ = lean_ctor_get(v_l_3169_, 1);
v_v_3306_ = lean_ctor_get(v_l_3169_, 2);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3329_ == 0)
{
lean_object* v_unused_3330_; lean_object* v_unused_3331_; lean_object* v_unused_3332_; 
v_unused_3330_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3330_);
v_unused_3331_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3331_);
v_unused_3332_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3332_);
v___x_3308_ = v_l_3169_;
v_isShared_3309_ = v_isSharedCheck_3329_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_v_3306_);
lean_inc(v_k_3305_);
lean_dec(v_l_3169_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3329_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_k_3310_; lean_object* v_v_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3325_; 
v_k_3310_ = lean_ctor_get(v_r_3304_, 1);
v_v_3311_ = lean_ctor_get(v_r_3304_, 2);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_r_3304_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; lean_object* v_unused_3327_; lean_object* v_unused_3328_; 
v_unused_3326_ = lean_ctor_get(v_r_3304_, 4);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v_r_3304_, 3);
lean_dec(v_unused_3327_);
v_unused_3328_ = lean_ctor_get(v_r_3304_, 0);
lean_dec(v_unused_3328_);
v___x_3313_ = v_r_3304_;
v_isShared_3314_ = v_isSharedCheck_3325_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_v_3311_);
lean_inc(v_k_3310_);
lean_dec(v_r_3304_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3325_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = lean_unsigned_to_nat(3u);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 4, v_l_3268_);
lean_ctor_set(v___x_3313_, 3, v_l_3268_);
lean_ctor_set(v___x_3313_, 2, v_v_3306_);
lean_ctor_set(v___x_3313_, 1, v_k_3305_);
lean_ctor_set(v___x_3313_, 0, v___x_3177_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_k_3305_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_v_3306_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_l_3268_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v_l_3268_);
v___x_3317_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_l_3268_);
lean_ctor_set(v___x_3308_, 2, v_v_3168_);
lean_ctor_set(v___x_3308_, 1, v_k_3167_);
lean_ctor_set(v___x_3308_, 0, v___x_3177_);
v___x_3319_ = v___x_3308_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3323_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3323_, 3, v_l_3268_);
lean_ctor_set(v_reuseFailAlloc_3323_, 4, v_l_3268_);
v___x_3319_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3319_);
lean_ctor_set(v___x_3172_, 3, v___x_3317_);
lean_ctor_set(v___x_3172_, 2, v_v_3311_);
lean_ctor_set(v___x_3172_, 1, v_k_3310_);
lean_ctor_set(v___x_3172_, 0, v___x_3315_);
v___x_3321_ = v___x_3172_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_k_3310_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_v_3311_);
lean_ctor_set(v_reuseFailAlloc_3322_, 3, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3322_, 4, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_unsigned_to_nat(2u);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_r_3304_);
lean_ctor_set(v___x_3172_, 0, v___x_3333_);
v___x_3335_ = v___x_3172_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3336_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3336_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3336_, 4, v_r_3304_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
else
{
lean_object* v___x_3338_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_l_3169_);
lean_ctor_set(v___x_3172_, 0, v___x_3177_);
v___x_3338_ = v___x_3172_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v_l_3169_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_del_object(v___x_3172_);
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
if (lean_obj_tag(v_l_3169_) == 0)
{
if (lean_obj_tag(v_r_3170_) == 0)
{
lean_object* v_size_3340_; lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_l_3343_; lean_object* v_r_3344_; lean_object* v_size_3345_; lean_object* v_k_3346_; lean_object* v_v_3347_; lean_object* v_l_3348_; lean_object* v_r_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_size_3340_ = lean_ctor_get(v_l_3169_, 0);
v_k_3341_ = lean_ctor_get(v_l_3169_, 1);
v_v_3342_ = lean_ctor_get(v_l_3169_, 2);
v_l_3343_ = lean_ctor_get(v_l_3169_, 3);
v_r_3344_ = lean_ctor_get(v_l_3169_, 4);
lean_inc(v_r_3344_);
v_size_3345_ = lean_ctor_get(v_r_3170_, 0);
v_k_3346_ = lean_ctor_get(v_r_3170_, 1);
v_v_3347_ = lean_ctor_get(v_r_3170_, 2);
v_l_3348_ = lean_ctor_get(v_r_3170_, 3);
lean_inc(v_l_3348_);
v_r_3349_ = lean_ctor_get(v_r_3170_, 4);
v___x_3350_ = lean_unsigned_to_nat(1u);
v___x_3351_ = lean_nat_dec_lt(v_size_3340_, v_size_3345_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3487_; 
lean_inc(v_l_3343_);
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; lean_object* v_unused_3490_; lean_object* v_unused_3491_; lean_object* v_unused_3492_; 
v_unused_3488_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_l_3169_, 2);
lean_dec(v_unused_3490_);
v_unused_3491_ = lean_ctor_get(v_l_3169_, 1);
lean_dec(v_unused_3491_);
v_unused_3492_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3492_);
v___x_3353_ = v_l_3169_;
v_isShared_3354_ = v_isSharedCheck_3487_;
goto v_resetjp_3352_;
}
else
{
lean_dec(v_l_3169_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3487_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v_tree_3356_; 
v___x_3355_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3341_, v_v_3342_, v_l_3343_, v_r_3344_);
v_tree_3356_ = lean_ctor_get(v___x_3355_, 2);
if (lean_obj_tag(v_tree_3356_) == 0)
{
lean_object* v_k_3357_; lean_object* v_v_3358_; lean_object* v_size_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
lean_inc_ref(v_tree_3356_);
v_k_3357_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_k_3357_);
v_v_3358_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_v_3358_);
lean_dec_ref(v___x_3355_);
v_size_3359_ = lean_ctor_get(v_tree_3356_, 0);
v___x_3360_ = lean_unsigned_to_nat(3u);
v___x_3361_ = lean_nat_mul(v___x_3360_, v_size_3359_);
v___x_3362_ = lean_nat_dec_lt(v___x_3361_, v_size_3345_);
lean_dec(v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_dec(v_l_3348_);
v___x_3363_ = lean_nat_add(v___x_3350_, v_size_3359_);
v___x_3364_ = lean_nat_add(v___x_3363_, v_size_3345_);
lean_dec(v___x_3363_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_r_3170_);
lean_ctor_set(v___x_3353_, 3, v_tree_3356_);
lean_ctor_set(v___x_3353_, 2, v_v_3358_);
lean_ctor_set(v___x_3353_, 1, v_k_3357_);
lean_ctor_set(v___x_3353_, 0, v___x_3364_);
v___x_3366_ = v___x_3353_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v_tree_3356_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v_r_3170_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
else
{
lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_r_3349_);
lean_inc(v_v_3347_);
lean_inc(v_k_3346_);
lean_inc(v_size_3345_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; lean_object* v_unused_3425_; lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3423_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_r_3170_, 2);
lean_dec(v_unused_3425_);
v_unused_3426_ = lean_ctor_get(v_r_3170_, 1);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3427_);
v___x_3369_ = v_r_3170_;
v_isShared_3370_ = v_isSharedCheck_3422_;
goto v_resetjp_3368_;
}
else
{
lean_dec(v_r_3170_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3422_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_size_3371_; lean_object* v_k_3372_; lean_object* v_v_3373_; lean_object* v_l_3374_; lean_object* v_r_3375_; lean_object* v_size_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_size_3371_ = lean_ctor_get(v_l_3348_, 0);
v_k_3372_ = lean_ctor_get(v_l_3348_, 1);
v_v_3373_ = lean_ctor_get(v_l_3348_, 2);
v_l_3374_ = lean_ctor_get(v_l_3348_, 3);
v_r_3375_ = lean_ctor_get(v_l_3348_, 4);
v_size_3376_ = lean_ctor_get(v_r_3349_, 0);
v___x_3377_ = lean_unsigned_to_nat(2u);
v___x_3378_ = lean_nat_mul(v___x_3377_, v_size_3376_);
v___x_3379_ = lean_nat_dec_lt(v_size_3371_, v___x_3378_);
lean_dec(v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3407_; 
lean_inc(v_r_3375_);
lean_inc(v_l_3374_);
lean_inc(v_v_3373_);
lean_inc(v_k_3372_);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_l_3348_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; lean_object* v_unused_3412_; 
v_unused_3408_ = lean_ctor_get(v_l_3348_, 4);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_l_3348_, 3);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_l_3348_, 2);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_l_3348_, 1);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_l_3348_, 0);
lean_dec(v_unused_3412_);
v___x_3381_ = v_l_3348_;
v_isShared_3382_ = v_isSharedCheck_3407_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v_l_3348_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3407_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3397_; 
v___x_3383_ = lean_nat_add(v___x_3350_, v_size_3359_);
v___x_3384_ = lean_nat_add(v___x_3383_, v_size_3345_);
lean_dec(v_size_3345_);
if (lean_obj_tag(v_l_3374_) == 0)
{
lean_object* v_size_3405_; 
v_size_3405_ = lean_ctor_get(v_l_3374_, 0);
lean_inc(v_size_3405_);
v___y_3397_ = v_size_3405_;
goto v___jp_3396_;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_unsigned_to_nat(0u);
v___y_3397_ = v___x_3406_;
goto v___jp_3396_;
}
v___jp_3385_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_nat_add(v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec(v___y_3387_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 4, v_r_3349_);
lean_ctor_set(v___x_3381_, 3, v_r_3375_);
lean_ctor_set(v___x_3381_, 2, v_v_3347_);
lean_ctor_set(v___x_3381_, 1, v_k_3346_);
lean_ctor_set(v___x_3381_, 0, v___x_3389_);
v___x_3391_ = v___x_3381_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_r_3375_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v_r_3349_);
v___x_3391_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3393_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 4, v___x_3391_);
lean_ctor_set(v___x_3369_, 3, v___y_3386_);
lean_ctor_set(v___x_3369_, 2, v_v_3373_);
lean_ctor_set(v___x_3369_, 1, v_k_3372_);
lean_ctor_set(v___x_3369_, 0, v___x_3384_);
v___x_3393_ = v___x_3369_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_k_3372_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_v_3373_);
lean_ctor_set(v_reuseFailAlloc_3394_, 3, v___y_3386_);
lean_ctor_set(v_reuseFailAlloc_3394_, 4, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
v___jp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3398_ = lean_nat_add(v___x_3383_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec(v___x_3383_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_l_3374_);
lean_ctor_set(v___x_3353_, 3, v_tree_3356_);
lean_ctor_set(v___x_3353_, 2, v_v_3358_);
lean_ctor_set(v___x_3353_, 1, v_k_3357_);
lean_ctor_set(v___x_3353_, 0, v___x_3398_);
v___x_3400_ = v___x_3353_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_tree_3356_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v_l_3374_);
v___x_3400_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_nat_add(v___x_3350_, v_size_3376_);
if (lean_obj_tag(v_r_3375_) == 0)
{
lean_object* v_size_3402_; 
v_size_3402_ = lean_ctor_get(v_r_3375_, 0);
lean_inc(v_size_3402_);
v___y_3386_ = v___x_3400_;
v___y_3387_ = v___x_3401_;
v___y_3388_ = v_size_3402_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_unsigned_to_nat(0u);
v___y_3386_ = v___x_3400_;
v___y_3387_ = v___x_3401_;
v___y_3388_ = v___x_3403_;
goto v___jp_3385_;
}
}
}
}
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3413_ = lean_nat_add(v___x_3350_, v_size_3359_);
v___x_3414_ = lean_nat_add(v___x_3413_, v_size_3345_);
lean_dec(v_size_3345_);
v___x_3415_ = lean_nat_add(v___x_3413_, v_size_3371_);
lean_dec(v___x_3413_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 4, v_l_3348_);
lean_ctor_set(v___x_3369_, 3, v_tree_3356_);
lean_ctor_set(v___x_3369_, 2, v_v_3358_);
lean_ctor_set(v___x_3369_, 1, v_k_3357_);
lean_ctor_set(v___x_3369_, 0, v___x_3415_);
v___x_3417_ = v___x_3369_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3421_, 3, v_tree_3356_);
lean_ctor_set(v_reuseFailAlloc_3421_, 4, v_l_3348_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_r_3349_);
lean_ctor_set(v___x_3353_, 3, v___x_3417_);
lean_ctor_set(v___x_3353_, 2, v_v_3347_);
lean_ctor_set(v___x_3353_, 1, v_k_3346_);
lean_ctor_set(v___x_3353_, 0, v___x_3414_);
v___x_3419_ = v___x_3353_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_r_3349_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
}
else
{
lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3481_; 
lean_inc(v_r_3349_);
lean_inc(v_v_3347_);
lean_inc(v_k_3346_);
lean_inc(v_size_3345_);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; lean_object* v_unused_3484_; lean_object* v_unused_3485_; lean_object* v_unused_3486_; 
v_unused_3482_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3483_);
v_unused_3484_ = lean_ctor_get(v_r_3170_, 2);
lean_dec(v_unused_3484_);
v_unused_3485_ = lean_ctor_get(v_r_3170_, 1);
lean_dec(v_unused_3485_);
v_unused_3486_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3486_);
v___x_3429_ = v_r_3170_;
v_isShared_3430_ = v_isSharedCheck_3481_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v_r_3170_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3481_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
if (lean_obj_tag(v_l_3348_) == 0)
{
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_k_3431_; lean_object* v_v_3432_; lean_object* v_size_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_inc(v_tree_3356_);
v_k_3431_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_k_3431_);
v_v_3432_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_v_3432_);
lean_dec_ref(v___x_3355_);
v_size_3433_ = lean_ctor_get(v_l_3348_, 0);
v___x_3434_ = lean_nat_add(v___x_3350_, v_size_3345_);
lean_dec(v_size_3345_);
v___x_3435_ = lean_nat_add(v___x_3350_, v_size_3433_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 4, v_l_3348_);
lean_ctor_set(v___x_3429_, 3, v_tree_3356_);
lean_ctor_set(v___x_3429_, 2, v_v_3432_);
lean_ctor_set(v___x_3429_, 1, v_k_3431_);
lean_ctor_set(v___x_3429_, 0, v___x_3435_);
v___x_3437_ = v___x_3429_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_k_3431_);
lean_ctor_set(v_reuseFailAlloc_3441_, 2, v_v_3432_);
lean_ctor_set(v_reuseFailAlloc_3441_, 3, v_tree_3356_);
lean_ctor_set(v_reuseFailAlloc_3441_, 4, v_l_3348_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_r_3349_);
lean_ctor_set(v___x_3353_, 3, v___x_3437_);
lean_ctor_set(v___x_3353_, 2, v_v_3347_);
lean_ctor_set(v___x_3353_, 1, v_k_3346_);
lean_ctor_set(v___x_3353_, 0, v___x_3434_);
v___x_3439_ = v___x_3353_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3440_, 3, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_r_3349_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
else
{
lean_object* v_k_3442_; lean_object* v_v_3443_; lean_object* v_k_3444_; lean_object* v_v_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v_size_3345_);
v_k_3442_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_k_3442_);
v_v_3443_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_v_3443_);
lean_dec_ref(v___x_3355_);
v_k_3444_ = lean_ctor_get(v_l_3348_, 1);
v_v_3445_ = lean_ctor_get(v_l_3348_, 2);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_l_3348_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; lean_object* v_unused_3461_; lean_object* v_unused_3462_; 
v_unused_3460_ = lean_ctor_get(v_l_3348_, 4);
lean_dec(v_unused_3460_);
v_unused_3461_ = lean_ctor_get(v_l_3348_, 3);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_l_3348_, 0);
lean_dec(v_unused_3462_);
v___x_3447_ = v_l_3348_;
v_isShared_3448_ = v_isSharedCheck_3459_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_v_3445_);
lean_inc(v_k_3444_);
lean_dec(v_l_3348_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3459_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_unsigned_to_nat(3u);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 4, v_r_3349_);
lean_ctor_set(v___x_3447_, 3, v_r_3349_);
lean_ctor_set(v___x_3447_, 2, v_v_3443_);
lean_ctor_set(v___x_3447_, 1, v_k_3442_);
lean_ctor_set(v___x_3447_, 0, v___x_3350_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_k_3442_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_v_3443_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_r_3349_);
v___x_3451_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 3, v_r_3349_);
lean_ctor_set(v___x_3429_, 0, v___x_3350_);
v___x_3453_ = v___x_3429_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v_r_3349_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v___x_3453_);
lean_ctor_set(v___x_3353_, 3, v___x_3451_);
lean_ctor_set(v___x_3353_, 2, v_v_3445_);
lean_ctor_set(v___x_3353_, 1, v_k_3444_);
lean_ctor_set(v___x_3353_, 0, v___x_3449_);
v___x_3455_ = v___x_3353_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_k_3444_);
lean_ctor_set(v_reuseFailAlloc_3456_, 2, v_v_3445_);
lean_ctor_set(v_reuseFailAlloc_3456_, 3, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3456_, 4, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_k_3463_; lean_object* v_v_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
lean_dec(v_size_3345_);
v_k_3463_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_k_3463_);
v_v_3464_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_v_3464_);
lean_dec_ref(v___x_3355_);
v___x_3465_ = lean_unsigned_to_nat(3u);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 4, v_l_3348_);
lean_ctor_set(v___x_3429_, 2, v_v_3464_);
lean_ctor_set(v___x_3429_, 1, v_k_3463_);
lean_ctor_set(v___x_3429_, 0, v___x_3350_);
v___x_3467_ = v___x_3429_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_k_3463_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_v_3464_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_l_3348_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_l_3348_);
v___x_3467_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_r_3349_);
lean_ctor_set(v___x_3353_, 3, v___x_3467_);
lean_ctor_set(v___x_3353_, 2, v_v_3347_);
lean_ctor_set(v___x_3353_, 1, v_k_3346_);
lean_ctor_set(v___x_3353_, 0, v___x_3465_);
v___x_3469_ = v___x_3353_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_r_3349_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
else
{
lean_object* v_k_3472_; lean_object* v_v_3473_; lean_object* v___x_3475_; 
v_k_3472_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_k_3472_);
v_v_3473_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_v_3473_);
lean_dec_ref(v___x_3355_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 3, v_r_3349_);
v___x_3475_ = v___x_3429_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_size_3345_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_k_3346_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_v_3347_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_r_3349_);
v___x_3475_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_unsigned_to_nat(2u);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v___x_3475_);
lean_ctor_set(v___x_3353_, 3, v_r_3349_);
lean_ctor_set(v___x_3353_, 2, v_v_3473_);
lean_ctor_set(v___x_3353_, 1, v_k_3472_);
lean_ctor_set(v___x_3353_, 0, v___x_3476_);
v___x_3478_ = v___x_3353_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3472_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3473_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v___x_3475_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
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
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3645_; 
lean_inc(v_r_3349_);
lean_inc(v_v_3347_);
lean_inc(v_k_3346_);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; lean_object* v_unused_3647_; lean_object* v_unused_3648_; lean_object* v_unused_3649_; lean_object* v_unused_3650_; 
v_unused_3646_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3646_);
v_unused_3647_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3647_);
v_unused_3648_ = lean_ctor_get(v_r_3170_, 2);
lean_dec(v_unused_3648_);
v_unused_3649_ = lean_ctor_get(v_r_3170_, 1);
lean_dec(v_unused_3649_);
v_unused_3650_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3650_);
v___x_3494_ = v_r_3170_;
v_isShared_3495_ = v_isSharedCheck_3645_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v_r_3170_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3645_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v_tree_3497_; 
v___x_3496_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3346_, v_v_3347_, v_l_3348_, v_r_3349_);
v_tree_3497_ = lean_ctor_get(v___x_3496_, 2);
lean_inc(v_tree_3497_);
if (lean_obj_tag(v_tree_3497_) == 0)
{
lean_object* v_k_3498_; lean_object* v_v_3499_; lean_object* v_size_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v_k_3498_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_k_3498_);
v_v_3499_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_v_3499_);
lean_dec_ref(v___x_3496_);
v_size_3500_ = lean_ctor_get(v_tree_3497_, 0);
v___x_3501_ = lean_unsigned_to_nat(3u);
v___x_3502_ = lean_nat_mul(v___x_3501_, v_size_3500_);
v___x_3503_ = lean_nat_dec_lt(v___x_3502_, v_size_3340_);
lean_dec(v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_dec(v_r_3344_);
v___x_3504_ = lean_nat_add(v___x_3350_, v_size_3340_);
v___x_3505_ = lean_nat_add(v___x_3504_, v_size_3500_);
lean_dec(v___x_3504_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_tree_3497_);
lean_ctor_set(v___x_3494_, 3, v_l_3169_);
lean_ctor_set(v___x_3494_, 2, v_v_3499_);
lean_ctor_set(v___x_3494_, 1, v_k_3498_);
lean_ctor_set(v___x_3494_, 0, v___x_3505_);
v___x_3507_ = v___x_3494_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3498_);
lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3499_);
lean_ctor_set(v_reuseFailAlloc_3508_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_tree_3497_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
else
{
lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3574_; 
lean_inc(v_l_3343_);
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
lean_inc(v_size_3340_);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; lean_object* v_unused_3576_; lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; 
v_unused_3575_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3575_);
v_unused_3576_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3576_);
v_unused_3577_ = lean_ctor_get(v_l_3169_, 2);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_l_3169_, 1);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3579_);
v___x_3510_ = v_l_3169_;
v_isShared_3511_ = v_isSharedCheck_3574_;
goto v_resetjp_3509_;
}
else
{
lean_dec(v_l_3169_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3574_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_size_3512_; lean_object* v_size_3513_; lean_object* v_k_3514_; lean_object* v_v_3515_; lean_object* v_l_3516_; lean_object* v_r_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_size_3512_ = lean_ctor_get(v_l_3343_, 0);
v_size_3513_ = lean_ctor_get(v_r_3344_, 0);
v_k_3514_ = lean_ctor_get(v_r_3344_, 1);
v_v_3515_ = lean_ctor_get(v_r_3344_, 2);
v_l_3516_ = lean_ctor_get(v_r_3344_, 3);
v_r_3517_ = lean_ctor_get(v_r_3344_, 4);
v___x_3518_ = lean_unsigned_to_nat(2u);
v___x_3519_ = lean_nat_mul(v___x_3518_, v_size_3512_);
v___x_3520_ = lean_nat_dec_lt(v_size_3513_, v___x_3519_);
lean_dec(v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3558_; 
lean_inc(v_r_3517_);
lean_inc(v_l_3516_);
lean_inc(v_v_3515_);
lean_inc(v_k_3514_);
lean_del_object(v___x_3510_);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_r_3344_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; lean_object* v_unused_3563_; 
v_unused_3559_ = lean_ctor_get(v_r_3344_, 4);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_r_3344_, 3);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_r_3344_, 2);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_r_3344_, 1);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_r_3344_, 0);
lean_dec(v_unused_3563_);
v___x_3522_ = v_r_3344_;
v_isShared_3523_ = v_isSharedCheck_3558_;
goto v_resetjp_3521_;
}
else
{
lean_dec(v_r_3344_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3558_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___x_3546_; lean_object* v___y_3548_; 
v___x_3524_ = lean_nat_add(v___x_3350_, v_size_3340_);
lean_dec(v_size_3340_);
v___x_3525_ = lean_nat_add(v___x_3524_, v_size_3500_);
lean_dec(v___x_3524_);
v___x_3546_ = lean_nat_add(v___x_3350_, v_size_3512_);
if (lean_obj_tag(v_l_3516_) == 0)
{
lean_object* v_size_3556_; 
v_size_3556_ = lean_ctor_get(v_l_3516_, 0);
lean_inc(v_size_3556_);
v___y_3548_ = v_size_3556_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_unsigned_to_nat(0u);
v___y_3548_ = v___x_3557_;
goto v___jp_3547_;
}
v___jp_3526_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = lean_nat_add(v___y_3527_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec(v___y_3527_);
lean_inc_ref(v_tree_3497_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v_tree_3497_);
lean_ctor_set(v___x_3522_, 3, v_r_3517_);
lean_ctor_set(v___x_3522_, 2, v_v_3499_);
lean_ctor_set(v___x_3522_, 1, v_k_3498_);
lean_ctor_set(v___x_3522_, 0, v___x_3530_);
v___x_3532_ = v___x_3522_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_k_3498_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_v_3499_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_r_3517_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v_tree_3497_);
v___x_3532_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_isSharedCheck_3539_ = !lean_is_exclusive(v_tree_3497_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; lean_object* v_unused_3541_; lean_object* v_unused_3542_; lean_object* v_unused_3543_; lean_object* v_unused_3544_; 
v_unused_3540_ = lean_ctor_get(v_tree_3497_, 4);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v_tree_3497_, 3);
lean_dec(v_unused_3541_);
v_unused_3542_ = lean_ctor_get(v_tree_3497_, 2);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v_tree_3497_, 1);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v_tree_3497_, 0);
lean_dec(v_unused_3544_);
v___x_3534_ = v_tree_3497_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_dec(v_tree_3497_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 4, v___x_3532_);
lean_ctor_set(v___x_3534_, 3, v___y_3528_);
lean_ctor_set(v___x_3534_, 2, v_v_3515_);
lean_ctor_set(v___x_3534_, 1, v_k_3514_);
lean_ctor_set(v___x_3534_, 0, v___x_3525_);
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v___y_3528_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v___x_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
v___jp_3547_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_nat_add(v___x_3546_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec(v___x_3546_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_l_3516_);
lean_ctor_set(v___x_3494_, 3, v_l_3343_);
lean_ctor_set(v___x_3494_, 2, v_v_3342_);
lean_ctor_set(v___x_3494_, 1, v_k_3341_);
lean_ctor_set(v___x_3494_, 0, v___x_3549_);
v___x_3551_ = v___x_3494_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_l_3516_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_nat_add(v___x_3350_, v_size_3500_);
if (lean_obj_tag(v_r_3517_) == 0)
{
lean_object* v_size_3553_; 
v_size_3553_ = lean_ctor_get(v_r_3517_, 0);
lean_inc(v_size_3553_);
v___y_3527_ = v___x_3552_;
v___y_3528_ = v___x_3551_;
v___y_3529_ = v_size_3553_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_unsigned_to_nat(0u);
v___y_3527_ = v___x_3552_;
v___y_3528_ = v___x_3551_;
v___y_3529_ = v___x_3554_;
goto v___jp_3526_;
}
}
}
}
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3564_ = lean_nat_add(v___x_3350_, v_size_3340_);
lean_dec(v_size_3340_);
v___x_3565_ = lean_nat_add(v___x_3564_, v_size_3500_);
lean_dec(v___x_3564_);
v___x_3566_ = lean_nat_add(v___x_3350_, v_size_3500_);
v___x_3567_ = lean_nat_add(v___x_3566_, v_size_3513_);
lean_dec(v___x_3566_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_tree_3497_);
lean_ctor_set(v___x_3494_, 3, v_r_3344_);
lean_ctor_set(v___x_3494_, 2, v_v_3499_);
lean_ctor_set(v___x_3494_, 1, v_k_3498_);
lean_ctor_set(v___x_3494_, 0, v___x_3567_);
v___x_3569_ = v___x_3494_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_k_3498_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v_v_3499_);
lean_ctor_set(v_reuseFailAlloc_3573_, 3, v_r_3344_);
lean_ctor_set(v_reuseFailAlloc_3573_, 4, v_tree_3497_);
v___x_3569_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3571_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 4, v___x_3569_);
lean_ctor_set(v___x_3510_, 0, v___x_3565_);
v___x_3571_ = v___x_3510_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3572_, 4, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3343_) == 0)
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3603_; 
lean_inc_ref(v_l_3343_);
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
lean_inc(v_size_3340_);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; lean_object* v_unused_3607_; lean_object* v_unused_3608_; 
v_unused_3604_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_l_3169_, 2);
lean_dec(v_unused_3606_);
v_unused_3607_ = lean_ctor_get(v_l_3169_, 1);
lean_dec(v_unused_3607_);
v_unused_3608_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3608_);
v___x_3581_ = v_l_3169_;
v_isShared_3582_ = v_isSharedCheck_3603_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_l_3169_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3603_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
if (lean_obj_tag(v_r_3344_) == 0)
{
lean_object* v_k_3583_; lean_object* v_v_3584_; lean_object* v_size_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v_k_3583_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_k_3583_);
v_v_3584_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_v_3584_);
lean_dec_ref(v___x_3496_);
v_size_3585_ = lean_ctor_get(v_r_3344_, 0);
v___x_3586_ = lean_nat_add(v___x_3350_, v_size_3340_);
lean_dec(v_size_3340_);
v___x_3587_ = lean_nat_add(v___x_3350_, v_size_3585_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_tree_3497_);
lean_ctor_set(v___x_3494_, 3, v_r_3344_);
lean_ctor_set(v___x_3494_, 2, v_v_3584_);
lean_ctor_set(v___x_3494_, 1, v_k_3583_);
lean_ctor_set(v___x_3494_, 0, v___x_3587_);
v___x_3589_ = v___x_3494_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_r_3344_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_tree_3497_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v___x_3589_);
lean_ctor_set(v___x_3581_, 0, v___x_3586_);
v___x_3591_ = v___x_3581_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3592_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3592_, 4, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
else
{
lean_object* v_k_3594_; lean_object* v_v_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
lean_dec(v_size_3340_);
v_k_3594_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_k_3594_);
v_v_3595_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_v_3595_);
lean_dec_ref(v___x_3496_);
v___x_3596_ = lean_unsigned_to_nat(3u);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_r_3344_);
lean_ctor_set(v___x_3494_, 3, v_r_3344_);
lean_ctor_set(v___x_3494_, 2, v_v_3595_);
lean_ctor_set(v___x_3494_, 1, v_k_3594_);
lean_ctor_set(v___x_3494_, 0, v___x_3350_);
v___x_3598_ = v___x_3494_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_k_3594_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_v_3595_);
lean_ctor_set(v_reuseFailAlloc_3602_, 3, v_r_3344_);
lean_ctor_set(v_reuseFailAlloc_3602_, 4, v_r_3344_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v___x_3598_);
lean_ctor_set(v___x_3581_, 0, v___x_3596_);
v___x_3600_ = v___x_3581_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3344_) == 0)
{
lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3633_; 
lean_inc(v_l_3343_);
lean_inc(v_v_3342_);
lean_inc(v_k_3341_);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; lean_object* v_unused_3635_; lean_object* v_unused_3636_; lean_object* v_unused_3637_; lean_object* v_unused_3638_; 
v_unused_3634_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3635_);
v_unused_3636_ = lean_ctor_get(v_l_3169_, 2);
lean_dec(v_unused_3636_);
v_unused_3637_ = lean_ctor_get(v_l_3169_, 1);
lean_dec(v_unused_3637_);
v_unused_3638_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3638_);
v___x_3610_ = v_l_3169_;
v_isShared_3611_ = v_isSharedCheck_3633_;
goto v_resetjp_3609_;
}
else
{
lean_dec(v_l_3169_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3633_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v_k_3612_; lean_object* v_v_3613_; lean_object* v_k_3614_; lean_object* v_v_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3629_; 
v_k_3612_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_k_3612_);
v_v_3613_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_v_3613_);
lean_dec_ref(v___x_3496_);
v_k_3614_ = lean_ctor_get(v_r_3344_, 1);
v_v_3615_ = lean_ctor_get(v_r_3344_, 2);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_r_3344_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; lean_object* v_unused_3631_; lean_object* v_unused_3632_; 
v_unused_3630_ = lean_ctor_get(v_r_3344_, 4);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_r_3344_, 3);
lean_dec(v_unused_3631_);
v_unused_3632_ = lean_ctor_get(v_r_3344_, 0);
lean_dec(v_unused_3632_);
v___x_3617_ = v_r_3344_;
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_v_3615_);
lean_inc(v_k_3614_);
lean_dec(v_r_3344_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3619_ = lean_unsigned_to_nat(3u);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 4, v_l_3343_);
lean_ctor_set(v___x_3617_, 3, v_l_3343_);
lean_ctor_set(v___x_3617_, 2, v_v_3342_);
lean_ctor_set(v___x_3617_, 1, v_k_3341_);
lean_ctor_set(v___x_3617_, 0, v___x_3350_);
v___x_3621_ = v___x_3617_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3628_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3628_, 4, v_l_3343_);
v___x_3621_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_l_3343_);
lean_ctor_set(v___x_3494_, 3, v_l_3343_);
lean_ctor_set(v___x_3494_, 2, v_v_3613_);
lean_ctor_set(v___x_3494_, 1, v_k_3612_);
lean_ctor_set(v___x_3494_, 0, v___x_3350_);
v___x_3623_ = v___x_3494_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_k_3612_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_v_3613_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_l_3343_);
lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_l_3343_);
v___x_3623_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 4, v___x_3623_);
lean_ctor_set(v___x_3610_, 3, v___x_3621_);
lean_ctor_set(v___x_3610_, 2, v_v_3615_);
lean_ctor_set(v___x_3610_, 1, v_k_3614_);
lean_ctor_set(v___x_3610_, 0, v___x_3619_);
v___x_3625_ = v___x_3610_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
}
else
{
lean_object* v_k_3639_; lean_object* v_v_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v_k_3639_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_k_3639_);
v_v_3640_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_v_3640_);
lean_dec_ref(v___x_3496_);
v___x_3641_ = lean_unsigned_to_nat(2u);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_r_3344_);
lean_ctor_set(v___x_3494_, 3, v_l_3169_);
lean_ctor_set(v___x_3494_, 2, v_v_3640_);
lean_ctor_set(v___x_3494_, 1, v_k_3639_);
lean_ctor_set(v___x_3494_, 0, v___x_3641_);
v___x_3643_ = v___x_3494_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3639_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3640_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_r_3344_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
}
}
else
{
return v_l_3169_;
}
}
else
{
return v_r_3170_;
}
}
}
else
{
lean_object* v_impl_3651_; lean_object* v___x_3652_; 
v_impl_3651_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3165_, v_l_3169_);
v___x_3652_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3651_) == 0)
{
if (lean_obj_tag(v_r_3170_) == 0)
{
lean_object* v_size_3653_; lean_object* v_size_3654_; lean_object* v_k_3655_; lean_object* v_v_3656_; lean_object* v_l_3657_; lean_object* v_r_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_size_3653_ = lean_ctor_get(v_impl_3651_, 0);
v_size_3654_ = lean_ctor_get(v_r_3170_, 0);
v_k_3655_ = lean_ctor_get(v_r_3170_, 1);
v_v_3656_ = lean_ctor_get(v_r_3170_, 2);
v_l_3657_ = lean_ctor_get(v_r_3170_, 3);
lean_inc(v_l_3657_);
v_r_3658_ = lean_ctor_get(v_r_3170_, 4);
v___x_3659_ = lean_unsigned_to_nat(3u);
v___x_3660_ = lean_nat_mul(v___x_3659_, v_size_3653_);
v___x_3661_ = lean_nat_dec_lt(v___x_3660_, v_size_3654_);
lean_dec(v___x_3660_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_dec(v_l_3657_);
v___x_3662_ = lean_nat_add(v___x_3652_, v_size_3653_);
v___x_3663_ = lean_nat_add(v___x_3662_, v_size_3654_);
lean_dec(v___x_3662_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 3, v_impl_3651_);
lean_ctor_set(v___x_3172_, 0, v___x_3663_);
v___x_3665_ = v___x_3172_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_impl_3651_);
lean_ctor_set(v_reuseFailAlloc_3666_, 4, v_r_3170_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
else
{
lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3730_; 
lean_inc(v_r_3658_);
lean_inc(v_v_3656_);
lean_inc(v_k_3655_);
lean_inc(v_size_3654_);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; 
v_unused_3731_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3170_, 2);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_r_3170_, 1);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3735_);
v___x_3668_ = v_r_3170_;
v_isShared_3669_ = v_isSharedCheck_3730_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v_r_3170_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3730_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v_size_3670_; lean_object* v_k_3671_; lean_object* v_v_3672_; lean_object* v_l_3673_; lean_object* v_r_3674_; lean_object* v_size_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v_size_3670_ = lean_ctor_get(v_l_3657_, 0);
v_k_3671_ = lean_ctor_get(v_l_3657_, 1);
v_v_3672_ = lean_ctor_get(v_l_3657_, 2);
v_l_3673_ = lean_ctor_get(v_l_3657_, 3);
v_r_3674_ = lean_ctor_get(v_l_3657_, 4);
v_size_3675_ = lean_ctor_get(v_r_3658_, 0);
v___x_3676_ = lean_unsigned_to_nat(2u);
v___x_3677_ = lean_nat_mul(v___x_3676_, v_size_3675_);
v___x_3678_ = lean_nat_dec_lt(v_size_3670_, v___x_3677_);
lean_dec(v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3706_; 
lean_inc(v_r_3674_);
lean_inc(v_l_3673_);
lean_inc(v_v_3672_);
lean_inc(v_k_3671_);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_l_3657_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; 
v_unused_3707_ = lean_ctor_get(v_l_3657_, 4);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_l_3657_, 3);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_l_3657_, 2);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_l_3657_, 1);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_l_3657_, 0);
lean_dec(v_unused_3711_);
v___x_3680_ = v_l_3657_;
v_isShared_3681_ = v_isSharedCheck_3706_;
goto v_resetjp_3679_;
}
else
{
lean_dec(v_l_3657_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3706_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3696_; 
v___x_3682_ = lean_nat_add(v___x_3652_, v_size_3653_);
v___x_3683_ = lean_nat_add(v___x_3682_, v_size_3654_);
lean_dec(v_size_3654_);
if (lean_obj_tag(v_l_3673_) == 0)
{
lean_object* v_size_3704_; 
v_size_3704_ = lean_ctor_get(v_l_3673_, 0);
lean_inc(v_size_3704_);
v___y_3696_ = v_size_3704_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_unsigned_to_nat(0u);
v___y_3696_ = v___x_3705_;
goto v___jp_3695_;
}
v___jp_3684_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_nat_add(v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec(v___y_3686_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 4, v_r_3658_);
lean_ctor_set(v___x_3680_, 3, v_r_3674_);
lean_ctor_set(v___x_3680_, 2, v_v_3656_);
lean_ctor_set(v___x_3680_, 1, v_k_3655_);
lean_ctor_set(v___x_3680_, 0, v___x_3688_);
v___x_3690_ = v___x_3680_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_k_3655_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_v_3656_);
lean_ctor_set(v_reuseFailAlloc_3694_, 3, v_r_3674_);
lean_ctor_set(v_reuseFailAlloc_3694_, 4, v_r_3658_);
v___x_3690_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3692_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v___x_3690_);
lean_ctor_set(v___x_3668_, 3, v___y_3685_);
lean_ctor_set(v___x_3668_, 2, v_v_3672_);
lean_ctor_set(v___x_3668_, 1, v_k_3671_);
lean_ctor_set(v___x_3668_, 0, v___x_3683_);
v___x_3692_ = v___x_3668_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_k_3671_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v_v_3672_);
lean_ctor_set(v_reuseFailAlloc_3693_, 3, v___y_3685_);
lean_ctor_set(v_reuseFailAlloc_3693_, 4, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
v___jp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3699_; 
v___x_3697_ = lean_nat_add(v___x_3682_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec(v___x_3682_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_l_3673_);
lean_ctor_set(v___x_3172_, 3, v_impl_3651_);
lean_ctor_set(v___x_3172_, 0, v___x_3697_);
v___x_3699_ = v___x_3172_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3703_, 3, v_impl_3651_);
lean_ctor_set(v_reuseFailAlloc_3703_, 4, v_l_3673_);
v___x_3699_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_nat_add(v___x_3652_, v_size_3675_);
if (lean_obj_tag(v_r_3674_) == 0)
{
lean_object* v_size_3701_; 
v_size_3701_ = lean_ctor_get(v_r_3674_, 0);
lean_inc(v_size_3701_);
v___y_3685_ = v___x_3699_;
v___y_3686_ = v___x_3700_;
v___y_3687_ = v_size_3701_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_unsigned_to_nat(0u);
v___y_3685_ = v___x_3699_;
v___y_3686_ = v___x_3700_;
v___y_3687_ = v___x_3702_;
goto v___jp_3684_;
}
}
}
}
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3716_; 
lean_del_object(v___x_3172_);
v___x_3712_ = lean_nat_add(v___x_3652_, v_size_3653_);
v___x_3713_ = lean_nat_add(v___x_3712_, v_size_3654_);
lean_dec(v_size_3654_);
v___x_3714_ = lean_nat_add(v___x_3712_, v_size_3670_);
lean_dec(v___x_3712_);
lean_inc_ref(v_impl_3651_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 4, v_l_3657_);
lean_ctor_set(v___x_3668_, 3, v_impl_3651_);
lean_ctor_set(v___x_3668_, 2, v_v_3168_);
lean_ctor_set(v___x_3668_, 1, v_k_3167_);
lean_ctor_set(v___x_3668_, 0, v___x_3714_);
v___x_3716_ = v___x_3668_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_impl_3651_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_l_3657_);
v___x_3716_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
v_isSharedCheck_3723_ = !lean_is_exclusive(v_impl_3651_);
if (v_isSharedCheck_3723_ == 0)
{
lean_object* v_unused_3724_; lean_object* v_unused_3725_; lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; 
v_unused_3724_ = lean_ctor_get(v_impl_3651_, 4);
lean_dec(v_unused_3724_);
v_unused_3725_ = lean_ctor_get(v_impl_3651_, 3);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_impl_3651_, 2);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_impl_3651_, 1);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_impl_3651_, 0);
lean_dec(v_unused_3728_);
v___x_3718_ = v_impl_3651_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_dec(v_impl_3651_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 4, v_r_3658_);
lean_ctor_set(v___x_3718_, 3, v___x_3716_);
lean_ctor_set(v___x_3718_, 2, v_v_3656_);
lean_ctor_set(v___x_3718_, 1, v_k_3655_);
lean_ctor_set(v___x_3718_, 0, v___x_3713_);
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_k_3655_);
lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_v_3656_);
lean_ctor_set(v_reuseFailAlloc_3722_, 3, v___x_3716_);
lean_ctor_set(v_reuseFailAlloc_3722_, 4, v_r_3658_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v_size_3736_ = lean_ctor_get(v_impl_3651_, 0);
v___x_3737_ = lean_nat_add(v___x_3652_, v_size_3736_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 3, v_impl_3651_);
lean_ctor_set(v___x_3172_, 0, v___x_3737_);
v___x_3739_ = v___x_3172_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v_impl_3651_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v_r_3170_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
else
{
if (lean_obj_tag(v_r_3170_) == 0)
{
lean_object* v_l_3741_; 
v_l_3741_ = lean_ctor_get(v_r_3170_, 3);
lean_inc(v_l_3741_);
if (lean_obj_tag(v_l_3741_) == 0)
{
lean_object* v_r_3742_; 
v_r_3742_ = lean_ctor_get(v_r_3170_, 4);
lean_inc(v_r_3742_);
if (lean_obj_tag(v_r_3742_) == 0)
{
lean_object* v_size_3743_; lean_object* v_k_3744_; lean_object* v_v_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3758_; 
v_size_3743_ = lean_ctor_get(v_r_3170_, 0);
v_k_3744_ = lean_ctor_get(v_r_3170_, 1);
v_v_3745_ = lean_ctor_get(v_r_3170_, 2);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3759_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3760_);
v___x_3747_ = v_r_3170_;
v_isShared_3748_ = v_isSharedCheck_3758_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_v_3745_);
lean_inc(v_k_3744_);
lean_inc(v_size_3743_);
lean_dec(v_r_3170_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3758_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_size_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
v_size_3749_ = lean_ctor_get(v_l_3741_, 0);
v___x_3750_ = lean_nat_add(v___x_3652_, v_size_3743_);
lean_dec(v_size_3743_);
v___x_3751_ = lean_nat_add(v___x_3652_, v_size_3749_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 4, v_l_3741_);
lean_ctor_set(v___x_3747_, 3, v_impl_3651_);
lean_ctor_set(v___x_3747_, 2, v_v_3168_);
lean_ctor_set(v___x_3747_, 1, v_k_3167_);
lean_ctor_set(v___x_3747_, 0, v___x_3751_);
v___x_3753_ = v___x_3747_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_impl_3651_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v_l_3741_);
v___x_3753_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_r_3742_);
lean_ctor_set(v___x_3172_, 3, v___x_3753_);
lean_ctor_set(v___x_3172_, 2, v_v_3745_);
lean_ctor_set(v___x_3172_, 1, v_k_3744_);
lean_ctor_set(v___x_3172_, 0, v___x_3750_);
v___x_3755_ = v___x_3172_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_r_3742_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_k_3761_; lean_object* v_v_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3785_; 
v_k_3761_ = lean_ctor_get(v_r_3170_, 1);
v_v_3762_ = lean_ctor_get(v_r_3170_, 2);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; lean_object* v_unused_3787_; lean_object* v_unused_3788_; 
v_unused_3786_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3788_);
v___x_3764_ = v_r_3170_;
v_isShared_3765_ = v_isSharedCheck_3785_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_v_3762_);
lean_inc(v_k_3761_);
lean_dec(v_r_3170_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3785_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3781_; 
v_k_3766_ = lean_ctor_get(v_l_3741_, 1);
v_v_3767_ = lean_ctor_get(v_l_3741_, 2);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_l_3741_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; lean_object* v_unused_3783_; lean_object* v_unused_3784_; 
v_unused_3782_ = lean_ctor_get(v_l_3741_, 4);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_l_3741_, 3);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_l_3741_, 0);
lean_dec(v_unused_3784_);
v___x_3769_ = v_l_3741_;
v_isShared_3770_ = v_isSharedCheck_3781_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
lean_dec(v_l_3741_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3781_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = lean_unsigned_to_nat(3u);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 4, v_r_3742_);
lean_ctor_set(v___x_3769_, 3, v_r_3742_);
lean_ctor_set(v___x_3769_, 2, v_v_3168_);
lean_ctor_set(v___x_3769_, 1, v_k_3167_);
lean_ctor_set(v___x_3769_, 0, v___x_3652_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_r_3742_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_r_3742_);
v___x_3773_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 3, v_r_3742_);
lean_ctor_set(v___x_3764_, 0, v___x_3652_);
v___x_3775_ = v___x_3764_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3779_, 3, v_r_3742_);
lean_ctor_set(v_reuseFailAlloc_3779_, 4, v_r_3742_);
v___x_3775_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3775_);
lean_ctor_set(v___x_3172_, 3, v___x_3773_);
lean_ctor_set(v___x_3172_, 2, v_v_3767_);
lean_ctor_set(v___x_3172_, 1, v_k_3766_);
lean_ctor_set(v___x_3172_, 0, v___x_3771_);
v___x_3777_ = v___x_3172_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3778_, 3, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3778_, 4, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3789_; 
v_r_3789_ = lean_ctor_get(v_r_3170_, 4);
lean_inc(v_r_3789_);
if (lean_obj_tag(v_r_3789_) == 0)
{
lean_object* v_k_3790_; lean_object* v_v_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3802_; 
v_k_3790_ = lean_ctor_get(v_r_3170_, 1);
v_v_3791_ = lean_ctor_get(v_r_3170_, 2);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; lean_object* v_unused_3804_; lean_object* v_unused_3805_; 
v_unused_3803_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_r_3170_, 0);
lean_dec(v_unused_3805_);
v___x_3793_ = v_r_3170_;
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_v_3791_);
lean_inc(v_k_3790_);
lean_dec(v_r_3170_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = lean_unsigned_to_nat(3u);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 4, v_l_3741_);
lean_ctor_set(v___x_3793_, 2, v_v_3168_);
lean_ctor_set(v___x_3793_, 1, v_k_3167_);
lean_ctor_set(v___x_3793_, 0, v___x_3652_);
v___x_3797_ = v___x_3793_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3801_, 3, v_l_3741_);
lean_ctor_set(v_reuseFailAlloc_3801_, 4, v_l_3741_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3799_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v_r_3789_);
lean_ctor_set(v___x_3172_, 3, v___x_3797_);
lean_ctor_set(v___x_3172_, 2, v_v_3791_);
lean_ctor_set(v___x_3172_, 1, v_k_3790_);
lean_ctor_set(v___x_3172_, 0, v___x_3795_);
v___x_3799_ = v___x_3172_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_k_3790_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_v_3791_);
lean_ctor_set(v_reuseFailAlloc_3800_, 3, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3800_, 4, v_r_3789_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_size_3806_; lean_object* v_k_3807_; lean_object* v_v_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3819_; 
v_size_3806_ = lean_ctor_get(v_r_3170_, 0);
v_k_3807_ = lean_ctor_get(v_r_3170_, 1);
v_v_3808_ = lean_ctor_get(v_r_3170_, 2);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_r_3170_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3820_ = lean_ctor_get(v_r_3170_, 4);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_r_3170_, 3);
lean_dec(v_unused_3821_);
v___x_3810_ = v_r_3170_;
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_v_3808_);
lean_inc(v_k_3807_);
lean_inc(v_size_3806_);
lean_dec(v_r_3170_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 3, v_r_3789_);
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_size_3806_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_r_3789_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_r_3789_);
v___x_3813_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3814_ = lean_unsigned_to_nat(2u);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3813_);
lean_ctor_set(v___x_3172_, 3, v_r_3789_);
lean_ctor_set(v___x_3172_, 0, v___x_3814_);
v___x_3816_ = v___x_3172_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3817_, 3, v_r_3789_);
lean_ctor_set(v_reuseFailAlloc_3817_, 4, v___x_3813_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
}
else
{
lean_object* v___x_3823_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 3, v_r_3170_);
lean_ctor_set(v___x_3172_, 0, v___x_3652_);
v___x_3823_ = v___x_3172_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_k_3167_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_v_3168_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_r_3170_);
lean_ctor_set(v_reuseFailAlloc_3824_, 4, v_r_3170_);
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
return v_t_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3827_, lean_object* v_t_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3827_, v_t_3828_);
lean_dec(v_k_3827_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3830_, lean_object* v_j_3831_){
_start:
{
lean_object* v_vars_3832_; lean_object* v_jps_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
v_vars_3832_ = lean_ctor_get(v_ctx_3830_, 0);
v_jps_3833_ = lean_ctor_get(v_ctx_3830_, 1);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_ctx_3830_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v_ctx_3830_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_jps_3833_);
lean_inc(v_vars_3832_);
lean_dec(v_ctx_3830_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3831_, v_jps_3833_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 1, v___x_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_vars_3832_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3842_, lean_object* v_j_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3842_, v_j_3843_);
lean_dec(v_j_3843_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3845_, lean_object* v_k_3846_, lean_object* v_t_3847_, lean_object* v_h_3848_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3846_, v_t_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3850_, lean_object* v_k_3851_, lean_object* v_t_3852_, lean_object* v_h_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3850_, v_k_3851_, v_t_3852_, v_h_3853_);
lean_dec(v_k_3851_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3855_, lean_object* v_x_3856_){
_start:
{
lean_object* v_vars_3857_; lean_object* v___x_3858_; 
v_vars_3857_ = lean_ctor_get(v_ctx_3855_, 0);
v___x_3858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3857_, v_x_3856_);
if (lean_obj_tag(v___x_3858_) == 1)
{
lean_object* v_val_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3867_; 
v_val_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3867_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_val_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3867_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_a_3863_; lean_object* v___x_3865_; 
v_a_3863_ = lean_ctor_get(v_val_3859_, 0);
lean_inc(v_a_3863_);
lean_dec(v_val_3859_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v_a_3863_);
v___x_3865_ = v___x_3861_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
else
{
lean_object* v___x_3868_; 
lean_dec(v___x_3858_);
v___x_3868_ = lean_box(0);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3869_, lean_object* v_x_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_IR_LocalContext_getType(v_ctx_3869_, v_x_3870_);
lean_dec(v_x_3870_);
lean_dec_ref(v_ctx_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3872_, lean_object* v_x_3873_){
_start:
{
lean_object* v_vars_3874_; lean_object* v___x_3875_; 
v_vars_3874_ = lean_ctor_get(v_ctx_3872_, 0);
v___x_3875_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3874_, v_x_3873_);
if (lean_obj_tag(v___x_3875_) == 1)
{
lean_object* v_val_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3885_; 
v_val_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3885_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_val_3876_);
lean_dec(v___x_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3885_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
if (lean_obj_tag(v_val_3876_) == 1)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; 
v_a_3880_ = lean_ctor_get(v_val_3876_, 1);
lean_inc(v_a_3880_);
lean_dec_ref_known(v_val_3876_, 2);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v_a_3880_);
v___x_3882_ = v___x_3878_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
else
{
lean_object* v___x_3884_; 
lean_del_object(v___x_3878_);
lean_dec(v_val_3876_);
v___x_3884_ = lean_box(0);
return v___x_3884_;
}
}
}
else
{
lean_object* v___x_3886_; 
lean_dec(v___x_3875_);
v___x_3886_ = lean_box(0);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_IR_LocalContext_getValue(v_ctx_3887_, v_x_3888_);
lean_dec(v_x_3888_);
lean_dec_ref(v_ctx_3887_);
return v_res_3889_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3890_, lean_object* v_v_u2081_3891_, lean_object* v_v_u2082_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_00_u03c1_3890_, v_v_u2081_3891_);
if (lean_obj_tag(v___x_3893_) == 0)
{
uint8_t v___x_3894_; 
v___x_3894_ = lean_nat_dec_eq(v_v_u2081_3891_, v_v_u2082_3892_);
return v___x_3894_;
}
else
{
lean_object* v_val_3895_; uint8_t v___x_3896_; 
v_val_3895_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3896_ = lean_nat_dec_eq(v_val_3895_, v_v_u2082_3892_);
lean_dec(v_val_3895_);
return v___x_3896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3897_, lean_object* v_v_u2081_3898_, lean_object* v_v_u2082_3899_){
_start:
{
uint8_t v_res_3900_; lean_object* v_r_3901_; 
v_res_3900_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3897_, v_v_u2081_3898_, v_v_u2082_3899_);
lean_dec(v_v_u2082_3899_);
lean_dec(v_v_u2081_3898_);
lean_dec(v_00_u03c1_3897_);
v_r_3901_ = lean_box(v_res_3900_);
return v_r_3901_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3904_, lean_object* v_x_3905_, lean_object* v_x_3906_){
_start:
{
if (lean_obj_tag(v_x_3905_) == 0)
{
if (lean_obj_tag(v_x_3906_) == 0)
{
lean_object* v_id_3907_; lean_object* v_id_3908_; uint8_t v___x_3909_; 
v_id_3907_ = lean_ctor_get(v_x_3905_, 0);
v_id_3908_ = lean_ctor_get(v_x_3906_, 0);
v___x_3909_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3904_, v_id_3907_, v_id_3908_);
return v___x_3909_;
}
else
{
uint8_t v___x_3910_; 
v___x_3910_ = 0;
return v___x_3910_;
}
}
else
{
if (lean_obj_tag(v_x_3906_) == 1)
{
uint8_t v___x_3911_; 
v___x_3911_ = 1;
return v___x_3911_;
}
else
{
uint8_t v___x_3912_; 
v___x_3912_ = 0;
return v___x_3912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_){
_start:
{
uint8_t v_res_3916_; lean_object* v_r_3917_; 
v_res_3916_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3913_, v_x_3914_, v_x_3915_);
lean_dec(v_x_3915_);
lean_dec(v_x_3914_);
lean_dec(v_00_u03c1_3913_);
v_r_3917_ = lean_box(v_res_3916_);
return v_r_3917_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3920_, lean_object* v_xs_3921_, lean_object* v_ys_3922_, lean_object* v_x_3923_){
_start:
{
lean_object* v_zero_3924_; uint8_t v_isZero_3925_; 
v_zero_3924_ = lean_unsigned_to_nat(0u);
v_isZero_3925_ = lean_nat_dec_eq(v_x_3923_, v_zero_3924_);
if (v_isZero_3925_ == 1)
{
lean_dec(v_x_3923_);
return v_isZero_3925_;
}
else
{
lean_object* v_one_3926_; lean_object* v_n_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; 
v_one_3926_ = lean_unsigned_to_nat(1u);
v_n_3927_ = lean_nat_sub(v_x_3923_, v_one_3926_);
lean_dec(v_x_3923_);
v___x_3928_ = lean_array_fget_borrowed(v_xs_3921_, v_n_3927_);
v___x_3929_ = lean_array_fget_borrowed(v_ys_3922_, v_n_3927_);
v___x_3930_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3920_, v___x_3928_, v___x_3929_);
if (v___x_3930_ == 0)
{
lean_dec(v_n_3927_);
return v___x_3930_;
}
else
{
v_x_3923_ = v_n_3927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3932_, lean_object* v_xs_3933_, lean_object* v_ys_3934_, lean_object* v_x_3935_){
_start:
{
uint8_t v_res_3936_; lean_object* v_r_3937_; 
v_res_3936_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3932_, v_xs_3933_, v_ys_3934_, v_x_3935_);
lean_dec_ref(v_ys_3934_);
lean_dec_ref(v_xs_3933_);
lean_dec(v_00_u03c1_3932_);
v_r_3937_ = lean_box(v_res_3936_);
return v_r_3937_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3938_, lean_object* v_args_u2081_3939_, lean_object* v_args_u2082_3940_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = lean_array_get_size(v_args_u2081_3939_);
v___x_3942_ = lean_array_get_size(v_args_u2082_3940_);
v___x_3943_ = lean_nat_dec_eq(v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
return v___x_3943_;
}
else
{
uint8_t v___x_3944_; 
v___x_3944_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3938_, v_args_u2081_3939_, v_args_u2082_3940_, v___x_3941_);
return v___x_3944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3945_, lean_object* v_args_u2081_3946_, lean_object* v_args_u2082_3947_){
_start:
{
uint8_t v_res_3948_; lean_object* v_r_3949_; 
v_res_3948_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3945_, v_args_u2081_3946_, v_args_u2082_3947_);
lean_dec_ref(v_args_u2082_3947_);
lean_dec_ref(v_args_u2081_3946_);
lean_dec(v_00_u03c1_3945_);
v_r_3949_ = lean_box(v_res_3948_);
return v_r_3949_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3950_, lean_object* v_xs_3951_, lean_object* v_ys_3952_, lean_object* v_hsz_3953_, lean_object* v_x_3954_, lean_object* v_x_3955_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3950_, v_xs_3951_, v_ys_3952_, v_x_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3957_, lean_object* v_xs_3958_, lean_object* v_ys_3959_, lean_object* v_hsz_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_){
_start:
{
uint8_t v_res_3963_; lean_object* v_r_3964_; 
v_res_3963_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3957_, v_xs_3958_, v_ys_3959_, v_hsz_3960_, v_x_3961_, v_x_3962_);
lean_dec_ref(v_ys_3959_);
lean_dec_ref(v_xs_3958_);
lean_dec(v_00_u03c1_3957_);
v_r_3964_ = lean_box(v_res_3963_);
return v_r_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3967_, lean_object* v_x_u2081_3968_, lean_object* v_x_u2082_3969_){
_start:
{
uint8_t v___x_3970_; 
v___x_3970_ = lean_nat_dec_eq(v_x_u2081_3968_, v_x_u2082_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3968_, v_x_u2082_3969_, v_00_u03c1_3967_);
return v___x_3971_;
}
else
{
lean_dec(v_x_u2082_3969_);
lean_dec(v_x_u2081_3968_);
return v_00_u03c1_3967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3972_, lean_object* v_p_u2081_3973_, lean_object* v_p_u2082_3974_){
_start:
{
lean_object* v_x_3975_; uint8_t v_borrow_3976_; lean_object* v_ty_3977_; lean_object* v_x_3978_; uint8_t v_borrow_3979_; lean_object* v_ty_3980_; uint8_t v___y_3982_; uint8_t v___x_3986_; 
v_x_3975_ = lean_ctor_get(v_p_u2081_3973_, 0);
lean_inc(v_x_3975_);
v_borrow_3976_ = lean_ctor_get_uint8(v_p_u2081_3973_, sizeof(void*)*2);
v_ty_3977_ = lean_ctor_get(v_p_u2081_3973_, 1);
lean_inc(v_ty_3977_);
lean_dec_ref(v_p_u2081_3973_);
v_x_3978_ = lean_ctor_get(v_p_u2082_3974_, 0);
lean_inc(v_x_3978_);
v_borrow_3979_ = lean_ctor_get_uint8(v_p_u2082_3974_, sizeof(void*)*2);
v_ty_3980_ = lean_ctor_get(v_p_u2082_3974_, 1);
lean_inc(v_ty_3980_);
lean_dec_ref(v_p_u2082_3974_);
v___x_3986_ = l_Lean_IR_instBEqIRType_beq(v_ty_3977_, v_ty_3980_);
lean_dec(v_ty_3980_);
lean_dec(v_ty_3977_);
if (v___x_3986_ == 0)
{
v___y_3982_ = v___x_3986_;
goto v___jp_3981_;
}
else
{
if (v_borrow_3979_ == 0)
{
if (v_borrow_3976_ == 0)
{
v___y_3982_ = v___x_3986_;
goto v___jp_3981_;
}
else
{
lean_object* v___x_3987_; 
lean_dec(v_x_3978_);
lean_dec(v_x_3975_);
lean_dec(v_00_u03c1_3972_);
v___x_3987_ = lean_box(0);
return v___x_3987_;
}
}
else
{
v___y_3982_ = v_borrow_3976_;
goto v___jp_3981_;
}
}
v___jp_3981_:
{
if (v___y_3982_ == 0)
{
lean_object* v___x_3983_; 
lean_dec(v_x_3978_);
lean_dec(v_x_3975_);
lean_dec(v_00_u03c1_3972_);
v___x_3983_ = lean_box(0);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = l_Lean_IR_addVarRename(v_00_u03c1_3972_, v_x_3975_, v_x_3978_);
v___x_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3988_, lean_object* v_ps_u2081_3989_, lean_object* v_ps_u2082_3990_, lean_object* v_a_3991_, lean_object* v_b_3992_){
_start:
{
uint8_t v___x_3993_; 
v___x_3993_ = lean_nat_dec_lt(v_a_3991_, v_upperBound_3988_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; 
lean_dec(v_a_3991_);
v___x_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3994_, 0, v_b_3992_);
return v___x_3994_;
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_3996_ = lean_array_get_borrowed(v___x_3995_, v_ps_u2081_3989_, v_a_3991_);
v___x_3997_ = lean_array_get_borrowed(v___x_3995_, v_ps_u2082_3990_, v_a_3991_);
lean_inc(v___x_3997_);
lean_inc(v___x_3996_);
v___x_3998_ = l_Lean_IR_addParamRename(v_b_3992_, v___x_3996_, v___x_3997_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_dec(v_a_3991_);
return v___x_3998_;
}
else
{
lean_object* v_val_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_val_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_val_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = lean_unsigned_to_nat(1u);
v___x_4001_ = lean_nat_add(v_a_3991_, v___x_4000_);
lean_dec(v_a_3991_);
v_a_3991_ = v___x_4001_;
v_b_3992_ = v_val_3999_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_4003_, lean_object* v_ps_u2081_4004_, lean_object* v_ps_u2082_4005_, lean_object* v_a_4006_, lean_object* v_b_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_4003_, v_ps_u2081_4004_, v_ps_u2082_4005_, v_a_4006_, v_b_4007_);
lean_dec_ref(v_ps_u2082_4005_);
lean_dec_ref(v_ps_u2081_4004_);
lean_dec(v_upperBound_4003_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_4009_, lean_object* v_ps_u2081_4010_, lean_object* v_ps_u2082_4011_){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4012_ = lean_array_get_size(v_ps_u2081_4010_);
v___x_4013_ = lean_array_get_size(v_ps_u2082_4011_);
v___x_4014_ = lean_nat_dec_eq(v___x_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec(v_00_u03c1_4009_);
v___x_4015_ = lean_box(0);
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_unsigned_to_nat(0u);
v___x_4017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_4012_, v_ps_u2081_4010_, v_ps_u2082_4011_, v___x_4016_, v_00_u03c1_4009_);
return v___x_4017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* v_00_u03c1_4018_, lean_object* v_ps_u2081_4019_, lean_object* v_ps_u2082_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_IR_addParamsRename(v_00_u03c1_4018_, v_ps_u2081_4019_, v_ps_u2082_4020_);
lean_dec_ref(v_ps_u2082_4020_);
lean_dec_ref(v_ps_u2081_4019_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object* v_upperBound_4022_, lean_object* v_ps_u2081_4023_, lean_object* v_ps_u2082_4024_, lean_object* v_inst_4025_, lean_object* v_R_4026_, lean_object* v_a_4027_, lean_object* v_b_4028_, lean_object* v_c_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_4022_, v_ps_u2081_4023_, v_ps_u2082_4024_, v_a_4027_, v_b_4028_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object* v_upperBound_4031_, lean_object* v_ps_u2081_4032_, lean_object* v_ps_u2082_4033_, lean_object* v_inst_4034_, lean_object* v_R_4035_, lean_object* v_a_4036_, lean_object* v_b_4037_, lean_object* v_c_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(v_upperBound_4031_, v_ps_u2081_4032_, v_ps_u2082_4033_, v_inst_4034_, v_R_4035_, v_a_4036_, v_b_4037_, v_c_4038_);
lean_dec_ref(v_ps_u2082_4033_);
lean_dec_ref(v_ps_u2081_4032_);
lean_dec(v_upperBound_4031_);
return v_res_4039_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* v_x_4040_, lean_object* v_x_4041_, lean_object* v_x_4042_){
_start:
{
lean_object* v_00_u03c1_4044_; lean_object* v_tgt_u2081_4045_; lean_object* v_b_u2081_4046_; lean_object* v_n_u2081_4047_; lean_object* v_x_u2081_4048_; lean_object* v_tgt_u2082_4049_; lean_object* v_b_u2082_4050_; lean_object* v_n_u2082_4051_; lean_object* v_x_u2082_4052_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; uint8_t v___y_4063_; lean_object* v_00_u03c1_4067_; lean_object* v_tgt_u2081_4068_; lean_object* v_b_u2081_4069_; lean_object* v_ty_u2081_4070_; lean_object* v_x_u2081_4071_; lean_object* v_tgt_u2082_4072_; lean_object* v_b_u2082_4073_; lean_object* v_ty_u2082_4074_; lean_object* v_x_u2082_4075_; lean_object* v_00_u03c1_4079_; lean_object* v_tgt_u2081_4080_; lean_object* v_b_u2081_4081_; uint64_t v_v_u2081_4082_; lean_object* v_tgt_u2082_4083_; lean_object* v_b_u2082_4084_; uint64_t v_v_u2082_4085_; uint8_t v___y_4090_; lean_object* v___y_4091_; uint8_t v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; uint8_t v___y_4098_; uint8_t v___y_4099_; uint8_t v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; uint8_t v___y_4105_; lean_object* v_00_u03c1_4107_; lean_object* v_x_u2081_4108_; lean_object* v_n_u2081_4109_; uint8_t v_c_u2081_4110_; uint8_t v_p_u2081_4111_; lean_object* v_b_u2081_4112_; lean_object* v_x_u2082_4113_; lean_object* v_n_u2082_4114_; uint8_t v_c_u2082_4115_; uint8_t v_p_u2082_4116_; lean_object* v_b_u2082_4117_; 
switch(lean_obj_tag(v_x_4041_))
{
case 0:
{
if (lean_obj_tag(v_x_4042_) == 0)
{
lean_object* v_tgt_4120_; lean_object* v_b_4121_; lean_object* v_i_4122_; lean_object* v_ys_4123_; lean_object* v_tgt_4124_; lean_object* v_b_4125_; lean_object* v_i_4126_; lean_object* v_ys_4127_; uint8_t v___y_4129_; uint8_t v___x_4132_; 
v_tgt_4120_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4120_);
v_b_4121_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4121_);
v_i_4122_ = lean_ctor_get(v_x_4041_, 2);
lean_inc_ref(v_i_4122_);
v_ys_4123_ = lean_ctor_get(v_x_4041_, 3);
lean_inc_ref(v_ys_4123_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4124_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4124_);
v_b_4125_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4125_);
v_i_4126_ = lean_ctor_get(v_x_4042_, 2);
lean_inc_ref(v_i_4126_);
v_ys_4127_ = lean_ctor_get(v_x_4042_, 3);
lean_inc_ref(v_ys_4127_);
lean_dec_ref_known(v_x_4042_, 4);
v___x_4132_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_4122_, v_i_4126_);
lean_dec_ref(v_i_4126_);
lean_dec_ref(v_i_4122_);
if (v___x_4132_ == 0)
{
lean_dec_ref(v_ys_4127_);
lean_dec_ref(v_ys_4123_);
v___y_4129_ = v___x_4132_;
goto v___jp_4128_;
}
else
{
uint8_t v___x_4133_; 
v___x_4133_ = l_Lean_IR_args_alphaEqv(v_x_4040_, v_ys_4123_, v_ys_4127_);
lean_dec_ref(v_ys_4127_);
lean_dec_ref(v_ys_4123_);
v___y_4129_ = v___x_4133_;
goto v___jp_4128_;
}
v___jp_4128_:
{
if (v___y_4129_ == 0)
{
lean_dec(v_b_4125_);
lean_dec(v_tgt_4124_);
lean_dec(v_b_4121_);
lean_dec(v_tgt_4120_);
lean_dec(v_x_4040_);
return v___y_4129_;
}
else
{
lean_object* v___x_4130_; 
v___x_4130_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4120_, v_tgt_4124_);
v_x_4040_ = v___x_4130_;
v_x_4041_ = v_b_4121_;
v_x_4042_ = v_b_4125_;
goto _start;
}
}
}
else
{
uint8_t v___x_4134_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4134_ = 0;
return v___x_4134_;
}
}
case 1:
{
if (lean_obj_tag(v_x_4042_) == 1)
{
lean_object* v_tgt_4135_; lean_object* v_b_4136_; lean_object* v_n_4137_; lean_object* v_x_4138_; lean_object* v_tgt_4139_; lean_object* v_b_4140_; lean_object* v_n_4141_; lean_object* v_x_4142_; 
v_tgt_4135_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4135_);
v_b_4136_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4136_);
v_n_4137_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_n_4137_);
v_x_4138_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_x_4138_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4139_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4139_);
v_b_4140_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4140_);
v_n_4141_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_n_4141_);
v_x_4142_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_x_4142_);
lean_dec_ref_known(v_x_4042_, 4);
v_00_u03c1_4044_ = v_x_4040_;
v_tgt_u2081_4045_ = v_tgt_4135_;
v_b_u2081_4046_ = v_b_4136_;
v_n_u2081_4047_ = v_n_4137_;
v_x_u2081_4048_ = v_x_4138_;
v_tgt_u2082_4049_ = v_tgt_4139_;
v_b_u2082_4050_ = v_b_4140_;
v_n_u2082_4051_ = v_n_4141_;
v_x_u2082_4052_ = v_x_4142_;
goto v___jp_4043_;
}
else
{
uint8_t v___x_4143_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4143_ = 0;
return v___x_4143_;
}
}
case 2:
{
if (lean_obj_tag(v_x_4042_) == 2)
{
lean_object* v_tgt_4144_; lean_object* v_b_4145_; lean_object* v_x_4146_; lean_object* v_i_4147_; uint8_t v_updtHeader_4148_; lean_object* v_ys_4149_; lean_object* v_tgt_4150_; lean_object* v_b_4151_; lean_object* v_x_4152_; lean_object* v_i_4153_; uint8_t v_updtHeader_4154_; lean_object* v_ys_4155_; uint8_t v___y_4161_; uint8_t v___x_4162_; 
v_tgt_4144_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4144_);
v_b_4145_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4145_);
v_x_4146_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_x_4146_);
v_i_4147_ = lean_ctor_get(v_x_4041_, 3);
lean_inc_ref(v_i_4147_);
v_updtHeader_4148_ = lean_ctor_get_uint8(v_x_4041_, sizeof(void*)*5);
v_ys_4149_ = lean_ctor_get(v_x_4041_, 4);
lean_inc_ref(v_ys_4149_);
lean_dec_ref_known(v_x_4041_, 5);
v_tgt_4150_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4150_);
v_b_4151_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4151_);
v_x_4152_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_x_4152_);
v_i_4153_ = lean_ctor_get(v_x_4042_, 3);
lean_inc_ref(v_i_4153_);
v_updtHeader_4154_ = lean_ctor_get_uint8(v_x_4042_, sizeof(void*)*5);
v_ys_4155_ = lean_ctor_get(v_x_4042_, 4);
lean_inc_ref(v_ys_4155_);
lean_dec_ref_known(v_x_4042_, 5);
v___x_4162_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4146_, v_x_4152_);
lean_dec(v_x_4152_);
lean_dec(v_x_4146_);
if (v___x_4162_ == 0)
{
lean_dec_ref(v_i_4153_);
lean_dec_ref(v_i_4147_);
v___y_4161_ = v___x_4162_;
goto v___jp_4160_;
}
else
{
uint8_t v___x_4163_; 
v___x_4163_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_4147_, v_i_4153_);
lean_dec_ref(v_i_4153_);
lean_dec_ref(v_i_4147_);
v___y_4161_ = v___x_4163_;
goto v___jp_4160_;
}
v___jp_4156_:
{
uint8_t v___x_4157_; 
v___x_4157_ = l_Lean_IR_args_alphaEqv(v_x_4040_, v_ys_4149_, v_ys_4155_);
lean_dec_ref(v_ys_4155_);
lean_dec_ref(v_ys_4149_);
if (v___x_4157_ == 0)
{
lean_dec(v_b_4151_);
lean_dec(v_tgt_4150_);
lean_dec(v_b_4145_);
lean_dec(v_tgt_4144_);
lean_dec(v_x_4040_);
return v___x_4157_;
}
else
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4144_, v_tgt_4150_);
v_x_4040_ = v___x_4158_;
v_x_4041_ = v_b_4145_;
v_x_4042_ = v_b_4151_;
goto _start;
}
}
v___jp_4160_:
{
if (v___y_4161_ == 0)
{
lean_dec_ref(v_ys_4155_);
lean_dec(v_b_4151_);
lean_dec(v_tgt_4150_);
lean_dec_ref(v_ys_4149_);
lean_dec(v_b_4145_);
lean_dec(v_tgt_4144_);
lean_dec(v_x_4040_);
return v___y_4161_;
}
else
{
if (v_updtHeader_4154_ == 0)
{
if (v_updtHeader_4148_ == 0)
{
goto v___jp_4156_;
}
else
{
lean_dec_ref(v_ys_4155_);
lean_dec(v_b_4151_);
lean_dec(v_tgt_4150_);
lean_dec_ref(v_ys_4149_);
lean_dec(v_b_4145_);
lean_dec(v_tgt_4144_);
lean_dec(v_x_4040_);
return v_updtHeader_4154_;
}
}
else
{
if (v_updtHeader_4148_ == 0)
{
lean_dec_ref(v_ys_4155_);
lean_dec(v_b_4151_);
lean_dec(v_tgt_4150_);
lean_dec_ref(v_ys_4149_);
lean_dec(v_b_4145_);
lean_dec(v_tgt_4144_);
lean_dec(v_x_4040_);
return v_updtHeader_4148_;
}
else
{
goto v___jp_4156_;
}
}
}
}
}
else
{
uint8_t v___x_4164_; 
lean_dec_ref_known(v_x_4041_, 5);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4164_ = 0;
return v___x_4164_;
}
}
case 3:
{
if (lean_obj_tag(v_x_4042_) == 3)
{
lean_object* v_tgt_4165_; lean_object* v_b_4166_; lean_object* v_i_4167_; lean_object* v_x_4168_; lean_object* v_tgt_4169_; lean_object* v_b_4170_; lean_object* v_i_4171_; lean_object* v_x_4172_; 
v_tgt_4165_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4165_);
v_b_4166_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4166_);
v_i_4167_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_i_4167_);
v_x_4168_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_x_4168_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4169_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4169_);
v_b_4170_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4170_);
v_i_4171_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_i_4171_);
v_x_4172_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_x_4172_);
lean_dec_ref_known(v_x_4042_, 4);
v_00_u03c1_4044_ = v_x_4040_;
v_tgt_u2081_4045_ = v_tgt_4165_;
v_b_u2081_4046_ = v_b_4166_;
v_n_u2081_4047_ = v_i_4167_;
v_x_u2081_4048_ = v_x_4168_;
v_tgt_u2082_4049_ = v_tgt_4169_;
v_b_u2082_4050_ = v_b_4170_;
v_n_u2082_4051_ = v_i_4171_;
v_x_u2082_4052_ = v_x_4172_;
goto v___jp_4043_;
}
else
{
uint8_t v___x_4173_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4173_ = 0;
return v___x_4173_;
}
}
case 4:
{
if (lean_obj_tag(v_x_4042_) == 4)
{
lean_object* v_tgt_4174_; lean_object* v_b_4175_; lean_object* v_i_4176_; lean_object* v_x_4177_; lean_object* v_tgt_4178_; lean_object* v_b_4179_; lean_object* v_i_4180_; lean_object* v_x_4181_; 
v_tgt_4174_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4174_);
v_b_4175_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4175_);
v_i_4176_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_i_4176_);
v_x_4177_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_x_4177_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4178_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4178_);
v_b_4179_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4179_);
v_i_4180_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_i_4180_);
v_x_4181_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_x_4181_);
lean_dec_ref_known(v_x_4042_, 4);
v_00_u03c1_4044_ = v_x_4040_;
v_tgt_u2081_4045_ = v_tgt_4174_;
v_b_u2081_4046_ = v_b_4175_;
v_n_u2081_4047_ = v_i_4176_;
v_x_u2081_4048_ = v_x_4177_;
v_tgt_u2082_4049_ = v_tgt_4178_;
v_b_u2082_4050_ = v_b_4179_;
v_n_u2082_4051_ = v_i_4180_;
v_x_u2082_4052_ = v_x_4181_;
goto v___jp_4043_;
}
else
{
uint8_t v___x_4182_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4182_ = 0;
return v___x_4182_;
}
}
case 5:
{
if (lean_obj_tag(v_x_4042_) == 5)
{
lean_object* v_tgt_4183_; lean_object* v_b_4184_; lean_object* v_ty_4185_; lean_object* v_n_4186_; lean_object* v_offset_4187_; lean_object* v_x_4188_; lean_object* v_tgt_4189_; lean_object* v_b_4190_; lean_object* v_ty_4191_; lean_object* v_n_4192_; lean_object* v_offset_4193_; lean_object* v_x_4194_; uint8_t v___y_4196_; uint8_t v___x_4201_; 
v_tgt_4183_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4183_);
v_b_4184_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4184_);
v_ty_4185_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_ty_4185_);
v_n_4186_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_n_4186_);
v_offset_4187_ = lean_ctor_get(v_x_4041_, 4);
lean_inc(v_offset_4187_);
v_x_4188_ = lean_ctor_get(v_x_4041_, 5);
lean_inc(v_x_4188_);
lean_dec_ref_known(v_x_4041_, 6);
v_tgt_4189_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4189_);
v_b_4190_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4190_);
v_ty_4191_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_ty_4191_);
v_n_4192_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_n_4192_);
v_offset_4193_ = lean_ctor_get(v_x_4042_, 4);
lean_inc(v_offset_4193_);
v_x_4194_ = lean_ctor_get(v_x_4042_, 5);
lean_inc(v_x_4194_);
lean_dec_ref_known(v_x_4042_, 6);
v___x_4201_ = l_Lean_IR_instBEqIRType_beq(v_ty_4185_, v_ty_4191_);
lean_dec(v_ty_4191_);
lean_dec(v_ty_4185_);
if (v___x_4201_ == 0)
{
lean_dec(v_n_4192_);
lean_dec(v_n_4186_);
v___y_4196_ = v___x_4201_;
goto v___jp_4195_;
}
else
{
uint8_t v___x_4202_; 
v___x_4202_ = lean_nat_dec_eq(v_n_4186_, v_n_4192_);
lean_dec(v_n_4192_);
lean_dec(v_n_4186_);
v___y_4196_ = v___x_4202_;
goto v___jp_4195_;
}
v___jp_4195_:
{
if (v___y_4196_ == 0)
{
lean_dec(v_x_4194_);
lean_dec(v_offset_4193_);
lean_dec(v_b_4190_);
lean_dec(v_tgt_4189_);
lean_dec(v_x_4188_);
lean_dec(v_offset_4187_);
lean_dec(v_b_4184_);
lean_dec(v_tgt_4183_);
lean_dec(v_x_4040_);
return v___y_4196_;
}
else
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_nat_dec_eq(v_offset_4187_, v_offset_4193_);
lean_dec(v_offset_4193_);
lean_dec(v_offset_4187_);
if (v___x_4197_ == 0)
{
lean_dec(v_x_4194_);
lean_dec(v_b_4190_);
lean_dec(v_tgt_4189_);
lean_dec(v_x_4188_);
lean_dec(v_b_4184_);
lean_dec(v_tgt_4183_);
lean_dec(v_x_4040_);
return v___x_4197_;
}
else
{
uint8_t v___x_4198_; 
v___x_4198_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4188_, v_x_4194_);
lean_dec(v_x_4194_);
lean_dec(v_x_4188_);
if (v___x_4198_ == 0)
{
lean_dec(v_b_4190_);
lean_dec(v_tgt_4189_);
lean_dec(v_b_4184_);
lean_dec(v_tgt_4183_);
lean_dec(v_x_4040_);
return v___x_4198_;
}
else
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4183_, v_tgt_4189_);
v_x_4040_ = v___x_4199_;
v_x_4041_ = v_b_4184_;
v_x_4042_ = v_b_4190_;
goto _start;
}
}
}
}
}
else
{
uint8_t v___x_4203_; 
lean_dec_ref_known(v_x_4041_, 6);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4203_ = 0;
return v___x_4203_;
}
}
case 6:
{
if (lean_obj_tag(v_x_4042_) == 6)
{
lean_object* v_tgt_4204_; lean_object* v_b_4205_; lean_object* v_ty_4206_; lean_object* v_c_4207_; lean_object* v_ys_4208_; lean_object* v_tgt_4209_; lean_object* v_b_4210_; lean_object* v_ty_4211_; lean_object* v_c_4212_; lean_object* v_ys_4213_; uint8_t v___y_4215_; uint8_t v___x_4219_; 
v_tgt_4204_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4204_);
v_b_4205_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4205_);
v_ty_4206_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_ty_4206_);
v_c_4207_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_c_4207_);
v_ys_4208_ = lean_ctor_get(v_x_4041_, 4);
lean_inc_ref(v_ys_4208_);
lean_dec_ref_known(v_x_4041_, 5);
v_tgt_4209_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4209_);
v_b_4210_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4210_);
v_ty_4211_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_ty_4211_);
v_c_4212_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_c_4212_);
v_ys_4213_ = lean_ctor_get(v_x_4042_, 4);
lean_inc_ref(v_ys_4213_);
lean_dec_ref_known(v_x_4042_, 5);
v___x_4219_ = l_Lean_IR_instBEqIRType_beq(v_ty_4206_, v_ty_4211_);
lean_dec(v_ty_4211_);
lean_dec(v_ty_4206_);
if (v___x_4219_ == 0)
{
lean_dec(v_c_4212_);
lean_dec(v_c_4207_);
v___y_4215_ = v___x_4219_;
goto v___jp_4214_;
}
else
{
uint8_t v___x_4220_; 
v___x_4220_ = lean_name_eq(v_c_4207_, v_c_4212_);
lean_dec(v_c_4212_);
lean_dec(v_c_4207_);
v___y_4215_ = v___x_4220_;
goto v___jp_4214_;
}
v___jp_4214_:
{
if (v___y_4215_ == 0)
{
lean_dec_ref(v_ys_4213_);
lean_dec(v_b_4210_);
lean_dec(v_tgt_4209_);
lean_dec_ref(v_ys_4208_);
lean_dec(v_b_4205_);
lean_dec(v_tgt_4204_);
lean_dec(v_x_4040_);
return v___y_4215_;
}
else
{
uint8_t v___x_4216_; 
v___x_4216_ = l_Lean_IR_args_alphaEqv(v_x_4040_, v_ys_4208_, v_ys_4213_);
lean_dec_ref(v_ys_4213_);
lean_dec_ref(v_ys_4208_);
if (v___x_4216_ == 0)
{
lean_dec(v_b_4210_);
lean_dec(v_tgt_4209_);
lean_dec(v_b_4205_);
lean_dec(v_tgt_4204_);
lean_dec(v_x_4040_);
return v___x_4216_;
}
else
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4204_, v_tgt_4209_);
v_x_4040_ = v___x_4217_;
v_x_4041_ = v_b_4205_;
v_x_4042_ = v_b_4210_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_4221_; 
lean_dec_ref_known(v_x_4041_, 5);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4221_ = 0;
return v___x_4221_;
}
}
case 7:
{
if (lean_obj_tag(v_x_4042_) == 7)
{
lean_object* v_tgt_4222_; lean_object* v_b_4223_; lean_object* v_c_4224_; lean_object* v_ys_4225_; lean_object* v_tgt_4226_; lean_object* v_b_4227_; lean_object* v_c_4228_; lean_object* v_ys_4229_; uint8_t v___y_4231_; uint8_t v___x_4234_; 
v_tgt_4222_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4222_);
v_b_4223_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4223_);
v_c_4224_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_c_4224_);
v_ys_4225_ = lean_ctor_get(v_x_4041_, 3);
lean_inc_ref(v_ys_4225_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4226_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4226_);
v_b_4227_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4227_);
v_c_4228_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_c_4228_);
v_ys_4229_ = lean_ctor_get(v_x_4042_, 3);
lean_inc_ref(v_ys_4229_);
lean_dec_ref_known(v_x_4042_, 4);
v___x_4234_ = lean_name_eq(v_c_4224_, v_c_4228_);
lean_dec(v_c_4228_);
lean_dec(v_c_4224_);
if (v___x_4234_ == 0)
{
lean_dec_ref(v_ys_4229_);
lean_dec_ref(v_ys_4225_);
v___y_4231_ = v___x_4234_;
goto v___jp_4230_;
}
else
{
uint8_t v___x_4235_; 
v___x_4235_ = l_Lean_IR_args_alphaEqv(v_x_4040_, v_ys_4225_, v_ys_4229_);
lean_dec_ref(v_ys_4229_);
lean_dec_ref(v_ys_4225_);
v___y_4231_ = v___x_4235_;
goto v___jp_4230_;
}
v___jp_4230_:
{
if (v___y_4231_ == 0)
{
lean_dec(v_b_4227_);
lean_dec(v_tgt_4226_);
lean_dec(v_b_4223_);
lean_dec(v_tgt_4222_);
lean_dec(v_x_4040_);
return v___y_4231_;
}
else
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4222_, v_tgt_4226_);
v_x_4040_ = v___x_4232_;
v_x_4041_ = v_b_4223_;
v_x_4042_ = v_b_4227_;
goto _start;
}
}
}
else
{
uint8_t v___x_4236_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4236_ = 0;
return v___x_4236_;
}
}
case 8:
{
if (lean_obj_tag(v_x_4042_) == 8)
{
lean_object* v_tgt_4237_; lean_object* v_b_4238_; lean_object* v_x_4239_; lean_object* v_ys_4240_; lean_object* v_tgt_4241_; lean_object* v_b_4242_; lean_object* v_x_4243_; lean_object* v_ys_4244_; uint8_t v___y_4246_; uint8_t v___x_4249_; 
v_tgt_4237_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4237_);
v_b_4238_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4238_);
v_x_4239_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_x_4239_);
v_ys_4240_ = lean_ctor_get(v_x_4041_, 3);
lean_inc_ref(v_ys_4240_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4241_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4241_);
v_b_4242_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4242_);
v_x_4243_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_x_4243_);
v_ys_4244_ = lean_ctor_get(v_x_4042_, 3);
lean_inc_ref(v_ys_4244_);
lean_dec_ref_known(v_x_4042_, 4);
v___x_4249_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4239_, v_x_4243_);
lean_dec(v_x_4243_);
lean_dec(v_x_4239_);
if (v___x_4249_ == 0)
{
lean_dec_ref(v_ys_4244_);
lean_dec_ref(v_ys_4240_);
v___y_4246_ = v___x_4249_;
goto v___jp_4245_;
}
else
{
uint8_t v___x_4250_; 
v___x_4250_ = l_Lean_IR_args_alphaEqv(v_x_4040_, v_ys_4240_, v_ys_4244_);
lean_dec_ref(v_ys_4244_);
lean_dec_ref(v_ys_4240_);
v___y_4246_ = v___x_4250_;
goto v___jp_4245_;
}
v___jp_4245_:
{
if (v___y_4246_ == 0)
{
lean_dec(v_b_4242_);
lean_dec(v_tgt_4241_);
lean_dec(v_b_4238_);
lean_dec(v_tgt_4237_);
lean_dec(v_x_4040_);
return v___y_4246_;
}
else
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4237_, v_tgt_4241_);
v_x_4040_ = v___x_4247_;
v_x_4041_ = v_b_4238_;
v_x_4042_ = v_b_4242_;
goto _start;
}
}
}
else
{
uint8_t v___x_4251_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4251_ = 0;
return v___x_4251_;
}
}
case 9:
{
if (lean_obj_tag(v_x_4042_) == 9)
{
lean_object* v_tgt_4252_; lean_object* v_b_4253_; lean_object* v_ty_4254_; lean_object* v_x_4255_; lean_object* v_tgt_4256_; lean_object* v_b_4257_; lean_object* v_ty_4258_; lean_object* v_x_4259_; 
v_tgt_4252_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4252_);
v_b_4253_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4253_);
v_ty_4254_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_ty_4254_);
v_x_4255_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_x_4255_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4256_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4256_);
v_b_4257_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4257_);
v_ty_4258_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_ty_4258_);
v_x_4259_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_x_4259_);
lean_dec_ref_known(v_x_4042_, 4);
v_00_u03c1_4067_ = v_x_4040_;
v_tgt_u2081_4068_ = v_tgt_4252_;
v_b_u2081_4069_ = v_b_4253_;
v_ty_u2081_4070_ = v_ty_4254_;
v_x_u2081_4071_ = v_x_4255_;
v_tgt_u2082_4072_ = v_tgt_4256_;
v_b_u2082_4073_ = v_b_4257_;
v_ty_u2082_4074_ = v_ty_4258_;
v_x_u2082_4075_ = v_x_4259_;
goto v___jp_4066_;
}
else
{
uint8_t v___x_4260_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4260_ = 0;
return v___x_4260_;
}
}
case 10:
{
if (lean_obj_tag(v_x_4042_) == 10)
{
lean_object* v_tgt_4261_; lean_object* v_b_4262_; lean_object* v_ty_4263_; lean_object* v_x_4264_; lean_object* v_tgt_4265_; lean_object* v_b_4266_; lean_object* v_ty_4267_; lean_object* v_x_4268_; 
v_tgt_4261_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4261_);
v_b_4262_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4262_);
v_ty_4263_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_ty_4263_);
v_x_4264_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_x_4264_);
lean_dec_ref_known(v_x_4041_, 4);
v_tgt_4265_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4265_);
v_b_4266_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4266_);
v_ty_4267_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_ty_4267_);
v_x_4268_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_x_4268_);
lean_dec_ref_known(v_x_4042_, 4);
v_00_u03c1_4067_ = v_x_4040_;
v_tgt_u2081_4068_ = v_tgt_4261_;
v_b_u2081_4069_ = v_b_4262_;
v_ty_u2081_4070_ = v_ty_4263_;
v_x_u2081_4071_ = v_x_4264_;
v_tgt_u2082_4072_ = v_tgt_4265_;
v_b_u2082_4073_ = v_b_4266_;
v_ty_u2082_4074_ = v_ty_4267_;
v_x_u2082_4075_ = v_x_4268_;
goto v___jp_4066_;
}
else
{
uint8_t v___x_4269_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4269_ = 0;
return v___x_4269_;
}
}
case 11:
{
if (lean_obj_tag(v_x_4042_) == 11)
{
lean_object* v_tgt_4270_; lean_object* v_b_4271_; uint8_t v_v_4272_; lean_object* v_tgt_4273_; lean_object* v_b_4274_; uint8_t v_v_4275_; uint8_t v___x_4276_; 
v_tgt_4270_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4270_);
v_b_4271_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4271_);
v_v_4272_ = lean_ctor_get_uint8(v_x_4041_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4041_, 2);
v_tgt_4273_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4273_);
v_b_4274_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4274_);
v_v_4275_ = lean_ctor_get_uint8(v_x_4042_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4042_, 2);
v___x_4276_ = lean_uint8_dec_eq(v_v_4272_, v_v_4275_);
if (v___x_4276_ == 0)
{
lean_dec(v_b_4274_);
lean_dec(v_tgt_4273_);
lean_dec(v_b_4271_);
lean_dec(v_tgt_4270_);
lean_dec(v_x_4040_);
return v___x_4276_;
}
else
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4270_, v_tgt_4273_);
v_x_4040_ = v___x_4277_;
v_x_4041_ = v_b_4271_;
v_x_4042_ = v_b_4274_;
goto _start;
}
}
else
{
uint8_t v___x_4279_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4279_ = 0;
return v___x_4279_;
}
}
case 12:
{
if (lean_obj_tag(v_x_4042_) == 12)
{
lean_object* v_tgt_4280_; lean_object* v_b_4281_; uint16_t v_v_4282_; lean_object* v_tgt_4283_; lean_object* v_b_4284_; uint16_t v_v_4285_; uint8_t v___x_4286_; 
v_tgt_4280_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4280_);
v_b_4281_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4281_);
v_v_4282_ = lean_ctor_get_uint16(v_x_4041_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4041_, 2);
v_tgt_4283_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4283_);
v_b_4284_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4284_);
v_v_4285_ = lean_ctor_get_uint16(v_x_4042_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4042_, 2);
v___x_4286_ = lean_uint16_dec_eq(v_v_4282_, v_v_4285_);
if (v___x_4286_ == 0)
{
lean_dec(v_b_4284_);
lean_dec(v_tgt_4283_);
lean_dec(v_b_4281_);
lean_dec(v_tgt_4280_);
lean_dec(v_x_4040_);
return v___x_4286_;
}
else
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4280_, v_tgt_4283_);
v_x_4040_ = v___x_4287_;
v_x_4041_ = v_b_4281_;
v_x_4042_ = v_b_4284_;
goto _start;
}
}
else
{
uint8_t v___x_4289_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4289_ = 0;
return v___x_4289_;
}
}
case 13:
{
if (lean_obj_tag(v_x_4042_) == 13)
{
lean_object* v_tgt_4290_; lean_object* v_b_4291_; uint32_t v_v_4292_; lean_object* v_tgt_4293_; lean_object* v_b_4294_; uint32_t v_v_4295_; uint8_t v___x_4296_; 
v_tgt_4290_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4290_);
v_b_4291_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4291_);
v_v_4292_ = lean_ctor_get_uint32(v_x_4041_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4041_, 2);
v_tgt_4293_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4293_);
v_b_4294_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4294_);
v_v_4295_ = lean_ctor_get_uint32(v_x_4042_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4042_, 2);
v___x_4296_ = lean_uint32_dec_eq(v_v_4292_, v_v_4295_);
if (v___x_4296_ == 0)
{
lean_dec(v_b_4294_);
lean_dec(v_tgt_4293_);
lean_dec(v_b_4291_);
lean_dec(v_tgt_4290_);
lean_dec(v_x_4040_);
return v___x_4296_;
}
else
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4290_, v_tgt_4293_);
v_x_4040_ = v___x_4297_;
v_x_4041_ = v_b_4291_;
v_x_4042_ = v_b_4294_;
goto _start;
}
}
else
{
uint8_t v___x_4299_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4299_ = 0;
return v___x_4299_;
}
}
case 14:
{
if (lean_obj_tag(v_x_4042_) == 14)
{
lean_object* v_tgt_4300_; lean_object* v_b_4301_; uint64_t v_v_4302_; lean_object* v_tgt_4303_; lean_object* v_b_4304_; uint64_t v_v_4305_; 
v_tgt_4300_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4300_);
v_b_4301_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4301_);
v_v_4302_ = lean_ctor_get_uint64(v_x_4041_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4041_, 2);
v_tgt_4303_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4303_);
v_b_4304_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4304_);
v_v_4305_ = lean_ctor_get_uint64(v_x_4042_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4042_, 2);
v_00_u03c1_4079_ = v_x_4040_;
v_tgt_u2081_4080_ = v_tgt_4300_;
v_b_u2081_4081_ = v_b_4301_;
v_v_u2081_4082_ = v_v_4302_;
v_tgt_u2082_4083_ = v_tgt_4303_;
v_b_u2082_4084_ = v_b_4304_;
v_v_u2082_4085_ = v_v_4305_;
goto v___jp_4078_;
}
else
{
uint8_t v___x_4306_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4306_ = 0;
return v___x_4306_;
}
}
case 15:
{
if (lean_obj_tag(v_x_4042_) == 15)
{
lean_object* v_tgt_4307_; lean_object* v_b_4308_; uint64_t v_v_4309_; lean_object* v_tgt_4310_; lean_object* v_b_4311_; uint64_t v_v_4312_; 
v_tgt_4307_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4307_);
v_b_4308_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4308_);
v_v_4309_ = lean_ctor_get_uint64(v_x_4041_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4041_, 2);
v_tgt_4310_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4310_);
v_b_4311_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4311_);
v_v_4312_ = lean_ctor_get_uint64(v_x_4042_, sizeof(void*)*2);
lean_dec_ref_known(v_x_4042_, 2);
v_00_u03c1_4079_ = v_x_4040_;
v_tgt_u2081_4080_ = v_tgt_4307_;
v_b_u2081_4081_ = v_b_4308_;
v_v_u2081_4082_ = v_v_4309_;
v_tgt_u2082_4083_ = v_tgt_4310_;
v_b_u2082_4084_ = v_b_4311_;
v_v_u2082_4085_ = v_v_4312_;
goto v___jp_4078_;
}
else
{
uint8_t v___x_4313_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4313_ = 0;
return v___x_4313_;
}
}
case 16:
{
if (lean_obj_tag(v_x_4042_) == 16)
{
lean_object* v_tgt_4314_; lean_object* v_b_4315_; lean_object* v_v_4316_; lean_object* v_tgt_4317_; lean_object* v_b_4318_; lean_object* v_v_4319_; uint8_t v___x_4320_; 
v_tgt_4314_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4314_);
v_b_4315_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4315_);
v_v_4316_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_v_4316_);
lean_dec_ref_known(v_x_4041_, 3);
v_tgt_4317_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4317_);
v_b_4318_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4318_);
v_v_4319_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_v_4319_);
lean_dec_ref_known(v_x_4042_, 3);
v___x_4320_ = lean_nat_dec_eq(v_v_4316_, v_v_4319_);
lean_dec(v_v_4319_);
lean_dec(v_v_4316_);
if (v___x_4320_ == 0)
{
lean_dec(v_b_4318_);
lean_dec(v_tgt_4317_);
lean_dec(v_b_4315_);
lean_dec(v_tgt_4314_);
lean_dec(v_x_4040_);
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4314_, v_tgt_4317_);
v_x_4040_ = v___x_4321_;
v_x_4041_ = v_b_4315_;
v_x_4042_ = v_b_4318_;
goto _start;
}
}
else
{
uint8_t v___x_4323_; 
lean_dec_ref_known(v_x_4041_, 3);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4323_ = 0;
return v___x_4323_;
}
}
case 17:
{
if (lean_obj_tag(v_x_4042_) == 17)
{
lean_object* v_tgt_4324_; lean_object* v_b_4325_; lean_object* v_v_4326_; lean_object* v_tgt_4327_; lean_object* v_b_4328_; lean_object* v_v_4329_; uint8_t v___x_4330_; 
v_tgt_4324_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4324_);
v_b_4325_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4325_);
v_v_4326_ = lean_ctor_get(v_x_4041_, 2);
lean_inc_ref(v_v_4326_);
lean_dec_ref_known(v_x_4041_, 3);
v_tgt_4327_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4327_);
v_b_4328_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4328_);
v_v_4329_ = lean_ctor_get(v_x_4042_, 2);
lean_inc_ref(v_v_4329_);
lean_dec_ref_known(v_x_4042_, 3);
v___x_4330_ = lean_string_dec_eq(v_v_4326_, v_v_4329_);
lean_dec_ref(v_v_4329_);
lean_dec_ref(v_v_4326_);
if (v___x_4330_ == 0)
{
lean_dec(v_b_4328_);
lean_dec(v_tgt_4327_);
lean_dec(v_b_4325_);
lean_dec(v_tgt_4324_);
lean_dec(v_x_4040_);
return v___x_4330_;
}
else
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4324_, v_tgt_4327_);
v_x_4040_ = v___x_4331_;
v_x_4041_ = v_b_4325_;
v_x_4042_ = v_b_4328_;
goto _start;
}
}
else
{
uint8_t v___x_4333_; 
lean_dec_ref_known(v_x_4041_, 3);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4333_ = 0;
return v___x_4333_;
}
}
case 18:
{
if (lean_obj_tag(v_x_4042_) == 18)
{
lean_object* v_tgt_4334_; lean_object* v_b_4335_; lean_object* v_x_4336_; lean_object* v_tgt_4337_; lean_object* v_b_4338_; lean_object* v_x_4339_; uint8_t v___x_4340_; 
v_tgt_4334_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tgt_4334_);
v_b_4335_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4335_);
v_x_4336_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_x_4336_);
lean_dec_ref_known(v_x_4041_, 3);
v_tgt_4337_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tgt_4337_);
v_b_4338_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4338_);
v_x_4339_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_x_4339_);
lean_dec_ref_known(v_x_4042_, 3);
v___x_4340_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4336_, v_x_4339_);
lean_dec(v_x_4339_);
lean_dec(v_x_4336_);
if (v___x_4340_ == 0)
{
lean_dec(v_b_4338_);
lean_dec(v_tgt_4337_);
lean_dec(v_b_4335_);
lean_dec(v_tgt_4334_);
lean_dec(v_x_4040_);
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; 
v___x_4341_ = l_Lean_IR_addVarRename(v_x_4040_, v_tgt_4334_, v_tgt_4337_);
v_x_4040_ = v___x_4341_;
v_x_4041_ = v_b_4335_;
v_x_4042_ = v_b_4338_;
goto _start;
}
}
else
{
uint8_t v___x_4343_; 
lean_dec_ref_known(v_x_4041_, 3);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4343_ = 0;
return v___x_4343_;
}
}
case 19:
{
if (lean_obj_tag(v_x_4042_) == 19)
{
lean_object* v_j_4344_; lean_object* v_xs_4345_; lean_object* v_v_4346_; lean_object* v_b_4347_; lean_object* v_j_4348_; lean_object* v_xs_4349_; lean_object* v_v_4350_; lean_object* v_b_4351_; lean_object* v___x_4352_; 
v_j_4344_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_j_4344_);
v_xs_4345_ = lean_ctor_get(v_x_4041_, 1);
lean_inc_ref(v_xs_4345_);
v_v_4346_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_v_4346_);
v_b_4347_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_b_4347_);
lean_dec_ref_known(v_x_4041_, 4);
v_j_4348_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_j_4348_);
v_xs_4349_ = lean_ctor_get(v_x_4042_, 1);
lean_inc_ref(v_xs_4349_);
v_v_4350_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_v_4350_);
v_b_4351_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_b_4351_);
lean_dec_ref_known(v_x_4042_, 4);
lean_inc(v_x_4040_);
v___x_4352_ = l_Lean_IR_addParamsRename(v_x_4040_, v_xs_4345_, v_xs_4349_);
lean_dec_ref(v_xs_4349_);
lean_dec_ref(v_xs_4345_);
if (lean_obj_tag(v___x_4352_) == 0)
{
uint8_t v___x_4353_; 
lean_dec(v_b_4351_);
lean_dec(v_v_4350_);
lean_dec(v_j_4348_);
lean_dec(v_b_4347_);
lean_dec(v_v_4346_);
lean_dec(v_j_4344_);
lean_dec(v_x_4040_);
v___x_4353_ = 0;
return v___x_4353_;
}
else
{
lean_object* v_val_4354_; uint8_t v___x_4355_; 
v_val_4354_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_val_4354_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4355_ = l_Lean_IR_FnBody_alphaEqv(v_val_4354_, v_v_4346_, v_v_4350_);
if (v___x_4355_ == 0)
{
lean_dec(v_b_4351_);
lean_dec(v_j_4348_);
lean_dec(v_b_4347_);
lean_dec(v_j_4344_);
lean_dec(v_x_4040_);
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Lean_IR_addVarRename(v_x_4040_, v_j_4344_, v_j_4348_);
v_x_4040_ = v___x_4356_;
v_x_4041_ = v_b_4347_;
v_x_4042_ = v_b_4351_;
goto _start;
}
}
}
else
{
uint8_t v___x_4358_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4358_ = 0;
return v___x_4358_;
}
}
case 20:
{
if (lean_obj_tag(v_x_4042_) == 20)
{
lean_object* v_x_4359_; lean_object* v_i_4360_; lean_object* v_y_4361_; lean_object* v_b_4362_; lean_object* v_x_4363_; lean_object* v_i_4364_; lean_object* v_y_4365_; lean_object* v_b_4366_; uint8_t v___y_4368_; uint8_t v___x_4371_; 
v_x_4359_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4359_);
v_i_4360_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_i_4360_);
v_y_4361_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_y_4361_);
v_b_4362_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_b_4362_);
lean_dec_ref_known(v_x_4041_, 4);
v_x_4363_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4363_);
v_i_4364_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_i_4364_);
v_y_4365_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_y_4365_);
v_b_4366_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_b_4366_);
lean_dec_ref_known(v_x_4042_, 4);
v___x_4371_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4359_, v_x_4363_);
lean_dec(v_x_4363_);
lean_dec(v_x_4359_);
if (v___x_4371_ == 0)
{
lean_dec(v_i_4364_);
lean_dec(v_i_4360_);
v___y_4368_ = v___x_4371_;
goto v___jp_4367_;
}
else
{
uint8_t v___x_4372_; 
v___x_4372_ = lean_nat_dec_eq(v_i_4360_, v_i_4364_);
lean_dec(v_i_4364_);
lean_dec(v_i_4360_);
v___y_4368_ = v___x_4372_;
goto v___jp_4367_;
}
v___jp_4367_:
{
if (v___y_4368_ == 0)
{
lean_dec(v_b_4366_);
lean_dec(v_y_4365_);
lean_dec(v_b_4362_);
lean_dec(v_y_4361_);
lean_dec(v_x_4040_);
return v___y_4368_;
}
else
{
uint8_t v___x_4369_; 
v___x_4369_ = l_Lean_IR_Arg_alphaEqv(v_x_4040_, v_y_4361_, v_y_4365_);
lean_dec(v_y_4365_);
lean_dec(v_y_4361_);
if (v___x_4369_ == 0)
{
lean_dec(v_b_4366_);
lean_dec(v_b_4362_);
lean_dec(v_x_4040_);
return v___x_4369_;
}
else
{
v_x_4041_ = v_b_4362_;
v_x_4042_ = v_b_4366_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_4373_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4373_ = 0;
return v___x_4373_;
}
}
case 21:
{
if (lean_obj_tag(v_x_4042_) == 21)
{
lean_object* v_x_4374_; lean_object* v_cidx_4375_; lean_object* v_b_4376_; lean_object* v_x_4377_; lean_object* v_cidx_4378_; lean_object* v_b_4379_; uint8_t v___y_4381_; uint8_t v___x_4383_; 
v_x_4374_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4374_);
v_cidx_4375_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_cidx_4375_);
v_b_4376_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_b_4376_);
lean_dec_ref_known(v_x_4041_, 3);
v_x_4377_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4377_);
v_cidx_4378_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_cidx_4378_);
v_b_4379_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_b_4379_);
lean_dec_ref_known(v_x_4042_, 3);
v___x_4383_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4374_, v_x_4377_);
lean_dec(v_x_4377_);
lean_dec(v_x_4374_);
if (v___x_4383_ == 0)
{
lean_dec(v_cidx_4378_);
lean_dec(v_cidx_4375_);
v___y_4381_ = v___x_4383_;
goto v___jp_4380_;
}
else
{
uint8_t v___x_4384_; 
v___x_4384_ = lean_nat_dec_eq(v_cidx_4375_, v_cidx_4378_);
lean_dec(v_cidx_4378_);
lean_dec(v_cidx_4375_);
v___y_4381_ = v___x_4384_;
goto v___jp_4380_;
}
v___jp_4380_:
{
if (v___y_4381_ == 0)
{
lean_dec(v_b_4379_);
lean_dec(v_b_4376_);
lean_dec(v_x_4040_);
return v___y_4381_;
}
else
{
v_x_4041_ = v_b_4376_;
v_x_4042_ = v_b_4379_;
goto _start;
}
}
}
else
{
uint8_t v___x_4385_; 
lean_dec_ref_known(v_x_4041_, 3);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4385_ = 0;
return v___x_4385_;
}
}
case 22:
{
if (lean_obj_tag(v_x_4042_) == 22)
{
lean_object* v_x_4386_; lean_object* v_i_4387_; lean_object* v_y_4388_; lean_object* v_b_4389_; lean_object* v_x_4390_; lean_object* v_i_4391_; lean_object* v_y_4392_; lean_object* v_b_4393_; uint8_t v___y_4395_; uint8_t v___x_4398_; 
v_x_4386_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4386_);
v_i_4387_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_i_4387_);
v_y_4388_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_y_4388_);
v_b_4389_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_b_4389_);
lean_dec_ref_known(v_x_4041_, 4);
v_x_4390_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4390_);
v_i_4391_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_i_4391_);
v_y_4392_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_y_4392_);
v_b_4393_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_b_4393_);
lean_dec_ref_known(v_x_4042_, 4);
v___x_4398_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4386_, v_x_4390_);
lean_dec(v_x_4390_);
lean_dec(v_x_4386_);
if (v___x_4398_ == 0)
{
lean_dec(v_i_4391_);
lean_dec(v_i_4387_);
v___y_4395_ = v___x_4398_;
goto v___jp_4394_;
}
else
{
uint8_t v___x_4399_; 
v___x_4399_ = lean_nat_dec_eq(v_i_4387_, v_i_4391_);
lean_dec(v_i_4391_);
lean_dec(v_i_4387_);
v___y_4395_ = v___x_4399_;
goto v___jp_4394_;
}
v___jp_4394_:
{
if (v___y_4395_ == 0)
{
lean_dec(v_b_4393_);
lean_dec(v_y_4392_);
lean_dec(v_b_4389_);
lean_dec(v_y_4388_);
lean_dec(v_x_4040_);
return v___y_4395_;
}
else
{
uint8_t v___x_4396_; 
v___x_4396_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_y_4388_, v_y_4392_);
lean_dec(v_y_4392_);
lean_dec(v_y_4388_);
if (v___x_4396_ == 0)
{
lean_dec(v_b_4393_);
lean_dec(v_b_4389_);
lean_dec(v_x_4040_);
return v___x_4396_;
}
else
{
v_x_4041_ = v_b_4389_;
v_x_4042_ = v_b_4393_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_4400_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4400_ = 0;
return v___x_4400_;
}
}
case 23:
{
if (lean_obj_tag(v_x_4042_) == 23)
{
lean_object* v_x_4401_; lean_object* v_i_4402_; lean_object* v_offset_4403_; lean_object* v_y_4404_; lean_object* v_ty_4405_; lean_object* v_b_4406_; lean_object* v_x_4407_; lean_object* v_i_4408_; lean_object* v_offset_4409_; lean_object* v_y_4410_; lean_object* v_ty_4411_; lean_object* v_b_4412_; uint8_t v___y_4414_; uint8_t v___x_4419_; 
v_x_4401_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4401_);
v_i_4402_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_i_4402_);
v_offset_4403_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_offset_4403_);
v_y_4404_ = lean_ctor_get(v_x_4041_, 3);
lean_inc(v_y_4404_);
v_ty_4405_ = lean_ctor_get(v_x_4041_, 4);
lean_inc(v_ty_4405_);
v_b_4406_ = lean_ctor_get(v_x_4041_, 5);
lean_inc(v_b_4406_);
lean_dec_ref_known(v_x_4041_, 6);
v_x_4407_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4407_);
v_i_4408_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_i_4408_);
v_offset_4409_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_offset_4409_);
v_y_4410_ = lean_ctor_get(v_x_4042_, 3);
lean_inc(v_y_4410_);
v_ty_4411_ = lean_ctor_get(v_x_4042_, 4);
lean_inc(v_ty_4411_);
v_b_4412_ = lean_ctor_get(v_x_4042_, 5);
lean_inc(v_b_4412_);
lean_dec_ref_known(v_x_4042_, 6);
v___x_4419_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4401_, v_x_4407_);
lean_dec(v_x_4407_);
lean_dec(v_x_4401_);
if (v___x_4419_ == 0)
{
lean_dec(v_i_4408_);
lean_dec(v_i_4402_);
v___y_4414_ = v___x_4419_;
goto v___jp_4413_;
}
else
{
uint8_t v___x_4420_; 
v___x_4420_ = lean_nat_dec_eq(v_i_4402_, v_i_4408_);
lean_dec(v_i_4408_);
lean_dec(v_i_4402_);
v___y_4414_ = v___x_4420_;
goto v___jp_4413_;
}
v___jp_4413_:
{
if (v___y_4414_ == 0)
{
lean_dec(v_b_4412_);
lean_dec(v_ty_4411_);
lean_dec(v_y_4410_);
lean_dec(v_offset_4409_);
lean_dec(v_b_4406_);
lean_dec(v_ty_4405_);
lean_dec(v_y_4404_);
lean_dec(v_offset_4403_);
lean_dec(v_x_4040_);
return v___y_4414_;
}
else
{
uint8_t v___x_4415_; 
v___x_4415_ = lean_nat_dec_eq(v_offset_4403_, v_offset_4409_);
lean_dec(v_offset_4409_);
lean_dec(v_offset_4403_);
if (v___x_4415_ == 0)
{
lean_dec(v_b_4412_);
lean_dec(v_ty_4411_);
lean_dec(v_y_4410_);
lean_dec(v_b_4406_);
lean_dec(v_ty_4405_);
lean_dec(v_y_4404_);
lean_dec(v_x_4040_);
return v___x_4415_;
}
else
{
uint8_t v___x_4416_; 
v___x_4416_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_y_4404_, v_y_4410_);
lean_dec(v_y_4410_);
lean_dec(v_y_4404_);
if (v___x_4416_ == 0)
{
lean_dec(v_b_4412_);
lean_dec(v_ty_4411_);
lean_dec(v_b_4406_);
lean_dec(v_ty_4405_);
lean_dec(v_x_4040_);
return v___x_4416_;
}
else
{
uint8_t v___x_4417_; 
v___x_4417_ = l_Lean_IR_instBEqIRType_beq(v_ty_4405_, v_ty_4411_);
lean_dec(v_ty_4411_);
lean_dec(v_ty_4405_);
if (v___x_4417_ == 0)
{
lean_dec(v_b_4412_);
lean_dec(v_b_4406_);
lean_dec(v_x_4040_);
return v___x_4417_;
}
else
{
v_x_4041_ = v_b_4406_;
v_x_4042_ = v_b_4412_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_4421_; 
lean_dec_ref_known(v_x_4041_, 6);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4421_ = 0;
return v___x_4421_;
}
}
case 24:
{
if (lean_obj_tag(v_x_4042_) == 24)
{
lean_object* v_x_4422_; lean_object* v_n_4423_; uint8_t v_c_4424_; uint8_t v_persistent_4425_; lean_object* v_b_4426_; lean_object* v_x_4427_; lean_object* v_n_4428_; uint8_t v_c_4429_; uint8_t v_persistent_4430_; lean_object* v_b_4431_; 
v_x_4422_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4422_);
v_n_4423_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_n_4423_);
v_c_4424_ = lean_ctor_get_uint8(v_x_4041_, sizeof(void*)*3);
v_persistent_4425_ = lean_ctor_get_uint8(v_x_4041_, sizeof(void*)*3 + 1);
v_b_4426_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_b_4426_);
lean_dec_ref_known(v_x_4041_, 3);
v_x_4427_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4427_);
v_n_4428_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_n_4428_);
v_c_4429_ = lean_ctor_get_uint8(v_x_4042_, sizeof(void*)*3);
v_persistent_4430_ = lean_ctor_get_uint8(v_x_4042_, sizeof(void*)*3 + 1);
v_b_4431_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_b_4431_);
lean_dec_ref_known(v_x_4042_, 3);
v_00_u03c1_4107_ = v_x_4040_;
v_x_u2081_4108_ = v_x_4422_;
v_n_u2081_4109_ = v_n_4423_;
v_c_u2081_4110_ = v_c_4424_;
v_p_u2081_4111_ = v_persistent_4425_;
v_b_u2081_4112_ = v_b_4426_;
v_x_u2082_4113_ = v_x_4427_;
v_n_u2082_4114_ = v_n_4428_;
v_c_u2082_4115_ = v_c_4429_;
v_p_u2082_4116_ = v_persistent_4430_;
v_b_u2082_4117_ = v_b_4431_;
goto v___jp_4106_;
}
else
{
uint8_t v___x_4432_; 
lean_dec_ref_known(v_x_4041_, 3);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4432_ = 0;
return v___x_4432_;
}
}
case 25:
{
if (lean_obj_tag(v_x_4042_) == 25)
{
lean_object* v_x_4433_; lean_object* v_n_4434_; uint8_t v_c_4435_; uint8_t v_persistent_4436_; lean_object* v_b_4437_; lean_object* v_x_4438_; lean_object* v_n_4439_; uint8_t v_c_4440_; uint8_t v_persistent_4441_; lean_object* v_b_4442_; 
v_x_4433_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4433_);
v_n_4434_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_n_4434_);
v_c_4435_ = lean_ctor_get_uint8(v_x_4041_, sizeof(void*)*3);
v_persistent_4436_ = lean_ctor_get_uint8(v_x_4041_, sizeof(void*)*3 + 1);
v_b_4437_ = lean_ctor_get(v_x_4041_, 2);
lean_inc(v_b_4437_);
lean_dec_ref_known(v_x_4041_, 3);
v_x_4438_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4438_);
v_n_4439_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_n_4439_);
v_c_4440_ = lean_ctor_get_uint8(v_x_4042_, sizeof(void*)*3);
v_persistent_4441_ = lean_ctor_get_uint8(v_x_4042_, sizeof(void*)*3 + 1);
v_b_4442_ = lean_ctor_get(v_x_4042_, 2);
lean_inc(v_b_4442_);
lean_dec_ref_known(v_x_4042_, 3);
v_00_u03c1_4107_ = v_x_4040_;
v_x_u2081_4108_ = v_x_4433_;
v_n_u2081_4109_ = v_n_4434_;
v_c_u2081_4110_ = v_c_4435_;
v_p_u2081_4111_ = v_persistent_4436_;
v_b_u2081_4112_ = v_b_4437_;
v_x_u2082_4113_ = v_x_4438_;
v_n_u2082_4114_ = v_n_4439_;
v_c_u2082_4115_ = v_c_4440_;
v_p_u2082_4116_ = v_persistent_4441_;
v_b_u2082_4117_ = v_b_4442_;
goto v___jp_4106_;
}
else
{
uint8_t v___x_4443_; 
lean_dec_ref_known(v_x_4041_, 3);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4443_ = 0;
return v___x_4443_;
}
}
case 26:
{
if (lean_obj_tag(v_x_4042_) == 26)
{
lean_object* v_x_4444_; lean_object* v_b_4445_; lean_object* v_x_4446_; lean_object* v_b_4447_; uint8_t v___x_4448_; 
v_x_4444_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4444_);
v_b_4445_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_b_4445_);
lean_dec_ref_known(v_x_4041_, 2);
v_x_4446_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4446_);
v_b_4447_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_b_4447_);
lean_dec_ref_known(v_x_4042_, 2);
v___x_4448_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4444_, v_x_4446_);
lean_dec(v_x_4446_);
lean_dec(v_x_4444_);
if (v___x_4448_ == 0)
{
lean_dec(v_b_4447_);
lean_dec(v_b_4445_);
lean_dec(v_x_4040_);
return v___x_4448_;
}
else
{
v_x_4041_ = v_b_4445_;
v_x_4042_ = v_b_4447_;
goto _start;
}
}
else
{
uint8_t v___x_4450_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4450_ = 0;
return v___x_4450_;
}
}
case 27:
{
if (lean_obj_tag(v_x_4042_) == 27)
{
lean_object* v_tid_4451_; lean_object* v_x_4452_; lean_object* v_cs_4453_; lean_object* v_tid_4454_; lean_object* v_x_4455_; lean_object* v_cs_4456_; uint8_t v___y_4458_; uint8_t v___x_4463_; 
v_tid_4451_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_tid_4451_);
v_x_4452_ = lean_ctor_get(v_x_4041_, 1);
lean_inc(v_x_4452_);
v_cs_4453_ = lean_ctor_get(v_x_4041_, 3);
lean_inc_ref(v_cs_4453_);
lean_dec_ref_known(v_x_4041_, 4);
v_tid_4454_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_tid_4454_);
v_x_4455_ = lean_ctor_get(v_x_4042_, 1);
lean_inc(v_x_4455_);
v_cs_4456_ = lean_ctor_get(v_x_4042_, 3);
lean_inc_ref(v_cs_4456_);
lean_dec_ref_known(v_x_4042_, 4);
v___x_4463_ = lean_name_eq(v_tid_4451_, v_tid_4454_);
lean_dec(v_tid_4454_);
lean_dec(v_tid_4451_);
if (v___x_4463_ == 0)
{
lean_dec(v_x_4455_);
lean_dec(v_x_4452_);
v___y_4458_ = v___x_4463_;
goto v___jp_4457_;
}
else
{
uint8_t v___x_4464_; 
v___x_4464_ = l_Lean_IR_VarId_alphaEqv(v_x_4040_, v_x_4452_, v_x_4455_);
lean_dec(v_x_4455_);
lean_dec(v_x_4452_);
v___y_4458_ = v___x_4464_;
goto v___jp_4457_;
}
v___jp_4457_:
{
if (v___y_4458_ == 0)
{
lean_dec_ref(v_cs_4456_);
lean_dec_ref(v_cs_4453_);
lean_dec(v_x_4040_);
return v___y_4458_;
}
else
{
lean_object* v___x_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4459_ = lean_array_get_size(v_cs_4453_);
v___x_4460_ = lean_array_get_size(v_cs_4456_);
v___x_4461_ = lean_nat_dec_eq(v___x_4459_, v___x_4460_);
if (v___x_4461_ == 0)
{
lean_dec_ref(v_cs_4456_);
lean_dec_ref(v_cs_4453_);
lean_dec(v_x_4040_);
return v___x_4461_;
}
else
{
uint8_t v___x_4462_; 
v___x_4462_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_4040_, v_cs_4453_, v_cs_4456_, v___x_4459_);
lean_dec_ref(v_cs_4456_);
lean_dec_ref(v_cs_4453_);
return v___x_4462_;
}
}
}
}
else
{
uint8_t v___x_4465_; 
lean_dec_ref_known(v_x_4041_, 4);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4465_ = 0;
return v___x_4465_;
}
}
case 28:
{
if (lean_obj_tag(v_x_4042_) == 28)
{
lean_object* v_x_4466_; lean_object* v_x_4467_; uint8_t v___x_4468_; 
v_x_4466_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_x_4466_);
lean_dec_ref_known(v_x_4041_, 1);
v_x_4467_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_x_4467_);
lean_dec_ref_known(v_x_4042_, 1);
v___x_4468_ = l_Lean_IR_Arg_alphaEqv(v_x_4040_, v_x_4466_, v_x_4467_);
lean_dec(v_x_4467_);
lean_dec(v_x_4466_);
lean_dec(v_x_4040_);
return v___x_4468_;
}
else
{
uint8_t v___x_4469_; 
lean_dec_ref_known(v_x_4041_, 1);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4469_ = 0;
return v___x_4469_;
}
}
case 29:
{
if (lean_obj_tag(v_x_4042_) == 29)
{
lean_object* v_j_4470_; lean_object* v_ys_4471_; lean_object* v_j_4472_; lean_object* v_ys_4473_; uint8_t v___x_4474_; 
v_j_4470_ = lean_ctor_get(v_x_4041_, 0);
lean_inc(v_j_4470_);
v_ys_4471_ = lean_ctor_get(v_x_4041_, 1);
lean_inc_ref(v_ys_4471_);
lean_dec_ref_known(v_x_4041_, 2);
v_j_4472_ = lean_ctor_get(v_x_4042_, 0);
lean_inc(v_j_4472_);
v_ys_4473_ = lean_ctor_get(v_x_4042_, 1);
lean_inc_ref(v_ys_4473_);
lean_dec_ref_known(v_x_4042_, 2);
v___x_4474_ = lean_nat_dec_eq(v_j_4470_, v_j_4472_);
lean_dec(v_j_4472_);
lean_dec(v_j_4470_);
if (v___x_4474_ == 0)
{
lean_dec_ref(v_ys_4473_);
lean_dec_ref(v_ys_4471_);
lean_dec(v_x_4040_);
return v___x_4474_;
}
else
{
uint8_t v___x_4475_; 
v___x_4475_ = l_Lean_IR_args_alphaEqv(v_x_4040_, v_ys_4471_, v_ys_4473_);
lean_dec_ref(v_ys_4473_);
lean_dec_ref(v_ys_4471_);
lean_dec(v_x_4040_);
return v___x_4475_;
}
}
else
{
uint8_t v___x_4476_; 
lean_dec_ref_known(v_x_4041_, 2);
lean_dec(v_x_4042_);
lean_dec(v_x_4040_);
v___x_4476_ = 0;
return v___x_4476_;
}
}
default: 
{
lean_dec(v_x_4040_);
if (lean_obj_tag(v_x_4042_) == 30)
{
uint8_t v___x_4477_; 
v___x_4477_ = 1;
return v___x_4477_;
}
else
{
uint8_t v___x_4478_; 
lean_dec(v_x_4042_);
v___x_4478_ = 0;
return v___x_4478_;
}
}
}
v___jp_4043_:
{
uint8_t v___x_4053_; 
v___x_4053_ = lean_nat_dec_eq(v_n_u2081_4047_, v_n_u2082_4051_);
lean_dec(v_n_u2082_4051_);
lean_dec(v_n_u2081_4047_);
if (v___x_4053_ == 0)
{
lean_dec(v_x_u2082_4052_);
lean_dec(v_b_u2082_4050_);
lean_dec(v_tgt_u2082_4049_);
lean_dec(v_x_u2081_4048_);
lean_dec(v_b_u2081_4046_);
lean_dec(v_tgt_u2081_4045_);
lean_dec(v_00_u03c1_4044_);
return v___x_4053_;
}
else
{
uint8_t v___x_4054_; 
v___x_4054_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_4044_, v_x_u2081_4048_, v_x_u2082_4052_);
lean_dec(v_x_u2082_4052_);
lean_dec(v_x_u2081_4048_);
if (v___x_4054_ == 0)
{
lean_dec(v_b_u2082_4050_);
lean_dec(v_tgt_u2082_4049_);
lean_dec(v_b_u2081_4046_);
lean_dec(v_tgt_u2081_4045_);
lean_dec(v_00_u03c1_4044_);
return v___x_4054_;
}
else
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_IR_addVarRename(v_00_u03c1_4044_, v_tgt_u2081_4045_, v_tgt_u2082_4049_);
v_x_4040_ = v___x_4055_;
v_x_4041_ = v_b_u2081_4046_;
v_x_4042_ = v_b_u2082_4050_;
goto _start;
}
}
}
v___jp_4057_:
{
if (v___y_4063_ == 0)
{
lean_dec(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec(v___y_4058_);
return v___y_4063_;
}
else
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lean_IR_addVarRename(v___y_4058_, v___y_4060_, v___y_4062_);
v_x_4040_ = v___x_4064_;
v_x_4041_ = v___y_4059_;
v_x_4042_ = v___y_4061_;
goto _start;
}
}
v___jp_4066_:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Lean_IR_instBEqIRType_beq(v_ty_u2081_4070_, v_ty_u2082_4074_);
lean_dec(v_ty_u2082_4074_);
lean_dec(v_ty_u2081_4070_);
if (v___x_4076_ == 0)
{
lean_dec(v_x_u2082_4075_);
lean_dec(v_x_u2081_4071_);
v___y_4058_ = v_00_u03c1_4067_;
v___y_4059_ = v_b_u2081_4069_;
v___y_4060_ = v_tgt_u2081_4068_;
v___y_4061_ = v_b_u2082_4073_;
v___y_4062_ = v_tgt_u2082_4072_;
v___y_4063_ = v___x_4076_;
goto v___jp_4057_;
}
else
{
uint8_t v___x_4077_; 
v___x_4077_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_4067_, v_x_u2081_4071_, v_x_u2082_4075_);
lean_dec(v_x_u2082_4075_);
lean_dec(v_x_u2081_4071_);
v___y_4058_ = v_00_u03c1_4067_;
v___y_4059_ = v_b_u2081_4069_;
v___y_4060_ = v_tgt_u2081_4068_;
v___y_4061_ = v_b_u2082_4073_;
v___y_4062_ = v_tgt_u2082_4072_;
v___y_4063_ = v___x_4077_;
goto v___jp_4057_;
}
}
v___jp_4078_:
{
uint8_t v___x_4086_; 
v___x_4086_ = lean_uint64_dec_eq(v_v_u2081_4082_, v_v_u2082_4085_);
if (v___x_4086_ == 0)
{
lean_dec(v_b_u2082_4084_);
lean_dec(v_tgt_u2082_4083_);
lean_dec(v_b_u2081_4081_);
lean_dec(v_tgt_u2081_4080_);
lean_dec(v_00_u03c1_4079_);
return v___x_4086_;
}
else
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_IR_addVarRename(v_00_u03c1_4079_, v_tgt_u2081_4080_, v_tgt_u2082_4083_);
v_x_4040_ = v___x_4087_;
v_x_4041_ = v_b_u2081_4081_;
v_x_4042_ = v_b_u2082_4084_;
goto _start;
}
}
v___jp_4089_:
{
if (v___y_4090_ == 0)
{
if (v___y_4092_ == 0)
{
v_x_4040_ = v___y_4091_;
v_x_4041_ = v___y_4093_;
v_x_4042_ = v___y_4094_;
goto _start;
}
else
{
lean_dec(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec(v___y_4091_);
return v___y_4090_;
}
}
else
{
if (v___y_4092_ == 0)
{
lean_dec(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec(v___y_4091_);
return v___y_4092_;
}
else
{
v_x_4040_ = v___y_4091_;
v_x_4041_ = v___y_4093_;
v_x_4042_ = v___y_4094_;
goto _start;
}
}
}
v___jp_4097_:
{
if (v___y_4105_ == 0)
{
lean_dec(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec(v___y_4101_);
return v___y_4105_;
}
else
{
if (v___y_4104_ == 0)
{
if (v___y_4099_ == 0)
{
v___y_4090_ = v___y_4098_;
v___y_4091_ = v___y_4101_;
v___y_4092_ = v___y_4100_;
v___y_4093_ = v___y_4102_;
v___y_4094_ = v___y_4103_;
goto v___jp_4089_;
}
else
{
lean_dec(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec(v___y_4101_);
return v___y_4104_;
}
}
else
{
if (v___y_4099_ == 0)
{
lean_dec(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec(v___y_4101_);
return v___y_4099_;
}
else
{
v___y_4090_ = v___y_4098_;
v___y_4091_ = v___y_4101_;
v___y_4092_ = v___y_4100_;
v___y_4093_ = v___y_4102_;
v___y_4094_ = v___y_4103_;
goto v___jp_4089_;
}
}
}
}
v___jp_4106_:
{
uint8_t v___x_4118_; 
v___x_4118_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_4107_, v_x_u2081_4108_, v_x_u2082_4113_);
lean_dec(v_x_u2082_4113_);
lean_dec(v_x_u2081_4108_);
if (v___x_4118_ == 0)
{
lean_dec(v_n_u2082_4114_);
lean_dec(v_n_u2081_4109_);
v___y_4098_ = v_p_u2082_4116_;
v___y_4099_ = v_c_u2081_4110_;
v___y_4100_ = v_p_u2081_4111_;
v___y_4101_ = v_00_u03c1_4107_;
v___y_4102_ = v_b_u2081_4112_;
v___y_4103_ = v_b_u2082_4117_;
v___y_4104_ = v_c_u2082_4115_;
v___y_4105_ = v___x_4118_;
goto v___jp_4097_;
}
else
{
uint8_t v___x_4119_; 
v___x_4119_ = lean_nat_dec_eq(v_n_u2081_4109_, v_n_u2082_4114_);
lean_dec(v_n_u2082_4114_);
lean_dec(v_n_u2081_4109_);
v___y_4098_ = v_p_u2082_4116_;
v___y_4099_ = v_c_u2081_4110_;
v___y_4100_ = v_p_u2081_4111_;
v___y_4101_ = v_00_u03c1_4107_;
v___y_4102_ = v_b_u2081_4112_;
v___y_4103_ = v_b_u2082_4117_;
v___y_4104_ = v_c_u2082_4115_;
v___y_4105_ = v___x_4119_;
goto v___jp_4097_;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* v_x_4479_, lean_object* v_xs_4480_, lean_object* v_ys_4481_, lean_object* v_x_4482_){
_start:
{
lean_object* v_zero_4483_; uint8_t v_isZero_4484_; 
v_zero_4483_ = lean_unsigned_to_nat(0u);
v_isZero_4484_ = lean_nat_dec_eq(v_x_4482_, v_zero_4483_);
if (v_isZero_4484_ == 1)
{
lean_dec(v_x_4482_);
lean_dec(v_x_4479_);
return v_isZero_4484_;
}
else
{
lean_object* v_one_4485_; lean_object* v_n_4486_; uint8_t v___y_4488_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_one_4485_ = lean_unsigned_to_nat(1u);
v_n_4486_ = lean_nat_sub(v_x_4482_, v_one_4485_);
lean_dec(v_x_4482_);
v___x_4490_ = lean_array_fget_borrowed(v_xs_4480_, v_n_4486_);
v___x_4491_ = lean_array_fget_borrowed(v_ys_4481_, v_n_4486_);
if (lean_obj_tag(v___x_4490_) == 0)
{
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_info_4492_; lean_object* v_b_4493_; lean_object* v_info_4494_; lean_object* v_b_4495_; uint8_t v___x_4496_; 
v_info_4492_ = lean_ctor_get(v___x_4490_, 0);
v_b_4493_ = lean_ctor_get(v___x_4490_, 1);
v_info_4494_ = lean_ctor_get(v___x_4491_, 0);
v_b_4495_ = lean_ctor_get(v___x_4491_, 1);
v___x_4496_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_4492_, v_info_4494_);
if (v___x_4496_ == 0)
{
v___y_4488_ = v___x_4496_;
goto v___jp_4487_;
}
else
{
uint8_t v___x_4497_; 
lean_inc(v_b_4495_);
lean_inc(v_b_4493_);
lean_inc(v_x_4479_);
v___x_4497_ = l_Lean_IR_FnBody_alphaEqv(v_x_4479_, v_b_4493_, v_b_4495_);
v___y_4488_ = v___x_4497_;
goto v___jp_4487_;
}
}
else
{
lean_dec(v_n_4486_);
lean_dec(v_x_4479_);
return v_isZero_4484_;
}
}
else
{
if (lean_obj_tag(v___x_4491_) == 1)
{
lean_object* v_b_4498_; lean_object* v_b_4499_; uint8_t v___x_4500_; 
v_b_4498_ = lean_ctor_get(v___x_4490_, 0);
v_b_4499_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_b_4499_);
lean_inc(v_b_4498_);
lean_inc(v_x_4479_);
v___x_4500_ = l_Lean_IR_FnBody_alphaEqv(v_x_4479_, v_b_4498_, v_b_4499_);
v___y_4488_ = v___x_4500_;
goto v___jp_4487_;
}
else
{
lean_dec(v_n_4486_);
lean_dec(v_x_4479_);
return v_isZero_4484_;
}
}
v___jp_4487_:
{
if (v___y_4488_ == 0)
{
lean_dec(v_n_4486_);
lean_dec(v_x_4479_);
return v___y_4488_;
}
else
{
v_x_4482_ = v_n_4486_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* v_x_4501_, lean_object* v_xs_4502_, lean_object* v_ys_4503_, lean_object* v_x_4504_){
_start:
{
uint8_t v_res_4505_; lean_object* v_r_4506_; 
v_res_4505_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_4501_, v_xs_4502_, v_ys_4503_, v_x_4504_);
lean_dec_ref(v_ys_4503_);
lean_dec_ref(v_xs_4502_);
v_r_4506_ = lean_box(v_res_4505_);
return v_r_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* v_x_4507_, lean_object* v_x_4508_, lean_object* v_x_4509_){
_start:
{
uint8_t v_res_4510_; lean_object* v_r_4511_; 
v_res_4510_ = l_Lean_IR_FnBody_alphaEqv(v_x_4507_, v_x_4508_, v_x_4509_);
v_r_4511_ = lean_box(v_res_4510_);
return v_r_4511_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object* v_x_4512_, lean_object* v_xs_4513_, lean_object* v_ys_4514_, lean_object* v_hsz_4515_, lean_object* v_x_4516_, lean_object* v_x_4517_){
_start:
{
uint8_t v___x_4518_; 
v___x_4518_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_4512_, v_xs_4513_, v_ys_4514_, v_x_4516_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* v_x_4519_, lean_object* v_xs_4520_, lean_object* v_ys_4521_, lean_object* v_hsz_4522_, lean_object* v_x_4523_, lean_object* v_x_4524_){
_start:
{
uint8_t v_res_4525_; lean_object* v_r_4526_; 
v_res_4525_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(v_x_4519_, v_xs_4520_, v_ys_4521_, v_hsz_4522_, v_x_4523_, v_x_4524_);
lean_dec_ref(v_ys_4521_);
lean_dec_ref(v_xs_4520_);
v_r_4526_ = lean_box(v_res_4525_);
return v_r_4526_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* v_b_u2081_4527_, lean_object* v_b_u2082_4528_){
_start:
{
lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4529_ = lean_box(1);
v___x_4530_ = l_Lean_IR_FnBody_alphaEqv(v___x_4529_, v_b_u2081_4527_, v_b_u2082_4528_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* v_b_u2081_4531_, lean_object* v_b_u2082_4532_){
_start:
{
uint8_t v_res_4533_; lean_object* v_r_4534_; 
v_res_4533_ = l_Lean_IR_FnBody_beq(v_b_u2081_4531_, v_b_u2082_4532_);
v_r_4534_ = lean_box(v_res_4533_);
return v_r_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* v_x_4555_, lean_object* v_t_4556_, lean_object* v_e_4557_){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4558_ = ((lean_object*)(l_Lean_IR_mkIf___closed__1));
v___x_4559_ = lean_box(1);
v___x_4560_ = ((lean_object*)(l_Lean_IR_mkIf___closed__4));
v___x_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v_e_4557_);
v___x_4562_ = ((lean_object*)(l_Lean_IR_mkIf___closed__7));
v___x_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
lean_ctor_set(v___x_4563_, 1, v_t_4556_);
v___x_4564_ = lean_unsigned_to_nat(2u);
v___x_4565_ = lean_mk_empty_array_with_capacity(v___x_4564_);
v___x_4566_ = lean_array_push(v___x_4565_, v___x_4561_);
v___x_4567_ = lean_array_push(v___x_4566_, v___x_4563_);
v___x_4568_ = lean_alloc_ctor(27, 4, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4558_);
lean_ctor_set(v___x_4568_, 1, v_x_4555_);
lean_ctor_set(v___x_4568_, 2, v___x_4559_);
lean_ctor_set(v___x_4568_, 3, v___x_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* v_t_4575_){
_start:
{
switch(lean_obj_tag(v_t_4575_))
{
case 5:
{
lean_object* v___x_4576_; 
v___x_4576_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__0));
return v___x_4576_;
}
case 3:
{
lean_object* v___x_4577_; 
v___x_4577_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__1));
return v___x_4577_;
}
case 4:
{
lean_object* v___x_4578_; 
v___x_4578_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__2));
return v___x_4578_;
}
case 0:
{
lean_object* v___x_4579_; 
v___x_4579_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__3));
return v___x_4579_;
}
case 9:
{
lean_object* v___x_4580_; 
v___x_4580_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__4));
return v___x_4580_;
}
default: 
{
lean_object* v___x_4581_; 
v___x_4581_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__5));
return v___x_4581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* v_t_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l_Lean_IR_getUnboxOpName(v_t_4582_);
lean_dec(v_t_4582_);
return v_res_4583_;
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
