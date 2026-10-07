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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___impl(lean_object* v_x_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_obj_tag_nat(v_x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorIdx___impl___boxed(lean_object* v_x_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_IR_Expr_ctorIdx___impl(v_x_1055_);
lean_dec_ref(v_x_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___redArg(lean_object* v_t_1057_, lean_object* v_k_1058_){
_start:
{
switch(lean_obj_tag(v_t_1057_))
{
case 0:
{
lean_object* v_i_1059_; lean_object* v_ys_1060_; lean_object* v___x_1061_; 
v_i_1059_ = lean_ctor_get(v_t_1057_, 0);
lean_inc_ref(v_i_1059_);
v_ys_1060_ = lean_ctor_get(v_t_1057_, 1);
lean_inc_ref(v_ys_1060_);
lean_dec_ref_known(v_t_1057_, 2);
v___x_1061_ = lean_apply_2(v_k_1058_, v_i_1059_, v_ys_1060_);
return v___x_1061_;
}
case 2:
{
lean_object* v_x_1062_; lean_object* v_i_1063_; uint8_t v_updtHeader_1064_; lean_object* v_ys_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_x_1062_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_x_1062_);
v_i_1063_ = lean_ctor_get(v_t_1057_, 1);
lean_inc_ref(v_i_1063_);
v_updtHeader_1064_ = lean_ctor_get_uint8(v_t_1057_, sizeof(void*)*3);
v_ys_1065_ = lean_ctor_get(v_t_1057_, 2);
lean_inc_ref(v_ys_1065_);
lean_dec_ref_known(v_t_1057_, 3);
v___x_1066_ = lean_box(v_updtHeader_1064_);
v___x_1067_ = lean_apply_4(v_k_1058_, v_x_1062_, v_i_1063_, v___x_1066_, v_ys_1065_);
return v___x_1067_;
}
case 5:
{
lean_object* v_n_1068_; lean_object* v_offset_1069_; lean_object* v_x_1070_; lean_object* v___x_1071_; 
v_n_1068_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_n_1068_);
v_offset_1069_ = lean_ctor_get(v_t_1057_, 1);
lean_inc(v_offset_1069_);
v_x_1070_ = lean_ctor_get(v_t_1057_, 2);
lean_inc(v_x_1070_);
lean_dec_ref_known(v_t_1057_, 3);
v___x_1071_ = lean_apply_3(v_k_1058_, v_n_1068_, v_offset_1069_, v_x_1070_);
return v___x_1071_;
}
case 6:
{
lean_object* v_c_1072_; lean_object* v_ys_1073_; lean_object* v___x_1074_; 
v_c_1072_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_c_1072_);
v_ys_1073_ = lean_ctor_get(v_t_1057_, 1);
lean_inc_ref(v_ys_1073_);
lean_dec_ref_known(v_t_1057_, 2);
v___x_1074_ = lean_apply_2(v_k_1058_, v_c_1072_, v_ys_1073_);
return v___x_1074_;
}
case 7:
{
lean_object* v_c_1075_; lean_object* v_ys_1076_; lean_object* v___x_1077_; 
v_c_1075_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_c_1075_);
v_ys_1076_ = lean_ctor_get(v_t_1057_, 1);
lean_inc_ref(v_ys_1076_);
lean_dec_ref_known(v_t_1057_, 2);
v___x_1077_ = lean_apply_2(v_k_1058_, v_c_1075_, v_ys_1076_);
return v___x_1077_;
}
case 8:
{
lean_object* v_x_1078_; lean_object* v_ys_1079_; lean_object* v___x_1080_; 
v_x_1078_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_x_1078_);
v_ys_1079_ = lean_ctor_get(v_t_1057_, 1);
lean_inc_ref(v_ys_1079_);
lean_dec_ref_known(v_t_1057_, 2);
v___x_1080_ = lean_apply_2(v_k_1058_, v_x_1078_, v_ys_1079_);
return v___x_1080_;
}
case 10:
{
lean_object* v_x_1081_; lean_object* v___x_1082_; 
v_x_1081_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_x_1081_);
lean_dec_ref_known(v_t_1057_, 1);
v___x_1082_ = lean_apply_1(v_k_1058_, v_x_1081_);
return v___x_1082_;
}
case 11:
{
lean_object* v_v_1083_; lean_object* v___x_1084_; 
v_v_1083_ = lean_ctor_get(v_t_1057_, 0);
lean_inc_ref(v_v_1083_);
lean_dec_ref_known(v_t_1057_, 1);
v___x_1084_ = lean_apply_1(v_k_1058_, v_v_1083_);
return v___x_1084_;
}
case 12:
{
lean_object* v_x_1085_; lean_object* v___x_1086_; 
v_x_1085_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_x_1085_);
lean_dec_ref_known(v_t_1057_, 1);
v___x_1086_ = lean_apply_1(v_k_1058_, v_x_1085_);
return v___x_1086_;
}
default: 
{
lean_object* v_n_1087_; lean_object* v_x_1088_; lean_object* v___x_1089_; 
v_n_1087_ = lean_ctor_get(v_t_1057_, 0);
lean_inc(v_n_1087_);
v_x_1088_ = lean_ctor_get(v_t_1057_, 1);
lean_inc(v_x_1088_);
lean_dec_ref(v_t_1057_);
v___x_1089_ = lean_apply_2(v_k_1058_, v_n_1087_, v_x_1088_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim(lean_object* v_motive_1090_, lean_object* v_ctorIdx_1091_, lean_object* v_t_1092_, lean_object* v_h_1093_, lean_object* v_k_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1092_, v_k_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctorElim___boxed(lean_object* v_motive_1096_, lean_object* v_ctorIdx_1097_, lean_object* v_t_1098_, lean_object* v_h_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_IR_Expr_ctorElim(v_motive_1096_, v_ctorIdx_1097_, v_t_1098_, v_h_1099_, v_k_1100_);
lean_dec(v_ctorIdx_1097_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim___redArg(lean_object* v_t_1102_, lean_object* v_ctor_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1102_, v_ctor_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ctor_elim(lean_object* v_motive_1105_, lean_object* v_t_1106_, lean_object* v_h_1107_, lean_object* v_ctor_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1106_, v_ctor_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim___redArg(lean_object* v_t_1110_, lean_object* v_reset_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1110_, v_reset_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reset_elim(lean_object* v_motive_1113_, lean_object* v_t_1114_, lean_object* v_h_1115_, lean_object* v_reset_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1114_, v_reset_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim___redArg(lean_object* v_t_1118_, lean_object* v_reuse_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1118_, v_reuse_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_reuse_elim(lean_object* v_motive_1121_, lean_object* v_t_1122_, lean_object* v_h_1123_, lean_object* v_reuse_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1122_, v_reuse_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim___redArg(lean_object* v_t_1126_, lean_object* v_proj_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1126_, v_proj_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_proj_elim(lean_object* v_motive_1129_, lean_object* v_t_1130_, lean_object* v_h_1131_, lean_object* v_proj_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1130_, v_proj_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim___redArg(lean_object* v_t_1134_, lean_object* v_uproj_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1134_, v_uproj_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_uproj_elim(lean_object* v_motive_1137_, lean_object* v_t_1138_, lean_object* v_h_1139_, lean_object* v_uproj_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1138_, v_uproj_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim___redArg(lean_object* v_t_1142_, lean_object* v_sproj_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1142_, v_sproj_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_sproj_elim(lean_object* v_motive_1145_, lean_object* v_t_1146_, lean_object* v_h_1147_, lean_object* v_sproj_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1146_, v_sproj_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim___redArg(lean_object* v_t_1150_, lean_object* v_fap_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1150_, v_fap_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_fap_elim(lean_object* v_motive_1153_, lean_object* v_t_1154_, lean_object* v_h_1155_, lean_object* v_fap_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1154_, v_fap_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim___redArg(lean_object* v_t_1158_, lean_object* v_pap_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1158_, v_pap_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_pap_elim(lean_object* v_motive_1161_, lean_object* v_t_1162_, lean_object* v_h_1163_, lean_object* v_pap_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1162_, v_pap_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim___redArg(lean_object* v_t_1166_, lean_object* v_ap_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1166_, v_ap_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_ap_elim(lean_object* v_motive_1169_, lean_object* v_t_1170_, lean_object* v_h_1171_, lean_object* v_ap_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1170_, v_ap_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim___redArg(lean_object* v_t_1174_, lean_object* v_box_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1174_, v_box_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_box_elim(lean_object* v_motive_1177_, lean_object* v_t_1178_, lean_object* v_h_1179_, lean_object* v_box_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1178_, v_box_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim___redArg(lean_object* v_t_1182_, lean_object* v_unbox_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1182_, v_unbox_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_unbox_elim(lean_object* v_motive_1185_, lean_object* v_t_1186_, lean_object* v_h_1187_, lean_object* v_unbox_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1186_, v_unbox_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim___redArg(lean_object* v_t_1190_, lean_object* v_lit_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1190_, v_lit_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_lit_elim(lean_object* v_motive_1193_, lean_object* v_t_1194_, lean_object* v_h_1195_, lean_object* v_lit_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1194_, v_lit_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim___redArg(lean_object* v_t_1198_, lean_object* v_isShared_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1198_, v_isShared_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_isShared_elim(lean_object* v_motive_1201_, lean_object* v_t_1202_, lean_object* v_h_1203_, lean_object* v_isShared_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_1202_, v_isShared_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(5u);
v___x_1229_ = lean_nat_to_int(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(10u);
v___x_1234_ = lean_nat_to_int(v___x_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_IR_instReprParam_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_unsigned_to_nat(6u);
v___x_1239_ = lean_nat_to_int(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___redArg(lean_object* v_x_1240_){
_start:
{
lean_object* v_x_1241_; uint8_t v_borrow_1242_; lean_object* v_ty_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_x_1241_ = lean_ctor_get(v_x_1240_, 0);
lean_inc(v_x_1241_);
v_borrow_1242_ = lean_ctor_get_uint8(v_x_1240_, sizeof(void*)*2);
v_ty_1243_ = lean_ctor_get(v_x_1240_, 1);
lean_inc(v_ty_1243_);
lean_dec_ref(v_x_1240_);
v___x_1244_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__5));
v___x_1245_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__3));
v___x_1246_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__4, &l_Lean_IR_instReprParam_repr___redArg___closed__4_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__4);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_1241_);
v___x_1249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = 0;
v___x_1251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1250_);
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1245_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2));
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = lean_box(1);
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__6));
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1244_);
v___x_1260_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__7, &l_Lean_IR_instReprParam_repr___redArg___closed__7_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__7);
v___x_1261_ = l_Bool_repr___redArg(v_borrow_1242_);
v___x_1262_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*1, v___x_1250_);
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1259_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___x_1253_);
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1255_);
v___x_1267_ = ((lean_object*)(l_Lean_IR_instReprParam_repr___redArg___closed__9));
v___x_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1244_);
v___x_1270_ = lean_obj_once(&l_Lean_IR_instReprParam_repr___redArg___closed__10, &l_Lean_IR_instReprParam_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprParam_repr___redArg___closed__10);
v___x_1271_ = l_Lean_IR_instReprIRType_repr(v_ty_1243_, v___x_1247_);
v___x_1272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*1, v___x_1250_);
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1269_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_obj_once(&l_Lean_IR_instReprVarId_repr___redArg___closed__10, &l_Lean_IR_instReprVarId_repr___redArg___closed__10_once, _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10);
v___x_1276_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__11));
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___x_1274_);
v___x_1278_ = ((lean_object*)(l_Lean_IR_instReprVarId_repr___redArg___closed__12));
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1275_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*1, v___x_1250_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr(lean_object* v_x_1282_, lean_object* v_prec_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_IR_instReprParam_repr___redArg(v_x_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam_repr___boxed(lean_object* v_x_1285_, lean_object* v_prec_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_IR_instReprParam_repr(v_x_1285_, v_prec_1286_);
lean_dec(v_prec_1286_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___impl(lean_object* v_x_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_obj_tag_nat(v_x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorIdx___impl___boxed(lean_object* v_x_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_IR_Alt_ctorIdx___impl(v_x_1292_);
lean_dec_ref(v_x_1292_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___redArg(lean_object* v_t_1294_, lean_object* v_k_1295_){
_start:
{
if (lean_obj_tag(v_t_1294_) == 0)
{
lean_object* v_info_1296_; lean_object* v_b_1297_; lean_object* v___x_1298_; 
v_info_1296_ = lean_ctor_get(v_t_1294_, 0);
lean_inc_ref(v_info_1296_);
v_b_1297_ = lean_ctor_get(v_t_1294_, 1);
lean_inc(v_b_1297_);
lean_dec_ref_known(v_t_1294_, 2);
v___x_1298_ = lean_apply_2(v_k_1295_, v_info_1296_, v_b_1297_);
return v___x_1298_;
}
else
{
lean_object* v_b_1299_; lean_object* v___x_1300_; 
v_b_1299_ = lean_ctor_get(v_t_1294_, 0);
lean_inc(v_b_1299_);
lean_dec_ref_known(v_t_1294_, 1);
v___x_1300_ = lean_apply_1(v_k_1295_, v_b_1299_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim(lean_object* v_motive__1_1301_, lean_object* v_ctorIdx_1302_, lean_object* v_t_1303_, lean_object* v_h_1304_, lean_object* v_k_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1303_, v_k_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctorElim___boxed(lean_object* v_motive__1_1307_, lean_object* v_ctorIdx_1308_, lean_object* v_t_1309_, lean_object* v_h_1310_, lean_object* v_k_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_IR_Alt_ctorElim(v_motive__1_1307_, v_ctorIdx_1308_, v_t_1309_, v_h_1310_, v_k_1311_);
lean_dec(v_ctorIdx_1308_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim___redArg(lean_object* v_t_1313_, lean_object* v_ctor_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1313_, v_ctor_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor_elim(lean_object* v_motive__1_1316_, lean_object* v_t_1317_, lean_object* v_h_1318_, lean_object* v_ctor_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1317_, v_ctor_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim___redArg(lean_object* v_t_1321_, lean_object* v_default_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1321_, v_default_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default_elim(lean_object* v_motive__1_1324_, lean_object* v_t_1325_, lean_object* v_h_1326_, lean_object* v_default_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_1325_, v_default_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___impl(lean_object* v_x_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_obj_tag_nat(v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorIdx___impl___boxed(lean_object* v_x_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_IR_FnBody_ctorIdx___impl(v_x_1331_);
lean_dec(v_x_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___redArg(lean_object* v_t_1333_, lean_object* v_k_1334_){
_start:
{
switch(lean_obj_tag(v_t_1333_))
{
case 0:
{
lean_object* v_x_1335_; lean_object* v_ty_1336_; lean_object* v_e_1337_; lean_object* v_b_1338_; lean_object* v___x_1339_; 
v_x_1335_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1335_);
v_ty_1336_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_ty_1336_);
v_e_1337_ = lean_ctor_get(v_t_1333_, 2);
lean_inc_ref(v_e_1337_);
v_b_1338_ = lean_ctor_get(v_t_1333_, 3);
lean_inc(v_b_1338_);
lean_dec_ref_known(v_t_1333_, 4);
v___x_1339_ = lean_apply_4(v_k_1334_, v_x_1335_, v_ty_1336_, v_e_1337_, v_b_1338_);
return v___x_1339_;
}
case 1:
{
lean_object* v_j_1340_; lean_object* v_xs_1341_; lean_object* v_v_1342_; lean_object* v_b_1343_; lean_object* v___x_1344_; 
v_j_1340_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_j_1340_);
v_xs_1341_ = lean_ctor_get(v_t_1333_, 1);
lean_inc_ref(v_xs_1341_);
v_v_1342_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_v_1342_);
v_b_1343_ = lean_ctor_get(v_t_1333_, 3);
lean_inc(v_b_1343_);
lean_dec_ref_known(v_t_1333_, 4);
v___x_1344_ = lean_apply_4(v_k_1334_, v_j_1340_, v_xs_1341_, v_v_1342_, v_b_1343_);
return v___x_1344_;
}
case 3:
{
lean_object* v_x_1345_; lean_object* v_cidx_1346_; lean_object* v_b_1347_; lean_object* v___x_1348_; 
v_x_1345_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1345_);
v_cidx_1346_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_cidx_1346_);
v_b_1347_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_b_1347_);
lean_dec_ref_known(v_t_1333_, 3);
v___x_1348_ = lean_apply_3(v_k_1334_, v_x_1345_, v_cidx_1346_, v_b_1347_);
return v___x_1348_;
}
case 5:
{
lean_object* v_x_1349_; lean_object* v_i_1350_; lean_object* v_offset_1351_; lean_object* v_y_1352_; lean_object* v_ty_1353_; lean_object* v_b_1354_; lean_object* v___x_1355_; 
v_x_1349_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1349_);
v_i_1350_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_i_1350_);
v_offset_1351_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_offset_1351_);
v_y_1352_ = lean_ctor_get(v_t_1333_, 3);
lean_inc(v_y_1352_);
v_ty_1353_ = lean_ctor_get(v_t_1333_, 4);
lean_inc(v_ty_1353_);
v_b_1354_ = lean_ctor_get(v_t_1333_, 5);
lean_inc(v_b_1354_);
lean_dec_ref_known(v_t_1333_, 6);
v___x_1355_ = lean_apply_6(v_k_1334_, v_x_1349_, v_i_1350_, v_offset_1351_, v_y_1352_, v_ty_1353_, v_b_1354_);
return v___x_1355_;
}
case 6:
{
lean_object* v_x_1356_; lean_object* v_n_1357_; uint8_t v_c_1358_; uint8_t v_persistent_1359_; lean_object* v_b_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_x_1356_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1356_);
v_n_1357_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_n_1357_);
v_c_1358_ = lean_ctor_get_uint8(v_t_1333_, sizeof(void*)*3);
v_persistent_1359_ = lean_ctor_get_uint8(v_t_1333_, sizeof(void*)*3 + 1);
v_b_1360_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_b_1360_);
lean_dec_ref_known(v_t_1333_, 3);
v___x_1361_ = lean_box(v_c_1358_);
v___x_1362_ = lean_box(v_persistent_1359_);
v___x_1363_ = lean_apply_5(v_k_1334_, v_x_1356_, v_n_1357_, v___x_1361_, v___x_1362_, v_b_1360_);
return v___x_1363_;
}
case 7:
{
lean_object* v_x_1364_; lean_object* v_n_1365_; uint8_t v_c_1366_; uint8_t v_persistent_1367_; lean_object* v_b_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_x_1364_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1364_);
v_n_1365_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_n_1365_);
v_c_1366_ = lean_ctor_get_uint8(v_t_1333_, sizeof(void*)*3);
v_persistent_1367_ = lean_ctor_get_uint8(v_t_1333_, sizeof(void*)*3 + 1);
v_b_1368_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_b_1368_);
lean_dec_ref_known(v_t_1333_, 3);
v___x_1369_ = lean_box(v_c_1366_);
v___x_1370_ = lean_box(v_persistent_1367_);
v___x_1371_ = lean_apply_5(v_k_1334_, v_x_1364_, v_n_1365_, v___x_1369_, v___x_1370_, v_b_1368_);
return v___x_1371_;
}
case 8:
{
lean_object* v_x_1372_; lean_object* v_b_1373_; lean_object* v___x_1374_; 
v_x_1372_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1372_);
v_b_1373_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_b_1373_);
lean_dec_ref_known(v_t_1333_, 2);
v___x_1374_ = lean_apply_2(v_k_1334_, v_x_1372_, v_b_1373_);
return v___x_1374_;
}
case 9:
{
lean_object* v_tid_1375_; lean_object* v_x_1376_; lean_object* v_xType_1377_; lean_object* v_cs_1378_; lean_object* v___x_1379_; 
v_tid_1375_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_tid_1375_);
v_x_1376_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_x_1376_);
v_xType_1377_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_xType_1377_);
v_cs_1378_ = lean_ctor_get(v_t_1333_, 3);
lean_inc_ref(v_cs_1378_);
lean_dec_ref_known(v_t_1333_, 4);
v___x_1379_ = lean_apply_4(v_k_1334_, v_tid_1375_, v_x_1376_, v_xType_1377_, v_cs_1378_);
return v___x_1379_;
}
case 10:
{
lean_object* v_x_1380_; lean_object* v___x_1381_; 
v_x_1380_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1380_);
lean_dec_ref_known(v_t_1333_, 1);
v___x_1381_ = lean_apply_1(v_k_1334_, v_x_1380_);
return v___x_1381_;
}
case 11:
{
lean_object* v_j_1382_; lean_object* v_ys_1383_; lean_object* v___x_1384_; 
v_j_1382_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_j_1382_);
v_ys_1383_ = lean_ctor_get(v_t_1333_, 1);
lean_inc_ref(v_ys_1383_);
lean_dec_ref_known(v_t_1333_, 2);
v___x_1384_ = lean_apply_2(v_k_1334_, v_j_1382_, v_ys_1383_);
return v___x_1384_;
}
case 12:
{
return v_k_1334_;
}
default: 
{
lean_object* v_x_1385_; lean_object* v_i_1386_; lean_object* v_y_1387_; lean_object* v_b_1388_; lean_object* v___x_1389_; 
v_x_1385_ = lean_ctor_get(v_t_1333_, 0);
lean_inc(v_x_1385_);
v_i_1386_ = lean_ctor_get(v_t_1333_, 1);
lean_inc(v_i_1386_);
v_y_1387_ = lean_ctor_get(v_t_1333_, 2);
lean_inc(v_y_1387_);
v_b_1388_ = lean_ctor_get(v_t_1333_, 3);
lean_inc(v_b_1388_);
lean_dec(v_t_1333_);
v___x_1389_ = lean_apply_4(v_k_1334_, v_x_1385_, v_i_1386_, v_y_1387_, v_b_1388_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim(lean_object* v_motive__2_1390_, lean_object* v_ctorIdx_1391_, lean_object* v_t_1392_, lean_object* v_h_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1392_, v_k_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ctorElim___boxed(lean_object* v_motive__2_1396_, lean_object* v_ctorIdx_1397_, lean_object* v_t_1398_, lean_object* v_h_1399_, lean_object* v_k_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_IR_FnBody_ctorElim(v_motive__2_1396_, v_ctorIdx_1397_, v_t_1398_, v_h_1399_, v_k_1400_);
lean_dec(v_ctorIdx_1397_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim___redArg(lean_object* v_t_1402_, lean_object* v_vdecl_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1402_, v_vdecl_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_vdecl_elim(lean_object* v_motive__2_1405_, lean_object* v_t_1406_, lean_object* v_h_1407_, lean_object* v_vdecl_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1406_, v_vdecl_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim___redArg(lean_object* v_t_1410_, lean_object* v_jdecl_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1410_, v_jdecl_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jdecl_elim(lean_object* v_motive__2_1413_, lean_object* v_t_1414_, lean_object* v_h_1415_, lean_object* v_jdecl_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1414_, v_jdecl_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim___redArg(lean_object* v_t_1418_, lean_object* v_set_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1418_, v_set_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_set_elim(lean_object* v_motive__2_1421_, lean_object* v_t_1422_, lean_object* v_h_1423_, lean_object* v_set_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1422_, v_set_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim___redArg(lean_object* v_t_1426_, lean_object* v_setTag_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1426_, v_setTag_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setTag_elim(lean_object* v_motive__2_1429_, lean_object* v_t_1430_, lean_object* v_h_1431_, lean_object* v_setTag_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1430_, v_setTag_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim___redArg(lean_object* v_t_1434_, lean_object* v_uset_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1434_, v_uset_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_uset_elim(lean_object* v_motive__2_1437_, lean_object* v_t_1438_, lean_object* v_h_1439_, lean_object* v_uset_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1438_, v_uset_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim___redArg(lean_object* v_t_1442_, lean_object* v_sset_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1442_, v_sset_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_sset_elim(lean_object* v_motive__2_1445_, lean_object* v_t_1446_, lean_object* v_h_1447_, lean_object* v_sset_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1446_, v_sset_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim___redArg(lean_object* v_t_1450_, lean_object* v_inc_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1450_, v_inc_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_inc_elim(lean_object* v_motive__2_1453_, lean_object* v_t_1454_, lean_object* v_h_1455_, lean_object* v_inc_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1454_, v_inc_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim___redArg(lean_object* v_t_1458_, lean_object* v_dec_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1458_, v_dec_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_dec_elim(lean_object* v_motive__2_1461_, lean_object* v_t_1462_, lean_object* v_h_1463_, lean_object* v_dec_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1462_, v_dec_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim___redArg(lean_object* v_t_1466_, lean_object* v_del_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1466_, v_del_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_del_elim(lean_object* v_motive__2_1469_, lean_object* v_t_1470_, lean_object* v_h_1471_, lean_object* v_del_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1470_, v_del_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim___redArg(lean_object* v_t_1474_, lean_object* v_case_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1474_, v_case_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_case_elim(lean_object* v_motive__2_1477_, lean_object* v_t_1478_, lean_object* v_h_1479_, lean_object* v_case_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1478_, v_case_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim___redArg(lean_object* v_t_1482_, lean_object* v_ret_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1482_, v_ret_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_ret_elim(lean_object* v_motive__2_1485_, lean_object* v_t_1486_, lean_object* v_h_1487_, lean_object* v_ret_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1486_, v_ret_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim___redArg(lean_object* v_t_1490_, lean_object* v_jmp_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1490_, v_jmp_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_jmp_elim(lean_object* v_motive__2_1493_, lean_object* v_t_1494_, lean_object* v_h_1495_, lean_object* v_jmp_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1494_, v_jmp_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim___redArg(lean_object* v_t_1498_, lean_object* v_unreachable_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1498_, v_unreachable_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_unreachable_elim(lean_object* v_motive__2_1501_, lean_object* v_t_1502_, lean_object* v_h_1503_, lean_object* v_unreachable_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_1502_, v_unreachable_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_IR_FnBody_nil(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_box(12);
return v___x_1520_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* v_x_1521_){
_start:
{
switch(lean_obj_tag(v_x_1521_))
{
case 9:
{
uint8_t v___x_1522_; 
v___x_1522_ = 1;
return v___x_1522_;
}
case 10:
{
uint8_t v___x_1523_; 
v___x_1523_ = 1;
return v___x_1523_;
}
case 11:
{
uint8_t v___x_1524_; 
v___x_1524_ = 1;
return v___x_1524_;
}
case 12:
{
uint8_t v___x_1525_; 
v___x_1525_ = 1;
return v___x_1525_;
}
default: 
{
uint8_t v___x_1526_; 
v___x_1526_ = 0;
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object* v_x_1527_){
_start:
{
uint8_t v_res_1528_; lean_object* v_r_1529_; 
v_res_1528_ = l_Lean_IR_FnBody_isTerminal(v_x_1527_);
lean_dec(v_x_1527_);
v_r_1529_ = lean_box(v_res_1528_);
return v_r_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object* v_x_1530_){
_start:
{
switch(lean_obj_tag(v_x_1530_))
{
case 0:
{
lean_object* v_b_1531_; 
v_b_1531_ = lean_ctor_get(v_x_1530_, 3);
lean_inc(v_b_1531_);
return v_b_1531_;
}
case 1:
{
lean_object* v_b_1532_; 
v_b_1532_ = lean_ctor_get(v_x_1530_, 3);
lean_inc(v_b_1532_);
return v_b_1532_;
}
case 2:
{
lean_object* v_b_1533_; 
v_b_1533_ = lean_ctor_get(v_x_1530_, 3);
lean_inc(v_b_1533_);
return v_b_1533_;
}
case 4:
{
lean_object* v_b_1534_; 
v_b_1534_ = lean_ctor_get(v_x_1530_, 3);
lean_inc(v_b_1534_);
return v_b_1534_;
}
case 5:
{
lean_object* v_b_1535_; 
v_b_1535_ = lean_ctor_get(v_x_1530_, 5);
lean_inc(v_b_1535_);
return v_b_1535_;
}
case 3:
{
lean_object* v_b_1536_; 
v_b_1536_ = lean_ctor_get(v_x_1530_, 2);
lean_inc(v_b_1536_);
return v_b_1536_;
}
case 6:
{
lean_object* v_b_1537_; 
v_b_1537_ = lean_ctor_get(v_x_1530_, 2);
lean_inc(v_b_1537_);
return v_b_1537_;
}
case 7:
{
lean_object* v_b_1538_; 
v_b_1538_ = lean_ctor_get(v_x_1530_, 2);
lean_inc(v_b_1538_);
return v_b_1538_;
}
case 8:
{
lean_object* v_b_1539_; 
v_b_1539_ = lean_ctor_get(v_x_1530_, 1);
lean_inc(v_b_1539_);
return v_b_1539_;
}
default: 
{
lean_inc(v_x_1530_);
return v_x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* v_x_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_IR_FnBody_body(v_x_1540_);
lean_dec(v_x_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
switch(lean_obj_tag(v_x_1542_))
{
case 0:
{
lean_object* v_x_1544_; lean_object* v_ty_1545_; lean_object* v_e_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_x_1544_ = lean_ctor_get(v_x_1542_, 0);
v_ty_1545_ = lean_ctor_get(v_x_1542_, 1);
v_e_1546_ = lean_ctor_get(v_x_1542_, 2);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_x_1542_, 3);
lean_dec(v_unused_1554_);
v___x_1548_ = v_x_1542_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_e_1546_);
lean_inc(v_ty_1545_);
lean_inc(v_x_1544_);
lean_dec(v_x_1542_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 3, v_x_1543_);
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_x_1544_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_ty_1545_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_e_1546_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_x_1543_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
case 1:
{
lean_object* v_j_1555_; lean_object* v_xs_1556_; lean_object* v_v_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_j_1555_ = lean_ctor_get(v_x_1542_, 0);
v_xs_1556_ = lean_ctor_get(v_x_1542_, 1);
v_v_1557_ = lean_ctor_get(v_x_1542_, 2);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v_x_1542_, 3);
lean_dec(v_unused_1565_);
v___x_1559_ = v_x_1542_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_v_1557_);
lean_inc(v_xs_1556_);
lean_inc(v_j_1555_);
lean_dec(v_x_1542_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 3, v_x_1543_);
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_j_1555_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_xs_1556_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1557_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_x_1543_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
case 2:
{
lean_object* v_x_1566_; lean_object* v_i_1567_; lean_object* v_y_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_x_1566_ = lean_ctor_get(v_x_1542_, 0);
v_i_1567_ = lean_ctor_get(v_x_1542_, 1);
v_y_1568_ = lean_ctor_get(v_x_1542_, 2);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_x_1542_, 3);
lean_dec(v_unused_1576_);
v___x_1570_ = v_x_1542_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_y_1568_);
lean_inc(v_i_1567_);
lean_inc(v_x_1566_);
lean_dec(v_x_1542_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 3, v_x_1543_);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_x_1566_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_i_1567_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_y_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_x_1543_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
case 4:
{
lean_object* v_x_1577_; lean_object* v_i_1578_; lean_object* v_y_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_x_1577_ = lean_ctor_get(v_x_1542_, 0);
v_i_1578_ = lean_ctor_get(v_x_1542_, 1);
v_y_1579_ = lean_ctor_get(v_x_1542_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v_x_1542_, 3);
lean_dec(v_unused_1587_);
v___x_1581_ = v_x_1542_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_y_1579_);
lean_inc(v_i_1578_);
lean_inc(v_x_1577_);
lean_dec(v_x_1542_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 3, v_x_1543_);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_x_1577_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_i_1578_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_y_1579_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_x_1543_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
case 5:
{
lean_object* v_x_1588_; lean_object* v_i_1589_; lean_object* v_offset_1590_; lean_object* v_y_1591_; lean_object* v_ty_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_x_1588_ = lean_ctor_get(v_x_1542_, 0);
v_i_1589_ = lean_ctor_get(v_x_1542_, 1);
v_offset_1590_ = lean_ctor_get(v_x_1542_, 2);
v_y_1591_ = lean_ctor_get(v_x_1542_, 3);
v_ty_1592_ = lean_ctor_get(v_x_1542_, 4);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_x_1542_, 5);
lean_dec(v_unused_1600_);
v___x_1594_ = v_x_1542_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_ty_1592_);
lean_inc(v_y_1591_);
lean_inc(v_offset_1590_);
lean_inc(v_i_1589_);
lean_inc(v_x_1588_);
lean_dec(v_x_1542_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 5, v_x_1543_);
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_x_1588_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_i_1589_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_offset_1590_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v_y_1591_);
lean_ctor_set(v_reuseFailAlloc_1598_, 4, v_ty_1592_);
lean_ctor_set(v_reuseFailAlloc_1598_, 5, v_x_1543_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
case 3:
{
lean_object* v_x_1601_; lean_object* v_cidx_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_x_1601_ = lean_ctor_get(v_x_1542_, 0);
v_cidx_1602_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v_x_1542_, 2);
lean_dec(v_unused_1610_);
v___x_1604_ = v_x_1542_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_cidx_1602_);
lean_inc(v_x_1601_);
lean_dec(v_x_1542_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 2, v_x_1543_);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_x_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_cidx_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_x_1543_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
case 6:
{
lean_object* v_x_1611_; lean_object* v_n_1612_; uint8_t v_c_1613_; uint8_t v_persistent_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_x_1611_ = lean_ctor_get(v_x_1542_, 0);
v_n_1612_ = lean_ctor_get(v_x_1542_, 1);
v_c_1613_ = lean_ctor_get_uint8(v_x_1542_, sizeof(void*)*3);
v_persistent_1614_ = lean_ctor_get_uint8(v_x_1542_, sizeof(void*)*3 + 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v_x_1542_, 2);
lean_dec(v_unused_1622_);
v___x_1616_ = v_x_1542_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_n_1612_);
lean_inc(v_x_1611_);
lean_dec(v_x_1542_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 2, v_x_1543_);
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_x_1611_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_n_1612_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_x_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*3, v_c_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*3 + 1, v_persistent_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
case 7:
{
lean_object* v_x_1623_; lean_object* v_n_1624_; uint8_t v_c_1625_; uint8_t v_persistent_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_x_1623_ = lean_ctor_get(v_x_1542_, 0);
v_n_1624_ = lean_ctor_get(v_x_1542_, 1);
v_c_1625_ = lean_ctor_get_uint8(v_x_1542_, sizeof(void*)*3);
v_persistent_1626_ = lean_ctor_get_uint8(v_x_1542_, sizeof(void*)*3 + 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v_x_1542_, 2);
lean_dec(v_unused_1634_);
v___x_1628_ = v_x_1542_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_n_1624_);
lean_inc(v_x_1623_);
lean_dec(v_x_1542_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 2, v_x_1543_);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_x_1623_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_n_1624_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_x_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1632_, sizeof(void*)*3, v_c_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1632_, sizeof(void*)*3 + 1, v_persistent_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
case 8:
{
lean_object* v_x_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_x_1635_ = lean_ctor_get(v_x_1542_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v_x_1542_, 1);
lean_dec(v_unused_1643_);
v___x_1637_ = v_x_1542_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_x_1635_);
lean_dec(v_x_1542_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 1, v_x_1543_);
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_x_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_x_1543_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
default: 
{
lean_dec(v_x_1543_);
return v_x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object* v_b_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_box(12);
v___x_1646_ = l_Lean_IR_FnBody_setBody(v_b_1644_, v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object* v_b_1647_){
_start:
{
lean_object* v___y_1649_; 
switch(lean_obj_tag(v_b_1647_))
{
case 0:
{
lean_object* v_b_1653_; 
v_b_1653_ = lean_ctor_get(v_b_1647_, 3);
lean_inc(v_b_1653_);
v___y_1649_ = v_b_1653_;
goto v___jp_1648_;
}
case 1:
{
lean_object* v_b_1654_; 
v_b_1654_ = lean_ctor_get(v_b_1647_, 3);
lean_inc(v_b_1654_);
v___y_1649_ = v_b_1654_;
goto v___jp_1648_;
}
case 2:
{
lean_object* v_b_1655_; 
v_b_1655_ = lean_ctor_get(v_b_1647_, 3);
lean_inc(v_b_1655_);
v___y_1649_ = v_b_1655_;
goto v___jp_1648_;
}
case 4:
{
lean_object* v_b_1656_; 
v_b_1656_ = lean_ctor_get(v_b_1647_, 3);
lean_inc(v_b_1656_);
v___y_1649_ = v_b_1656_;
goto v___jp_1648_;
}
case 5:
{
lean_object* v_b_1657_; 
v_b_1657_ = lean_ctor_get(v_b_1647_, 5);
lean_inc(v_b_1657_);
v___y_1649_ = v_b_1657_;
goto v___jp_1648_;
}
case 3:
{
lean_object* v_b_1658_; 
v_b_1658_ = lean_ctor_get(v_b_1647_, 2);
lean_inc(v_b_1658_);
v___y_1649_ = v_b_1658_;
goto v___jp_1648_;
}
case 6:
{
lean_object* v_b_1659_; 
v_b_1659_ = lean_ctor_get(v_b_1647_, 2);
lean_inc(v_b_1659_);
v___y_1649_ = v_b_1659_;
goto v___jp_1648_;
}
case 7:
{
lean_object* v_b_1660_; 
v_b_1660_ = lean_ctor_get(v_b_1647_, 2);
lean_inc(v_b_1660_);
v___y_1649_ = v_b_1660_;
goto v___jp_1648_;
}
case 8:
{
lean_object* v_b_1661_; 
v_b_1661_ = lean_ctor_get(v_b_1647_, 1);
lean_inc(v_b_1661_);
v___y_1649_ = v_b_1661_;
goto v___jp_1648_;
}
default: 
{
lean_inc(v_b_1647_);
v___y_1649_ = v_b_1647_;
goto v___jp_1648_;
}
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v_c_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_box(12);
v_c_1651_ = l_Lean_IR_FnBody_setBody(v_b_1647_, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_c_1651_);
lean_ctor_set(v___x_1652_, 1, v___y_1649_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v_b_1663_; 
v_b_1663_ = lean_ctor_get(v_x_1662_, 1);
lean_inc(v_b_1663_);
return v_b_1663_;
}
else
{
lean_object* v_b_1664_; 
v_b_1664_ = lean_ctor_get(v_x_1662_, 0);
lean_inc(v_b_1664_);
return v_b_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_IR_Alt_body(v_x_1665_);
lean_dec_ref(v_x_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v_info_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_info_1669_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_x_1667_, 1);
lean_dec(v_unused_1677_);
v___x_1671_ = v_x_1667_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_info_1669_);
lean_dec(v_x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v_x_1668_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_info_1669_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_x_1668_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_x_1667_, 0);
lean_dec(v_unused_1685_);
v___x_1679_ = v_x_1667_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v_x_1667_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v_x_1668_);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_x_1668_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object* v_f_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_object* v_info_1688_; lean_object* v_b_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
v_info_1688_ = lean_ctor_get(v_x_1687_, 0);
v_b_1689_ = lean_ctor_get(v_x_1687_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v_x_1687_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_b_1689_);
lean_inc(v_info_1688_);
lean_dec(v_x_1687_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1693_ = lean_apply_1(v_f_1686_, v_b_1689_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v___x_1693_);
v___x_1695_ = v___x_1691_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_info_1688_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_b_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_b_1698_ = lean_ctor_get(v_x_1687_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v_x_1687_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_b_1698_);
lean_dec(v_x_1687_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_apply_1(v_f_1686_, v_b_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(lean_object* v_info_1707_, lean_object* v_b_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_info_1707_);
lean_ctor_set(v___x_1709_, 1, v_b_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(lean_object* v_b_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_b_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM___redArg(lean_object* v_inst_1713_, lean_object* v_f_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v_toApplicative_1716_; 
v_toApplicative_1716_ = lean_ctor_get(v_inst_1713_, 0);
lean_inc_ref(v_toApplicative_1716_);
lean_dec_ref(v_inst_1713_);
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v_toFunctor_1717_; lean_object* v_info_1718_; lean_object* v_b_1719_; lean_object* v_map_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_toFunctor_1717_ = lean_ctor_get(v_toApplicative_1716_, 0);
lean_inc_ref(v_toFunctor_1717_);
lean_dec_ref(v_toApplicative_1716_);
v_info_1718_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_info_1718_);
v_b_1719_ = lean_ctor_get(v_x_1715_, 1);
lean_inc(v_b_1719_);
lean_dec_ref_known(v_x_1715_, 2);
v_map_1720_ = lean_ctor_get(v_toFunctor_1717_, 0);
lean_inc(v_map_1720_);
lean_dec_ref(v_toFunctor_1717_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1721_, 0, v_info_1718_);
v___x_1722_ = lean_apply_1(v_f_1714_, v_b_1719_);
v___x_1723_ = lean_apply_4(v_map_1720_, lean_box(0), lean_box(0), v___f_1721_, v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v_toFunctor_1724_; lean_object* v_b_1725_; lean_object* v_map_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_toFunctor_1724_ = lean_ctor_get(v_toApplicative_1716_, 0);
lean_inc_ref(v_toFunctor_1724_);
lean_dec_ref(v_toApplicative_1716_);
v_b_1725_ = lean_ctor_get(v_x_1715_, 0);
lean_inc(v_b_1725_);
lean_dec_ref_known(v_x_1715_, 1);
v_map_1726_ = lean_ctor_get(v_toFunctor_1724_, 0);
lean_inc(v_map_1726_);
lean_dec_ref(v_toFunctor_1724_);
v___f_1727_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_1728_ = lean_apply_1(v_f_1714_, v_b_1725_);
v___x_1729_ = lean_apply_4(v_map_1726_, lean_box(0), lean_box(0), v___f_1727_, v___x_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBodyM(lean_object* v_m_1730_, lean_object* v_inst_1731_, lean_object* v_f_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v_toApplicative_1734_; 
v_toApplicative_1734_ = lean_ctor_get(v_inst_1731_, 0);
lean_inc_ref(v_toApplicative_1734_);
lean_dec_ref(v_inst_1731_);
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_object* v_toFunctor_1735_; lean_object* v_info_1736_; lean_object* v_b_1737_; lean_object* v_map_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_toFunctor_1735_ = lean_ctor_get(v_toApplicative_1734_, 0);
lean_inc_ref(v_toFunctor_1735_);
lean_dec_ref(v_toApplicative_1734_);
v_info_1736_ = lean_ctor_get(v_x_1733_, 0);
lean_inc_ref(v_info_1736_);
v_b_1737_ = lean_ctor_get(v_x_1733_, 1);
lean_inc(v_b_1737_);
lean_dec_ref_known(v_x_1733_, 2);
v_map_1738_ = lean_ctor_get(v_toFunctor_1735_, 0);
lean_inc(v_map_1738_);
lean_dec_ref(v_toFunctor_1735_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_IR_Alt_modifyBodyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1739_, 0, v_info_1736_);
v___x_1740_ = lean_apply_1(v_f_1732_, v_b_1737_);
v___x_1741_ = lean_apply_4(v_map_1738_, lean_box(0), lean_box(0), v___f_1739_, v___x_1740_);
return v___x_1741_;
}
else
{
lean_object* v_toFunctor_1742_; lean_object* v_b_1743_; lean_object* v_map_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_toFunctor_1742_ = lean_ctor_get(v_toApplicative_1734_, 0);
lean_inc_ref(v_toFunctor_1742_);
lean_dec_ref(v_toApplicative_1734_);
v_b_1743_ = lean_ctor_get(v_x_1733_, 0);
lean_inc(v_b_1743_);
lean_dec_ref_known(v_x_1733_, 1);
v_map_1744_ = lean_ctor_get(v_toFunctor_1742_, 0);
lean_inc(v_map_1744_);
lean_dec_ref(v_toFunctor_1742_);
v___f_1745_ = ((lean_object*)(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0));
v___x_1746_ = lean_apply_1(v_f_1732_, v_b_1743_);
v___x_1747_ = lean_apply_4(v_map_1744_, lean_box(0), lean_box(0), v___f_1745_, v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 0)
{
uint8_t v___x_1749_; 
v___x_1749_ = 0;
return v___x_1749_;
}
else
{
uint8_t v___x_1750_; 
v___x_1750_ = 1;
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* v_x_1751_){
_start:
{
uint8_t v_res_1752_; lean_object* v_r_1753_; 
v_res_1752_ = l_Lean_IR_Alt_isDefault(v_x_1751_);
lean_dec_ref(v_x_1751_);
v_r_1753_ = lean_box(v_res_1752_);
return v_r_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object* v_bs_1754_, lean_object* v_b_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v_b_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_box(12);
v_b_1757_ = l_Lean_IR_FnBody_setBody(v_b_1755_, v___x_1756_);
v___x_1758_ = lean_array_push(v_bs_1754_, v_b_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object* v_b_1759_, lean_object* v_r_1760_){
_start:
{
lean_object* v___y_1762_; uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_IR_FnBody_isTerminal(v_b_1759_);
if (v___x_1765_ == 0)
{
switch(lean_obj_tag(v_b_1759_))
{
case 0:
{
lean_object* v_b_1766_; 
v_b_1766_ = lean_ctor_get(v_b_1759_, 3);
lean_inc(v_b_1766_);
v___y_1762_ = v_b_1766_;
goto v___jp_1761_;
}
case 1:
{
lean_object* v_b_1767_; 
v_b_1767_ = lean_ctor_get(v_b_1759_, 3);
lean_inc(v_b_1767_);
v___y_1762_ = v_b_1767_;
goto v___jp_1761_;
}
case 2:
{
lean_object* v_b_1768_; 
v_b_1768_ = lean_ctor_get(v_b_1759_, 3);
lean_inc(v_b_1768_);
v___y_1762_ = v_b_1768_;
goto v___jp_1761_;
}
case 4:
{
lean_object* v_b_1769_; 
v_b_1769_ = lean_ctor_get(v_b_1759_, 3);
lean_inc(v_b_1769_);
v___y_1762_ = v_b_1769_;
goto v___jp_1761_;
}
case 5:
{
lean_object* v_b_1770_; 
v_b_1770_ = lean_ctor_get(v_b_1759_, 5);
lean_inc(v_b_1770_);
v___y_1762_ = v_b_1770_;
goto v___jp_1761_;
}
case 3:
{
lean_object* v_b_1771_; 
v_b_1771_ = lean_ctor_get(v_b_1759_, 2);
lean_inc(v_b_1771_);
v___y_1762_ = v_b_1771_;
goto v___jp_1761_;
}
case 6:
{
lean_object* v_b_1772_; 
v_b_1772_ = lean_ctor_get(v_b_1759_, 2);
lean_inc(v_b_1772_);
v___y_1762_ = v_b_1772_;
goto v___jp_1761_;
}
case 7:
{
lean_object* v_b_1773_; 
v_b_1773_ = lean_ctor_get(v_b_1759_, 2);
lean_inc(v_b_1773_);
v___y_1762_ = v_b_1773_;
goto v___jp_1761_;
}
case 8:
{
lean_object* v_b_1774_; 
v_b_1774_ = lean_ctor_get(v_b_1759_, 1);
lean_inc(v_b_1774_);
v___y_1762_ = v_b_1774_;
goto v___jp_1761_;
}
default: 
{
lean_inc(v_b_1759_);
v___y_1762_ = v_b_1759_;
goto v___jp_1761_;
}
}
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_r_1760_);
lean_ctor_set(v___x_1775_, 1, v_b_1759_);
return v___x_1775_;
}
v___jp_1761_:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_IR_push(v_r_1760_, v_b_1759_);
v_b_1759_ = v___y_1762_;
v_r_1760_ = v___x_1763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object* v_b_1778_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_IR_FnBody_flatten___closed__0));
v___x_1780_ = l_Lean_IR_flattenAux(v_b_1778_, v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0(lean_object* v___x_1781_, lean_object* v_msg_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_panic_fn_borrowed(v___x_1781_, v_msg_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(lean_object* v___x_1784_, lean_object* v_msg_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_1784_, v_msg_1785_);
lean_dec_ref(v___x_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object* v_a_1791_, lean_object* v_i_1792_, lean_object* v_b_1793_){
_start:
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_nat_dec_eq(v_i_1792_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v_i_1797_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1796_ = lean_unsigned_to_nat(1u);
v_i_1797_ = lean_nat_sub(v_i_1792_, v___x_1796_);
lean_dec(v_i_1792_);
v___x_1803_ = ((lean_object*)(l_Lean_IR_instInhabitedFnBody_default__1));
v___x_1804_ = lean_array_get_size(v_a_1791_);
v___x_1805_ = lean_nat_dec_lt(v_i_1797_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v_fst_1818_; lean_object* v_snd_1819_; 
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1803_);
lean_ctor_set(v___x_1806_, 1, v_a_1791_);
v___x_1807_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__0));
v___x_1808_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__1));
v___x_1809_ = lean_unsigned_to_nat(463u);
v___x_1810_ = lean_unsigned_to_nat(4u);
v___x_1811_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__2));
lean_inc(v_i_1797_);
v___x_1812_ = l_Nat_reprFast(v_i_1797_);
v___x_1813_ = lean_string_append(v___x_1811_, v___x_1812_);
lean_dec_ref(v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Lean_IR_reshapeAux___closed__3));
v___x_1815_ = lean_string_append(v___x_1813_, v___x_1814_);
v___x_1816_ = l_mkPanicMessageWithDecl(v___x_1807_, v___x_1808_, v___x_1809_, v___x_1810_, v___x_1815_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_panic_fn_borrowed(v___x_1806_, v___x_1816_);
lean_dec_ref_known(v___x_1806_, 2);
v_fst_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_fst_1818_);
v_snd_1819_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_snd_1819_);
lean_dec(v___x_1817_);
v_fst_1799_ = v_fst_1818_;
v_snd_1800_ = v_snd_1819_;
goto v___jp_1798_;
}
else
{
lean_object* v_e_1820_; lean_object* v_xs_x27_1821_; 
v_e_1820_ = lean_array_fget(v_a_1791_, v_i_1797_);
v_xs_x27_1821_ = lean_array_fset(v_a_1791_, v_i_1797_, v___x_1803_);
v_fst_1799_ = v_e_1820_;
v_snd_1800_ = v_xs_x27_1821_;
goto v___jp_1798_;
}
v___jp_1798_:
{
lean_object* v_b_1801_; 
v_b_1801_ = l_Lean_IR_FnBody_setBody(v_fst_1799_, v_b_1793_);
v_a_1791_ = v_snd_1800_;
v_i_1792_ = v_i_1797_;
v_b_1793_ = v_b_1801_;
goto _start;
}
}
else
{
lean_dec(v_i_1792_);
lean_dec_ref(v_a_1791_);
return v_b_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object* v_bs_1822_, lean_object* v_term_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_array_get_size(v_bs_1822_);
v___x_1825_ = l_Lean_IR_reshapeAux(v_bs_1822_, v___x_1824_, v_term_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object* v_f_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 1)
{
lean_object* v_j_1828_; lean_object* v_xs_1829_; lean_object* v_v_1830_; lean_object* v_b_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
v_j_1828_ = lean_ctor_get(v_x_1827_, 0);
v_xs_1829_ = lean_ctor_get(v_x_1827_, 1);
v_v_1830_ = lean_ctor_get(v_x_1827_, 2);
v_b_1831_ = lean_ctor_get(v_x_1827_, 3);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1833_ = v_x_1827_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_b_1831_);
lean_inc(v_v_1830_);
lean_inc(v_xs_1829_);
lean_inc(v_j_1828_);
lean_dec(v_x_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_apply_1(v_f_1826_, v_v_1830_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 2, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_j_1828_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_xs_1829_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v_b_1831_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_dec_ref(v_f_1826_);
return v_x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* v_bs_1859_, lean_object* v_f_1860_){
_start:
{
lean_object* v___f_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___f_1861_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPs___lam__0), 2, 1);
lean_closure_set(v___f_1861_, 0, v_f_1860_);
v___x_1862_ = ((lean_object*)(l_Lean_IR_modifyJPs___closed__9));
v_sz_1863_ = lean_array_size(v_bs_1859_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1862_, v___f_1861_, v_sz_1863_, v___x_1864_, v_bs_1859_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__0(lean_object* v_j_1866_, lean_object* v_xs_1867_, lean_object* v_b_1868_, lean_object* v_toPure_1869_, lean_object* v_____do__lift_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1871_, 0, v_j_1866_);
lean_ctor_set(v___x_1871_, 1, v_xs_1867_);
lean_ctor_set(v___x_1871_, 2, v_____do__lift_1870_);
lean_ctor_set(v___x_1871_, 3, v_b_1868_);
v___x_1872_ = lean_apply_2(v_toPure_1869_, lean_box(0), v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg___lam__1(lean_object* v_toPure_1873_, lean_object* v_f_1874_, lean_object* v_toBind_1875_, lean_object* v_b_1876_){
_start:
{
if (lean_obj_tag(v_b_1876_) == 1)
{
lean_object* v_j_1877_; lean_object* v_xs_1878_; lean_object* v_v_1879_; lean_object* v_b_1880_; lean_object* v___f_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_j_1877_ = lean_ctor_get(v_b_1876_, 0);
lean_inc(v_j_1877_);
v_xs_1878_ = lean_ctor_get(v_b_1876_, 1);
lean_inc_ref(v_xs_1878_);
v_v_1879_ = lean_ctor_get(v_b_1876_, 2);
lean_inc(v_v_1879_);
v_b_1880_ = lean_ctor_get(v_b_1876_, 3);
lean_inc(v_b_1880_);
lean_dec_ref_known(v_b_1876_, 4);
v___f_1881_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1881_, 0, v_j_1877_);
lean_closure_set(v___f_1881_, 1, v_xs_1878_);
lean_closure_set(v___f_1881_, 2, v_b_1880_);
lean_closure_set(v___f_1881_, 3, v_toPure_1873_);
v___x_1882_ = lean_apply_1(v_f_1874_, v_v_1879_);
v___x_1883_ = lean_apply_4(v_toBind_1875_, lean_box(0), lean_box(0), v___x_1882_, v___f_1881_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; 
lean_dec(v_toBind_1875_);
lean_dec(v_f_1874_);
v___x_1884_ = lean_apply_2(v_toPure_1873_, lean_box(0), v_b_1876_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM___redArg(lean_object* v_inst_1885_, lean_object* v_bs_1886_, lean_object* v_f_1887_){
_start:
{
lean_object* v_toApplicative_1888_; lean_object* v_toBind_1889_; lean_object* v_toPure_1890_; lean_object* v___f_1891_; size_t v_sz_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v_toApplicative_1888_ = lean_ctor_get(v_inst_1885_, 0);
v_toBind_1889_ = lean_ctor_get(v_inst_1885_, 1);
v_toPure_1890_ = lean_ctor_get(v_toApplicative_1888_, 1);
lean_inc(v_toBind_1889_);
lean_inc(v_toPure_1890_);
v___f_1891_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1891_, 0, v_toPure_1890_);
lean_closure_set(v___f_1891_, 1, v_f_1887_);
lean_closure_set(v___f_1891_, 2, v_toBind_1889_);
v_sz_1892_ = lean_array_size(v_bs_1886_);
v___x_1893_ = ((size_t)0ULL);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1885_, v___f_1891_, v_sz_1892_, v___x_1893_, v_bs_1886_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPsM(lean_object* v_m_1895_, lean_object* v_inst_1896_, lean_object* v_bs_1897_, lean_object* v_f_1898_){
_start:
{
lean_object* v_toApplicative_1899_; lean_object* v_toBind_1900_; lean_object* v_toPure_1901_; lean_object* v___f_1902_; size_t v_sz_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v_toApplicative_1899_ = lean_ctor_get(v_inst_1896_, 0);
v_toBind_1900_ = lean_ctor_get(v_inst_1896_, 1);
v_toPure_1901_ = lean_ctor_get(v_toApplicative_1899_, 1);
lean_inc(v_toBind_1900_);
lean_inc(v_toPure_1901_);
v___f_1902_ = lean_alloc_closure((void*)(l_Lean_IR_modifyJPsM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1902_, 0, v_toPure_1901_);
lean_closure_set(v___f_1902_, 1, v_f_1898_);
lean_closure_set(v___f_1902_, 2, v_toBind_1900_);
v_sz_1903_ = lean_array_size(v_bs_1897_);
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1896_, v___f_1902_, v_sz_1903_, v___x_1904_, v_bs_1897_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl(lean_object* v_x_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_obj_tag_nat(v_x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorIdx___impl___boxed(lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_IR_Decl_ctorIdx___impl(v_x_1908_);
lean_dec_ref(v_x_1908_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___redArg(lean_object* v_t_1910_, lean_object* v_k_1911_){
_start:
{
if (lean_obj_tag(v_t_1910_) == 0)
{
lean_object* v_f_1912_; lean_object* v_xs_1913_; lean_object* v_type_1914_; lean_object* v_body_1915_; lean_object* v_info_1916_; lean_object* v___x_1917_; 
v_f_1912_ = lean_ctor_get(v_t_1910_, 0);
lean_inc(v_f_1912_);
v_xs_1913_ = lean_ctor_get(v_t_1910_, 1);
lean_inc_ref(v_xs_1913_);
v_type_1914_ = lean_ctor_get(v_t_1910_, 2);
lean_inc(v_type_1914_);
v_body_1915_ = lean_ctor_get(v_t_1910_, 3);
lean_inc(v_body_1915_);
v_info_1916_ = lean_ctor_get(v_t_1910_, 4);
lean_inc(v_info_1916_);
lean_dec_ref_known(v_t_1910_, 5);
v___x_1917_ = lean_apply_5(v_k_1911_, v_f_1912_, v_xs_1913_, v_type_1914_, v_body_1915_, v_info_1916_);
return v___x_1917_;
}
else
{
lean_object* v_f_1918_; lean_object* v_xs_1919_; lean_object* v_type_1920_; lean_object* v_ext_1921_; lean_object* v___x_1922_; 
v_f_1918_ = lean_ctor_get(v_t_1910_, 0);
lean_inc(v_f_1918_);
v_xs_1919_ = lean_ctor_get(v_t_1910_, 1);
lean_inc_ref(v_xs_1919_);
v_type_1920_ = lean_ctor_get(v_t_1910_, 2);
lean_inc(v_type_1920_);
v_ext_1921_ = lean_ctor_get(v_t_1910_, 3);
lean_inc(v_ext_1921_);
lean_dec_ref_known(v_t_1910_, 4);
v___x_1922_ = lean_apply_4(v_k_1911_, v_f_1918_, v_xs_1919_, v_type_1920_, v_ext_1921_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim(lean_object* v_motive_1923_, lean_object* v_ctorIdx_1924_, lean_object* v_t_1925_, lean_object* v_h_1926_, lean_object* v_k_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1925_, v_k_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_ctorElim___boxed(lean_object* v_motive_1929_, lean_object* v_ctorIdx_1930_, lean_object* v_t_1931_, lean_object* v_h_1932_, lean_object* v_k_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_IR_Decl_ctorElim(v_motive_1929_, v_ctorIdx_1930_, v_t_1931_, v_h_1932_, v_k_1933_);
lean_dec(v_ctorIdx_1930_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim___redArg(lean_object* v_t_1935_, lean_object* v_fdecl_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1935_, v_fdecl_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_fdecl_elim(lean_object* v_motive_1938_, lean_object* v_t_1939_, lean_object* v_h_1940_, lean_object* v_fdecl_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1939_, v_fdecl_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim___redArg(lean_object* v_t_1943_, lean_object* v_extern_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1943_, v_extern_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_extern_elim(lean_object* v_motive_1946_, lean_object* v_t_1947_, lean_object* v_h_1948_, lean_object* v_extern_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_1947_, v_extern_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object* v_x_1960_){
_start:
{
lean_object* v_f_1961_; 
v_f_1961_ = lean_ctor_get(v_x_1960_, 0);
lean_inc(v_f_1961_);
return v_f_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object* v_x_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_IR_Decl_name(v_x_1962_);
lean_dec_ref(v_x_1962_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object* v_x_1964_){
_start:
{
lean_object* v_xs_1965_; 
v_xs_1965_ = lean_ctor_get(v_x_1964_, 1);
lean_inc_ref(v_xs_1965_);
return v_xs_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object* v_x_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_IR_Decl_params(v_x_1966_);
lean_dec_ref(v_x_1966_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object* v_x_1968_){
_start:
{
lean_object* v_type_1969_; 
v_type_1969_ = lean_ctor_get(v_x_1968_, 2);
lean_inc(v_type_1969_);
return v_type_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* v_x_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_IR_Decl_resultType(v_x_1970_);
lean_dec_ref(v_x_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object* v_x_1972_){
_start:
{
if (lean_obj_tag(v_x_1972_) == 1)
{
uint8_t v___x_1973_; 
v___x_1973_ = 1;
return v___x_1973_;
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = 0;
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* v_x_1975_){
_start:
{
uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_res_1976_ = l_Lean_IR_Decl_isExtern(v_x_1975_);
lean_dec_ref(v_x_1975_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* v_x_1978_){
_start:
{
if (lean_obj_tag(v_x_1978_) == 0)
{
lean_object* v_info_1979_; 
v_info_1979_ = lean_ctor_get(v_x_1978_, 4);
lean_inc(v_info_1979_);
return v_info_1979_;
}
else
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_box(0);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* v_x_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_IR_Decl_getInfo(v_x_1981_);
lean_dec_ref(v_x_1981_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object* v_msg_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l_Lean_IR_instInhabitedDecl_default));
v___x_1985_ = lean_panic_fn_borrowed(v___x_1984_, v_msg_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__3(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1989_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__2));
v___x_1990_ = lean_unsigned_to_nat(9u);
v___x_1991_ = lean_unsigned_to_nat(382u);
v___x_1992_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__1));
v___x_1993_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__0));
v___x_1994_ = l_mkPanicMessageWithDecl(v___x_1993_, v___x_1992_, v___x_1991_, v___x_1990_, v___x_1989_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* v_d_1995_, lean_object* v_bNew_1996_){
_start:
{
if (lean_obj_tag(v_d_1995_) == 0)
{
lean_object* v_f_1997_; lean_object* v_xs_1998_; lean_object* v_type_1999_; lean_object* v_info_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_f_1997_ = lean_ctor_get(v_d_1995_, 0);
v_xs_1998_ = lean_ctor_get(v_d_1995_, 1);
v_type_1999_ = lean_ctor_get(v_d_1995_, 2);
v_info_2000_ = lean_ctor_get(v_d_1995_, 4);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_d_1995_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v_d_1995_, 3);
lean_dec(v_unused_2008_);
v___x_2002_ = v_d_1995_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_info_2000_);
lean_inc(v_type_1999_);
lean_inc(v_xs_1998_);
lean_inc(v_f_1997_);
lean_dec(v_d_1995_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 3, v_bNew_1996_);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_f_1997_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_xs_1998_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_type_1999_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_bNew_1996_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_info_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_bNew_1996_);
lean_dec_ref(v_d_1995_);
v___x_2009_ = lean_obj_once(&l_Lean_IR_Decl_updateBody_x21___closed__3, &l_Lean_IR_Decl_updateBody_x21___closed__3_once, _init_l_Lean_IR_Decl_updateBody_x21___closed__3);
v___x_2010_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_2009_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object* v_f_2011_, lean_object* v_xs_2012_, lean_object* v_ty_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(12);
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2016_, 0, v_f_2011_);
lean_ctor_set(v___x_2016_, 1, v_xs_2012_);
lean_ctor_set(v___x_2016_, 2, v_ty_2013_);
lean_ctor_set(v___x_2016_, 3, v___x_2014_);
lean_ctor_set(v___x_2016_, 4, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object* v_k_2017_, lean_object* v_v_2018_, lean_object* v_t_2019_){
_start:
{
if (lean_obj_tag(v_t_2019_) == 0)
{
lean_object* v_size_2020_; lean_object* v_k_2021_; lean_object* v_v_2022_; lean_object* v_l_2023_; lean_object* v_r_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2305_; 
v_size_2020_ = lean_ctor_get(v_t_2019_, 0);
v_k_2021_ = lean_ctor_get(v_t_2019_, 1);
v_v_2022_ = lean_ctor_get(v_t_2019_, 2);
v_l_2023_ = lean_ctor_get(v_t_2019_, 3);
v_r_2024_ = lean_ctor_get(v_t_2019_, 4);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_t_2019_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2026_ = v_t_2019_;
v_isShared_2027_ = v_isSharedCheck_2305_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_r_2024_);
lean_inc(v_l_2023_);
lean_inc(v_v_2022_);
lean_inc(v_k_2021_);
lean_inc(v_size_2020_);
lean_dec(v_t_2019_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2305_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_lt(v_k_2017_, v_k_2021_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_nat_dec_eq(v_k_2017_, v_k_2021_);
if (v___x_2029_ == 0)
{
lean_object* v_impl_2030_; lean_object* v___x_2031_; 
lean_dec(v_size_2020_);
v_impl_2030_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2017_, v_v_2018_, v_r_2024_);
v___x_2031_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2023_) == 0)
{
lean_object* v_size_2032_; lean_object* v_size_2033_; lean_object* v_k_2034_; lean_object* v_v_2035_; lean_object* v_l_2036_; lean_object* v_r_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_size_2032_ = lean_ctor_get(v_l_2023_, 0);
v_size_2033_ = lean_ctor_get(v_impl_2030_, 0);
v_k_2034_ = lean_ctor_get(v_impl_2030_, 1);
v_v_2035_ = lean_ctor_get(v_impl_2030_, 2);
v_l_2036_ = lean_ctor_get(v_impl_2030_, 3);
lean_inc(v_l_2036_);
v_r_2037_ = lean_ctor_get(v_impl_2030_, 4);
v___x_2038_ = lean_unsigned_to_nat(3u);
v___x_2039_ = lean_nat_mul(v___x_2038_, v_size_2032_);
v___x_2040_ = lean_nat_dec_lt(v___x_2039_, v_size_2033_);
lean_dec(v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_dec(v_l_2036_);
v___x_2041_ = lean_nat_add(v___x_2031_, v_size_2032_);
v___x_2042_ = lean_nat_add(v___x_2041_, v_size_2033_);
lean_dec(v___x_2041_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_impl_2030_);
lean_ctor_set(v___x_2026_, 0, v___x_2042_);
v___x_2044_ = v___x_2026_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_l_2023_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_impl_2030_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
else
{
lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2109_; 
lean_inc(v_r_2037_);
lean_inc(v_v_2035_);
lean_inc(v_k_2034_);
lean_inc(v_size_2033_);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_impl_2030_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; lean_object* v_unused_2111_; lean_object* v_unused_2112_; lean_object* v_unused_2113_; lean_object* v_unused_2114_; 
v_unused_2110_ = lean_ctor_get(v_impl_2030_, 4);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_impl_2030_, 3);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_impl_2030_, 2);
lean_dec(v_unused_2112_);
v_unused_2113_ = lean_ctor_get(v_impl_2030_, 1);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v_impl_2030_, 0);
lean_dec(v_unused_2114_);
v___x_2047_ = v_impl_2030_;
v_isShared_2048_ = v_isSharedCheck_2109_;
goto v_resetjp_2046_;
}
else
{
lean_dec(v_impl_2030_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2109_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_size_2049_; lean_object* v_k_2050_; lean_object* v_v_2051_; lean_object* v_l_2052_; lean_object* v_r_2053_; lean_object* v_size_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_size_2049_ = lean_ctor_get(v_l_2036_, 0);
v_k_2050_ = lean_ctor_get(v_l_2036_, 1);
v_v_2051_ = lean_ctor_get(v_l_2036_, 2);
v_l_2052_ = lean_ctor_get(v_l_2036_, 3);
v_r_2053_ = lean_ctor_get(v_l_2036_, 4);
v_size_2054_ = lean_ctor_get(v_r_2037_, 0);
v___x_2055_ = lean_unsigned_to_nat(2u);
v___x_2056_ = lean_nat_mul(v___x_2055_, v_size_2054_);
v___x_2057_ = lean_nat_dec_lt(v_size_2049_, v___x_2056_);
lean_dec(v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2085_; 
lean_inc(v_r_2053_);
lean_inc(v_l_2052_);
lean_inc(v_v_2051_);
lean_inc(v_k_2050_);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_l_2036_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; lean_object* v_unused_2090_; 
v_unused_2086_ = lean_ctor_get(v_l_2036_, 4);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_l_2036_, 3);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_l_2036_, 2);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_l_2036_, 1);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_l_2036_, 0);
lean_dec(v_unused_2090_);
v___x_2059_ = v_l_2036_;
v_isShared_2060_ = v_isSharedCheck_2085_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_l_2036_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2085_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2075_; 
v___x_2061_ = lean_nat_add(v___x_2031_, v_size_2032_);
v___x_2062_ = lean_nat_add(v___x_2061_, v_size_2033_);
lean_dec(v_size_2033_);
if (lean_obj_tag(v_l_2052_) == 0)
{
lean_object* v_size_2083_; 
v_size_2083_ = lean_ctor_get(v_l_2052_, 0);
lean_inc(v_size_2083_);
v___y_2075_ = v_size_2083_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___y_2075_ = v___x_2084_;
goto v___jp_2074_;
}
v___jp_2063_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_nat_add(v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec(v___y_2065_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_r_2037_);
lean_ctor_set(v___x_2059_, 3, v_r_2053_);
lean_ctor_set(v___x_2059_, 2, v_v_2035_);
lean_ctor_set(v___x_2059_, 1, v_k_2034_);
lean_ctor_set(v___x_2059_, 0, v___x_2067_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_2034_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_2035_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_r_2053_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_r_2037_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 4, v___x_2069_);
lean_ctor_set(v___x_2047_, 3, v___y_2064_);
lean_ctor_set(v___x_2047_, 2, v_v_2051_);
lean_ctor_set(v___x_2047_, 1, v_k_2050_);
lean_ctor_set(v___x_2047_, 0, v___x_2062_);
v___x_2071_ = v___x_2047_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_k_2050_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_v_2051_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v___y_2064_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_nat_add(v___x_2061_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec(v___x_2061_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_l_2052_);
lean_ctor_set(v___x_2026_, 0, v___x_2076_);
v___x_2078_ = v___x_2026_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_l_2023_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_l_2052_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_nat_add(v___x_2031_, v_size_2054_);
if (lean_obj_tag(v_r_2053_) == 0)
{
lean_object* v_size_2080_; 
v_size_2080_ = lean_ctor_get(v_r_2053_, 0);
lean_inc(v_size_2080_);
v___y_2064_ = v___x_2078_;
v___y_2065_ = v___x_2079_;
v___y_2066_ = v_size_2080_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___y_2064_ = v___x_2078_;
v___y_2065_ = v___x_2079_;
v___y_2066_ = v___x_2081_;
goto v___jp_2063_;
}
}
}
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
lean_del_object(v___x_2026_);
v___x_2091_ = lean_nat_add(v___x_2031_, v_size_2032_);
v___x_2092_ = lean_nat_add(v___x_2091_, v_size_2033_);
lean_dec(v_size_2033_);
v___x_2093_ = lean_nat_add(v___x_2091_, v_size_2049_);
lean_dec(v___x_2091_);
lean_inc_ref(v_l_2023_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 4, v_l_2036_);
lean_ctor_set(v___x_2047_, 3, v_l_2023_);
lean_ctor_set(v___x_2047_, 2, v_v_2022_);
lean_ctor_set(v___x_2047_, 1, v_k_2021_);
lean_ctor_set(v___x_2047_, 0, v___x_2093_);
v___x_2095_ = v___x_2047_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_l_2023_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_l_2036_);
v___x_2095_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_isSharedCheck_2102_ = !lean_is_exclusive(v_l_2023_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; lean_object* v_unused_2107_; 
v_unused_2103_ = lean_ctor_get(v_l_2023_, 4);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_l_2023_, 3);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_l_2023_, 2);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_l_2023_, 1);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_l_2023_, 0);
lean_dec(v_unused_2107_);
v___x_2097_ = v_l_2023_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_dec(v_l_2023_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 4, v_r_2037_);
lean_ctor_set(v___x_2097_, 3, v___x_2095_);
lean_ctor_set(v___x_2097_, 2, v_v_2035_);
lean_ctor_set(v___x_2097_, 1, v_k_2034_);
lean_ctor_set(v___x_2097_, 0, v___x_2092_);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_k_2034_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_v_2035_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v_r_2037_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2115_; 
v_l_2115_ = lean_ctor_get(v_impl_2030_, 3);
lean_inc(v_l_2115_);
if (lean_obj_tag(v_l_2115_) == 0)
{
lean_object* v_r_2116_; lean_object* v_k_2117_; lean_object* v_v_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2141_; 
v_r_2116_ = lean_ctor_get(v_impl_2030_, 4);
v_k_2117_ = lean_ctor_get(v_impl_2030_, 1);
v_v_2118_ = lean_ctor_get(v_impl_2030_, 2);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_impl_2030_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; lean_object* v_unused_2143_; 
v_unused_2142_ = lean_ctor_get(v_impl_2030_, 3);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_impl_2030_, 0);
lean_dec(v_unused_2143_);
v___x_2120_ = v_impl_2030_;
v_isShared_2121_ = v_isSharedCheck_2141_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_r_2116_);
lean_inc(v_v_2118_);
lean_inc(v_k_2117_);
lean_dec(v_impl_2030_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2141_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_k_2122_; lean_object* v_v_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2137_; 
v_k_2122_ = lean_ctor_get(v_l_2115_, 1);
v_v_2123_ = lean_ctor_get(v_l_2115_, 2);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_l_2115_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; lean_object* v_unused_2139_; lean_object* v_unused_2140_; 
v_unused_2138_ = lean_ctor_get(v_l_2115_, 4);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v_l_2115_, 3);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_l_2115_, 0);
lean_dec(v_unused_2140_);
v___x_2125_ = v_l_2115_;
v_isShared_2126_ = v_isSharedCheck_2137_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_v_2123_);
lean_inc(v_k_2122_);
lean_dec(v_l_2115_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2137_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2116_, 2);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_r_2116_);
lean_ctor_set(v___x_2125_, 3, v_r_2116_);
lean_ctor_set(v___x_2125_, 2, v_v_2022_);
lean_ctor_set(v___x_2125_, 1, v_k_2021_);
lean_ctor_set(v___x_2125_, 0, v___x_2031_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_r_2116_);
v___x_2129_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
lean_inc(v_r_2116_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 3, v_r_2116_);
lean_ctor_set(v___x_2120_, 0, v___x_2031_);
v___x_2131_ = v___x_2120_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_k_2117_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_v_2118_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v_r_2116_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v___x_2131_);
lean_ctor_set(v___x_2026_, 3, v___x_2129_);
lean_ctor_set(v___x_2026_, 2, v_v_2123_);
lean_ctor_set(v___x_2026_, 1, v_k_2122_);
lean_ctor_set(v___x_2026_, 0, v___x_2127_);
v___x_2133_ = v___x_2026_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_k_2122_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_2123_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
else
{
lean_object* v_r_2144_; 
v_r_2144_ = lean_ctor_get(v_impl_2030_, 4);
lean_inc(v_r_2144_);
if (lean_obj_tag(v_r_2144_) == 0)
{
lean_object* v_k_2145_; lean_object* v_v_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2157_; 
v_k_2145_ = lean_ctor_get(v_impl_2030_, 1);
v_v_2146_ = lean_ctor_get(v_impl_2030_, 2);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_impl_2030_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; 
v_unused_2158_ = lean_ctor_get(v_impl_2030_, 4);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_impl_2030_, 3);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_impl_2030_, 0);
lean_dec(v_unused_2160_);
v___x_2148_ = v_impl_2030_;
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_v_2146_);
lean_inc(v_k_2145_);
lean_dec(v_impl_2030_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_unsigned_to_nat(3u);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 4, v_l_2115_);
lean_ctor_set(v___x_2148_, 2, v_v_2022_);
lean_ctor_set(v___x_2148_, 1, v_k_2021_);
lean_ctor_set(v___x_2148_, 0, v___x_2031_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_l_2115_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_r_2144_);
lean_ctor_set(v___x_2026_, 3, v___x_2152_);
lean_ctor_set(v___x_2026_, 2, v_v_2146_);
lean_ctor_set(v___x_2026_, 1, v_k_2145_);
lean_ctor_set(v___x_2026_, 0, v___x_2150_);
v___x_2154_ = v___x_2026_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2145_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2146_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_r_2144_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_unsigned_to_nat(2u);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_impl_2030_);
lean_ctor_set(v___x_2026_, 3, v_r_2144_);
lean_ctor_set(v___x_2026_, 0, v___x_2161_);
v___x_2163_ = v___x_2026_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_r_2144_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_impl_2030_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v___x_2166_; 
lean_dec(v_v_2022_);
lean_dec(v_k_2021_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 2, v_v_2018_);
lean_ctor_set(v___x_2026_, 1, v_k_2017_);
v___x_2166_ = v___x_2026_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_size_2020_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_k_2017_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_v_2018_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_l_2023_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_r_2024_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_impl_2168_; lean_object* v___x_2169_; 
lean_dec(v_size_2020_);
v_impl_2168_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2017_, v_v_2018_, v_l_2023_);
v___x_2169_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2024_) == 0)
{
lean_object* v_size_2170_; lean_object* v_size_2171_; lean_object* v_k_2172_; lean_object* v_v_2173_; lean_object* v_l_2174_; lean_object* v_r_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_size_2170_ = lean_ctor_get(v_r_2024_, 0);
v_size_2171_ = lean_ctor_get(v_impl_2168_, 0);
v_k_2172_ = lean_ctor_get(v_impl_2168_, 1);
v_v_2173_ = lean_ctor_get(v_impl_2168_, 2);
v_l_2174_ = lean_ctor_get(v_impl_2168_, 3);
v_r_2175_ = lean_ctor_get(v_impl_2168_, 4);
lean_inc(v_r_2175_);
v___x_2176_ = lean_unsigned_to_nat(3u);
v___x_2177_ = lean_nat_mul(v___x_2176_, v_size_2170_);
v___x_2178_ = lean_nat_dec_lt(v___x_2177_, v_size_2171_);
lean_dec(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec(v_r_2175_);
v___x_2179_ = lean_nat_add(v___x_2169_, v_size_2171_);
v___x_2180_ = lean_nat_add(v___x_2179_, v_size_2170_);
lean_dec(v___x_2179_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 3, v_impl_2168_);
lean_ctor_set(v___x_2026_, 0, v___x_2180_);
v___x_2182_ = v___x_2026_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_impl_2168_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_r_2024_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2249_; 
lean_inc(v_l_2174_);
lean_inc(v_v_2173_);
lean_inc(v_k_2172_);
lean_inc(v_size_2171_);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_impl_2168_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; lean_object* v_unused_2251_; lean_object* v_unused_2252_; lean_object* v_unused_2253_; lean_object* v_unused_2254_; 
v_unused_2250_ = lean_ctor_get(v_impl_2168_, 4);
lean_dec(v_unused_2250_);
v_unused_2251_ = lean_ctor_get(v_impl_2168_, 3);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_impl_2168_, 2);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_impl_2168_, 1);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_impl_2168_, 0);
lean_dec(v_unused_2254_);
v___x_2185_ = v_impl_2168_;
v_isShared_2186_ = v_isSharedCheck_2249_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v_impl_2168_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2249_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_size_2187_; lean_object* v_size_2188_; lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v_l_2191_; lean_object* v_r_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_size_2187_ = lean_ctor_get(v_l_2174_, 0);
v_size_2188_ = lean_ctor_get(v_r_2175_, 0);
v_k_2189_ = lean_ctor_get(v_r_2175_, 1);
v_v_2190_ = lean_ctor_get(v_r_2175_, 2);
v_l_2191_ = lean_ctor_get(v_r_2175_, 3);
v_r_2192_ = lean_ctor_get(v_r_2175_, 4);
v___x_2193_ = lean_unsigned_to_nat(2u);
v___x_2194_ = lean_nat_mul(v___x_2193_, v_size_2187_);
v___x_2195_ = lean_nat_dec_lt(v_size_2188_, v___x_2194_);
lean_dec(v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2224_; 
lean_inc(v_r_2192_);
lean_inc(v_l_2191_);
lean_inc(v_v_2190_);
lean_inc(v_k_2189_);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_r_2175_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2225_ = lean_ctor_get(v_r_2175_, 4);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_r_2175_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_r_2175_, 2);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_r_2175_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_r_2175_, 0);
lean_dec(v_unused_2229_);
v___x_2197_ = v_r_2175_;
v_isShared_2198_ = v_isSharedCheck_2224_;
goto v_resetjp_2196_;
}
else
{
lean_dec(v_r_2175_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2224_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___x_2212_; lean_object* v___y_2214_; 
v___x_2199_ = lean_nat_add(v___x_2169_, v_size_2171_);
lean_dec(v_size_2171_);
v___x_2200_ = lean_nat_add(v___x_2199_, v_size_2170_);
lean_dec(v___x_2199_);
v___x_2212_ = lean_nat_add(v___x_2169_, v_size_2187_);
if (lean_obj_tag(v_l_2191_) == 0)
{
lean_object* v_size_2222_; 
v_size_2222_ = lean_ctor_get(v_l_2191_, 0);
lean_inc(v_size_2222_);
v___y_2214_ = v_size_2222_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___y_2214_ = v___x_2223_;
goto v___jp_2213_;
}
v___jp_2201_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_nat_add(v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec(v___y_2203_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 4, v_r_2024_);
lean_ctor_set(v___x_2197_, 3, v_r_2192_);
lean_ctor_set(v___x_2197_, 2, v_v_2022_);
lean_ctor_set(v___x_2197_, 1, v_k_2021_);
lean_ctor_set(v___x_2197_, 0, v___x_2205_);
v___x_2207_ = v___x_2197_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_r_2192_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_r_2024_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 4, v___x_2207_);
lean_ctor_set(v___x_2185_, 3, v___y_2202_);
lean_ctor_set(v___x_2185_, 2, v_v_2190_);
lean_ctor_set(v___x_2185_, 1, v_k_2189_);
lean_ctor_set(v___x_2185_, 0, v___x_2200_);
v___x_2209_ = v___x_2185_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2189_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2190_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v___y_2202_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
v___jp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_nat_add(v___x_2212_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec(v___x_2212_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_l_2191_);
lean_ctor_set(v___x_2026_, 3, v_l_2174_);
lean_ctor_set(v___x_2026_, 2, v_v_2173_);
lean_ctor_set(v___x_2026_, 1, v_k_2172_);
lean_ctor_set(v___x_2026_, 0, v___x_2215_);
v___x_2217_ = v___x_2026_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2172_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2173_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_l_2174_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_l_2191_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_nat_add(v___x_2169_, v_size_2170_);
if (lean_obj_tag(v_r_2192_) == 0)
{
lean_object* v_size_2219_; 
v_size_2219_ = lean_ctor_get(v_r_2192_, 0);
lean_inc(v_size_2219_);
v___y_2202_ = v___x_2217_;
v___y_2203_ = v___x_2218_;
v___y_2204_ = v_size_2219_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___y_2202_ = v___x_2217_;
v___y_2203_ = v___x_2218_;
v___y_2204_ = v___x_2220_;
goto v___jp_2201_;
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
lean_del_object(v___x_2026_);
v___x_2230_ = lean_nat_add(v___x_2169_, v_size_2171_);
lean_dec(v_size_2171_);
v___x_2231_ = lean_nat_add(v___x_2230_, v_size_2170_);
lean_dec(v___x_2230_);
v___x_2232_ = lean_nat_add(v___x_2169_, v_size_2170_);
v___x_2233_ = lean_nat_add(v___x_2232_, v_size_2188_);
lean_dec(v___x_2232_);
lean_inc_ref(v_r_2024_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 4, v_r_2024_);
lean_ctor_set(v___x_2185_, 3, v_r_2175_);
lean_ctor_set(v___x_2185_, 2, v_v_2022_);
lean_ctor_set(v___x_2185_, 1, v_k_2021_);
lean_ctor_set(v___x_2185_, 0, v___x_2233_);
v___x_2235_ = v___x_2185_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_r_2175_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_r_2024_);
v___x_2235_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_isSharedCheck_2242_ = !lean_is_exclusive(v_r_2024_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; lean_object* v_unused_2245_; lean_object* v_unused_2246_; lean_object* v_unused_2247_; 
v_unused_2243_ = lean_ctor_get(v_r_2024_, 4);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_r_2024_, 3);
lean_dec(v_unused_2244_);
v_unused_2245_ = lean_ctor_get(v_r_2024_, 2);
lean_dec(v_unused_2245_);
v_unused_2246_ = lean_ctor_get(v_r_2024_, 1);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_r_2024_, 0);
lean_dec(v_unused_2247_);
v___x_2237_ = v_r_2024_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_dec(v_r_2024_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v___x_2235_);
lean_ctor_set(v___x_2237_, 3, v_l_2174_);
lean_ctor_set(v___x_2237_, 2, v_v_2173_);
lean_ctor_set(v___x_2237_, 1, v_k_2172_);
lean_ctor_set(v___x_2237_, 0, v___x_2231_);
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_k_2172_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_v_2173_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_l_2174_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v___x_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2255_; 
v_l_2255_ = lean_ctor_get(v_impl_2168_, 3);
if (lean_obj_tag(v_l_2255_) == 0)
{
lean_object* v_r_2256_; lean_object* v_k_2257_; lean_object* v_v_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2269_; 
lean_inc_ref(v_l_2255_);
v_r_2256_ = lean_ctor_get(v_impl_2168_, 4);
v_k_2257_ = lean_ctor_get(v_impl_2168_, 1);
v_v_2258_ = lean_ctor_get(v_impl_2168_, 2);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_impl_2168_);
if (v_isSharedCheck_2269_ == 0)
{
lean_object* v_unused_2270_; lean_object* v_unused_2271_; 
v_unused_2270_ = lean_ctor_get(v_impl_2168_, 3);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_impl_2168_, 0);
lean_dec(v_unused_2271_);
v___x_2260_ = v_impl_2168_;
v_isShared_2261_ = v_isSharedCheck_2269_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_r_2256_);
lean_inc(v_v_2258_);
lean_inc(v_k_2257_);
lean_dec(v_impl_2168_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2269_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2256_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 3, v_r_2256_);
lean_ctor_set(v___x_2260_, 2, v_v_2022_);
lean_ctor_set(v___x_2260_, 1, v_k_2021_);
lean_ctor_set(v___x_2260_, 0, v___x_2169_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_r_2256_);
lean_ctor_set(v_reuseFailAlloc_2268_, 4, v_r_2256_);
v___x_2264_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2266_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v___x_2264_);
lean_ctor_set(v___x_2026_, 3, v_l_2255_);
lean_ctor_set(v___x_2026_, 2, v_v_2258_);
lean_ctor_set(v___x_2026_, 1, v_k_2257_);
lean_ctor_set(v___x_2026_, 0, v___x_2262_);
v___x_2266_ = v___x_2026_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_k_2257_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v_v_2258_);
lean_ctor_set(v_reuseFailAlloc_2267_, 3, v_l_2255_);
lean_ctor_set(v_reuseFailAlloc_2267_, 4, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_object* v_r_2272_; 
v_r_2272_ = lean_ctor_get(v_impl_2168_, 4);
lean_inc(v_r_2272_);
if (lean_obj_tag(v_r_2272_) == 0)
{
lean_object* v_k_2273_; lean_object* v_v_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2297_; 
lean_inc(v_l_2255_);
v_k_2273_ = lean_ctor_get(v_impl_2168_, 1);
v_v_2274_ = lean_ctor_get(v_impl_2168_, 2);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_impl_2168_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; lean_object* v_unused_2299_; lean_object* v_unused_2300_; 
v_unused_2298_ = lean_ctor_get(v_impl_2168_, 4);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_impl_2168_, 3);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_impl_2168_, 0);
lean_dec(v_unused_2300_);
v___x_2276_ = v_impl_2168_;
v_isShared_2277_ = v_isSharedCheck_2297_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_v_2274_);
lean_inc(v_k_2273_);
lean_dec(v_impl_2168_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2297_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v_k_2278_; lean_object* v_v_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2293_; 
v_k_2278_ = lean_ctor_get(v_r_2272_, 1);
v_v_2279_ = lean_ctor_get(v_r_2272_, 2);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_r_2272_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2294_ = lean_ctor_get(v_r_2272_, 4);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_r_2272_, 3);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_r_2272_, 0);
lean_dec(v_unused_2296_);
v___x_2281_ = v_r_2272_;
v_isShared_2282_ = v_isSharedCheck_2293_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_v_2279_);
lean_inc(v_k_2278_);
lean_dec(v_r_2272_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2293_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = lean_unsigned_to_nat(3u);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v_l_2255_);
lean_ctor_set(v___x_2281_, 3, v_l_2255_);
lean_ctor_set(v___x_2281_, 2, v_v_2274_);
lean_ctor_set(v___x_2281_, 1, v_k_2273_);
lean_ctor_set(v___x_2281_, 0, v___x_2169_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2273_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2274_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_l_2255_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_l_2255_);
v___x_2285_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2287_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 4, v_l_2255_);
lean_ctor_set(v___x_2276_, 2, v_v_2022_);
lean_ctor_set(v___x_2276_, 1, v_k_2021_);
lean_ctor_set(v___x_2276_, 0, v___x_2169_);
v___x_2287_ = v___x_2276_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_l_2255_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_l_2255_);
v___x_2287_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v___x_2287_);
lean_ctor_set(v___x_2026_, 3, v___x_2285_);
lean_ctor_set(v___x_2026_, 2, v_v_2279_);
lean_ctor_set(v___x_2026_, 1, v_k_2278_);
lean_ctor_set(v___x_2026_, 0, v___x_2283_);
v___x_2289_ = v___x_2026_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_k_2278_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_v_2279_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_unsigned_to_nat(2u);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_r_2272_);
lean_ctor_set(v___x_2026_, 3, v_impl_2168_);
lean_ctor_set(v___x_2026_, 0, v___x_2301_);
v___x_2303_ = v___x_2026_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v_impl_2168_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v_r_2272_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_k_2017_);
lean_ctor_set(v___x_2307_, 2, v_v_2018_);
lean_ctor_set(v___x_2307_, 3, v_t_2019_);
lean_ctor_set(v___x_2307_, 4, v_t_2019_);
return v___x_2307_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object* v_k_2308_, lean_object* v_t_2309_){
_start:
{
if (lean_obj_tag(v_t_2309_) == 0)
{
lean_object* v_k_2310_; lean_object* v_l_2311_; lean_object* v_r_2312_; uint8_t v___x_2313_; 
v_k_2310_ = lean_ctor_get(v_t_2309_, 1);
v_l_2311_ = lean_ctor_get(v_t_2309_, 3);
v_r_2312_ = lean_ctor_get(v_t_2309_, 4);
v___x_2313_ = lean_nat_dec_lt(v_k_2308_, v_k_2310_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; 
v___x_2314_ = lean_nat_dec_eq(v_k_2308_, v_k_2310_);
if (v___x_2314_ == 0)
{
v_t_2309_ = v_r_2312_;
goto _start;
}
else
{
return v___x_2314_;
}
}
else
{
v_t_2309_ = v_l_2311_;
goto _start;
}
}
else
{
uint8_t v___x_2317_; 
v___x_2317_ = 0;
return v___x_2317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object* v_k_2318_, lean_object* v_t_2319_){
_start:
{
uint8_t v_res_2320_; lean_object* v_r_2321_; 
v_res_2320_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2318_, v_t_2319_);
lean_dec(v_t_2319_);
lean_dec(v_k_2318_);
v_r_2321_ = lean_box(v_res_2320_);
return v_r_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* v_idx_2322_){
_start:
{
lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = lean_box(1);
v___x_2324_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_box(0);
v___x_2326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_idx_2322_, v___x_2325_, v___x_2323_);
return v___x_2326_;
}
else
{
lean_dec(v_idx_2322_);
return v___x_2323_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object* v_00_u03b2_2327_, lean_object* v_k_2328_, lean_object* v_t_2329_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2328_, v_t_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object* v_00_u03b2_2331_, lean_object* v_k_2332_, lean_object* v_t_2333_){
_start:
{
uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_res_2334_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(v_00_u03b2_2331_, v_k_2332_, v_t_2333_);
lean_dec(v_t_2333_);
lean_dec(v_k_2332_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object* v_00_u03b2_2336_, lean_object* v_k_2337_, lean_object* v_v_2338_, lean_object* v_t_2339_, lean_object* v_hl_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2337_, v_v_2338_, v_t_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl(lean_object* v_x_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_obj_tag_nat(v_x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl___boxed(lean_object* v_x_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_IR_LocalContextEntry_ctorIdx___impl(v_x_2344_);
lean_dec_ref(v_x_2344_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object* v_t_2346_, lean_object* v_k_2347_){
_start:
{
switch(lean_obj_tag(v_t_2346_))
{
case 0:
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v_t_2346_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v_t_2346_, 1);
v___x_2349_ = lean_apply_1(v_k_2347_, v_a_2348_);
return v___x_2349_;
}
case 1:
{
lean_object* v_a_2350_; lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2350_ = lean_ctor_get(v_t_2346_, 0);
lean_inc(v_a_2350_);
v_a_2351_ = lean_ctor_get(v_t_2346_, 1);
lean_inc_ref(v_a_2351_);
lean_dec_ref_known(v_t_2346_, 2);
v___x_2352_ = lean_apply_2(v_k_2347_, v_a_2350_, v_a_2351_);
return v___x_2352_;
}
default: 
{
lean_object* v_a_2353_; lean_object* v_a_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v_t_2346_, 0);
lean_inc_ref(v_a_2353_);
v_a_2354_ = lean_ctor_get(v_t_2346_, 1);
lean_inc(v_a_2354_);
lean_dec_ref_known(v_t_2346_, 2);
v___x_2355_ = lean_apply_2(v_k_2347_, v_a_2353_, v_a_2354_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim(lean_object* v_motive_2356_, lean_object* v_ctorIdx_2357_, lean_object* v_t_2358_, lean_object* v_h_2359_, lean_object* v_k_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2358_, v_k_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___boxed(lean_object* v_motive_2362_, lean_object* v_ctorIdx_2363_, lean_object* v_t_2364_, lean_object* v_h_2365_, lean_object* v_k_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_IR_LocalContextEntry_ctorElim(v_motive_2362_, v_ctorIdx_2363_, v_t_2364_, v_h_2365_, v_k_2366_);
lean_dec(v_ctorIdx_2363_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim___redArg(lean_object* v_t_2368_, lean_object* v_param_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2368_, v_param_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_param_elim(lean_object* v_motive_2371_, lean_object* v_t_2372_, lean_object* v_h_2373_, lean_object* v_param_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2372_, v_param_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim___redArg(lean_object* v_t_2376_, lean_object* v_localVar_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2376_, v_localVar_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_localVar_elim(lean_object* v_motive_2379_, lean_object* v_t_2380_, lean_object* v_h_2381_, lean_object* v_localVar_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2380_, v_localVar_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim___redArg(lean_object* v_t_2384_, lean_object* v_joinPoint_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2384_, v_joinPoint_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_joinPoint_elim(lean_object* v_motive_2387_, lean_object* v_t_2388_, lean_object* v_h_2389_, lean_object* v_joinPoint_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_2388_, v_joinPoint_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* v_ctx_2392_, lean_object* v_x_2393_, lean_object* v_t_2394_, lean_object* v_v_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2396_, 0, v_t_2394_);
lean_ctor_set(v___x_2396_, 1, v_v_2395_);
v___x_2397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2393_, v___x_2396_, v_ctx_2392_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* v_ctx_2398_, lean_object* v_j_2399_, lean_object* v_xs_2400_, lean_object* v_b_2401_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_xs_2400_);
lean_ctor_set(v___x_2402_, 1, v_b_2401_);
v___x_2403_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_j_2399_, v___x_2402_, v_ctx_2398_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* v_ctx_2404_, lean_object* v_p_2405_){
_start:
{
lean_object* v_x_2406_; lean_object* v_ty_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_x_2406_ = lean_ctor_get(v_p_2405_, 0);
lean_inc(v_x_2406_);
v_ty_2407_ = lean_ctor_get(v_p_2405_, 1);
lean_inc(v_ty_2407_);
lean_dec_ref(v_p_2405_);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_ty_2407_);
v___x_2409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2406_, v___x_2408_, v_ctx_2404_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object* v_as_2410_, size_t v_i_2411_, size_t v_stop_2412_, lean_object* v_b_2413_){
_start:
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_usize_dec_eq(v_i_2411_, v_stop_2412_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; 
v___x_2415_ = lean_array_uget_borrowed(v_as_2410_, v_i_2411_);
lean_inc(v___x_2415_);
v___x_2416_ = l_Lean_IR_LocalContext_addParam(v_b_2413_, v___x_2415_);
v___x_2417_ = ((size_t)1ULL);
v___x_2418_ = lean_usize_add(v_i_2411_, v___x_2417_);
v_i_2411_ = v___x_2418_;
v_b_2413_ = v___x_2416_;
goto _start;
}
else
{
return v_b_2413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* v_as_2420_, lean_object* v_i_2421_, lean_object* v_stop_2422_, lean_object* v_b_2423_){
_start:
{
size_t v_i_boxed_2424_; size_t v_stop_boxed_2425_; lean_object* v_res_2426_; 
v_i_boxed_2424_ = lean_unbox_usize(v_i_2421_);
lean_dec(v_i_2421_);
v_stop_boxed_2425_ = lean_unbox_usize(v_stop_2422_);
lean_dec(v_stop_2422_);
v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_2420_, v_i_boxed_2424_, v_stop_boxed_2425_, v_b_2423_);
lean_dec_ref(v_as_2420_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* v_ctx_2427_, lean_object* v_ps_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = lean_array_get_size(v_ps_2428_);
v___x_2431_ = lean_nat_dec_lt(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
return v_ctx_2427_;
}
else
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_nat_dec_le(v___x_2430_, v___x_2430_);
if (v___x_2432_ == 0)
{
if (v___x_2431_ == 0)
{
return v_ctx_2427_;
}
else
{
size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = ((size_t)0ULL);
v___x_2434_ = lean_usize_of_nat(v___x_2430_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2428_, v___x_2433_, v___x_2434_, v_ctx_2427_);
return v___x_2435_;
}
}
else
{
size_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = lean_usize_of_nat(v___x_2430_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2428_, v___x_2436_, v___x_2437_, v_ctx_2427_);
return v___x_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_2439_, lean_object* v_ps_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_IR_LocalContext_addParams(v_ctx_2439_, v_ps_2440_);
lean_dec_ref(v_ps_2440_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(lean_object* v_t_2442_, lean_object* v_k_2443_){
_start:
{
if (lean_obj_tag(v_t_2442_) == 0)
{
lean_object* v_k_2444_; lean_object* v_v_2445_; lean_object* v_l_2446_; lean_object* v_r_2447_; uint8_t v___x_2448_; 
v_k_2444_ = lean_ctor_get(v_t_2442_, 1);
v_v_2445_ = lean_ctor_get(v_t_2442_, 2);
v_l_2446_ = lean_ctor_get(v_t_2442_, 3);
v_r_2447_ = lean_ctor_get(v_t_2442_, 4);
v___x_2448_ = lean_nat_dec_lt(v_k_2443_, v_k_2444_);
if (v___x_2448_ == 0)
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_nat_dec_eq(v_k_2443_, v_k_2444_);
if (v___x_2449_ == 0)
{
v_t_2442_ = v_r_2447_;
goto _start;
}
else
{
lean_object* v___x_2451_; 
lean_inc(v_v_2445_);
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_v_2445_);
return v___x_2451_;
}
}
else
{
v_t_2442_ = v_l_2446_;
goto _start;
}
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_box(0);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(lean_object* v_t_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_2454_, v_k_2455_);
lean_dec(v_k_2455_);
lean_dec(v_t_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_2457_, lean_object* v_idx_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2457_, v_idx_2458_);
if (lean_obj_tag(v___x_2459_) == 1)
{
lean_object* v_val_2460_; 
v_val_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v___x_2459_, 1);
if (lean_obj_tag(v_val_2460_) == 2)
{
uint8_t v___x_2461_; 
lean_dec_ref_known(v_val_2460_, 2);
v___x_2461_ = 1;
return v___x_2461_;
}
else
{
uint8_t v___x_2462_; 
lean_dec(v_val_2460_);
v___x_2462_ = 0;
return v___x_2462_;
}
}
else
{
uint8_t v___x_2463_; 
lean_dec(v___x_2459_);
v___x_2463_ = 0;
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_2464_, lean_object* v_idx_2465_){
_start:
{
uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_res_2466_ = l_Lean_IR_LocalContext_isJP(v_ctx_2464_, v_idx_2465_);
lean_dec(v_idx_2465_);
lean_dec(v_ctx_2464_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(lean_object* v_00_u03b4_2468_, lean_object* v_t_2469_, lean_object* v_k_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_2469_, v_k_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___boxed(lean_object* v_00_u03b4_2472_, lean_object* v_t_2473_, lean_object* v_k_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(v_00_u03b4_2472_, v_t_2473_, v_k_2474_);
lean_dec(v_k_2474_);
lean_dec(v_t_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_2476_, lean_object* v_j_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2476_, v_j_2477_);
if (lean_obj_tag(v___x_2478_) == 1)
{
lean_object* v_val_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2488_; 
v_val_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_val_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2488_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
if (lean_obj_tag(v_val_2479_) == 2)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; 
v_a_2483_ = lean_ctor_get(v_val_2479_, 1);
lean_inc(v_a_2483_);
lean_dec_ref_known(v_val_2479_, 2);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v_a_2483_);
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
else
{
lean_object* v___x_2487_; 
lean_del_object(v___x_2481_);
lean_dec(v_val_2479_);
v___x_2487_ = lean_box(0);
return v___x_2487_;
}
}
}
else
{
lean_object* v___x_2489_; 
lean_dec(v___x_2478_);
v___x_2489_ = lean_box(0);
return v___x_2489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_2490_, lean_object* v_j_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_2490_, v_j_2491_);
lean_dec(v_j_2491_);
lean_dec(v_ctx_2490_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_2493_, lean_object* v_j_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2493_, v_j_2494_);
if (lean_obj_tag(v___x_2495_) == 1)
{
lean_object* v_val_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2505_; 
v_val_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_val_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2505_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
if (lean_obj_tag(v_val_2496_) == 2)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; 
v_a_2500_ = lean_ctor_get(v_val_2496_, 0);
lean_inc_ref(v_a_2500_);
lean_dec_ref_known(v_val_2496_, 2);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v_a_2500_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
else
{
lean_object* v___x_2504_; 
lean_del_object(v___x_2498_);
lean_dec(v_val_2496_);
v___x_2504_ = lean_box(0);
return v___x_2504_;
}
}
}
else
{
lean_object* v___x_2506_; 
lean_dec(v___x_2495_);
v___x_2506_ = lean_box(0);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_2507_, lean_object* v_j_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_2507_, v_j_2508_);
lean_dec(v_j_2508_);
lean_dec(v_ctx_2507_);
return v_res_2509_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_2510_, lean_object* v_idx_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2510_, v_idx_2511_);
if (lean_obj_tag(v___x_2512_) == 1)
{
lean_object* v_val_2513_; 
v_val_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_val_2513_);
lean_dec_ref_known(v___x_2512_, 1);
if (lean_obj_tag(v_val_2513_) == 0)
{
uint8_t v___x_2514_; 
lean_dec_ref_known(v_val_2513_, 1);
v___x_2514_ = 1;
return v___x_2514_;
}
else
{
uint8_t v___x_2515_; 
lean_dec(v_val_2513_);
v___x_2515_ = 0;
return v___x_2515_;
}
}
else
{
uint8_t v___x_2516_; 
lean_dec(v___x_2512_);
v___x_2516_ = 0;
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_2517_, lean_object* v_idx_2518_){
_start:
{
uint8_t v_res_2519_; lean_object* v_r_2520_; 
v_res_2519_ = l_Lean_IR_LocalContext_isParam(v_ctx_2517_, v_idx_2518_);
lean_dec(v_idx_2518_);
lean_dec(v_ctx_2517_);
v_r_2520_ = lean_box(v_res_2519_);
return v_r_2520_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_2521_, lean_object* v_idx_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_2521_, v_idx_2522_);
if (lean_obj_tag(v___x_2523_) == 1)
{
lean_object* v_val_2524_; 
v_val_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v___x_2523_, 1);
if (lean_obj_tag(v_val_2524_) == 1)
{
uint8_t v___x_2525_; 
lean_dec_ref_known(v_val_2524_, 2);
v___x_2525_ = 1;
return v___x_2525_;
}
else
{
uint8_t v___x_2526_; 
lean_dec(v_val_2524_);
v___x_2526_ = 0;
return v___x_2526_;
}
}
else
{
uint8_t v___x_2527_; 
lean_dec(v___x_2523_);
v___x_2527_ = 0;
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_2528_, lean_object* v_idx_2529_){
_start:
{
uint8_t v_res_2530_; lean_object* v_r_2531_; 
v_res_2530_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_2528_, v_idx_2529_);
lean_dec(v_idx_2529_);
lean_dec(v_ctx_2528_);
v_r_2531_ = lean_box(v_res_2530_);
return v_r_2531_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object* v_ctx_2532_, lean_object* v_idx_2533_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2533_, v_ctx_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object* v_ctx_2535_, lean_object* v_idx_2536_){
_start:
{
uint8_t v_res_2537_; lean_object* v_r_2538_; 
v_res_2537_ = l_Lean_IR_LocalContext_contains(v_ctx_2535_, v_idx_2536_);
lean_dec(v_idx_2536_);
lean_dec(v_ctx_2535_);
v_r_2538_ = lean_box(v_res_2537_);
return v_r_2538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_2539_, lean_object* v_t_2540_){
_start:
{
if (lean_obj_tag(v_t_2540_) == 0)
{
lean_object* v_k_2541_; lean_object* v_v_2542_; lean_object* v_l_2543_; lean_object* v_r_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_3199_; 
v_k_2541_ = lean_ctor_get(v_t_2540_, 1);
v_v_2542_ = lean_ctor_get(v_t_2540_, 2);
v_l_2543_ = lean_ctor_get(v_t_2540_, 3);
v_r_2544_ = lean_ctor_get(v_t_2540_, 4);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_t_2540_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v_t_2540_, 0);
lean_dec(v_unused_3200_);
v___x_2546_ = v_t_2540_;
v_isShared_2547_ = v_isSharedCheck_3199_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_r_2544_);
lean_inc(v_l_2543_);
lean_inc(v_v_2542_);
lean_inc(v_k_2541_);
lean_dec(v_t_2540_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_3199_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_lt(v_k_2539_, v_k_2541_);
if (v___x_2548_ == 0)
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_nat_dec_eq(v_k_2539_, v_k_2541_);
if (v___x_2549_ == 0)
{
lean_object* v_impl_2550_; lean_object* v___x_2551_; 
v_impl_2550_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2539_, v_r_2544_);
v___x_2551_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2550_) == 0)
{
if (lean_obj_tag(v_l_2543_) == 0)
{
lean_object* v_size_2552_; lean_object* v_size_2553_; lean_object* v_k_2554_; lean_object* v_v_2555_; lean_object* v_l_2556_; lean_object* v_r_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v_size_2552_ = lean_ctor_get(v_impl_2550_, 0);
v_size_2553_ = lean_ctor_get(v_l_2543_, 0);
v_k_2554_ = lean_ctor_get(v_l_2543_, 1);
v_v_2555_ = lean_ctor_get(v_l_2543_, 2);
v_l_2556_ = lean_ctor_get(v_l_2543_, 3);
v_r_2557_ = lean_ctor_get(v_l_2543_, 4);
lean_inc(v_r_2557_);
v___x_2558_ = lean_unsigned_to_nat(3u);
v___x_2559_ = lean_nat_mul(v___x_2558_, v_size_2552_);
v___x_2560_ = lean_nat_dec_lt(v___x_2559_, v_size_2553_);
lean_dec(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
lean_dec(v_r_2557_);
v___x_2561_ = lean_nat_add(v___x_2551_, v_size_2553_);
v___x_2562_ = lean_nat_add(v___x_2561_, v_size_2552_);
lean_dec(v___x_2561_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_impl_2550_);
lean_ctor_set(v___x_2546_, 0, v___x_2562_);
v___x_2564_ = v___x_2546_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_impl_2550_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2631_; 
lean_inc(v_l_2556_);
lean_inc(v_v_2555_);
lean_inc(v_k_2554_);
lean_inc(v_size_2553_);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; 
v_unused_2632_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_l_2543_, 2);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_l_2543_, 1);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2636_);
v___x_2567_ = v_l_2543_;
v_isShared_2568_ = v_isSharedCheck_2631_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v_l_2543_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2631_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_size_2569_; lean_object* v_size_2570_; lean_object* v_k_2571_; lean_object* v_v_2572_; lean_object* v_l_2573_; lean_object* v_r_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v_size_2569_ = lean_ctor_get(v_l_2556_, 0);
v_size_2570_ = lean_ctor_get(v_r_2557_, 0);
v_k_2571_ = lean_ctor_get(v_r_2557_, 1);
v_v_2572_ = lean_ctor_get(v_r_2557_, 2);
v_l_2573_ = lean_ctor_get(v_r_2557_, 3);
v_r_2574_ = lean_ctor_get(v_r_2557_, 4);
v___x_2575_ = lean_unsigned_to_nat(2u);
v___x_2576_ = lean_nat_mul(v___x_2575_, v_size_2569_);
v___x_2577_ = lean_nat_dec_lt(v_size_2570_, v___x_2576_);
lean_dec(v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2606_; 
lean_inc(v_r_2574_);
lean_inc(v_l_2573_);
lean_inc(v_v_2572_);
lean_inc(v_k_2571_);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_r_2557_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; lean_object* v_unused_2610_; lean_object* v_unused_2611_; 
v_unused_2607_ = lean_ctor_get(v_r_2557_, 4);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_r_2557_, 3);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_r_2557_, 2);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v_r_2557_, 1);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v_r_2557_, 0);
lean_dec(v_unused_2611_);
v___x_2579_ = v_r_2557_;
v_isShared_2580_ = v_isSharedCheck_2606_;
goto v_resetjp_2578_;
}
else
{
lean_dec(v_r_2557_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2606_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___x_2594_; lean_object* v___y_2596_; 
v___x_2581_ = lean_nat_add(v___x_2551_, v_size_2553_);
lean_dec(v_size_2553_);
v___x_2582_ = lean_nat_add(v___x_2581_, v_size_2552_);
lean_dec(v___x_2581_);
v___x_2594_ = lean_nat_add(v___x_2551_, v_size_2569_);
if (lean_obj_tag(v_l_2573_) == 0)
{
lean_object* v_size_2604_; 
v_size_2604_ = lean_ctor_get(v_l_2573_, 0);
lean_inc(v_size_2604_);
v___y_2596_ = v_size_2604_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___y_2596_ = v___x_2605_;
goto v___jp_2595_;
}
v___jp_2583_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_nat_add(v___y_2584_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec(v___y_2584_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_impl_2550_);
lean_ctor_set(v___x_2579_, 3, v_r_2574_);
lean_ctor_set(v___x_2579_, 2, v_v_2542_);
lean_ctor_set(v___x_2579_, 1, v_k_2541_);
lean_ctor_set(v___x_2579_, 0, v___x_2587_);
v___x_2589_ = v___x_2579_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_r_2574_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_impl_2550_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 4, v___x_2589_);
lean_ctor_set(v___x_2567_, 3, v___y_2585_);
lean_ctor_set(v___x_2567_, 2, v_v_2572_);
lean_ctor_set(v___x_2567_, 1, v_k_2571_);
lean_ctor_set(v___x_2567_, 0, v___x_2582_);
v___x_2591_ = v___x_2567_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_k_2571_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_v_2572_);
lean_ctor_set(v_reuseFailAlloc_2592_, 3, v___y_2585_);
lean_ctor_set(v_reuseFailAlloc_2592_, 4, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
v___jp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = lean_nat_add(v___x_2594_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec(v___x_2594_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_l_2573_);
lean_ctor_set(v___x_2546_, 3, v_l_2556_);
lean_ctor_set(v___x_2546_, 2, v_v_2555_);
lean_ctor_set(v___x_2546_, 1, v_k_2554_);
lean_ctor_set(v___x_2546_, 0, v___x_2597_);
v___x_2599_ = v___x_2546_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2554_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_v_2555_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_l_2556_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_l_2573_);
v___x_2599_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_nat_add(v___x_2551_, v_size_2552_);
if (lean_obj_tag(v_r_2574_) == 0)
{
lean_object* v_size_2601_; 
v_size_2601_ = lean_ctor_get(v_r_2574_, 0);
lean_inc(v_size_2601_);
v___y_2584_ = v___x_2600_;
v___y_2585_ = v___x_2599_;
v___y_2586_ = v_size_2601_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_unsigned_to_nat(0u);
v___y_2584_ = v___x_2600_;
v___y_2585_ = v___x_2599_;
v___y_2586_ = v___x_2602_;
goto v___jp_2583_;
}
}
}
}
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_del_object(v___x_2546_);
v___x_2612_ = lean_nat_add(v___x_2551_, v_size_2553_);
lean_dec(v_size_2553_);
v___x_2613_ = lean_nat_add(v___x_2612_, v_size_2552_);
lean_dec(v___x_2612_);
v___x_2614_ = lean_nat_add(v___x_2551_, v_size_2552_);
v___x_2615_ = lean_nat_add(v___x_2614_, v_size_2570_);
lean_dec(v___x_2614_);
lean_inc_ref(v_impl_2550_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 4, v_impl_2550_);
lean_ctor_set(v___x_2567_, 3, v_r_2557_);
lean_ctor_set(v___x_2567_, 2, v_v_2542_);
lean_ctor_set(v___x_2567_, 1, v_k_2541_);
lean_ctor_set(v___x_2567_, 0, v___x_2615_);
v___x_2617_ = v___x_2567_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_r_2557_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_impl_2550_);
v___x_2617_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_isSharedCheck_2624_ = !lean_is_exclusive(v_impl_2550_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; lean_object* v_unused_2626_; lean_object* v_unused_2627_; lean_object* v_unused_2628_; lean_object* v_unused_2629_; 
v_unused_2625_ = lean_ctor_get(v_impl_2550_, 4);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_impl_2550_, 3);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_impl_2550_, 2);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_impl_2550_, 1);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_impl_2550_, 0);
lean_dec(v_unused_2629_);
v___x_2619_ = v_impl_2550_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v_impl_2550_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v___x_2617_);
lean_ctor_set(v___x_2619_, 3, v_l_2556_);
lean_ctor_set(v___x_2619_, 2, v_v_2555_);
lean_ctor_set(v___x_2619_, 1, v_k_2554_);
lean_ctor_set(v___x_2619_, 0, v___x_2613_);
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_k_2554_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_v_2555_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_l_2556_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v___x_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v_size_2637_ = lean_ctor_get(v_impl_2550_, 0);
v___x_2638_ = lean_nat_add(v___x_2551_, v_size_2637_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_impl_2550_);
lean_ctor_set(v___x_2546_, 0, v___x_2638_);
v___x_2640_ = v___x_2546_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_impl_2550_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
if (lean_obj_tag(v_l_2543_) == 0)
{
lean_object* v_l_2642_; 
v_l_2642_ = lean_ctor_get(v_l_2543_, 3);
if (lean_obj_tag(v_l_2642_) == 0)
{
lean_object* v_r_2643_; 
lean_inc_ref(v_l_2642_);
v_r_2643_ = lean_ctor_get(v_l_2543_, 4);
lean_inc(v_r_2643_);
if (lean_obj_tag(v_r_2643_) == 0)
{
lean_object* v_size_2644_; lean_object* v_k_2645_; lean_object* v_v_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2659_; 
v_size_2644_ = lean_ctor_get(v_l_2543_, 0);
v_k_2645_ = lean_ctor_get(v_l_2543_, 1);
v_v_2646_ = lean_ctor_get(v_l_2543_, 2);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2659_ == 0)
{
lean_object* v_unused_2660_; lean_object* v_unused_2661_; 
v_unused_2660_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2661_);
v___x_2648_ = v_l_2543_;
v_isShared_2649_ = v_isSharedCheck_2659_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_v_2646_);
lean_inc(v_k_2645_);
lean_inc(v_size_2644_);
lean_dec(v_l_2543_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2659_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_size_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v_size_2650_ = lean_ctor_get(v_r_2643_, 0);
v___x_2651_ = lean_nat_add(v___x_2551_, v_size_2644_);
lean_dec(v_size_2644_);
v___x_2652_ = lean_nat_add(v___x_2551_, v_size_2650_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 4, v_impl_2550_);
lean_ctor_set(v___x_2648_, 3, v_r_2643_);
lean_ctor_set(v___x_2648_, 2, v_v_2542_);
lean_ctor_set(v___x_2648_, 1, v_k_2541_);
lean_ctor_set(v___x_2648_, 0, v___x_2652_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2658_, 3, v_r_2643_);
lean_ctor_set(v_reuseFailAlloc_2658_, 4, v_impl_2550_);
v___x_2654_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v___x_2654_);
lean_ctor_set(v___x_2546_, 3, v_l_2642_);
lean_ctor_set(v___x_2546_, 2, v_v_2646_);
lean_ctor_set(v___x_2546_, 1, v_k_2645_);
lean_ctor_set(v___x_2546_, 0, v___x_2651_);
v___x_2656_ = v___x_2546_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_k_2645_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_v_2646_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_l_2642_);
lean_ctor_set(v_reuseFailAlloc_2657_, 4, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_k_2662_; lean_object* v_v_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2674_; 
v_k_2662_ = lean_ctor_get(v_l_2543_, 1);
v_v_2663_ = lean_ctor_get(v_l_2543_, 2);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; 
v_unused_2675_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2677_);
v___x_2665_ = v_l_2543_;
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_v_2663_);
lean_inc(v_k_2662_);
lean_dec(v_l_2543_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = lean_unsigned_to_nat(3u);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 3, v_r_2643_);
lean_ctor_set(v___x_2665_, 2, v_v_2542_);
lean_ctor_set(v___x_2665_, 1, v_k_2541_);
lean_ctor_set(v___x_2665_, 0, v___x_2551_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_r_2643_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_r_2643_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v___x_2669_);
lean_ctor_set(v___x_2546_, 3, v_l_2642_);
lean_ctor_set(v___x_2546_, 2, v_v_2663_);
lean_ctor_set(v___x_2546_, 1, v_k_2662_);
lean_ctor_set(v___x_2546_, 0, v___x_2667_);
v___x_2671_ = v___x_2546_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_k_2662_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_v_2663_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_l_2642_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
else
{
lean_object* v_r_2678_; 
v_r_2678_ = lean_ctor_get(v_l_2543_, 4);
lean_inc(v_r_2678_);
if (lean_obj_tag(v_r_2678_) == 0)
{
lean_object* v_k_2679_; lean_object* v_v_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2703_; 
lean_inc(v_l_2642_);
v_k_2679_ = lean_ctor_get(v_l_2543_, 1);
v_v_2680_ = lean_ctor_get(v_l_2543_, 2);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2704_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2706_);
v___x_2682_ = v_l_2543_;
v_isShared_2683_ = v_isSharedCheck_2703_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_v_2680_);
lean_inc(v_k_2679_);
lean_dec(v_l_2543_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2703_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v_k_2684_; lean_object* v_v_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2699_; 
v_k_2684_ = lean_ctor_get(v_r_2678_, 1);
v_v_2685_ = lean_ctor_get(v_r_2678_, 2);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_r_2678_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; lean_object* v_unused_2701_; lean_object* v_unused_2702_; 
v_unused_2700_ = lean_ctor_get(v_r_2678_, 4);
lean_dec(v_unused_2700_);
v_unused_2701_ = lean_ctor_get(v_r_2678_, 3);
lean_dec(v_unused_2701_);
v_unused_2702_ = lean_ctor_get(v_r_2678_, 0);
lean_dec(v_unused_2702_);
v___x_2687_ = v_r_2678_;
v_isShared_2688_ = v_isSharedCheck_2699_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_v_2685_);
lean_inc(v_k_2684_);
lean_dec(v_r_2678_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2699_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2689_ = lean_unsigned_to_nat(3u);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v_l_2642_);
lean_ctor_set(v___x_2687_, 3, v_l_2642_);
lean_ctor_set(v___x_2687_, 2, v_v_2680_);
lean_ctor_set(v___x_2687_, 1, v_k_2679_);
lean_ctor_set(v___x_2687_, 0, v___x_2551_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_k_2679_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_v_2680_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_l_2642_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v_l_2642_);
v___x_2691_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 4, v_l_2642_);
lean_ctor_set(v___x_2682_, 2, v_v_2542_);
lean_ctor_set(v___x_2682_, 1, v_k_2541_);
lean_ctor_set(v___x_2682_, 0, v___x_2551_);
v___x_2693_ = v___x_2682_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_l_2642_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_l_2642_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2695_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v___x_2693_);
lean_ctor_set(v___x_2546_, 3, v___x_2691_);
lean_ctor_set(v___x_2546_, 2, v_v_2685_);
lean_ctor_set(v___x_2546_, 1, v_k_2684_);
lean_ctor_set(v___x_2546_, 0, v___x_2689_);
v___x_2695_ = v___x_2546_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_k_2684_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_v_2685_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_unsigned_to_nat(2u);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_r_2678_);
lean_ctor_set(v___x_2546_, 0, v___x_2707_);
v___x_2709_ = v___x_2546_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v_r_2678_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v___x_2712_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_l_2543_);
lean_ctor_set(v___x_2546_, 0, v___x_2551_);
v___x_2712_ = v___x_2546_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2713_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2713_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_2713_, 4, v_l_2543_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
else
{
lean_del_object(v___x_2546_);
lean_dec(v_v_2542_);
lean_dec(v_k_2541_);
if (lean_obj_tag(v_l_2543_) == 0)
{
if (lean_obj_tag(v_r_2544_) == 0)
{
lean_object* v_size_2714_; lean_object* v_k_2715_; lean_object* v_v_2716_; lean_object* v_l_2717_; lean_object* v_r_2718_; lean_object* v_size_2719_; lean_object* v_k_2720_; lean_object* v_v_2721_; lean_object* v_l_2722_; lean_object* v_r_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_size_2714_ = lean_ctor_get(v_l_2543_, 0);
v_k_2715_ = lean_ctor_get(v_l_2543_, 1);
v_v_2716_ = lean_ctor_get(v_l_2543_, 2);
v_l_2717_ = lean_ctor_get(v_l_2543_, 3);
v_r_2718_ = lean_ctor_get(v_l_2543_, 4);
lean_inc(v_r_2718_);
v_size_2719_ = lean_ctor_get(v_r_2544_, 0);
v_k_2720_ = lean_ctor_get(v_r_2544_, 1);
v_v_2721_ = lean_ctor_get(v_r_2544_, 2);
v_l_2722_ = lean_ctor_get(v_r_2544_, 3);
lean_inc(v_l_2722_);
v_r_2723_ = lean_ctor_get(v_r_2544_, 4);
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_nat_dec_lt(v_size_2714_, v_size_2719_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2861_; 
lean_inc(v_l_2717_);
lean_inc(v_v_2716_);
lean_inc(v_k_2715_);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; lean_object* v_unused_2863_; lean_object* v_unused_2864_; lean_object* v_unused_2865_; lean_object* v_unused_2866_; 
v_unused_2862_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2862_);
v_unused_2863_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_l_2543_, 2);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_l_2543_, 1);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2866_);
v___x_2727_ = v_l_2543_;
v_isShared_2728_ = v_isSharedCheck_2861_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v_l_2543_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2861_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v_tree_2730_; 
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2715_, v_v_2716_, v_l_2717_, v_r_2718_);
v_tree_2730_ = lean_ctor_get(v___x_2729_, 2);
if (lean_obj_tag(v_tree_2730_) == 0)
{
lean_object* v_k_2731_; lean_object* v_v_2732_; lean_object* v_size_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
lean_inc_ref(v_tree_2730_);
v_k_2731_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_k_2731_);
v_v_2732_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_v_2732_);
lean_dec_ref(v___x_2729_);
v_size_2733_ = lean_ctor_get(v_tree_2730_, 0);
v___x_2734_ = lean_unsigned_to_nat(3u);
v___x_2735_ = lean_nat_mul(v___x_2734_, v_size_2733_);
v___x_2736_ = lean_nat_dec_lt(v___x_2735_, v_size_2719_);
lean_dec(v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec(v_l_2722_);
v___x_2737_ = lean_nat_add(v___x_2724_, v_size_2733_);
v___x_2738_ = lean_nat_add(v___x_2737_, v_size_2719_);
lean_dec(v___x_2737_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v_r_2544_);
lean_ctor_set(v___x_2727_, 3, v_tree_2730_);
lean_ctor_set(v___x_2727_, 2, v_v_2732_);
lean_ctor_set(v___x_2727_, 1, v_k_2731_);
lean_ctor_set(v___x_2727_, 0, v___x_2738_);
v___x_2740_ = v___x_2727_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2741_, 3, v_tree_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 4, v_r_2544_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2796_; 
lean_inc(v_r_2723_);
lean_inc(v_v_2721_);
lean_inc(v_k_2720_);
lean_inc(v_size_2719_);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; lean_object* v_unused_2800_; lean_object* v_unused_2801_; 
v_unused_2797_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_r_2544_, 2);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_r_2544_, 1);
lean_dec(v_unused_2800_);
v_unused_2801_ = lean_ctor_get(v_r_2544_, 0);
lean_dec(v_unused_2801_);
v___x_2743_ = v_r_2544_;
v_isShared_2744_ = v_isSharedCheck_2796_;
goto v_resetjp_2742_;
}
else
{
lean_dec(v_r_2544_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2796_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_size_2745_; lean_object* v_k_2746_; lean_object* v_v_2747_; lean_object* v_l_2748_; lean_object* v_r_2749_; lean_object* v_size_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v_size_2745_ = lean_ctor_get(v_l_2722_, 0);
v_k_2746_ = lean_ctor_get(v_l_2722_, 1);
v_v_2747_ = lean_ctor_get(v_l_2722_, 2);
v_l_2748_ = lean_ctor_get(v_l_2722_, 3);
v_r_2749_ = lean_ctor_get(v_l_2722_, 4);
v_size_2750_ = lean_ctor_get(v_r_2723_, 0);
v___x_2751_ = lean_unsigned_to_nat(2u);
v___x_2752_ = lean_nat_mul(v___x_2751_, v_size_2750_);
v___x_2753_ = lean_nat_dec_lt(v_size_2745_, v___x_2752_);
lean_dec(v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2781_; 
lean_inc(v_r_2749_);
lean_inc(v_l_2748_);
lean_inc(v_v_2747_);
lean_inc(v_k_2746_);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_l_2722_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; lean_object* v_unused_2783_; lean_object* v_unused_2784_; lean_object* v_unused_2785_; lean_object* v_unused_2786_; 
v_unused_2782_ = lean_ctor_get(v_l_2722_, 4);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_l_2722_, 3);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_l_2722_, 2);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_l_2722_, 1);
lean_dec(v_unused_2785_);
v_unused_2786_ = lean_ctor_get(v_l_2722_, 0);
lean_dec(v_unused_2786_);
v___x_2755_ = v_l_2722_;
v_isShared_2756_ = v_isSharedCheck_2781_;
goto v_resetjp_2754_;
}
else
{
lean_dec(v_l_2722_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2781_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2771_; 
v___x_2757_ = lean_nat_add(v___x_2724_, v_size_2733_);
v___x_2758_ = lean_nat_add(v___x_2757_, v_size_2719_);
lean_dec(v_size_2719_);
if (lean_obj_tag(v_l_2748_) == 0)
{
lean_object* v_size_2779_; 
v_size_2779_ = lean_ctor_get(v_l_2748_, 0);
lean_inc(v_size_2779_);
v___y_2771_ = v_size_2779_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_unsigned_to_nat(0u);
v___y_2771_ = v___x_2780_;
goto v___jp_2770_;
}
v___jp_2759_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = lean_nat_add(v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec(v___y_2761_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 4, v_r_2723_);
lean_ctor_set(v___x_2755_, 3, v_r_2749_);
lean_ctor_set(v___x_2755_, 2, v_v_2721_);
lean_ctor_set(v___x_2755_, 1, v_k_2720_);
lean_ctor_set(v___x_2755_, 0, v___x_2763_);
v___x_2765_ = v___x_2755_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2769_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2769_, 3, v_r_2749_);
lean_ctor_set(v_reuseFailAlloc_2769_, 4, v_r_2723_);
v___x_2765_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2767_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v___x_2765_);
lean_ctor_set(v___x_2743_, 3, v___y_2760_);
lean_ctor_set(v___x_2743_, 2, v_v_2747_);
lean_ctor_set(v___x_2743_, 1, v_k_2746_);
lean_ctor_set(v___x_2743_, 0, v___x_2758_);
v___x_2767_ = v___x_2743_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_k_2746_);
lean_ctor_set(v_reuseFailAlloc_2768_, 2, v_v_2747_);
lean_ctor_set(v_reuseFailAlloc_2768_, 3, v___y_2760_);
lean_ctor_set(v_reuseFailAlloc_2768_, 4, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
v___jp_2770_:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_nat_add(v___x_2757_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec(v___x_2757_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v_l_2748_);
lean_ctor_set(v___x_2727_, 3, v_tree_2730_);
lean_ctor_set(v___x_2727_, 2, v_v_2732_);
lean_ctor_set(v___x_2727_, 1, v_k_2731_);
lean_ctor_set(v___x_2727_, 0, v___x_2772_);
v___x_2774_ = v___x_2727_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_tree_2730_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v_l_2748_);
v___x_2774_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_nat_add(v___x_2724_, v_size_2750_);
if (lean_obj_tag(v_r_2749_) == 0)
{
lean_object* v_size_2776_; 
v_size_2776_ = lean_ctor_get(v_r_2749_, 0);
lean_inc(v_size_2776_);
v___y_2760_ = v___x_2774_;
v___y_2761_ = v___x_2775_;
v___y_2762_ = v_size_2776_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___y_2760_ = v___x_2774_;
v___y_2761_ = v___x_2775_;
v___y_2762_ = v___x_2777_;
goto v___jp_2759_;
}
}
}
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2787_ = lean_nat_add(v___x_2724_, v_size_2733_);
v___x_2788_ = lean_nat_add(v___x_2787_, v_size_2719_);
lean_dec(v_size_2719_);
v___x_2789_ = lean_nat_add(v___x_2787_, v_size_2745_);
lean_dec(v___x_2787_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v_l_2722_);
lean_ctor_set(v___x_2743_, 3, v_tree_2730_);
lean_ctor_set(v___x_2743_, 2, v_v_2732_);
lean_ctor_set(v___x_2743_, 1, v_k_2731_);
lean_ctor_set(v___x_2743_, 0, v___x_2789_);
v___x_2791_ = v___x_2743_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v_tree_2730_);
lean_ctor_set(v_reuseFailAlloc_2795_, 4, v_l_2722_);
v___x_2791_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v_r_2723_);
lean_ctor_set(v___x_2727_, 3, v___x_2791_);
lean_ctor_set(v___x_2727_, 2, v_v_2721_);
lean_ctor_set(v___x_2727_, 1, v_k_2720_);
lean_ctor_set(v___x_2727_, 0, v___x_2788_);
v___x_2793_ = v___x_2727_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_r_2723_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
else
{
lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2855_; 
lean_inc(v_r_2723_);
lean_inc(v_v_2721_);
lean_inc(v_k_2720_);
lean_inc(v_size_2719_);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; lean_object* v_unused_2857_; lean_object* v_unused_2858_; lean_object* v_unused_2859_; lean_object* v_unused_2860_; 
v_unused_2856_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_2857_);
v_unused_2858_ = lean_ctor_get(v_r_2544_, 2);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_r_2544_, 1);
lean_dec(v_unused_2859_);
v_unused_2860_ = lean_ctor_get(v_r_2544_, 0);
lean_dec(v_unused_2860_);
v___x_2803_ = v_r_2544_;
v_isShared_2804_ = v_isSharedCheck_2855_;
goto v_resetjp_2802_;
}
else
{
lean_dec(v_r_2544_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2855_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
if (lean_obj_tag(v_l_2722_) == 0)
{
if (lean_obj_tag(v_r_2723_) == 0)
{
lean_object* v_k_2805_; lean_object* v_v_2806_; lean_object* v_size_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
lean_inc(v_tree_2730_);
v_k_2805_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_k_2805_);
v_v_2806_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_v_2806_);
lean_dec_ref(v___x_2729_);
v_size_2807_ = lean_ctor_get(v_l_2722_, 0);
v___x_2808_ = lean_nat_add(v___x_2724_, v_size_2719_);
lean_dec(v_size_2719_);
v___x_2809_ = lean_nat_add(v___x_2724_, v_size_2807_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 4, v_l_2722_);
lean_ctor_set(v___x_2803_, 3, v_tree_2730_);
lean_ctor_set(v___x_2803_, 2, v_v_2806_);
lean_ctor_set(v___x_2803_, 1, v_k_2805_);
lean_ctor_set(v___x_2803_, 0, v___x_2809_);
v___x_2811_ = v___x_2803_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2809_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_k_2805_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_v_2806_);
lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_tree_2730_);
lean_ctor_set(v_reuseFailAlloc_2815_, 4, v_l_2722_);
v___x_2811_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v_r_2723_);
lean_ctor_set(v___x_2727_, 3, v___x_2811_);
lean_ctor_set(v___x_2727_, 2, v_v_2721_);
lean_ctor_set(v___x_2727_, 1, v_k_2720_);
lean_ctor_set(v___x_2727_, 0, v___x_2808_);
v___x_2813_ = v___x_2727_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_r_2723_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v_k_2816_; lean_object* v_v_2817_; lean_object* v_k_2818_; lean_object* v_v_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_size_2719_);
v_k_2816_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_k_2816_);
v_v_2817_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_v_2817_);
lean_dec_ref(v___x_2729_);
v_k_2818_ = lean_ctor_get(v_l_2722_, 1);
v_v_2819_ = lean_ctor_get(v_l_2722_, 2);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_l_2722_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; lean_object* v_unused_2835_; lean_object* v_unused_2836_; 
v_unused_2834_ = lean_ctor_get(v_l_2722_, 4);
lean_dec(v_unused_2834_);
v_unused_2835_ = lean_ctor_get(v_l_2722_, 3);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_l_2722_, 0);
lean_dec(v_unused_2836_);
v___x_2821_ = v_l_2722_;
v_isShared_2822_ = v_isSharedCheck_2833_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_v_2819_);
lean_inc(v_k_2818_);
lean_dec(v_l_2722_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2833_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_unsigned_to_nat(3u);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 4, v_r_2723_);
lean_ctor_set(v___x_2821_, 3, v_r_2723_);
lean_ctor_set(v___x_2821_, 2, v_v_2817_);
lean_ctor_set(v___x_2821_, 1, v_k_2816_);
lean_ctor_set(v___x_2821_, 0, v___x_2724_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2816_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2817_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_r_2723_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_r_2723_);
v___x_2825_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 3, v_r_2723_);
lean_ctor_set(v___x_2803_, 0, v___x_2724_);
v___x_2827_ = v___x_2803_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2831_, 3, v_r_2723_);
lean_ctor_set(v_reuseFailAlloc_2831_, 4, v_r_2723_);
v___x_2827_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2829_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v___x_2827_);
lean_ctor_set(v___x_2727_, 3, v___x_2825_);
lean_ctor_set(v___x_2727_, 2, v_v_2819_);
lean_ctor_set(v___x_2727_, 1, v_k_2818_);
lean_ctor_set(v___x_2727_, 0, v___x_2823_);
v___x_2829_ = v___x_2727_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_k_2818_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_v_2819_);
lean_ctor_set(v_reuseFailAlloc_2830_, 3, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2830_, 4, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2723_) == 0)
{
lean_object* v_k_2837_; lean_object* v_v_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
lean_dec(v_size_2719_);
v_k_2837_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_k_2837_);
v_v_2838_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_v_2838_);
lean_dec_ref(v___x_2729_);
v___x_2839_ = lean_unsigned_to_nat(3u);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 4, v_l_2722_);
lean_ctor_set(v___x_2803_, 2, v_v_2838_);
lean_ctor_set(v___x_2803_, 1, v_k_2837_);
lean_ctor_set(v___x_2803_, 0, v___x_2724_);
v___x_2841_ = v___x_2803_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_k_2837_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_v_2838_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_l_2722_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_l_2722_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v_r_2723_);
lean_ctor_set(v___x_2727_, 3, v___x_2841_);
lean_ctor_set(v___x_2727_, 2, v_v_2721_);
lean_ctor_set(v___x_2727_, 1, v_k_2720_);
lean_ctor_set(v___x_2727_, 0, v___x_2839_);
v___x_2843_ = v___x_2727_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v_r_2723_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_k_2846_; lean_object* v_v_2847_; lean_object* v___x_2849_; 
v_k_2846_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_k_2846_);
v_v_2847_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_v_2847_);
lean_dec_ref(v___x_2729_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 3, v_r_2723_);
v___x_2849_ = v___x_2803_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_size_2719_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_r_2723_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_r_2723_);
v___x_2849_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(2u);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v___x_2849_);
lean_ctor_set(v___x_2727_, 3, v_r_2723_);
lean_ctor_set(v___x_2727_, 2, v_v_2847_);
lean_ctor_set(v___x_2727_, 1, v_k_2846_);
lean_ctor_set(v___x_2727_, 0, v___x_2850_);
v___x_2852_ = v___x_2727_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_k_2846_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_v_2847_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_r_2723_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v___x_2849_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
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
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_3019_; 
lean_inc(v_r_2723_);
lean_inc(v_v_2721_);
lean_inc(v_k_2720_);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; lean_object* v_unused_3021_; lean_object* v_unused_3022_; lean_object* v_unused_3023_; lean_object* v_unused_3024_; 
v_unused_3020_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_3020_);
v_unused_3021_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v_r_2544_, 2);
lean_dec(v_unused_3022_);
v_unused_3023_ = lean_ctor_get(v_r_2544_, 1);
lean_dec(v_unused_3023_);
v_unused_3024_ = lean_ctor_get(v_r_2544_, 0);
lean_dec(v_unused_3024_);
v___x_2868_ = v_r_2544_;
v_isShared_2869_ = v_isSharedCheck_3019_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v_r_2544_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_3019_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v_tree_2871_; 
v___x_2870_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2720_, v_v_2721_, v_l_2722_, v_r_2723_);
v_tree_2871_ = lean_ctor_get(v___x_2870_, 2);
lean_inc(v_tree_2871_);
if (lean_obj_tag(v_tree_2871_) == 0)
{
lean_object* v_k_2872_; lean_object* v_v_2873_; lean_object* v_size_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_k_2872_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_k_2872_);
v_v_2873_ = lean_ctor_get(v___x_2870_, 1);
lean_inc(v_v_2873_);
lean_dec_ref(v___x_2870_);
v_size_2874_ = lean_ctor_get(v_tree_2871_, 0);
v___x_2875_ = lean_unsigned_to_nat(3u);
v___x_2876_ = lean_nat_mul(v___x_2875_, v_size_2874_);
v___x_2877_ = lean_nat_dec_lt(v___x_2876_, v_size_2714_);
lean_dec(v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_dec(v_r_2718_);
v___x_2878_ = lean_nat_add(v___x_2724_, v_size_2714_);
v___x_2879_ = lean_nat_add(v___x_2878_, v_size_2874_);
lean_dec(v___x_2878_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_tree_2871_);
lean_ctor_set(v___x_2868_, 3, v_l_2543_);
lean_ctor_set(v___x_2868_, 2, v_v_2873_);
lean_ctor_set(v___x_2868_, 1, v_k_2872_);
lean_ctor_set(v___x_2868_, 0, v___x_2879_);
v___x_2881_ = v___x_2868_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_k_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_v_2873_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_tree_2871_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
else
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2948_; 
lean_inc(v_l_2717_);
lean_inc(v_v_2716_);
lean_inc(v_k_2715_);
lean_inc(v_size_2714_);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; lean_object* v_unused_2951_; lean_object* v_unused_2952_; lean_object* v_unused_2953_; 
v_unused_2949_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_l_2543_, 2);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v_l_2543_, 1);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2953_);
v___x_2884_ = v_l_2543_;
v_isShared_2885_ = v_isSharedCheck_2948_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v_l_2543_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2948_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v_size_2886_; lean_object* v_size_2887_; lean_object* v_k_2888_; lean_object* v_v_2889_; lean_object* v_l_2890_; lean_object* v_r_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v_size_2886_ = lean_ctor_get(v_l_2717_, 0);
v_size_2887_ = lean_ctor_get(v_r_2718_, 0);
v_k_2888_ = lean_ctor_get(v_r_2718_, 1);
v_v_2889_ = lean_ctor_get(v_r_2718_, 2);
v_l_2890_ = lean_ctor_get(v_r_2718_, 3);
v_r_2891_ = lean_ctor_get(v_r_2718_, 4);
v___x_2892_ = lean_unsigned_to_nat(2u);
v___x_2893_ = lean_nat_mul(v___x_2892_, v_size_2886_);
v___x_2894_ = lean_nat_dec_lt(v_size_2887_, v___x_2893_);
lean_dec(v___x_2893_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2932_; 
lean_inc(v_r_2891_);
lean_inc(v_l_2890_);
lean_inc(v_v_2889_);
lean_inc(v_k_2888_);
lean_del_object(v___x_2884_);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_r_2718_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; lean_object* v_unused_2934_; lean_object* v_unused_2935_; lean_object* v_unused_2936_; lean_object* v_unused_2937_; 
v_unused_2933_ = lean_ctor_get(v_r_2718_, 4);
lean_dec(v_unused_2933_);
v_unused_2934_ = lean_ctor_get(v_r_2718_, 3);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_r_2718_, 2);
lean_dec(v_unused_2935_);
v_unused_2936_ = lean_ctor_get(v_r_2718_, 1);
lean_dec(v_unused_2936_);
v_unused_2937_ = lean_ctor_get(v_r_2718_, 0);
lean_dec(v_unused_2937_);
v___x_2896_ = v_r_2718_;
v_isShared_2897_ = v_isSharedCheck_2932_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v_r_2718_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2932_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___x_2920_; lean_object* v___y_2922_; 
v___x_2898_ = lean_nat_add(v___x_2724_, v_size_2714_);
lean_dec(v_size_2714_);
v___x_2899_ = lean_nat_add(v___x_2898_, v_size_2874_);
lean_dec(v___x_2898_);
v___x_2920_ = lean_nat_add(v___x_2724_, v_size_2886_);
if (lean_obj_tag(v_l_2890_) == 0)
{
lean_object* v_size_2930_; 
v_size_2930_ = lean_ctor_get(v_l_2890_, 0);
lean_inc(v_size_2930_);
v___y_2922_ = v_size_2930_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_unsigned_to_nat(0u);
v___y_2922_ = v___x_2931_;
goto v___jp_2921_;
}
v___jp_2900_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_nat_add(v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec(v___y_2902_);
lean_inc_ref(v_tree_2871_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 4, v_tree_2871_);
lean_ctor_set(v___x_2896_, 3, v_r_2891_);
lean_ctor_set(v___x_2896_, 2, v_v_2873_);
lean_ctor_set(v___x_2896_, 1, v_k_2872_);
lean_ctor_set(v___x_2896_, 0, v___x_2904_);
v___x_2906_ = v___x_2896_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_k_2872_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_v_2873_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_r_2891_);
lean_ctor_set(v_reuseFailAlloc_2919_, 4, v_tree_2871_);
v___x_2906_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_isSharedCheck_2913_ = !lean_is_exclusive(v_tree_2871_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2914_ = lean_ctor_get(v_tree_2871_, 4);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_tree_2871_, 3);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_tree_2871_, 2);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_tree_2871_, 1);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_tree_2871_, 0);
lean_dec(v_unused_2918_);
v___x_2908_ = v_tree_2871_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v_tree_2871_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 4, v___x_2906_);
lean_ctor_set(v___x_2908_, 3, v___y_2901_);
lean_ctor_set(v___x_2908_, 2, v_v_2889_);
lean_ctor_set(v___x_2908_, 1, v_k_2888_);
lean_ctor_set(v___x_2908_, 0, v___x_2899_);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2888_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2889_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v___y_2901_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
v___jp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2923_ = lean_nat_add(v___x_2920_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec(v___x_2920_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_l_2890_);
lean_ctor_set(v___x_2868_, 3, v_l_2717_);
lean_ctor_set(v___x_2868_, 2, v_v_2716_);
lean_ctor_set(v___x_2868_, 1, v_k_2715_);
lean_ctor_set(v___x_2868_, 0, v___x_2923_);
v___x_2925_ = v___x_2868_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2715_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2716_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_l_2717_);
lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_l_2890_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_nat_add(v___x_2724_, v_size_2874_);
if (lean_obj_tag(v_r_2891_) == 0)
{
lean_object* v_size_2927_; 
v_size_2927_ = lean_ctor_get(v_r_2891_, 0);
lean_inc(v_size_2927_);
v___y_2901_ = v___x_2925_;
v___y_2902_ = v___x_2926_;
v___y_2903_ = v_size_2927_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___y_2901_ = v___x_2925_;
v___y_2902_ = v___x_2926_;
v___y_2903_ = v___x_2928_;
goto v___jp_2900_;
}
}
}
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2938_ = lean_nat_add(v___x_2724_, v_size_2714_);
lean_dec(v_size_2714_);
v___x_2939_ = lean_nat_add(v___x_2938_, v_size_2874_);
lean_dec(v___x_2938_);
v___x_2940_ = lean_nat_add(v___x_2724_, v_size_2874_);
v___x_2941_ = lean_nat_add(v___x_2940_, v_size_2887_);
lean_dec(v___x_2940_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_tree_2871_);
lean_ctor_set(v___x_2868_, 3, v_r_2718_);
lean_ctor_set(v___x_2868_, 2, v_v_2873_);
lean_ctor_set(v___x_2868_, 1, v_k_2872_);
lean_ctor_set(v___x_2868_, 0, v___x_2941_);
v___x_2943_ = v___x_2868_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_k_2872_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_v_2873_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_r_2718_);
lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_tree_2871_);
v___x_2943_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 4, v___x_2943_);
lean_ctor_set(v___x_2884_, 0, v___x_2939_);
v___x_2945_ = v___x_2884_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_k_2715_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_v_2716_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v_l_2717_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2717_) == 0)
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2977_; 
lean_inc_ref(v_l_2717_);
lean_inc(v_v_2716_);
lean_inc(v_k_2715_);
lean_inc(v_size_2714_);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; lean_object* v_unused_2979_; lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; 
v_unused_2978_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_l_2543_, 2);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_l_2543_, 1);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_2982_);
v___x_2955_ = v_l_2543_;
v_isShared_2956_ = v_isSharedCheck_2977_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_l_2543_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2977_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
if (lean_obj_tag(v_r_2718_) == 0)
{
lean_object* v_k_2957_; lean_object* v_v_2958_; lean_object* v_size_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v_k_2957_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_k_2957_);
v_v_2958_ = lean_ctor_get(v___x_2870_, 1);
lean_inc(v_v_2958_);
lean_dec_ref(v___x_2870_);
v_size_2959_ = lean_ctor_get(v_r_2718_, 0);
v___x_2960_ = lean_nat_add(v___x_2724_, v_size_2714_);
lean_dec(v_size_2714_);
v___x_2961_ = lean_nat_add(v___x_2724_, v_size_2959_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_tree_2871_);
lean_ctor_set(v___x_2868_, 3, v_r_2718_);
lean_ctor_set(v___x_2868_, 2, v_v_2958_);
lean_ctor_set(v___x_2868_, 1, v_k_2957_);
lean_ctor_set(v___x_2868_, 0, v___x_2961_);
v___x_2963_ = v___x_2868_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_k_2957_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_v_2958_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_r_2718_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_tree_2871_);
v___x_2963_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 4, v___x_2963_);
lean_ctor_set(v___x_2955_, 0, v___x_2960_);
v___x_2965_ = v___x_2955_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2715_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2716_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_l_2717_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
else
{
lean_object* v_k_2968_; lean_object* v_v_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
lean_dec(v_size_2714_);
v_k_2968_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_k_2968_);
v_v_2969_ = lean_ctor_get(v___x_2870_, 1);
lean_inc(v_v_2969_);
lean_dec_ref(v___x_2870_);
v___x_2970_ = lean_unsigned_to_nat(3u);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_r_2718_);
lean_ctor_set(v___x_2868_, 3, v_r_2718_);
lean_ctor_set(v___x_2868_, 2, v_v_2969_);
lean_ctor_set(v___x_2868_, 1, v_k_2968_);
lean_ctor_set(v___x_2868_, 0, v___x_2724_);
v___x_2972_ = v___x_2868_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_k_2968_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_v_2969_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_r_2718_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_r_2718_);
v___x_2972_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 4, v___x_2972_);
lean_ctor_set(v___x_2955_, 0, v___x_2970_);
v___x_2974_ = v___x_2955_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_k_2715_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_v_2716_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_l_2717_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2718_) == 0)
{
lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3007_; 
lean_inc(v_l_2717_);
lean_inc(v_v_2716_);
lean_inc(v_k_2715_);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_l_2543_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; lean_object* v_unused_3009_; lean_object* v_unused_3010_; lean_object* v_unused_3011_; lean_object* v_unused_3012_; 
v_unused_3008_ = lean_ctor_get(v_l_2543_, 4);
lean_dec(v_unused_3008_);
v_unused_3009_ = lean_ctor_get(v_l_2543_, 3);
lean_dec(v_unused_3009_);
v_unused_3010_ = lean_ctor_get(v_l_2543_, 2);
lean_dec(v_unused_3010_);
v_unused_3011_ = lean_ctor_get(v_l_2543_, 1);
lean_dec(v_unused_3011_);
v_unused_3012_ = lean_ctor_get(v_l_2543_, 0);
lean_dec(v_unused_3012_);
v___x_2984_ = v_l_2543_;
v_isShared_2985_ = v_isSharedCheck_3007_;
goto v_resetjp_2983_;
}
else
{
lean_dec(v_l_2543_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3007_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v_k_2986_; lean_object* v_v_2987_; lean_object* v_k_2988_; lean_object* v_v_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3003_; 
v_k_2986_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_k_2986_);
v_v_2987_ = lean_ctor_get(v___x_2870_, 1);
lean_inc(v_v_2987_);
lean_dec_ref(v___x_2870_);
v_k_2988_ = lean_ctor_get(v_r_2718_, 1);
v_v_2989_ = lean_ctor_get(v_r_2718_, 2);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_r_2718_);
if (v_isSharedCheck_3003_ == 0)
{
lean_object* v_unused_3004_; lean_object* v_unused_3005_; lean_object* v_unused_3006_; 
v_unused_3004_ = lean_ctor_get(v_r_2718_, 4);
lean_dec(v_unused_3004_);
v_unused_3005_ = lean_ctor_get(v_r_2718_, 3);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_r_2718_, 0);
lean_dec(v_unused_3006_);
v___x_2991_ = v_r_2718_;
v_isShared_2992_ = v_isSharedCheck_3003_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_v_2989_);
lean_inc(v_k_2988_);
lean_dec(v_r_2718_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3003_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = lean_unsigned_to_nat(3u);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 4, v_l_2717_);
lean_ctor_set(v___x_2991_, 3, v_l_2717_);
lean_ctor_set(v___x_2991_, 2, v_v_2716_);
lean_ctor_set(v___x_2991_, 1, v_k_2715_);
lean_ctor_set(v___x_2991_, 0, v___x_2724_);
v___x_2995_ = v___x_2991_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_k_2715_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v_v_2716_);
lean_ctor_set(v_reuseFailAlloc_3002_, 3, v_l_2717_);
lean_ctor_set(v_reuseFailAlloc_3002_, 4, v_l_2717_);
v___x_2995_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_l_2717_);
lean_ctor_set(v___x_2868_, 3, v_l_2717_);
lean_ctor_set(v___x_2868_, 2, v_v_2987_);
lean_ctor_set(v___x_2868_, 1, v_k_2986_);
lean_ctor_set(v___x_2868_, 0, v___x_2724_);
v___x_2997_ = v___x_2868_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_k_2986_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_v_2987_);
lean_ctor_set(v_reuseFailAlloc_3001_, 3, v_l_2717_);
lean_ctor_set(v_reuseFailAlloc_3001_, 4, v_l_2717_);
v___x_2997_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 4, v___x_2997_);
lean_ctor_set(v___x_2984_, 3, v___x_2995_);
lean_ctor_set(v___x_2984_, 2, v_v_2989_);
lean_ctor_set(v___x_2984_, 1, v_k_2988_);
lean_ctor_set(v___x_2984_, 0, v___x_2993_);
v___x_2999_ = v___x_2984_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_k_2988_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_v_2989_);
lean_ctor_set(v_reuseFailAlloc_3000_, 3, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3000_, 4, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
}
else
{
lean_object* v_k_3013_; lean_object* v_v_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v_k_3013_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_k_3013_);
v_v_3014_ = lean_ctor_get(v___x_2870_, 1);
lean_inc(v_v_3014_);
lean_dec_ref(v___x_2870_);
v___x_3015_ = lean_unsigned_to_nat(2u);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_r_2718_);
lean_ctor_set(v___x_2868_, 3, v_l_2543_);
lean_ctor_set(v___x_2868_, 2, v_v_3014_);
lean_ctor_set(v___x_2868_, 1, v_k_3013_);
lean_ctor_set(v___x_2868_, 0, v___x_3015_);
v___x_3017_ = v___x_2868_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_3013_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_3014_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_l_2543_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_r_2718_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
}
}
else
{
return v_l_2543_;
}
}
else
{
return v_r_2544_;
}
}
}
else
{
lean_object* v_impl_3025_; lean_object* v___x_3026_; 
v_impl_3025_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2539_, v_l_2543_);
v___x_3026_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3025_) == 0)
{
if (lean_obj_tag(v_r_2544_) == 0)
{
lean_object* v_size_3027_; lean_object* v_size_3028_; lean_object* v_k_3029_; lean_object* v_v_3030_; lean_object* v_l_3031_; lean_object* v_r_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_size_3027_ = lean_ctor_get(v_impl_3025_, 0);
v_size_3028_ = lean_ctor_get(v_r_2544_, 0);
v_k_3029_ = lean_ctor_get(v_r_2544_, 1);
v_v_3030_ = lean_ctor_get(v_r_2544_, 2);
v_l_3031_ = lean_ctor_get(v_r_2544_, 3);
lean_inc(v_l_3031_);
v_r_3032_ = lean_ctor_get(v_r_2544_, 4);
v___x_3033_ = lean_unsigned_to_nat(3u);
v___x_3034_ = lean_nat_mul(v___x_3033_, v_size_3027_);
v___x_3035_ = lean_nat_dec_lt(v___x_3034_, v_size_3028_);
lean_dec(v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v_l_3031_);
v___x_3036_ = lean_nat_add(v___x_3026_, v_size_3027_);
v___x_3037_ = lean_nat_add(v___x_3036_, v_size_3028_);
lean_dec(v___x_3036_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 3, v_impl_3025_);
lean_ctor_set(v___x_2546_, 0, v___x_3037_);
v___x_3039_ = v___x_2546_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3040_, 3, v_impl_3025_);
lean_ctor_set(v_reuseFailAlloc_3040_, 4, v_r_2544_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3104_; 
lean_inc(v_r_3032_);
lean_inc(v_v_3030_);
lean_inc(v_k_3029_);
lean_inc(v_size_3028_);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; 
v_unused_3105_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_r_2544_, 2);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_r_2544_, 1);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_r_2544_, 0);
lean_dec(v_unused_3109_);
v___x_3042_ = v_r_2544_;
v_isShared_3043_ = v_isSharedCheck_3104_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v_r_2544_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3104_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_size_3044_; lean_object* v_k_3045_; lean_object* v_v_3046_; lean_object* v_l_3047_; lean_object* v_r_3048_; lean_object* v_size_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v_size_3044_ = lean_ctor_get(v_l_3031_, 0);
v_k_3045_ = lean_ctor_get(v_l_3031_, 1);
v_v_3046_ = lean_ctor_get(v_l_3031_, 2);
v_l_3047_ = lean_ctor_get(v_l_3031_, 3);
v_r_3048_ = lean_ctor_get(v_l_3031_, 4);
v_size_3049_ = lean_ctor_get(v_r_3032_, 0);
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = lean_nat_mul(v___x_3050_, v_size_3049_);
v___x_3052_ = lean_nat_dec_lt(v_size_3044_, v___x_3051_);
lean_dec(v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3080_; 
lean_inc(v_r_3048_);
lean_inc(v_l_3047_);
lean_inc(v_v_3046_);
lean_inc(v_k_3045_);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_l_3031_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; lean_object* v_unused_3082_; lean_object* v_unused_3083_; lean_object* v_unused_3084_; lean_object* v_unused_3085_; 
v_unused_3081_ = lean_ctor_get(v_l_3031_, 4);
lean_dec(v_unused_3081_);
v_unused_3082_ = lean_ctor_get(v_l_3031_, 3);
lean_dec(v_unused_3082_);
v_unused_3083_ = lean_ctor_get(v_l_3031_, 2);
lean_dec(v_unused_3083_);
v_unused_3084_ = lean_ctor_get(v_l_3031_, 1);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v_l_3031_, 0);
lean_dec(v_unused_3085_);
v___x_3054_ = v_l_3031_;
v_isShared_3055_ = v_isSharedCheck_3080_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v_l_3031_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3080_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3070_; 
v___x_3056_ = lean_nat_add(v___x_3026_, v_size_3027_);
v___x_3057_ = lean_nat_add(v___x_3056_, v_size_3028_);
lean_dec(v_size_3028_);
if (lean_obj_tag(v_l_3047_) == 0)
{
lean_object* v_size_3078_; 
v_size_3078_ = lean_ctor_get(v_l_3047_, 0);
lean_inc(v_size_3078_);
v___y_3070_ = v_size_3078_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___y_3070_ = v___x_3079_;
goto v___jp_3069_;
}
v___jp_3058_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = lean_nat_add(v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec(v___y_3060_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 4, v_r_3032_);
lean_ctor_set(v___x_3054_, 3, v_r_3048_);
lean_ctor_set(v___x_3054_, 2, v_v_3030_);
lean_ctor_set(v___x_3054_, 1, v_k_3029_);
lean_ctor_set(v___x_3054_, 0, v___x_3062_);
v___x_3064_ = v___x_3054_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_k_3029_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_v_3030_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_r_3048_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_r_3032_);
v___x_3064_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 4, v___x_3064_);
lean_ctor_set(v___x_3042_, 3, v___y_3059_);
lean_ctor_set(v___x_3042_, 2, v_v_3046_);
lean_ctor_set(v___x_3042_, 1, v_k_3045_);
lean_ctor_set(v___x_3042_, 0, v___x_3057_);
v___x_3066_ = v___x_3042_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_k_3045_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_v_3046_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v___y_3059_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
v___jp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_nat_add(v___x_3056_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec(v___x_3056_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_l_3047_);
lean_ctor_set(v___x_2546_, 3, v_impl_3025_);
lean_ctor_set(v___x_2546_, 0, v___x_3071_);
v___x_3073_ = v___x_2546_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_impl_3025_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_l_3047_);
v___x_3073_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_nat_add(v___x_3026_, v_size_3049_);
if (lean_obj_tag(v_r_3048_) == 0)
{
lean_object* v_size_3075_; 
v_size_3075_ = lean_ctor_get(v_r_3048_, 0);
lean_inc(v_size_3075_);
v___y_3059_ = v___x_3073_;
v___y_3060_ = v___x_3074_;
v___y_3061_ = v_size_3075_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_unsigned_to_nat(0u);
v___y_3059_ = v___x_3073_;
v___y_3060_ = v___x_3074_;
v___y_3061_ = v___x_3076_;
goto v___jp_3058_;
}
}
}
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
lean_del_object(v___x_2546_);
v___x_3086_ = lean_nat_add(v___x_3026_, v_size_3027_);
v___x_3087_ = lean_nat_add(v___x_3086_, v_size_3028_);
lean_dec(v_size_3028_);
v___x_3088_ = lean_nat_add(v___x_3086_, v_size_3044_);
lean_dec(v___x_3086_);
lean_inc_ref(v_impl_3025_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 4, v_l_3031_);
lean_ctor_set(v___x_3042_, 3, v_impl_3025_);
lean_ctor_set(v___x_3042_, 2, v_v_2542_);
lean_ctor_set(v___x_3042_, 1, v_k_2541_);
lean_ctor_set(v___x_3042_, 0, v___x_3088_);
v___x_3090_ = v___x_3042_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_impl_3025_);
lean_ctor_set(v_reuseFailAlloc_3103_, 4, v_l_3031_);
v___x_3090_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
v_isSharedCheck_3097_ = !lean_is_exclusive(v_impl_3025_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; lean_object* v_unused_3099_; lean_object* v_unused_3100_; lean_object* v_unused_3101_; lean_object* v_unused_3102_; 
v_unused_3098_ = lean_ctor_get(v_impl_3025_, 4);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_impl_3025_, 3);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_impl_3025_, 2);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_impl_3025_, 1);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v_impl_3025_, 0);
lean_dec(v_unused_3102_);
v___x_3092_ = v_impl_3025_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v_impl_3025_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_r_3032_);
lean_ctor_set(v___x_3092_, 3, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v_v_3030_);
lean_ctor_set(v___x_3092_, 1, v_k_3029_);
lean_ctor_set(v___x_3092_, 0, v___x_3087_);
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3029_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3030_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_r_3032_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v_size_3110_ = lean_ctor_get(v_impl_3025_, 0);
v___x_3111_ = lean_nat_add(v___x_3026_, v_size_3110_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 3, v_impl_3025_);
lean_ctor_set(v___x_2546_, 0, v___x_3111_);
v___x_3113_ = v___x_2546_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_impl_3025_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_r_2544_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
if (lean_obj_tag(v_r_2544_) == 0)
{
lean_object* v_l_3115_; 
v_l_3115_ = lean_ctor_get(v_r_2544_, 3);
lean_inc(v_l_3115_);
if (lean_obj_tag(v_l_3115_) == 0)
{
lean_object* v_r_3116_; 
v_r_3116_ = lean_ctor_get(v_r_2544_, 4);
lean_inc(v_r_3116_);
if (lean_obj_tag(v_r_3116_) == 0)
{
lean_object* v_size_3117_; lean_object* v_k_3118_; lean_object* v_v_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3132_; 
v_size_3117_ = lean_ctor_get(v_r_2544_, 0);
v_k_3118_ = lean_ctor_get(v_r_2544_, 1);
v_v_3119_ = lean_ctor_get(v_r_2544_, 2);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3133_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_3134_);
v___x_3121_ = v_r_2544_;
v_isShared_3122_ = v_isSharedCheck_3132_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_v_3119_);
lean_inc(v_k_3118_);
lean_inc(v_size_3117_);
lean_dec(v_r_2544_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3132_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_size_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
v_size_3123_ = lean_ctor_get(v_l_3115_, 0);
v___x_3124_ = lean_nat_add(v___x_3026_, v_size_3117_);
lean_dec(v_size_3117_);
v___x_3125_ = lean_nat_add(v___x_3026_, v_size_3123_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 4, v_l_3115_);
lean_ctor_set(v___x_3121_, 3, v_impl_3025_);
lean_ctor_set(v___x_3121_, 2, v_v_2542_);
lean_ctor_set(v___x_3121_, 1, v_k_2541_);
lean_ctor_set(v___x_3121_, 0, v___x_3125_);
v___x_3127_ = v___x_3121_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_impl_3025_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_l_3115_);
v___x_3127_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3129_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_r_3116_);
lean_ctor_set(v___x_2546_, 3, v___x_3127_);
lean_ctor_set(v___x_2546_, 2, v_v_3119_);
lean_ctor_set(v___x_2546_, 1, v_k_3118_);
lean_ctor_set(v___x_2546_, 0, v___x_3124_);
v___x_3129_ = v___x_2546_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_k_3118_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_v_3119_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_r_3116_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_k_3135_; lean_object* v_v_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3159_; 
v_k_3135_ = lean_ctor_get(v_r_2544_, 1);
v_v_3136_ = lean_ctor_get(v_r_2544_, 2);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; lean_object* v_unused_3161_; lean_object* v_unused_3162_; 
v_unused_3160_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_r_2544_, 0);
lean_dec(v_unused_3162_);
v___x_3138_ = v_r_2544_;
v_isShared_3139_ = v_isSharedCheck_3159_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_v_3136_);
lean_inc(v_k_3135_);
lean_dec(v_r_2544_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3159_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_k_3140_; lean_object* v_v_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3155_; 
v_k_3140_ = lean_ctor_get(v_l_3115_, 1);
v_v_3141_ = lean_ctor_get(v_l_3115_, 2);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_l_3115_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; lean_object* v_unused_3157_; lean_object* v_unused_3158_; 
v_unused_3156_ = lean_ctor_get(v_l_3115_, 4);
lean_dec(v_unused_3156_);
v_unused_3157_ = lean_ctor_get(v_l_3115_, 3);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_l_3115_, 0);
lean_dec(v_unused_3158_);
v___x_3143_ = v_l_3115_;
v_isShared_3144_ = v_isSharedCheck_3155_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_v_3141_);
lean_inc(v_k_3140_);
lean_dec(v_l_3115_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3155_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_unsigned_to_nat(3u);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 4, v_r_3116_);
lean_ctor_set(v___x_3143_, 3, v_r_3116_);
lean_ctor_set(v___x_3143_, 2, v_v_2542_);
lean_ctor_set(v___x_3143_, 1, v_k_2541_);
lean_ctor_set(v___x_3143_, 0, v___x_3026_);
v___x_3147_ = v___x_3143_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_r_3116_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v_r_3116_);
v___x_3147_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3149_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 3, v_r_3116_);
lean_ctor_set(v___x_3138_, 0, v___x_3026_);
v___x_3149_ = v___x_3138_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_k_3135_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_v_3136_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_r_3116_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v_r_3116_);
v___x_3149_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3151_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v___x_3149_);
lean_ctor_set(v___x_2546_, 3, v___x_3147_);
lean_ctor_set(v___x_2546_, 2, v_v_3141_);
lean_ctor_set(v___x_2546_, 1, v_k_3140_);
lean_ctor_set(v___x_2546_, 0, v___x_3145_);
v___x_3151_ = v___x_2546_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_k_3140_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v_v_3141_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v___x_3147_);
lean_ctor_set(v_reuseFailAlloc_3152_, 4, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3163_; 
v_r_3163_ = lean_ctor_get(v_r_2544_, 4);
lean_inc(v_r_3163_);
if (lean_obj_tag(v_r_3163_) == 0)
{
lean_object* v_k_3164_; lean_object* v_v_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3176_; 
v_k_3164_ = lean_ctor_get(v_r_2544_, 1);
v_v_3165_ = lean_ctor_get(v_r_2544_, 2);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; lean_object* v_unused_3178_; lean_object* v_unused_3179_; 
v_unused_3177_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_r_2544_, 0);
lean_dec(v_unused_3179_);
v___x_3167_ = v_r_2544_;
v_isShared_3168_ = v_isSharedCheck_3176_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_v_3165_);
lean_inc(v_k_3164_);
lean_dec(v_r_2544_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3176_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_unsigned_to_nat(3u);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_l_3115_);
lean_ctor_set(v___x_3167_, 2, v_v_2542_);
lean_ctor_set(v___x_3167_, 1, v_k_2541_);
lean_ctor_set(v___x_3167_, 0, v___x_3026_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_l_3115_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_l_3115_);
v___x_3171_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3173_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v_r_3163_);
lean_ctor_set(v___x_2546_, 3, v___x_3171_);
lean_ctor_set(v___x_2546_, 2, v_v_3165_);
lean_ctor_set(v___x_2546_, 1, v_k_3164_);
lean_ctor_set(v___x_2546_, 0, v___x_3169_);
v___x_3173_ = v___x_2546_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_k_3164_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_v_3165_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_r_3163_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_size_3180_; lean_object* v_k_3181_; lean_object* v_v_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3193_; 
v_size_3180_ = lean_ctor_get(v_r_2544_, 0);
v_k_3181_ = lean_ctor_get(v_r_2544_, 1);
v_v_3182_ = lean_ctor_get(v_r_2544_, 2);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_r_2544_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; lean_object* v_unused_3195_; 
v_unused_3194_ = lean_ctor_get(v_r_2544_, 4);
lean_dec(v_unused_3194_);
v_unused_3195_ = lean_ctor_get(v_r_2544_, 3);
lean_dec(v_unused_3195_);
v___x_3184_ = v_r_2544_;
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_v_3182_);
lean_inc(v_k_3181_);
lean_inc(v_size_3180_);
lean_dec(v_r_2544_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 3, v_r_3163_);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_size_3180_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_k_3181_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_v_3182_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v_r_3163_);
lean_ctor_set(v_reuseFailAlloc_3192_, 4, v_r_3163_);
v___x_3187_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_unsigned_to_nat(2u);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v___x_3187_);
lean_ctor_set(v___x_2546_, 3, v_r_3163_);
lean_ctor_set(v___x_2546_, 0, v___x_3188_);
v___x_3190_ = v___x_2546_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_r_3163_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v___x_3187_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
}
else
{
lean_object* v___x_3197_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 3, v_r_2544_);
lean_ctor_set(v___x_2546_, 0, v___x_3026_);
v___x_3197_ = v___x_2546_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_r_2544_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_r_2544_);
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
else
{
return v_t_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3201_, lean_object* v_t_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3201_, v_t_3202_);
lean_dec(v_k_3201_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3204_, lean_object* v_j_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3205_, v_ctx_3204_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3207_, lean_object* v_j_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3207_, v_j_3208_);
lean_dec(v_j_3208_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3210_, lean_object* v_k_3211_, lean_object* v_t_3212_, lean_object* v_h_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3211_, v_t_3212_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3215_, lean_object* v_k_3216_, lean_object* v_t_3217_, lean_object* v_h_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3215_, v_k_3216_, v_t_3217_, v_h_3218_);
lean_dec(v_k_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_3220_, v_x_3221_);
if (lean_obj_tag(v___x_3222_) == 1)
{
lean_object* v_val_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3236_; 
v_val_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3236_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_val_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3236_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
switch(lean_obj_tag(v_val_3223_))
{
case 0:
{
lean_object* v_a_3227_; lean_object* v___x_3229_; 
v_a_3227_ = lean_ctor_get(v_val_3223_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v_val_3223_, 1);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v_a_3227_);
v___x_3229_ = v___x_3225_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
case 1:
{
lean_object* v_a_3231_; lean_object* v___x_3233_; 
v_a_3231_ = lean_ctor_get(v_val_3223_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v_val_3223_, 2);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v_a_3231_);
v___x_3233_ = v___x_3225_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
default: 
{
lean_object* v___x_3235_; 
lean_del_object(v___x_3225_);
lean_dec(v_val_3223_);
v___x_3235_ = lean_box(0);
return v___x_3235_;
}
}
}
}
else
{
lean_object* v___x_3237_; 
lean_dec(v___x_3222_);
v___x_3237_ = lean_box(0);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_IR_LocalContext_getType(v_ctx_3238_, v_x_3239_);
lean_dec(v_x_3239_);
lean_dec(v_ctx_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_3241_, v_x_3242_);
if (lean_obj_tag(v___x_3243_) == 1)
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3253_; 
v_val_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3253_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3253_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
if (lean_obj_tag(v_val_3244_) == 1)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; 
v_a_3248_ = lean_ctor_get(v_val_3244_, 1);
lean_inc_ref(v_a_3248_);
lean_dec_ref_known(v_val_3244_, 2);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v_a_3248_);
v___x_3250_ = v___x_3246_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
else
{
lean_object* v___x_3252_; 
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
v___x_3252_ = lean_box(0);
return v___x_3252_;
}
}
}
else
{
lean_object* v___x_3254_; 
lean_dec(v___x_3243_);
v___x_3254_ = lean_box(0);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3255_, lean_object* v_x_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_IR_LocalContext_getValue(v_ctx_3255_, v_x_3256_);
lean_dec(v_x_3256_);
lean_dec(v_ctx_3255_);
return v_res_3257_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3258_, lean_object* v_v_u2081_3259_, lean_object* v_v_u2082_3260_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_00_u03c1_3258_, v_v_u2081_3259_);
if (lean_obj_tag(v___x_3261_) == 0)
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_nat_dec_eq(v_v_u2081_3259_, v_v_u2082_3260_);
return v___x_3262_;
}
else
{
lean_object* v_val_3263_; uint8_t v___x_3264_; 
v_val_3263_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_val_3263_);
lean_dec_ref_known(v___x_3261_, 1);
v___x_3264_ = lean_nat_dec_eq(v_val_3263_, v_v_u2082_3260_);
lean_dec(v_val_3263_);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3265_, lean_object* v_v_u2081_3266_, lean_object* v_v_u2082_3267_){
_start:
{
uint8_t v_res_3268_; lean_object* v_r_3269_; 
v_res_3268_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3265_, v_v_u2081_3266_, v_v_u2082_3267_);
lean_dec(v_v_u2082_3267_);
lean_dec(v_v_u2081_3266_);
lean_dec(v_00_u03c1_3265_);
v_r_3269_ = lean_box(v_res_3268_);
return v_r_3269_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3272_, lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3273_) == 0)
{
if (lean_obj_tag(v_x_3274_) == 0)
{
lean_object* v_id_3275_; lean_object* v_id_3276_; uint8_t v___x_3277_; 
v_id_3275_ = lean_ctor_get(v_x_3273_, 0);
v_id_3276_ = lean_ctor_get(v_x_3274_, 0);
v___x_3277_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3272_, v_id_3275_, v_id_3276_);
return v___x_3277_;
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = 0;
return v___x_3278_;
}
}
else
{
if (lean_obj_tag(v_x_3274_) == 1)
{
uint8_t v___x_3279_; 
v___x_3279_ = 1;
return v___x_3279_;
}
else
{
uint8_t v___x_3280_; 
v___x_3280_ = 0;
return v___x_3280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_){
_start:
{
uint8_t v_res_3284_; lean_object* v_r_3285_; 
v_res_3284_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3281_, v_x_3282_, v_x_3283_);
lean_dec(v_x_3283_);
lean_dec(v_x_3282_);
lean_dec(v_00_u03c1_3281_);
v_r_3285_ = lean_box(v_res_3284_);
return v_r_3285_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3288_, lean_object* v_xs_3289_, lean_object* v_ys_3290_, lean_object* v_x_3291_){
_start:
{
lean_object* v_zero_3292_; uint8_t v_isZero_3293_; 
v_zero_3292_ = lean_unsigned_to_nat(0u);
v_isZero_3293_ = lean_nat_dec_eq(v_x_3291_, v_zero_3292_);
if (v_isZero_3293_ == 1)
{
lean_dec(v_x_3291_);
return v_isZero_3293_;
}
else
{
lean_object* v_one_3294_; lean_object* v_n_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v_one_3294_ = lean_unsigned_to_nat(1u);
v_n_3295_ = lean_nat_sub(v_x_3291_, v_one_3294_);
lean_dec(v_x_3291_);
v___x_3296_ = lean_array_fget_borrowed(v_xs_3289_, v_n_3295_);
v___x_3297_ = lean_array_fget_borrowed(v_ys_3290_, v_n_3295_);
v___x_3298_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3288_, v___x_3296_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_dec(v_n_3295_);
return v___x_3298_;
}
else
{
v_x_3291_ = v_n_3295_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3300_, lean_object* v_xs_3301_, lean_object* v_ys_3302_, lean_object* v_x_3303_){
_start:
{
uint8_t v_res_3304_; lean_object* v_r_3305_; 
v_res_3304_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3300_, v_xs_3301_, v_ys_3302_, v_x_3303_);
lean_dec_ref(v_ys_3302_);
lean_dec_ref(v_xs_3301_);
lean_dec(v_00_u03c1_3300_);
v_r_3305_ = lean_box(v_res_3304_);
return v_r_3305_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3306_, lean_object* v_args_u2081_3307_, lean_object* v_args_u2082_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3309_ = lean_array_get_size(v_args_u2081_3307_);
v___x_3310_ = lean_array_get_size(v_args_u2082_3308_);
v___x_3311_ = lean_nat_dec_eq(v___x_3309_, v___x_3310_);
if (v___x_3311_ == 0)
{
return v___x_3311_;
}
else
{
uint8_t v___x_3312_; 
v___x_3312_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3306_, v_args_u2081_3307_, v_args_u2082_3308_, v___x_3309_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3313_, lean_object* v_args_u2081_3314_, lean_object* v_args_u2082_3315_){
_start:
{
uint8_t v_res_3316_; lean_object* v_r_3317_; 
v_res_3316_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3313_, v_args_u2081_3314_, v_args_u2082_3315_);
lean_dec_ref(v_args_u2082_3315_);
lean_dec_ref(v_args_u2081_3314_);
lean_dec(v_00_u03c1_3313_);
v_r_3317_ = lean_box(v_res_3316_);
return v_r_3317_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3318_, lean_object* v_xs_3319_, lean_object* v_ys_3320_, lean_object* v_hsz_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
uint8_t v___x_3324_; 
v___x_3324_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3318_, v_xs_3319_, v_ys_3320_, v_x_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3325_, lean_object* v_xs_3326_, lean_object* v_ys_3327_, lean_object* v_hsz_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
uint8_t v_res_3331_; lean_object* v_r_3332_; 
v_res_3331_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3325_, v_xs_3326_, v_ys_3327_, v_hsz_3328_, v_x_3329_, v_x_3330_);
lean_dec_ref(v_ys_3327_);
lean_dec_ref(v_xs_3326_);
lean_dec(v_00_u03c1_3325_);
v_r_3332_ = lean_box(v_res_3331_);
return v_r_3332_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* v_00_u03c1_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v_c_u2081_3339_; lean_object* v_ys_u2081_3340_; lean_object* v_c_u2082_3341_; lean_object* v_ys_u2082_3342_; lean_object* v_n_u2081_3346_; lean_object* v_x_u2081_3347_; lean_object* v_n_u2082_3348_; lean_object* v_x_u2082_3349_; 
switch(lean_obj_tag(v_x_3336_))
{
case 0:
{
if (lean_obj_tag(v_x_3337_) == 0)
{
lean_object* v_i_3352_; lean_object* v_ys_3353_; lean_object* v_i_3354_; lean_object* v_ys_3355_; uint8_t v___x_3356_; 
v_i_3352_ = lean_ctor_get(v_x_3336_, 0);
v_ys_3353_ = lean_ctor_get(v_x_3336_, 1);
v_i_3354_ = lean_ctor_get(v_x_3337_, 0);
v_ys_3355_ = lean_ctor_get(v_x_3337_, 1);
v___x_3356_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3352_, v_i_3354_);
if (v___x_3356_ == 0)
{
return v___x_3356_;
}
else
{
uint8_t v___x_3357_; 
v___x_3357_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3335_, v_ys_3353_, v_ys_3355_);
return v___x_3357_;
}
}
else
{
uint8_t v___x_3358_; 
v___x_3358_ = 0;
return v___x_3358_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3337_) == 1)
{
lean_object* v_n_3359_; lean_object* v_x_3360_; lean_object* v_n_3361_; lean_object* v_x_3362_; 
v_n_3359_ = lean_ctor_get(v_x_3336_, 0);
v_x_3360_ = lean_ctor_get(v_x_3336_, 1);
v_n_3361_ = lean_ctor_get(v_x_3337_, 0);
v_x_3362_ = lean_ctor_get(v_x_3337_, 1);
v_n_u2081_3346_ = v_n_3359_;
v_x_u2081_3347_ = v_x_3360_;
v_n_u2082_3348_ = v_n_3361_;
v_x_u2082_3349_ = v_x_3362_;
goto v___jp_3345_;
}
else
{
uint8_t v___x_3363_; 
v___x_3363_ = 0;
return v___x_3363_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3337_) == 2)
{
lean_object* v_x_3364_; lean_object* v_i_3365_; uint8_t v_updtHeader_3366_; lean_object* v_ys_3367_; lean_object* v_x_3368_; lean_object* v_i_3369_; uint8_t v_updtHeader_3370_; lean_object* v_ys_3371_; uint8_t v___y_3373_; uint8_t v___x_3376_; 
v_x_3364_ = lean_ctor_get(v_x_3336_, 0);
v_i_3365_ = lean_ctor_get(v_x_3336_, 1);
v_updtHeader_3366_ = lean_ctor_get_uint8(v_x_3336_, sizeof(void*)*3);
v_ys_3367_ = lean_ctor_get(v_x_3336_, 2);
v_x_3368_ = lean_ctor_get(v_x_3337_, 0);
v_i_3369_ = lean_ctor_get(v_x_3337_, 1);
v_updtHeader_3370_ = lean_ctor_get_uint8(v_x_3337_, sizeof(void*)*3);
v_ys_3371_ = lean_ctor_get(v_x_3337_, 2);
v___x_3376_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_3364_, v_x_3368_);
if (v___x_3376_ == 0)
{
v___y_3373_ = v___x_3376_;
goto v___jp_3372_;
}
else
{
uint8_t v___x_3377_; 
v___x_3377_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3365_, v_i_3369_);
v___y_3373_ = v___x_3377_;
goto v___jp_3372_;
}
v___jp_3372_:
{
if (v___y_3373_ == 0)
{
return v___y_3373_;
}
else
{
if (v_updtHeader_3370_ == 0)
{
if (v_updtHeader_3366_ == 0)
{
uint8_t v___x_3374_; 
v___x_3374_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3335_, v_ys_3367_, v_ys_3371_);
return v___x_3374_;
}
else
{
return v_updtHeader_3370_;
}
}
else
{
if (v_updtHeader_3366_ == 0)
{
return v_updtHeader_3366_;
}
else
{
uint8_t v___x_3375_; 
v___x_3375_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3335_, v_ys_3367_, v_ys_3371_);
return v___x_3375_;
}
}
}
}
}
else
{
uint8_t v___x_3378_; 
v___x_3378_ = 0;
return v___x_3378_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3337_) == 3)
{
lean_object* v_i_3379_; lean_object* v_x_3380_; lean_object* v_i_3381_; lean_object* v_x_3382_; 
v_i_3379_ = lean_ctor_get(v_x_3336_, 0);
v_x_3380_ = lean_ctor_get(v_x_3336_, 1);
v_i_3381_ = lean_ctor_get(v_x_3337_, 0);
v_x_3382_ = lean_ctor_get(v_x_3337_, 1);
v_n_u2081_3346_ = v_i_3379_;
v_x_u2081_3347_ = v_x_3380_;
v_n_u2082_3348_ = v_i_3381_;
v_x_u2082_3349_ = v_x_3382_;
goto v___jp_3345_;
}
else
{
uint8_t v___x_3383_; 
v___x_3383_ = 0;
return v___x_3383_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3337_) == 4)
{
lean_object* v_i_3384_; lean_object* v_x_3385_; lean_object* v_i_3386_; lean_object* v_x_3387_; 
v_i_3384_ = lean_ctor_get(v_x_3336_, 0);
v_x_3385_ = lean_ctor_get(v_x_3336_, 1);
v_i_3386_ = lean_ctor_get(v_x_3337_, 0);
v_x_3387_ = lean_ctor_get(v_x_3337_, 1);
v_n_u2081_3346_ = v_i_3384_;
v_x_u2081_3347_ = v_x_3385_;
v_n_u2082_3348_ = v_i_3386_;
v_x_u2082_3349_ = v_x_3387_;
goto v___jp_3345_;
}
else
{
uint8_t v___x_3388_; 
v___x_3388_ = 0;
return v___x_3388_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3337_) == 5)
{
lean_object* v_n_3389_; lean_object* v_offset_3390_; lean_object* v_x_3391_; lean_object* v_n_3392_; lean_object* v_offset_3393_; lean_object* v_x_3394_; uint8_t v___x_3395_; 
v_n_3389_ = lean_ctor_get(v_x_3336_, 0);
v_offset_3390_ = lean_ctor_get(v_x_3336_, 1);
v_x_3391_ = lean_ctor_get(v_x_3336_, 2);
v_n_3392_ = lean_ctor_get(v_x_3337_, 0);
v_offset_3393_ = lean_ctor_get(v_x_3337_, 1);
v_x_3394_ = lean_ctor_get(v_x_3337_, 2);
v___x_3395_ = lean_nat_dec_eq(v_n_3389_, v_n_3392_);
if (v___x_3395_ == 0)
{
return v___x_3395_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_nat_dec_eq(v_offset_3390_, v_offset_3393_);
if (v___x_3396_ == 0)
{
return v___x_3396_;
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_3391_, v_x_3394_);
return v___x_3397_;
}
}
}
else
{
uint8_t v___x_3398_; 
v___x_3398_ = 0;
return v___x_3398_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3337_) == 6)
{
lean_object* v_c_3399_; lean_object* v_ys_3400_; lean_object* v_c_3401_; lean_object* v_ys_3402_; 
v_c_3399_ = lean_ctor_get(v_x_3336_, 0);
v_ys_3400_ = lean_ctor_get(v_x_3336_, 1);
v_c_3401_ = lean_ctor_get(v_x_3337_, 0);
v_ys_3402_ = lean_ctor_get(v_x_3337_, 1);
v_c_u2081_3339_ = v_c_3399_;
v_ys_u2081_3340_ = v_ys_3400_;
v_c_u2082_3341_ = v_c_3401_;
v_ys_u2082_3342_ = v_ys_3402_;
goto v___jp_3338_;
}
else
{
uint8_t v___x_3403_; 
v___x_3403_ = 0;
return v___x_3403_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3337_) == 7)
{
lean_object* v_c_3404_; lean_object* v_ys_3405_; lean_object* v_c_3406_; lean_object* v_ys_3407_; 
v_c_3404_ = lean_ctor_get(v_x_3336_, 0);
v_ys_3405_ = lean_ctor_get(v_x_3336_, 1);
v_c_3406_ = lean_ctor_get(v_x_3337_, 0);
v_ys_3407_ = lean_ctor_get(v_x_3337_, 1);
v_c_u2081_3339_ = v_c_3404_;
v_ys_u2081_3340_ = v_ys_3405_;
v_c_u2082_3341_ = v_c_3406_;
v_ys_u2082_3342_ = v_ys_3407_;
goto v___jp_3338_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = 0;
return v___x_3408_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3337_) == 8)
{
lean_object* v_x_3409_; lean_object* v_ys_3410_; lean_object* v_x_3411_; lean_object* v_ys_3412_; uint8_t v___x_3413_; 
v_x_3409_ = lean_ctor_get(v_x_3336_, 0);
v_ys_3410_ = lean_ctor_get(v_x_3336_, 1);
v_x_3411_ = lean_ctor_get(v_x_3337_, 0);
v_ys_3412_ = lean_ctor_get(v_x_3337_, 1);
v___x_3413_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_3409_, v_x_3411_);
if (v___x_3413_ == 0)
{
return v___x_3413_;
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3335_, v_ys_3410_, v_ys_3412_);
return v___x_3414_;
}
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = 0;
return v___x_3415_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3337_) == 9)
{
lean_object* v_ty_3416_; lean_object* v_x_3417_; lean_object* v_ty_3418_; lean_object* v_x_3419_; uint8_t v___x_3420_; 
v_ty_3416_ = lean_ctor_get(v_x_3336_, 0);
v_x_3417_ = lean_ctor_get(v_x_3336_, 1);
v_ty_3418_ = lean_ctor_get(v_x_3337_, 0);
v_x_3419_ = lean_ctor_get(v_x_3337_, 1);
v___x_3420_ = l_Lean_IR_instBEqIRType_beq(v_ty_3416_, v_ty_3418_);
if (v___x_3420_ == 0)
{
return v___x_3420_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_3417_, v_x_3419_);
return v___x_3421_;
}
}
else
{
uint8_t v___x_3422_; 
v___x_3422_ = 0;
return v___x_3422_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3337_) == 10)
{
lean_object* v_x_3423_; lean_object* v_x_3424_; uint8_t v___x_3425_; 
v_x_3423_ = lean_ctor_get(v_x_3336_, 0);
v_x_3424_ = lean_ctor_get(v_x_3337_, 0);
v___x_3425_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_3423_, v_x_3424_);
return v___x_3425_;
}
else
{
uint8_t v___x_3426_; 
v___x_3426_ = 0;
return v___x_3426_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3337_) == 11)
{
lean_object* v_v_3427_; lean_object* v_v_3428_; uint8_t v___x_3429_; 
v_v_3427_ = lean_ctor_get(v_x_3336_, 0);
v_v_3428_ = lean_ctor_get(v_x_3337_, 0);
v___x_3429_ = l_Lean_IR_instBEqLitVal_beq(v_v_3427_, v_v_3428_);
return v___x_3429_;
}
else
{
uint8_t v___x_3430_; 
v___x_3430_ = 0;
return v___x_3430_;
}
}
default: 
{
if (lean_obj_tag(v_x_3337_) == 12)
{
lean_object* v_x_3431_; lean_object* v_x_3432_; uint8_t v___x_3433_; 
v_x_3431_ = lean_ctor_get(v_x_3336_, 0);
v_x_3432_ = lean_ctor_get(v_x_3337_, 0);
v___x_3433_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_3431_, v_x_3432_);
return v___x_3433_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = 0;
return v___x_3434_;
}
}
}
v___jp_3338_:
{
uint8_t v___x_3343_; 
v___x_3343_ = lean_name_eq(v_c_u2081_3339_, v_c_u2082_3341_);
if (v___x_3343_ == 0)
{
return v___x_3343_;
}
else
{
uint8_t v___x_3344_; 
v___x_3344_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3335_, v_ys_u2081_3340_, v_ys_u2082_3342_);
return v___x_3344_;
}
}
v___jp_3345_:
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_nat_dec_eq(v_n_u2081_3346_, v_n_u2082_3348_);
if (v___x_3350_ == 0)
{
return v___x_3350_;
}
else
{
uint8_t v___x_3351_; 
v___x_3351_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3335_, v_x_u2081_3347_, v_x_u2082_3349_);
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* v_00_u03c1_3435_, lean_object* v_x_3436_, lean_object* v_x_3437_){
_start:
{
uint8_t v_res_3438_; lean_object* v_r_3439_; 
v_res_3438_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_3435_, v_x_3436_, v_x_3437_);
lean_dec_ref(v_x_3437_);
lean_dec_ref(v_x_3436_);
lean_dec(v_00_u03c1_3435_);
v_r_3439_ = lean_box(v_res_3438_);
return v_r_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3442_, lean_object* v_x_u2081_3443_, lean_object* v_x_u2082_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_nat_dec_eq(v_x_u2081_3443_, v_x_u2082_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3443_, v_x_u2082_3444_, v_00_u03c1_3442_);
return v___x_3446_;
}
else
{
lean_dec(v_x_u2082_3444_);
lean_dec(v_x_u2081_3443_);
return v_00_u03c1_3442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3447_, lean_object* v_p_u2081_3448_, lean_object* v_p_u2082_3449_){
_start:
{
lean_object* v_x_3450_; uint8_t v_borrow_3451_; lean_object* v_ty_3452_; lean_object* v_x_3453_; uint8_t v_borrow_3454_; lean_object* v_ty_3455_; uint8_t v___y_3457_; uint8_t v___x_3461_; 
v_x_3450_ = lean_ctor_get(v_p_u2081_3448_, 0);
lean_inc(v_x_3450_);
v_borrow_3451_ = lean_ctor_get_uint8(v_p_u2081_3448_, sizeof(void*)*2);
v_ty_3452_ = lean_ctor_get(v_p_u2081_3448_, 1);
lean_inc(v_ty_3452_);
lean_dec_ref(v_p_u2081_3448_);
v_x_3453_ = lean_ctor_get(v_p_u2082_3449_, 0);
lean_inc(v_x_3453_);
v_borrow_3454_ = lean_ctor_get_uint8(v_p_u2082_3449_, sizeof(void*)*2);
v_ty_3455_ = lean_ctor_get(v_p_u2082_3449_, 1);
lean_inc(v_ty_3455_);
lean_dec_ref(v_p_u2082_3449_);
v___x_3461_ = l_Lean_IR_instBEqIRType_beq(v_ty_3452_, v_ty_3455_);
lean_dec(v_ty_3455_);
lean_dec(v_ty_3452_);
if (v___x_3461_ == 0)
{
v___y_3457_ = v___x_3461_;
goto v___jp_3456_;
}
else
{
if (v_borrow_3454_ == 0)
{
if (v_borrow_3451_ == 0)
{
v___y_3457_ = v___x_3461_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3462_; 
lean_dec(v_x_3453_);
lean_dec(v_x_3450_);
lean_dec(v_00_u03c1_3447_);
v___x_3462_ = lean_box(0);
return v___x_3462_;
}
}
else
{
v___y_3457_ = v_borrow_3451_;
goto v___jp_3456_;
}
}
v___jp_3456_:
{
if (v___y_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_dec(v_x_3453_);
lean_dec(v_x_3450_);
lean_dec(v_00_u03c1_3447_);
v___x_3458_ = lean_box(0);
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = l_Lean_IR_addVarRename(v_00_u03c1_3447_, v_x_3450_, v_x_3453_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3463_, lean_object* v_ps_u2081_3464_, lean_object* v_ps_u2082_3465_, lean_object* v_a_3466_, lean_object* v_b_3467_){
_start:
{
uint8_t v___x_3468_; 
v___x_3468_ = lean_nat_dec_lt(v_a_3466_, v_upperBound_3463_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_dec(v_a_3466_);
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v_b_3467_);
return v___x_3469_;
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3470_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_3471_ = lean_array_get_borrowed(v___x_3470_, v_ps_u2081_3464_, v_a_3466_);
v___x_3472_ = lean_array_get_borrowed(v___x_3470_, v_ps_u2082_3465_, v_a_3466_);
lean_inc(v___x_3472_);
lean_inc(v___x_3471_);
v___x_3473_ = l_Lean_IR_addParamRename(v_b_3467_, v___x_3471_, v___x_3472_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_dec(v_a_3466_);
return v___x_3473_;
}
else
{
lean_object* v_val_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_val_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___x_3475_ = lean_unsigned_to_nat(1u);
v___x_3476_ = lean_nat_add(v_a_3466_, v___x_3475_);
lean_dec(v_a_3466_);
v_a_3466_ = v___x_3476_;
v_b_3467_ = v_val_3474_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_3478_, lean_object* v_ps_u2081_3479_, lean_object* v_ps_u2082_3480_, lean_object* v_a_3481_, lean_object* v_b_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3478_, v_ps_u2081_3479_, v_ps_u2082_3480_, v_a_3481_, v_b_3482_);
lean_dec_ref(v_ps_u2082_3480_);
lean_dec_ref(v_ps_u2081_3479_);
lean_dec(v_upperBound_3478_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_3484_, lean_object* v_ps_u2081_3485_, lean_object* v_ps_u2082_3486_){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3487_ = lean_array_get_size(v_ps_u2081_3485_);
v___x_3488_ = lean_array_get_size(v_ps_u2082_3486_);
v___x_3489_ = lean_nat_dec_eq(v___x_3487_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
lean_dec(v_00_u03c1_3484_);
v___x_3490_ = lean_box(0);
return v___x_3490_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_3487_, v_ps_u2081_3485_, v_ps_u2082_3486_, v___x_3491_, v_00_u03c1_3484_);
return v___x_3492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* v_00_u03c1_3493_, lean_object* v_ps_u2081_3494_, lean_object* v_ps_u2082_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_IR_addParamsRename(v_00_u03c1_3493_, v_ps_u2081_3494_, v_ps_u2082_3495_);
lean_dec_ref(v_ps_u2082_3495_);
lean_dec_ref(v_ps_u2081_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object* v_upperBound_3497_, lean_object* v_ps_u2081_3498_, lean_object* v_ps_u2082_3499_, lean_object* v_inst_3500_, lean_object* v_R_3501_, lean_object* v_a_3502_, lean_object* v_b_3503_, lean_object* v_c_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3497_, v_ps_u2081_3498_, v_ps_u2082_3499_, v_a_3502_, v_b_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object* v_upperBound_3506_, lean_object* v_ps_u2081_3507_, lean_object* v_ps_u2082_3508_, lean_object* v_inst_3509_, lean_object* v_R_3510_, lean_object* v_a_3511_, lean_object* v_b_3512_, lean_object* v_c_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(v_upperBound_3506_, v_ps_u2081_3507_, v_ps_u2082_3508_, v_inst_3509_, v_R_3510_, v_a_3511_, v_b_3512_, v_c_3513_);
lean_dec_ref(v_ps_u2082_3508_);
lean_dec_ref(v_ps_u2081_3507_);
lean_dec(v_upperBound_3506_);
return v_res_3514_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* v_x_3515_, lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3527_; uint8_t v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; uint8_t v___y_3532_; uint8_t v___y_3533_; uint8_t v___y_3534_; lean_object* v_00_u03c1_3536_; lean_object* v_x_u2081_3537_; lean_object* v_n_u2081_3538_; uint8_t v_c_u2081_3539_; uint8_t v_p_u2081_3540_; lean_object* v_b_u2081_3541_; lean_object* v_x_u2082_3542_; lean_object* v_n_u2082_3543_; uint8_t v_c_u2082_3544_; uint8_t v_p_u2082_3545_; lean_object* v_b_u2082_3546_; 
switch(lean_obj_tag(v_x_3516_))
{
case 0:
{
if (lean_obj_tag(v_x_3517_) == 0)
{
lean_object* v_x_3549_; lean_object* v_ty_3550_; lean_object* v_e_3551_; lean_object* v_b_3552_; lean_object* v_x_3553_; lean_object* v_ty_3554_; lean_object* v_e_3555_; lean_object* v_b_3556_; uint8_t v___y_3558_; uint8_t v___x_3561_; 
v_x_3549_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3549_);
v_ty_3550_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_ty_3550_);
v_e_3551_ = lean_ctor_get(v_x_3516_, 2);
lean_inc_ref(v_e_3551_);
v_b_3552_ = lean_ctor_get(v_x_3516_, 3);
lean_inc(v_b_3552_);
lean_dec_ref_known(v_x_3516_, 4);
v_x_3553_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3553_);
v_ty_3554_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_ty_3554_);
v_e_3555_ = lean_ctor_get(v_x_3517_, 2);
lean_inc_ref(v_e_3555_);
v_b_3556_ = lean_ctor_get(v_x_3517_, 3);
lean_inc(v_b_3556_);
lean_dec_ref_known(v_x_3517_, 4);
v___x_3561_ = l_Lean_IR_instBEqIRType_beq(v_ty_3550_, v_ty_3554_);
lean_dec(v_ty_3554_);
lean_dec(v_ty_3550_);
if (v___x_3561_ == 0)
{
lean_dec_ref(v_e_3555_);
lean_dec_ref(v_e_3551_);
v___y_3558_ = v___x_3561_;
goto v___jp_3557_;
}
else
{
uint8_t v___x_3562_; 
v___x_3562_ = l_Lean_IR_Expr_alphaEqv(v_x_3515_, v_e_3551_, v_e_3555_);
lean_dec_ref(v_e_3555_);
lean_dec_ref(v_e_3551_);
v___y_3558_ = v___x_3562_;
goto v___jp_3557_;
}
v___jp_3557_:
{
if (v___y_3558_ == 0)
{
lean_dec(v_b_3556_);
lean_dec(v_x_3553_);
lean_dec(v_b_3552_);
lean_dec(v_x_3549_);
lean_dec(v_x_3515_);
return v___y_3558_;
}
else
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_IR_addVarRename(v_x_3515_, v_x_3549_, v_x_3553_);
v_x_3515_ = v___x_3559_;
v_x_3516_ = v_b_3552_;
v_x_3517_ = v_b_3556_;
goto _start;
}
}
}
else
{
uint8_t v___x_3563_; 
lean_dec_ref_known(v_x_3516_, 4);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3563_ = 0;
return v___x_3563_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3517_) == 1)
{
lean_object* v_j_3564_; lean_object* v_xs_3565_; lean_object* v_v_3566_; lean_object* v_b_3567_; lean_object* v_j_3568_; lean_object* v_xs_3569_; lean_object* v_v_3570_; lean_object* v_b_3571_; lean_object* v___x_3572_; 
v_j_3564_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_j_3564_);
v_xs_3565_ = lean_ctor_get(v_x_3516_, 1);
lean_inc_ref(v_xs_3565_);
v_v_3566_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_v_3566_);
v_b_3567_ = lean_ctor_get(v_x_3516_, 3);
lean_inc(v_b_3567_);
lean_dec_ref_known(v_x_3516_, 4);
v_j_3568_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_j_3568_);
v_xs_3569_ = lean_ctor_get(v_x_3517_, 1);
lean_inc_ref(v_xs_3569_);
v_v_3570_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_v_3570_);
v_b_3571_ = lean_ctor_get(v_x_3517_, 3);
lean_inc(v_b_3571_);
lean_dec_ref_known(v_x_3517_, 4);
lean_inc(v_x_3515_);
v___x_3572_ = l_Lean_IR_addParamsRename(v_x_3515_, v_xs_3565_, v_xs_3569_);
lean_dec_ref(v_xs_3569_);
lean_dec_ref(v_xs_3565_);
if (lean_obj_tag(v___x_3572_) == 0)
{
uint8_t v___x_3573_; 
lean_dec(v_b_3571_);
lean_dec(v_v_3570_);
lean_dec(v_j_3568_);
lean_dec(v_b_3567_);
lean_dec(v_v_3566_);
lean_dec(v_j_3564_);
lean_dec(v_x_3515_);
v___x_3573_ = 0;
return v___x_3573_;
}
else
{
lean_object* v_val_3574_; uint8_t v___x_3575_; 
v_val_3574_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3575_ = l_Lean_IR_FnBody_alphaEqv(v_val_3574_, v_v_3566_, v_v_3570_);
if (v___x_3575_ == 0)
{
lean_dec(v_b_3571_);
lean_dec(v_j_3568_);
lean_dec(v_b_3567_);
lean_dec(v_j_3564_);
lean_dec(v_x_3515_);
return v___x_3575_;
}
else
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_IR_addVarRename(v_x_3515_, v_j_3564_, v_j_3568_);
v_x_3515_ = v___x_3576_;
v_x_3516_ = v_b_3567_;
v_x_3517_ = v_b_3571_;
goto _start;
}
}
}
else
{
uint8_t v___x_3578_; 
lean_dec_ref_known(v_x_3516_, 4);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3578_ = 0;
return v___x_3578_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3517_) == 2)
{
lean_object* v_x_3579_; lean_object* v_i_3580_; lean_object* v_y_3581_; lean_object* v_b_3582_; lean_object* v_x_3583_; lean_object* v_i_3584_; lean_object* v_y_3585_; lean_object* v_b_3586_; uint8_t v___y_3588_; uint8_t v___x_3591_; 
v_x_3579_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3579_);
v_i_3580_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_i_3580_);
v_y_3581_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_y_3581_);
v_b_3582_ = lean_ctor_get(v_x_3516_, 3);
lean_inc(v_b_3582_);
lean_dec_ref_known(v_x_3516_, 4);
v_x_3583_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3583_);
v_i_3584_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_i_3584_);
v_y_3585_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_y_3585_);
v_b_3586_ = lean_ctor_get(v_x_3517_, 3);
lean_inc(v_b_3586_);
lean_dec_ref_known(v_x_3517_, 4);
v___x_3591_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_x_3579_, v_x_3583_);
lean_dec(v_x_3583_);
lean_dec(v_x_3579_);
if (v___x_3591_ == 0)
{
lean_dec(v_i_3584_);
lean_dec(v_i_3580_);
v___y_3588_ = v___x_3591_;
goto v___jp_3587_;
}
else
{
uint8_t v___x_3592_; 
v___x_3592_ = lean_nat_dec_eq(v_i_3580_, v_i_3584_);
lean_dec(v_i_3584_);
lean_dec(v_i_3580_);
v___y_3588_ = v___x_3592_;
goto v___jp_3587_;
}
v___jp_3587_:
{
if (v___y_3588_ == 0)
{
lean_dec(v_b_3586_);
lean_dec(v_y_3585_);
lean_dec(v_b_3582_);
lean_dec(v_y_3581_);
lean_dec(v_x_3515_);
return v___y_3588_;
}
else
{
uint8_t v___x_3589_; 
v___x_3589_ = l_Lean_IR_Arg_alphaEqv(v_x_3515_, v_y_3581_, v_y_3585_);
lean_dec(v_y_3585_);
lean_dec(v_y_3581_);
if (v___x_3589_ == 0)
{
lean_dec(v_b_3586_);
lean_dec(v_b_3582_);
lean_dec(v_x_3515_);
return v___x_3589_;
}
else
{
v_x_3516_ = v_b_3582_;
v_x_3517_ = v_b_3586_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3593_; 
lean_dec_ref_known(v_x_3516_, 4);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3593_ = 0;
return v___x_3593_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3517_) == 3)
{
lean_object* v_x_3594_; lean_object* v_cidx_3595_; lean_object* v_b_3596_; lean_object* v_x_3597_; lean_object* v_cidx_3598_; lean_object* v_b_3599_; uint8_t v___y_3601_; uint8_t v___x_3603_; 
v_x_3594_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3594_);
v_cidx_3595_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_cidx_3595_);
v_b_3596_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_b_3596_);
lean_dec_ref_known(v_x_3516_, 3);
v_x_3597_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3597_);
v_cidx_3598_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_cidx_3598_);
v_b_3599_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_b_3599_);
lean_dec_ref_known(v_x_3517_, 3);
v___x_3603_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_x_3594_, v_x_3597_);
lean_dec(v_x_3597_);
lean_dec(v_x_3594_);
if (v___x_3603_ == 0)
{
lean_dec(v_cidx_3598_);
lean_dec(v_cidx_3595_);
v___y_3601_ = v___x_3603_;
goto v___jp_3600_;
}
else
{
uint8_t v___x_3604_; 
v___x_3604_ = lean_nat_dec_eq(v_cidx_3595_, v_cidx_3598_);
lean_dec(v_cidx_3598_);
lean_dec(v_cidx_3595_);
v___y_3601_ = v___x_3604_;
goto v___jp_3600_;
}
v___jp_3600_:
{
if (v___y_3601_ == 0)
{
lean_dec(v_b_3599_);
lean_dec(v_b_3596_);
lean_dec(v_x_3515_);
return v___y_3601_;
}
else
{
v_x_3516_ = v_b_3596_;
v_x_3517_ = v_b_3599_;
goto _start;
}
}
}
else
{
uint8_t v___x_3605_; 
lean_dec_ref_known(v_x_3516_, 3);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3605_ = 0;
return v___x_3605_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3517_) == 4)
{
lean_object* v_x_3606_; lean_object* v_i_3607_; lean_object* v_y_3608_; lean_object* v_b_3609_; lean_object* v_x_3610_; lean_object* v_i_3611_; lean_object* v_y_3612_; lean_object* v_b_3613_; uint8_t v___y_3615_; uint8_t v___x_3618_; 
v_x_3606_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3606_);
v_i_3607_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_i_3607_);
v_y_3608_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_y_3608_);
v_b_3609_ = lean_ctor_get(v_x_3516_, 3);
lean_inc(v_b_3609_);
lean_dec_ref_known(v_x_3516_, 4);
v_x_3610_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3610_);
v_i_3611_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_i_3611_);
v_y_3612_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_y_3612_);
v_b_3613_ = lean_ctor_get(v_x_3517_, 3);
lean_inc(v_b_3613_);
lean_dec_ref_known(v_x_3517_, 4);
v___x_3618_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_x_3606_, v_x_3610_);
lean_dec(v_x_3610_);
lean_dec(v_x_3606_);
if (v___x_3618_ == 0)
{
lean_dec(v_i_3611_);
lean_dec(v_i_3607_);
v___y_3615_ = v___x_3618_;
goto v___jp_3614_;
}
else
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_nat_dec_eq(v_i_3607_, v_i_3611_);
lean_dec(v_i_3611_);
lean_dec(v_i_3607_);
v___y_3615_ = v___x_3619_;
goto v___jp_3614_;
}
v___jp_3614_:
{
if (v___y_3615_ == 0)
{
lean_dec(v_b_3613_);
lean_dec(v_y_3612_);
lean_dec(v_b_3609_);
lean_dec(v_y_3608_);
lean_dec(v_x_3515_);
return v___y_3615_;
}
else
{
uint8_t v___x_3616_; 
v___x_3616_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_y_3608_, v_y_3612_);
lean_dec(v_y_3612_);
lean_dec(v_y_3608_);
if (v___x_3616_ == 0)
{
lean_dec(v_b_3613_);
lean_dec(v_b_3609_);
lean_dec(v_x_3515_);
return v___x_3616_;
}
else
{
v_x_3516_ = v_b_3609_;
v_x_3517_ = v_b_3613_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3620_; 
lean_dec_ref_known(v_x_3516_, 4);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3620_ = 0;
return v___x_3620_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3517_) == 5)
{
lean_object* v_x_3621_; lean_object* v_i_3622_; lean_object* v_offset_3623_; lean_object* v_y_3624_; lean_object* v_ty_3625_; lean_object* v_b_3626_; lean_object* v_x_3627_; lean_object* v_i_3628_; lean_object* v_offset_3629_; lean_object* v_y_3630_; lean_object* v_ty_3631_; lean_object* v_b_3632_; uint8_t v___y_3634_; uint8_t v___x_3639_; 
v_x_3621_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3621_);
v_i_3622_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_i_3622_);
v_offset_3623_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_offset_3623_);
v_y_3624_ = lean_ctor_get(v_x_3516_, 3);
lean_inc(v_y_3624_);
v_ty_3625_ = lean_ctor_get(v_x_3516_, 4);
lean_inc(v_ty_3625_);
v_b_3626_ = lean_ctor_get(v_x_3516_, 5);
lean_inc(v_b_3626_);
lean_dec_ref_known(v_x_3516_, 6);
v_x_3627_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3627_);
v_i_3628_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_i_3628_);
v_offset_3629_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_offset_3629_);
v_y_3630_ = lean_ctor_get(v_x_3517_, 3);
lean_inc(v_y_3630_);
v_ty_3631_ = lean_ctor_get(v_x_3517_, 4);
lean_inc(v_ty_3631_);
v_b_3632_ = lean_ctor_get(v_x_3517_, 5);
lean_inc(v_b_3632_);
lean_dec_ref_known(v_x_3517_, 6);
v___x_3639_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_x_3621_, v_x_3627_);
lean_dec(v_x_3627_);
lean_dec(v_x_3621_);
if (v___x_3639_ == 0)
{
lean_dec(v_i_3628_);
lean_dec(v_i_3622_);
v___y_3634_ = v___x_3639_;
goto v___jp_3633_;
}
else
{
uint8_t v___x_3640_; 
v___x_3640_ = lean_nat_dec_eq(v_i_3622_, v_i_3628_);
lean_dec(v_i_3628_);
lean_dec(v_i_3622_);
v___y_3634_ = v___x_3640_;
goto v___jp_3633_;
}
v___jp_3633_:
{
if (v___y_3634_ == 0)
{
lean_dec(v_b_3632_);
lean_dec(v_ty_3631_);
lean_dec(v_y_3630_);
lean_dec(v_offset_3629_);
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_y_3624_);
lean_dec(v_offset_3623_);
lean_dec(v_x_3515_);
return v___y_3634_;
}
else
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_nat_dec_eq(v_offset_3623_, v_offset_3629_);
lean_dec(v_offset_3629_);
lean_dec(v_offset_3623_);
if (v___x_3635_ == 0)
{
lean_dec(v_b_3632_);
lean_dec(v_ty_3631_);
lean_dec(v_y_3630_);
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_y_3624_);
lean_dec(v_x_3515_);
return v___x_3635_;
}
else
{
uint8_t v___x_3636_; 
v___x_3636_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_y_3624_, v_y_3630_);
lean_dec(v_y_3630_);
lean_dec(v_y_3624_);
if (v___x_3636_ == 0)
{
lean_dec(v_b_3632_);
lean_dec(v_ty_3631_);
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_x_3515_);
return v___x_3636_;
}
else
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_IR_instBEqIRType_beq(v_ty_3625_, v_ty_3631_);
lean_dec(v_ty_3631_);
lean_dec(v_ty_3625_);
if (v___x_3637_ == 0)
{
lean_dec(v_b_3632_);
lean_dec(v_b_3626_);
lean_dec(v_x_3515_);
return v___x_3637_;
}
else
{
v_x_3516_ = v_b_3626_;
v_x_3517_ = v_b_3632_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_3641_; 
lean_dec_ref_known(v_x_3516_, 6);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3641_ = 0;
return v___x_3641_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3517_) == 6)
{
lean_object* v_x_3642_; lean_object* v_n_3643_; uint8_t v_c_3644_; uint8_t v_persistent_3645_; lean_object* v_b_3646_; lean_object* v_x_3647_; lean_object* v_n_3648_; uint8_t v_c_3649_; uint8_t v_persistent_3650_; lean_object* v_b_3651_; 
v_x_3642_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3642_);
v_n_3643_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_n_3643_);
v_c_3644_ = lean_ctor_get_uint8(v_x_3516_, sizeof(void*)*3);
v_persistent_3645_ = lean_ctor_get_uint8(v_x_3516_, sizeof(void*)*3 + 1);
v_b_3646_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_b_3646_);
lean_dec_ref_known(v_x_3516_, 3);
v_x_3647_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3647_);
v_n_3648_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_n_3648_);
v_c_3649_ = lean_ctor_get_uint8(v_x_3517_, sizeof(void*)*3);
v_persistent_3650_ = lean_ctor_get_uint8(v_x_3517_, sizeof(void*)*3 + 1);
v_b_3651_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_b_3651_);
lean_dec_ref_known(v_x_3517_, 3);
v_00_u03c1_3536_ = v_x_3515_;
v_x_u2081_3537_ = v_x_3642_;
v_n_u2081_3538_ = v_n_3643_;
v_c_u2081_3539_ = v_c_3644_;
v_p_u2081_3540_ = v_persistent_3645_;
v_b_u2081_3541_ = v_b_3646_;
v_x_u2082_3542_ = v_x_3647_;
v_n_u2082_3543_ = v_n_3648_;
v_c_u2082_3544_ = v_c_3649_;
v_p_u2082_3545_ = v_persistent_3650_;
v_b_u2082_3546_ = v_b_3651_;
goto v___jp_3535_;
}
else
{
uint8_t v___x_3652_; 
lean_dec_ref_known(v_x_3516_, 3);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3652_ = 0;
return v___x_3652_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3517_) == 7)
{
lean_object* v_x_3653_; lean_object* v_n_3654_; uint8_t v_c_3655_; uint8_t v_persistent_3656_; lean_object* v_b_3657_; lean_object* v_x_3658_; lean_object* v_n_3659_; uint8_t v_c_3660_; uint8_t v_persistent_3661_; lean_object* v_b_3662_; 
v_x_3653_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3653_);
v_n_3654_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_n_3654_);
v_c_3655_ = lean_ctor_get_uint8(v_x_3516_, sizeof(void*)*3);
v_persistent_3656_ = lean_ctor_get_uint8(v_x_3516_, sizeof(void*)*3 + 1);
v_b_3657_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_b_3657_);
lean_dec_ref_known(v_x_3516_, 3);
v_x_3658_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3658_);
v_n_3659_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_n_3659_);
v_c_3660_ = lean_ctor_get_uint8(v_x_3517_, sizeof(void*)*3);
v_persistent_3661_ = lean_ctor_get_uint8(v_x_3517_, sizeof(void*)*3 + 1);
v_b_3662_ = lean_ctor_get(v_x_3517_, 2);
lean_inc(v_b_3662_);
lean_dec_ref_known(v_x_3517_, 3);
v_00_u03c1_3536_ = v_x_3515_;
v_x_u2081_3537_ = v_x_3653_;
v_n_u2081_3538_ = v_n_3654_;
v_c_u2081_3539_ = v_c_3655_;
v_p_u2081_3540_ = v_persistent_3656_;
v_b_u2081_3541_ = v_b_3657_;
v_x_u2082_3542_ = v_x_3658_;
v_n_u2082_3543_ = v_n_3659_;
v_c_u2082_3544_ = v_c_3660_;
v_p_u2082_3545_ = v_persistent_3661_;
v_b_u2082_3546_ = v_b_3662_;
goto v___jp_3535_;
}
else
{
uint8_t v___x_3663_; 
lean_dec_ref_known(v_x_3516_, 3);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3663_ = 0;
return v___x_3663_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3517_) == 8)
{
lean_object* v_x_3664_; lean_object* v_b_3665_; lean_object* v_x_3666_; lean_object* v_b_3667_; uint8_t v___x_3668_; 
v_x_3664_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3664_);
v_b_3665_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_b_3665_);
lean_dec_ref_known(v_x_3516_, 2);
v_x_3666_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3666_);
v_b_3667_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_b_3667_);
lean_dec_ref_known(v_x_3517_, 2);
v___x_3668_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_x_3664_, v_x_3666_);
lean_dec(v_x_3666_);
lean_dec(v_x_3664_);
if (v___x_3668_ == 0)
{
lean_dec(v_b_3667_);
lean_dec(v_b_3665_);
lean_dec(v_x_3515_);
return v___x_3668_;
}
else
{
v_x_3516_ = v_b_3665_;
v_x_3517_ = v_b_3667_;
goto _start;
}
}
else
{
uint8_t v___x_3670_; 
lean_dec_ref_known(v_x_3516_, 2);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3670_ = 0;
return v___x_3670_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3517_) == 9)
{
lean_object* v_tid_3671_; lean_object* v_x_3672_; lean_object* v_cs_3673_; lean_object* v_tid_3674_; lean_object* v_x_3675_; lean_object* v_cs_3676_; uint8_t v___y_3678_; uint8_t v___x_3683_; 
v_tid_3671_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_tid_3671_);
v_x_3672_ = lean_ctor_get(v_x_3516_, 1);
lean_inc(v_x_3672_);
v_cs_3673_ = lean_ctor_get(v_x_3516_, 3);
lean_inc_ref(v_cs_3673_);
lean_dec_ref_known(v_x_3516_, 4);
v_tid_3674_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_tid_3674_);
v_x_3675_ = lean_ctor_get(v_x_3517_, 1);
lean_inc(v_x_3675_);
v_cs_3676_ = lean_ctor_get(v_x_3517_, 3);
lean_inc_ref(v_cs_3676_);
lean_dec_ref_known(v_x_3517_, 4);
v___x_3683_ = lean_name_eq(v_tid_3671_, v_tid_3674_);
lean_dec(v_tid_3674_);
lean_dec(v_tid_3671_);
if (v___x_3683_ == 0)
{
lean_dec(v_x_3675_);
lean_dec(v_x_3672_);
v___y_3678_ = v___x_3683_;
goto v___jp_3677_;
}
else
{
uint8_t v___x_3684_; 
v___x_3684_ = l_Lean_IR_VarId_alphaEqv(v_x_3515_, v_x_3672_, v_x_3675_);
lean_dec(v_x_3675_);
lean_dec(v_x_3672_);
v___y_3678_ = v___x_3684_;
goto v___jp_3677_;
}
v___jp_3677_:
{
if (v___y_3678_ == 0)
{
lean_dec_ref(v_cs_3676_);
lean_dec_ref(v_cs_3673_);
lean_dec(v_x_3515_);
return v___y_3678_;
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3679_ = lean_array_get_size(v_cs_3673_);
v___x_3680_ = lean_array_get_size(v_cs_3676_);
v___x_3681_ = lean_nat_dec_eq(v___x_3679_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_dec_ref(v_cs_3676_);
lean_dec_ref(v_cs_3673_);
lean_dec(v_x_3515_);
return v___x_3681_;
}
else
{
uint8_t v___x_3682_; 
v___x_3682_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3515_, v_cs_3673_, v_cs_3676_, v___x_3679_);
lean_dec_ref(v_cs_3676_);
lean_dec_ref(v_cs_3673_);
return v___x_3682_;
}
}
}
}
else
{
uint8_t v___x_3685_; 
lean_dec_ref_known(v_x_3516_, 4);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3685_ = 0;
return v___x_3685_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3517_) == 10)
{
lean_object* v_x_3686_; lean_object* v_x_3687_; uint8_t v___x_3688_; 
v_x_3686_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_x_3686_);
lean_dec_ref_known(v_x_3516_, 1);
v_x_3687_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_x_3687_);
lean_dec_ref_known(v_x_3517_, 1);
v___x_3688_ = l_Lean_IR_Arg_alphaEqv(v_x_3515_, v_x_3686_, v_x_3687_);
lean_dec(v_x_3687_);
lean_dec(v_x_3686_);
lean_dec(v_x_3515_);
return v___x_3688_;
}
else
{
uint8_t v___x_3689_; 
lean_dec_ref_known(v_x_3516_, 1);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3689_ = 0;
return v___x_3689_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3517_) == 11)
{
lean_object* v_j_3690_; lean_object* v_ys_3691_; lean_object* v_j_3692_; lean_object* v_ys_3693_; uint8_t v___x_3694_; 
v_j_3690_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_j_3690_);
v_ys_3691_ = lean_ctor_get(v_x_3516_, 1);
lean_inc_ref(v_ys_3691_);
lean_dec_ref_known(v_x_3516_, 2);
v_j_3692_ = lean_ctor_get(v_x_3517_, 0);
lean_inc(v_j_3692_);
v_ys_3693_ = lean_ctor_get(v_x_3517_, 1);
lean_inc_ref(v_ys_3693_);
lean_dec_ref_known(v_x_3517_, 2);
v___x_3694_ = lean_nat_dec_eq(v_j_3690_, v_j_3692_);
lean_dec(v_j_3692_);
lean_dec(v_j_3690_);
if (v___x_3694_ == 0)
{
lean_dec_ref(v_ys_3693_);
lean_dec_ref(v_ys_3691_);
lean_dec(v_x_3515_);
return v___x_3694_;
}
else
{
uint8_t v___x_3695_; 
v___x_3695_ = l_Lean_IR_args_alphaEqv(v_x_3515_, v_ys_3691_, v_ys_3693_);
lean_dec_ref(v_ys_3693_);
lean_dec_ref(v_ys_3691_);
lean_dec(v_x_3515_);
return v___x_3695_;
}
}
else
{
uint8_t v___x_3696_; 
lean_dec_ref_known(v_x_3516_, 2);
lean_dec(v_x_3517_);
lean_dec(v_x_3515_);
v___x_3696_ = 0;
return v___x_3696_;
}
}
default: 
{
lean_dec(v_x_3515_);
if (lean_obj_tag(v_x_3517_) == 12)
{
uint8_t v___x_3697_; 
v___x_3697_ = 1;
return v___x_3697_;
}
else
{
uint8_t v___x_3698_; 
lean_dec(v_x_3517_);
v___x_3698_ = 0;
return v___x_3698_;
}
}
}
v___jp_3518_:
{
if (v___y_3523_ == 0)
{
if (v___y_3522_ == 0)
{
v_x_3515_ = v___y_3521_;
v_x_3516_ = v___y_3520_;
v_x_3517_ = v___y_3519_;
goto _start;
}
else
{
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
return v___y_3523_;
}
}
else
{
if (v___y_3522_ == 0)
{
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
return v___y_3522_;
}
else
{
v_x_3515_ = v___y_3521_;
v_x_3516_ = v___y_3520_;
v_x_3517_ = v___y_3519_;
goto _start;
}
}
}
v___jp_3526_:
{
if (v___y_3534_ == 0)
{
lean_dec(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v___y_3527_);
return v___y_3534_;
}
else
{
if (v___y_3528_ == 0)
{
if (v___y_3533_ == 0)
{
v___y_3519_ = v___y_3527_;
v___y_3520_ = v___y_3529_;
v___y_3521_ = v___y_3530_;
v___y_3522_ = v___y_3531_;
v___y_3523_ = v___y_3532_;
goto v___jp_3518_;
}
else
{
lean_dec(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v___y_3527_);
return v___y_3528_;
}
}
else
{
if (v___y_3533_ == 0)
{
lean_dec(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v___y_3527_);
return v___y_3533_;
}
else
{
v___y_3519_ = v___y_3527_;
v___y_3520_ = v___y_3529_;
v___y_3521_ = v___y_3530_;
v___y_3522_ = v___y_3531_;
v___y_3523_ = v___y_3532_;
goto v___jp_3518_;
}
}
}
}
v___jp_3535_:
{
uint8_t v___x_3547_; 
v___x_3547_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3536_, v_x_u2081_3537_, v_x_u2082_3542_);
lean_dec(v_x_u2082_3542_);
lean_dec(v_x_u2081_3537_);
if (v___x_3547_ == 0)
{
lean_dec(v_n_u2082_3543_);
lean_dec(v_n_u2081_3538_);
v___y_3527_ = v_b_u2082_3546_;
v___y_3528_ = v_c_u2082_3544_;
v___y_3529_ = v_b_u2081_3541_;
v___y_3530_ = v_00_u03c1_3536_;
v___y_3531_ = v_p_u2081_3540_;
v___y_3532_ = v_p_u2082_3545_;
v___y_3533_ = v_c_u2081_3539_;
v___y_3534_ = v___x_3547_;
goto v___jp_3526_;
}
else
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_nat_dec_eq(v_n_u2081_3538_, v_n_u2082_3543_);
lean_dec(v_n_u2082_3543_);
lean_dec(v_n_u2081_3538_);
v___y_3527_ = v_b_u2082_3546_;
v___y_3528_ = v_c_u2082_3544_;
v___y_3529_ = v_b_u2081_3541_;
v___y_3530_ = v_00_u03c1_3536_;
v___y_3531_ = v_p_u2081_3540_;
v___y_3532_ = v_p_u2082_3545_;
v___y_3533_ = v_c_u2081_3539_;
v___y_3534_ = v___x_3548_;
goto v___jp_3526_;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* v_x_3699_, lean_object* v_xs_3700_, lean_object* v_ys_3701_, lean_object* v_x_3702_){
_start:
{
lean_object* v_zero_3703_; uint8_t v_isZero_3704_; 
v_zero_3703_ = lean_unsigned_to_nat(0u);
v_isZero_3704_ = lean_nat_dec_eq(v_x_3702_, v_zero_3703_);
if (v_isZero_3704_ == 1)
{
lean_dec(v_x_3702_);
lean_dec(v_x_3699_);
return v_isZero_3704_;
}
else
{
lean_object* v_one_3705_; lean_object* v_n_3706_; uint8_t v___y_3708_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_one_3705_ = lean_unsigned_to_nat(1u);
v_n_3706_ = lean_nat_sub(v_x_3702_, v_one_3705_);
lean_dec(v_x_3702_);
v___x_3710_ = lean_array_fget_borrowed(v_xs_3700_, v_n_3706_);
v___x_3711_ = lean_array_fget_borrowed(v_ys_3701_, v_n_3706_);
if (lean_obj_tag(v___x_3710_) == 0)
{
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_info_3712_; lean_object* v_b_3713_; lean_object* v_info_3714_; lean_object* v_b_3715_; uint8_t v___x_3716_; 
v_info_3712_ = lean_ctor_get(v___x_3710_, 0);
v_b_3713_ = lean_ctor_get(v___x_3710_, 1);
v_info_3714_ = lean_ctor_get(v___x_3711_, 0);
v_b_3715_ = lean_ctor_get(v___x_3711_, 1);
v___x_3716_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_3712_, v_info_3714_);
if (v___x_3716_ == 0)
{
v___y_3708_ = v___x_3716_;
goto v___jp_3707_;
}
else
{
uint8_t v___x_3717_; 
lean_inc(v_b_3715_);
lean_inc(v_b_3713_);
lean_inc(v_x_3699_);
v___x_3717_ = l_Lean_IR_FnBody_alphaEqv(v_x_3699_, v_b_3713_, v_b_3715_);
v___y_3708_ = v___x_3717_;
goto v___jp_3707_;
}
}
else
{
lean_dec(v_n_3706_);
lean_dec(v_x_3699_);
return v_isZero_3704_;
}
}
else
{
if (lean_obj_tag(v___x_3711_) == 1)
{
lean_object* v_b_3718_; lean_object* v_b_3719_; uint8_t v___x_3720_; 
v_b_3718_ = lean_ctor_get(v___x_3710_, 0);
v_b_3719_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_b_3719_);
lean_inc(v_b_3718_);
lean_inc(v_x_3699_);
v___x_3720_ = l_Lean_IR_FnBody_alphaEqv(v_x_3699_, v_b_3718_, v_b_3719_);
v___y_3708_ = v___x_3720_;
goto v___jp_3707_;
}
else
{
lean_dec(v_n_3706_);
lean_dec(v_x_3699_);
return v_isZero_3704_;
}
}
v___jp_3707_:
{
if (v___y_3708_ == 0)
{
lean_dec(v_n_3706_);
lean_dec(v_x_3699_);
return v___y_3708_;
}
else
{
v_x_3702_ = v_n_3706_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* v_x_3721_, lean_object* v_xs_3722_, lean_object* v_ys_3723_, lean_object* v_x_3724_){
_start:
{
uint8_t v_res_3725_; lean_object* v_r_3726_; 
v_res_3725_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3721_, v_xs_3722_, v_ys_3723_, v_x_3724_);
lean_dec_ref(v_ys_3723_);
lean_dec_ref(v_xs_3722_);
v_r_3726_ = lean_box(v_res_3725_);
return v_r_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* v_x_3727_, lean_object* v_x_3728_, lean_object* v_x_3729_){
_start:
{
uint8_t v_res_3730_; lean_object* v_r_3731_; 
v_res_3730_ = l_Lean_IR_FnBody_alphaEqv(v_x_3727_, v_x_3728_, v_x_3729_);
v_r_3731_ = lean_box(v_res_3730_);
return v_r_3731_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object* v_x_3732_, lean_object* v_xs_3733_, lean_object* v_ys_3734_, lean_object* v_hsz_3735_, lean_object* v_x_3736_, lean_object* v_x_3737_){
_start:
{
uint8_t v___x_3738_; 
v___x_3738_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3732_, v_xs_3733_, v_ys_3734_, v_x_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* v_x_3739_, lean_object* v_xs_3740_, lean_object* v_ys_3741_, lean_object* v_hsz_3742_, lean_object* v_x_3743_, lean_object* v_x_3744_){
_start:
{
uint8_t v_res_3745_; lean_object* v_r_3746_; 
v_res_3745_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(v_x_3739_, v_xs_3740_, v_ys_3741_, v_hsz_3742_, v_x_3743_, v_x_3744_);
lean_dec_ref(v_ys_3741_);
lean_dec_ref(v_xs_3740_);
v_r_3746_ = lean_box(v_res_3745_);
return v_r_3746_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* v_b_u2081_3747_, lean_object* v_b_u2082_3748_){
_start:
{
lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3749_ = lean_box(1);
v___x_3750_ = l_Lean_IR_FnBody_alphaEqv(v___x_3749_, v_b_u2081_3747_, v_b_u2082_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* v_b_u2081_3751_, lean_object* v_b_u2082_3752_){
_start:
{
uint8_t v_res_3753_; lean_object* v_r_3754_; 
v_res_3753_ = l_Lean_IR_FnBody_beq(v_b_u2081_3751_, v_b_u2082_3752_);
v_r_3754_ = lean_box(v_res_3753_);
return v_r_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* v_x_3775_, lean_object* v_t_3776_, lean_object* v_e_3777_){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3778_ = ((lean_object*)(l_Lean_IR_mkIf___closed__1));
v___x_3779_ = lean_box(1);
v___x_3780_ = ((lean_object*)(l_Lean_IR_mkIf___closed__4));
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v_e_3777_);
v___x_3782_ = ((lean_object*)(l_Lean_IR_mkIf___closed__7));
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set(v___x_3783_, 1, v_t_3776_);
v___x_3784_ = lean_unsigned_to_nat(2u);
v___x_3785_ = lean_mk_empty_array_with_capacity(v___x_3784_);
v___x_3786_ = lean_array_push(v___x_3785_, v___x_3781_);
v___x_3787_ = lean_array_push(v___x_3786_, v___x_3783_);
v___x_3788_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3778_);
lean_ctor_set(v___x_3788_, 1, v_x_3775_);
lean_ctor_set(v___x_3788_, 2, v___x_3779_);
lean_ctor_set(v___x_3788_, 3, v___x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* v_t_3795_){
_start:
{
switch(lean_obj_tag(v_t_3795_))
{
case 5:
{
lean_object* v___x_3796_; 
v___x_3796_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__0));
return v___x_3796_;
}
case 3:
{
lean_object* v___x_3797_; 
v___x_3797_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__1));
return v___x_3797_;
}
case 4:
{
lean_object* v___x_3798_; 
v___x_3798_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__2));
return v___x_3798_;
}
case 0:
{
lean_object* v___x_3799_; 
v___x_3799_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__3));
return v___x_3799_;
}
case 9:
{
lean_object* v___x_3800_; 
v___x_3800_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__4));
return v___x_3800_;
}
default: 
{
lean_object* v___x_3801_; 
v___x_3801_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__5));
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* v_t_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_IR_getUnboxOpName(v_t_3802_);
lean_dec(v_t_3802_);
return v_res_3803_;
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
