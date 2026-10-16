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
static const lean_ctor_object l_Lean_IR_Decl_getInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_IR_Decl_getInfo___closed__0 = (const lean_object*)&l_Lean_IR_Decl_getInfo___closed__0_value;
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
lean_inc_ref(v_info_1916_);
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
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
lean_object* v_info_1982_; 
v_info_1982_ = lean_ctor_get(v_x_1981_, 4);
lean_inc_ref(v_info_1982_);
return v_info_1982_;
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = ((lean_object*)(l_Lean_IR_Decl_getInfo___closed__0));
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* v_x_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_IR_Decl_getInfo(v_x_1984_);
lean_dec_ref(v_x_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(lean_object* v_msg_1986_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_IR_instInhabitedDecl_default));
v___x_1988_ = lean_panic_fn_borrowed(v___x_1987_, v_msg_1986_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__3(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1992_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__2));
v___x_1993_ = lean_unsigned_to_nat(9u);
v___x_1994_ = lean_unsigned_to_nat(384u);
v___x_1995_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__1));
v___x_1996_ = ((lean_object*)(l_Lean_IR_Decl_updateBody_x21___closed__0));
v___x_1997_ = l_mkPanicMessageWithDecl(v___x_1996_, v___x_1995_, v___x_1994_, v___x_1993_, v___x_1992_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* v_d_1998_, lean_object* v_bNew_1999_){
_start:
{
if (lean_obj_tag(v_d_1998_) == 0)
{
lean_object* v_f_2000_; lean_object* v_xs_2001_; lean_object* v_type_2002_; lean_object* v_info_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_f_2000_ = lean_ctor_get(v_d_1998_, 0);
v_xs_2001_ = lean_ctor_get(v_d_1998_, 1);
v_type_2002_ = lean_ctor_get(v_d_1998_, 2);
v_info_2003_ = lean_ctor_get(v_d_1998_, 4);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_d_1998_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_d_1998_, 3);
lean_dec(v_unused_2011_);
v___x_2005_ = v_d_1998_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_info_2003_);
lean_inc(v_type_2002_);
lean_inc(v_xs_2001_);
lean_inc(v_f_2000_);
lean_dec(v_d_1998_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 3, v_bNew_1999_);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_f_2000_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_xs_2001_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_type_2002_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_bNew_1999_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_info_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_bNew_1999_);
lean_dec_ref(v_d_1998_);
v___x_2012_ = lean_obj_once(&l_Lean_IR_Decl_updateBody_x21___closed__3, &l_Lean_IR_Decl_updateBody_x21___closed__3_once, _init_l_Lean_IR_Decl_updateBody_x21___closed__3);
v___x_2013_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_2012_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkDummyExternDecl(lean_object* v_f_2014_, lean_object* v_xs_2015_, lean_object* v_ty_2016_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_box(12);
v___x_2018_ = ((lean_object*)(l_Lean_IR_Decl_getInfo___closed__0));
v___x_2019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2019_, 0, v_f_2014_);
lean_ctor_set(v___x_2019_, 1, v_xs_2015_);
lean_ctor_set(v___x_2019_, 2, v_ty_2016_);
lean_ctor_set(v___x_2019_, 3, v___x_2017_);
lean_ctor_set(v___x_2019_, 4, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(lean_object* v_k_2020_, lean_object* v_v_2021_, lean_object* v_t_2022_){
_start:
{
if (lean_obj_tag(v_t_2022_) == 0)
{
lean_object* v_size_2023_; lean_object* v_k_2024_; lean_object* v_v_2025_; lean_object* v_l_2026_; lean_object* v_r_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2308_; 
v_size_2023_ = lean_ctor_get(v_t_2022_, 0);
v_k_2024_ = lean_ctor_get(v_t_2022_, 1);
v_v_2025_ = lean_ctor_get(v_t_2022_, 2);
v_l_2026_ = lean_ctor_get(v_t_2022_, 3);
v_r_2027_ = lean_ctor_get(v_t_2022_, 4);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_t_2022_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2029_ = v_t_2022_;
v_isShared_2030_ = v_isSharedCheck_2308_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_r_2027_);
lean_inc(v_l_2026_);
lean_inc(v_v_2025_);
lean_inc(v_k_2024_);
lean_inc(v_size_2023_);
lean_dec(v_t_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2308_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_nat_dec_lt(v_k_2020_, v_k_2024_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_nat_dec_eq(v_k_2020_, v_k_2024_);
if (v___x_2032_ == 0)
{
lean_object* v_impl_2033_; lean_object* v___x_2034_; 
lean_dec(v_size_2023_);
v_impl_2033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2020_, v_v_2021_, v_r_2027_);
v___x_2034_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2026_) == 0)
{
lean_object* v_size_2035_; lean_object* v_size_2036_; lean_object* v_k_2037_; lean_object* v_v_2038_; lean_object* v_l_2039_; lean_object* v_r_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_size_2035_ = lean_ctor_get(v_l_2026_, 0);
v_size_2036_ = lean_ctor_get(v_impl_2033_, 0);
v_k_2037_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2038_ = lean_ctor_get(v_impl_2033_, 2);
v_l_2039_ = lean_ctor_get(v_impl_2033_, 3);
lean_inc(v_l_2039_);
v_r_2040_ = lean_ctor_get(v_impl_2033_, 4);
v___x_2041_ = lean_unsigned_to_nat(3u);
v___x_2042_ = lean_nat_mul(v___x_2041_, v_size_2035_);
v___x_2043_ = lean_nat_dec_lt(v___x_2042_, v_size_2036_);
lean_dec(v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_l_2039_);
v___x_2044_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2045_ = lean_nat_add(v___x_2044_, v_size_2036_);
lean_dec(v___x_2044_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_impl_2033_);
lean_ctor_set(v___x_2029_, 0, v___x_2045_);
v___x_2047_ = v___x_2029_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_impl_2033_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2112_; 
lean_inc(v_r_2040_);
lean_inc(v_v_2038_);
lean_inc(v_k_2037_);
lean_inc(v_size_2036_);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; 
v_unused_2113_ = lean_ctor_get(v_impl_2033_, 4);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_impl_2033_, 2);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_impl_2033_, 1);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2117_);
v___x_2050_ = v_impl_2033_;
v_isShared_2051_ = v_isSharedCheck_2112_;
goto v_resetjp_2049_;
}
else
{
lean_dec(v_impl_2033_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2112_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_size_2052_; lean_object* v_k_2053_; lean_object* v_v_2054_; lean_object* v_l_2055_; lean_object* v_r_2056_; lean_object* v_size_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_size_2052_ = lean_ctor_get(v_l_2039_, 0);
v_k_2053_ = lean_ctor_get(v_l_2039_, 1);
v_v_2054_ = lean_ctor_get(v_l_2039_, 2);
v_l_2055_ = lean_ctor_get(v_l_2039_, 3);
v_r_2056_ = lean_ctor_get(v_l_2039_, 4);
v_size_2057_ = lean_ctor_get(v_r_2040_, 0);
v___x_2058_ = lean_unsigned_to_nat(2u);
v___x_2059_ = lean_nat_mul(v___x_2058_, v_size_2057_);
v___x_2060_ = lean_nat_dec_lt(v_size_2052_, v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2088_; 
lean_inc(v_r_2056_);
lean_inc(v_l_2055_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_l_2039_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; 
v_unused_2089_ = lean_ctor_get(v_l_2039_, 4);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_l_2039_, 3);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_l_2039_, 2);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_l_2039_, 1);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_l_2039_, 0);
lean_dec(v_unused_2093_);
v___x_2062_ = v_l_2039_;
v_isShared_2063_ = v_isSharedCheck_2088_;
goto v_resetjp_2061_;
}
else
{
lean_dec(v_l_2039_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2088_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2078_; 
v___x_2064_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2065_ = lean_nat_add(v___x_2064_, v_size_2036_);
lean_dec(v_size_2036_);
if (lean_obj_tag(v_l_2055_) == 0)
{
lean_object* v_size_2086_; 
v_size_2086_ = lean_ctor_get(v_l_2055_, 0);
lean_inc(v_size_2086_);
v___y_2078_ = v_size_2086_;
goto v___jp_2077_;
}
else
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___y_2078_ = v___x_2087_;
goto v___jp_2077_;
}
v___jp_2066_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_nat_add(v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec(v___y_2068_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 4, v_r_2040_);
lean_ctor_set(v___x_2062_, 3, v_r_2056_);
lean_ctor_set(v___x_2062_, 2, v_v_2038_);
lean_ctor_set(v___x_2062_, 1, v_k_2037_);
lean_ctor_set(v___x_2062_, 0, v___x_2070_);
v___x_2072_ = v___x_2062_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_r_2056_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_r_2040_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 4, v___x_2072_);
lean_ctor_set(v___x_2050_, 3, v___y_2067_);
lean_ctor_set(v___x_2050_, 2, v_v_2054_);
lean_ctor_set(v___x_2050_, 1, v_k_2053_);
lean_ctor_set(v___x_2050_, 0, v___x_2065_);
v___x_2074_ = v___x_2050_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v___y_2067_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
v___jp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_nat_add(v___x_2064_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec(v___x_2064_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_l_2055_);
lean_ctor_set(v___x_2029_, 0, v___x_2079_);
v___x_2081_ = v___x_2029_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_l_2055_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_nat_add(v___x_2034_, v_size_2057_);
if (lean_obj_tag(v_r_2056_) == 0)
{
lean_object* v_size_2083_; 
v_size_2083_ = lean_ctor_get(v_r_2056_, 0);
lean_inc(v_size_2083_);
v___y_2067_ = v___x_2081_;
v___y_2068_ = v___x_2082_;
v___y_2069_ = v_size_2083_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___y_2067_ = v___x_2081_;
v___y_2068_ = v___x_2082_;
v___y_2069_ = v___x_2084_;
goto v___jp_2066_;
}
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
lean_del_object(v___x_2029_);
v___x_2094_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2095_ = lean_nat_add(v___x_2094_, v_size_2036_);
lean_dec(v_size_2036_);
v___x_2096_ = lean_nat_add(v___x_2094_, v_size_2052_);
lean_dec(v___x_2094_);
lean_inc_ref(v_l_2026_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 4, v_l_2039_);
lean_ctor_set(v___x_2050_, 3, v_l_2026_);
lean_ctor_set(v___x_2050_, 2, v_v_2025_);
lean_ctor_set(v___x_2050_, 1, v_k_2024_);
lean_ctor_set(v___x_2050_, 0, v___x_2096_);
v___x_2098_ = v___x_2050_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_l_2039_);
v___x_2098_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_isSharedCheck_2105_ = !lean_is_exclusive(v_l_2026_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; lean_object* v_unused_2107_; lean_object* v_unused_2108_; lean_object* v_unused_2109_; lean_object* v_unused_2110_; 
v_unused_2106_ = lean_ctor_get(v_l_2026_, 4);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_l_2026_, 3);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_l_2026_, 2);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_l_2026_, 1);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_l_2026_, 0);
lean_dec(v_unused_2110_);
v___x_2100_ = v_l_2026_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_dec(v_l_2026_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 4, v_r_2040_);
lean_ctor_set(v___x_2100_, 3, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v_v_2038_);
lean_ctor_set(v___x_2100_, 1, v_k_2037_);
lean_ctor_set(v___x_2100_, 0, v___x_2095_);
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_r_2040_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2118_; 
v_l_2118_ = lean_ctor_get(v_impl_2033_, 3);
lean_inc(v_l_2118_);
if (lean_obj_tag(v_l_2118_) == 0)
{
lean_object* v_r_2119_; lean_object* v_k_2120_; lean_object* v_v_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2144_; 
v_r_2119_ = lean_ctor_get(v_impl_2033_, 4);
v_k_2120_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2121_ = lean_ctor_get(v_impl_2033_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2145_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2146_);
v___x_2123_ = v_impl_2033_;
v_isShared_2124_ = v_isSharedCheck_2144_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_r_2119_);
lean_inc(v_v_2121_);
lean_inc(v_k_2120_);
lean_dec(v_impl_2033_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2144_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_k_2125_; lean_object* v_v_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2140_; 
v_k_2125_ = lean_ctor_get(v_l_2118_, 1);
v_v_2126_ = lean_ctor_get(v_l_2118_, 2);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_l_2118_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; 
v_unused_2141_ = lean_ctor_get(v_l_2118_, 4);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_l_2118_, 3);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_l_2118_, 0);
lean_dec(v_unused_2143_);
v___x_2128_ = v_l_2118_;
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_v_2126_);
lean_inc(v_k_2125_);
lean_dec(v_l_2118_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2119_, 2);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v_r_2119_);
lean_ctor_set(v___x_2128_, 3, v_r_2119_);
lean_ctor_set(v___x_2128_, 2, v_v_2025_);
lean_ctor_set(v___x_2128_, 1, v_k_2024_);
lean_ctor_set(v___x_2128_, 0, v___x_2034_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_r_2119_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_r_2119_);
v___x_2132_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
lean_inc(v_r_2119_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 3, v_r_2119_);
lean_ctor_set(v___x_2123_, 0, v___x_2034_);
v___x_2134_ = v___x_2123_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_r_2119_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_r_2119_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2134_);
lean_ctor_set(v___x_2029_, 3, v___x_2132_);
lean_ctor_set(v___x_2029_, 2, v_v_2126_);
lean_ctor_set(v___x_2029_, 1, v_k_2125_);
lean_ctor_set(v___x_2029_, 0, v___x_2130_);
v___x_2136_ = v___x_2029_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_2125_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_2126_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
else
{
lean_object* v_r_2147_; 
v_r_2147_ = lean_ctor_get(v_impl_2033_, 4);
lean_inc(v_r_2147_);
if (lean_obj_tag(v_r_2147_) == 0)
{
lean_object* v_k_2148_; lean_object* v_v_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2160_; 
v_k_2148_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2149_ = lean_ctor_get(v_impl_2033_, 2);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2161_ = lean_ctor_get(v_impl_2033_, 4);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2163_);
v___x_2151_ = v_impl_2033_;
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_v_2149_);
lean_inc(v_k_2148_);
lean_dec(v_impl_2033_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = lean_unsigned_to_nat(3u);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 4, v_l_2118_);
lean_ctor_set(v___x_2151_, 2, v_v_2025_);
lean_ctor_set(v___x_2151_, 1, v_k_2024_);
lean_ctor_set(v___x_2151_, 0, v___x_2034_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_l_2118_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_l_2118_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_r_2147_);
lean_ctor_set(v___x_2029_, 3, v___x_2155_);
lean_ctor_set(v___x_2029_, 2, v_v_2149_);
lean_ctor_set(v___x_2029_, 1, v_k_2148_);
lean_ctor_set(v___x_2029_, 0, v___x_2153_);
v___x_2157_ = v___x_2029_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_k_2148_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_v_2149_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_r_2147_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_unsigned_to_nat(2u);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_impl_2033_);
lean_ctor_set(v___x_2029_, 3, v_r_2147_);
lean_ctor_set(v___x_2029_, 0, v___x_2164_);
v___x_2166_ = v___x_2029_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_r_2147_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_impl_2033_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
else
{
lean_object* v___x_2169_; 
lean_dec(v_v_2025_);
lean_dec(v_k_2024_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 2, v_v_2021_);
lean_ctor_set(v___x_2029_, 1, v_k_2020_);
v___x_2169_ = v___x_2029_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_size_2023_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_k_2020_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_v_2021_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_l_2026_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_r_2027_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_impl_2171_; lean_object* v___x_2172_; 
lean_dec(v_size_2023_);
v_impl_2171_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2020_, v_v_2021_, v_l_2026_);
v___x_2172_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2027_) == 0)
{
lean_object* v_size_2173_; lean_object* v_size_2174_; lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v_l_2177_; lean_object* v_r_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_size_2173_ = lean_ctor_get(v_r_2027_, 0);
v_size_2174_ = lean_ctor_get(v_impl_2171_, 0);
v_k_2175_ = lean_ctor_get(v_impl_2171_, 1);
v_v_2176_ = lean_ctor_get(v_impl_2171_, 2);
v_l_2177_ = lean_ctor_get(v_impl_2171_, 3);
v_r_2178_ = lean_ctor_get(v_impl_2171_, 4);
lean_inc(v_r_2178_);
v___x_2179_ = lean_unsigned_to_nat(3u);
v___x_2180_ = lean_nat_mul(v___x_2179_, v_size_2173_);
v___x_2181_ = lean_nat_dec_lt(v___x_2180_, v_size_2174_);
lean_dec(v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec(v_r_2178_);
v___x_2182_ = lean_nat_add(v___x_2172_, v_size_2174_);
v___x_2183_ = lean_nat_add(v___x_2182_, v_size_2173_);
lean_dec(v___x_2182_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 3, v_impl_2171_);
lean_ctor_set(v___x_2029_, 0, v___x_2183_);
v___x_2185_ = v___x_2029_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_impl_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_r_2027_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2252_; 
lean_inc(v_l_2177_);
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_inc(v_size_2174_);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_impl_2171_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; 
v_unused_2253_ = lean_ctor_get(v_impl_2171_, 4);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_impl_2171_, 3);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_impl_2171_, 2);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_impl_2171_, 1);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_impl_2171_, 0);
lean_dec(v_unused_2257_);
v___x_2188_ = v_impl_2171_;
v_isShared_2189_ = v_isSharedCheck_2252_;
goto v_resetjp_2187_;
}
else
{
lean_dec(v_impl_2171_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2252_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_size_2190_; lean_object* v_size_2191_; lean_object* v_k_2192_; lean_object* v_v_2193_; lean_object* v_l_2194_; lean_object* v_r_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v_size_2190_ = lean_ctor_get(v_l_2177_, 0);
v_size_2191_ = lean_ctor_get(v_r_2178_, 0);
v_k_2192_ = lean_ctor_get(v_r_2178_, 1);
v_v_2193_ = lean_ctor_get(v_r_2178_, 2);
v_l_2194_ = lean_ctor_get(v_r_2178_, 3);
v_r_2195_ = lean_ctor_get(v_r_2178_, 4);
v___x_2196_ = lean_unsigned_to_nat(2u);
v___x_2197_ = lean_nat_mul(v___x_2196_, v_size_2190_);
v___x_2198_ = lean_nat_dec_lt(v_size_2191_, v___x_2197_);
lean_dec(v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2227_; 
lean_inc(v_r_2195_);
lean_inc(v_l_2194_);
lean_inc(v_v_2193_);
lean_inc(v_k_2192_);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_r_2178_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2228_ = lean_ctor_get(v_r_2178_, 4);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_r_2178_, 3);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_r_2178_, 2);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_r_2178_, 1);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_r_2178_, 0);
lean_dec(v_unused_2232_);
v___x_2200_ = v_r_2178_;
v_isShared_2201_ = v_isSharedCheck_2227_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v_r_2178_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2227_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___x_2215_; lean_object* v___y_2217_; 
v___x_2202_ = lean_nat_add(v___x_2172_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2203_ = lean_nat_add(v___x_2202_, v_size_2173_);
lean_dec(v___x_2202_);
v___x_2215_ = lean_nat_add(v___x_2172_, v_size_2190_);
if (lean_obj_tag(v_l_2194_) == 0)
{
lean_object* v_size_2225_; 
v_size_2225_ = lean_ctor_get(v_l_2194_, 0);
lean_inc(v_size_2225_);
v___y_2217_ = v_size_2225_;
goto v___jp_2216_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___y_2217_ = v___x_2226_;
goto v___jp_2216_;
}
v___jp_2204_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_nat_add(v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec(v___y_2206_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 4, v_r_2027_);
lean_ctor_set(v___x_2200_, 3, v_r_2195_);
lean_ctor_set(v___x_2200_, 2, v_v_2025_);
lean_ctor_set(v___x_2200_, 1, v_k_2024_);
lean_ctor_set(v___x_2200_, 0, v___x_2208_);
v___x_2210_ = v___x_2200_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_r_2195_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_r_2027_);
v___x_2210_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 4, v___x_2210_);
lean_ctor_set(v___x_2188_, 3, v___y_2205_);
lean_ctor_set(v___x_2188_, 2, v_v_2193_);
lean_ctor_set(v___x_2188_, 1, v_k_2192_);
lean_ctor_set(v___x_2188_, 0, v___x_2203_);
v___x_2212_ = v___x_2188_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_k_2192_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_v_2193_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v___y_2205_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
v___jp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_nat_add(v___x_2215_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec(v___x_2215_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_l_2194_);
lean_ctor_set(v___x_2029_, 3, v_l_2177_);
lean_ctor_set(v___x_2029_, 2, v_v_2176_);
lean_ctor_set(v___x_2029_, 1, v_k_2175_);
lean_ctor_set(v___x_2029_, 0, v___x_2218_);
v___x_2220_ = v___x_2029_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_l_2177_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_l_2194_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_nat_add(v___x_2172_, v_size_2173_);
if (lean_obj_tag(v_r_2195_) == 0)
{
lean_object* v_size_2222_; 
v_size_2222_ = lean_ctor_get(v_r_2195_, 0);
lean_inc(v_size_2222_);
v___y_2205_ = v___x_2220_;
v___y_2206_ = v___x_2221_;
v___y_2207_ = v_size_2222_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___y_2205_ = v___x_2220_;
v___y_2206_ = v___x_2221_;
v___y_2207_ = v___x_2223_;
goto v___jp_2204_;
}
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_del_object(v___x_2029_);
v___x_2233_ = lean_nat_add(v___x_2172_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2234_ = lean_nat_add(v___x_2233_, v_size_2173_);
lean_dec(v___x_2233_);
v___x_2235_ = lean_nat_add(v___x_2172_, v_size_2173_);
v___x_2236_ = lean_nat_add(v___x_2235_, v_size_2191_);
lean_dec(v___x_2235_);
lean_inc_ref(v_r_2027_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 4, v_r_2027_);
lean_ctor_set(v___x_2188_, 3, v_r_2178_);
lean_ctor_set(v___x_2188_, 2, v_v_2025_);
lean_ctor_set(v___x_2188_, 1, v_k_2024_);
lean_ctor_set(v___x_2188_, 0, v___x_2236_);
v___x_2238_ = v___x_2188_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_r_2178_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_r_2027_);
v___x_2238_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_isSharedCheck_2245_ = !lean_is_exclusive(v_r_2027_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; lean_object* v_unused_2247_; lean_object* v_unused_2248_; lean_object* v_unused_2249_; lean_object* v_unused_2250_; 
v_unused_2246_ = lean_ctor_get(v_r_2027_, 4);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_r_2027_, 3);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_r_2027_, 2);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_r_2027_, 1);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_r_2027_, 0);
lean_dec(v_unused_2250_);
v___x_2240_ = v_r_2027_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_dec(v_r_2027_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v___x_2238_);
lean_ctor_set(v___x_2240_, 3, v_l_2177_);
lean_ctor_set(v___x_2240_, 2, v_v_2176_);
lean_ctor_set(v___x_2240_, 1, v_k_2175_);
lean_ctor_set(v___x_2240_, 0, v___x_2234_);
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_l_2177_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v___x_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2258_; 
v_l_2258_ = lean_ctor_get(v_impl_2171_, 3);
if (lean_obj_tag(v_l_2258_) == 0)
{
lean_object* v_r_2259_; lean_object* v_k_2260_; lean_object* v_v_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2272_; 
lean_inc_ref(v_l_2258_);
v_r_2259_ = lean_ctor_get(v_impl_2171_, 4);
v_k_2260_ = lean_ctor_get(v_impl_2171_, 1);
v_v_2261_ = lean_ctor_get(v_impl_2171_, 2);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_impl_2171_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; lean_object* v_unused_2274_; 
v_unused_2273_ = lean_ctor_get(v_impl_2171_, 3);
lean_dec(v_unused_2273_);
v_unused_2274_ = lean_ctor_get(v_impl_2171_, 0);
lean_dec(v_unused_2274_);
v___x_2263_ = v_impl_2171_;
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_r_2259_);
lean_inc(v_v_2261_);
lean_inc(v_k_2260_);
lean_dec(v_impl_2171_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2259_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 3, v_r_2259_);
lean_ctor_set(v___x_2263_, 2, v_v_2025_);
lean_ctor_set(v___x_2263_, 1, v_k_2024_);
lean_ctor_set(v___x_2263_, 0, v___x_2172_);
v___x_2267_ = v___x_2263_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_r_2259_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_r_2259_);
v___x_2267_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2267_);
lean_ctor_set(v___x_2029_, 3, v_l_2258_);
lean_ctor_set(v___x_2029_, 2, v_v_2261_);
lean_ctor_set(v___x_2029_, 1, v_k_2260_);
lean_ctor_set(v___x_2029_, 0, v___x_2265_);
v___x_2269_ = v___x_2029_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_k_2260_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_v_2261_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_r_2275_; 
v_r_2275_ = lean_ctor_get(v_impl_2171_, 4);
lean_inc(v_r_2275_);
if (lean_obj_tag(v_r_2275_) == 0)
{
lean_object* v_k_2276_; lean_object* v_v_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2300_; 
lean_inc(v_l_2258_);
v_k_2276_ = lean_ctor_get(v_impl_2171_, 1);
v_v_2277_ = lean_ctor_get(v_impl_2171_, 2);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_impl_2171_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; lean_object* v_unused_2302_; lean_object* v_unused_2303_; 
v_unused_2301_ = lean_ctor_get(v_impl_2171_, 4);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_impl_2171_, 3);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_impl_2171_, 0);
lean_dec(v_unused_2303_);
v___x_2279_ = v_impl_2171_;
v_isShared_2280_ = v_isSharedCheck_2300_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_v_2277_);
lean_inc(v_k_2276_);
lean_dec(v_impl_2171_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2300_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v_k_2281_; lean_object* v_v_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2296_; 
v_k_2281_ = lean_ctor_get(v_r_2275_, 1);
v_v_2282_ = lean_ctor_get(v_r_2275_, 2);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_r_2275_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; lean_object* v_unused_2298_; lean_object* v_unused_2299_; 
v_unused_2297_ = lean_ctor_get(v_r_2275_, 4);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_r_2275_, 3);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_r_2275_, 0);
lean_dec(v_unused_2299_);
v___x_2284_ = v_r_2275_;
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_v_2282_);
lean_inc(v_k_2281_);
lean_dec(v_r_2275_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_unsigned_to_nat(3u);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 4, v_l_2258_);
lean_ctor_set(v___x_2284_, 3, v_l_2258_);
lean_ctor_set(v___x_2284_, 2, v_v_2277_);
lean_ctor_set(v___x_2284_, 1, v_k_2276_);
lean_ctor_set(v___x_2284_, 0, v___x_2172_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_k_2276_);
lean_ctor_set(v_reuseFailAlloc_2295_, 2, v_v_2277_);
lean_ctor_set(v_reuseFailAlloc_2295_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2295_, 4, v_l_2258_);
v___x_2288_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 4, v_l_2258_);
lean_ctor_set(v___x_2279_, 2, v_v_2025_);
lean_ctor_set(v___x_2279_, 1, v_k_2024_);
lean_ctor_set(v___x_2279_, 0, v___x_2172_);
v___x_2290_ = v___x_2279_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v_l_2258_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2290_);
lean_ctor_set(v___x_2029_, 3, v___x_2288_);
lean_ctor_set(v___x_2029_, 2, v_v_2282_);
lean_ctor_set(v___x_2029_, 1, v_k_2281_);
lean_ctor_set(v___x_2029_, 0, v___x_2286_);
v___x_2292_ = v___x_2029_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_k_2281_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_v_2282_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_unsigned_to_nat(2u);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_r_2275_);
lean_ctor_set(v___x_2029_, 3, v_impl_2171_);
lean_ctor_set(v___x_2029_, 0, v___x_2304_);
v___x_2306_ = v___x_2029_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_k_2024_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_v_2025_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_impl_2171_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_r_2275_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v_k_2020_);
lean_ctor_set(v___x_2310_, 2, v_v_2021_);
lean_ctor_set(v___x_2310_, 3, v_t_2022_);
lean_ctor_set(v___x_2310_, 4, v_t_2022_);
return v___x_2310_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(lean_object* v_k_2311_, lean_object* v_t_2312_){
_start:
{
if (lean_obj_tag(v_t_2312_) == 0)
{
lean_object* v_k_2313_; lean_object* v_l_2314_; lean_object* v_r_2315_; uint8_t v___x_2316_; 
v_k_2313_ = lean_ctor_get(v_t_2312_, 1);
v_l_2314_ = lean_ctor_get(v_t_2312_, 3);
v_r_2315_ = lean_ctor_get(v_t_2312_, 4);
v___x_2316_ = lean_nat_dec_lt(v_k_2311_, v_k_2313_);
if (v___x_2316_ == 0)
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_nat_dec_eq(v_k_2311_, v_k_2313_);
if (v___x_2317_ == 0)
{
v_t_2312_ = v_r_2315_;
goto _start;
}
else
{
return v___x_2317_;
}
}
else
{
v_t_2312_ = v_l_2314_;
goto _start;
}
}
else
{
uint8_t v___x_2320_; 
v___x_2320_ = 0;
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(lean_object* v_k_2321_, lean_object* v_t_2322_){
_start:
{
uint8_t v_res_2323_; lean_object* v_r_2324_; 
v_res_2323_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2321_, v_t_2322_);
lean_dec(v_t_2322_);
lean_dec(v_k_2321_);
v_r_2324_ = lean_box(v_res_2323_);
return v_r_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* v_idx_2325_){
_start:
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_box(1);
v___x_2327_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_idx_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_box(0);
v___x_2329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_idx_2325_, v___x_2328_, v___x_2326_);
return v___x_2329_;
}
else
{
lean_dec(v_idx_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(lean_object* v_00_u03b2_2330_, lean_object* v_k_2331_, lean_object* v_t_2332_){
_start:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_k_2331_, v_t_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_k_2335_, lean_object* v_t_2336_){
_start:
{
uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_res_2337_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(v_00_u03b2_2334_, v_k_2335_, v_t_2336_);
lean_dec(v_t_2336_);
lean_dec(v_k_2335_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(lean_object* v_00_u03b2_2339_, lean_object* v_k_2340_, lean_object* v_v_2341_, lean_object* v_t_2342_, lean_object* v_hl_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_2340_, v_v_2341_, v_t_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl(lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_obj_tag_nat(v_x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorIdx___impl___boxed(lean_object* v_x_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_IR_LocalContextEntry_ctorIdx___impl(v_x_2347_);
lean_dec_ref(v_x_2347_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContextEntry_ctorElim___redArg(lean_object* v_t_2349_, lean_object* v_k_2350_){
_start:
{
if (lean_obj_tag(v_t_2349_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v_t_2349_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v_t_2349_, 1);
v___x_2352_ = lean_apply_1(v_k_2350_, v_a_2351_);
return v___x_2352_;
}
else
{
lean_object* v_a_2353_; lean_object* v_a_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v_t_2349_, 0);
lean_inc(v_a_2353_);
v_a_2354_ = lean_ctor_get(v_t_2349_, 1);
lean_inc_ref(v_a_2354_);
lean_dec_ref_known(v_t_2349_, 2);
v___x_2355_ = lean_apply_2(v_k_2350_, v_a_2353_, v_a_2354_);
return v___x_2355_;
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
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* v_ctx_2384_, lean_object* v_x_2385_, lean_object* v_t_2386_, lean_object* v_v_2387_){
_start:
{
lean_object* v_vars_2388_; lean_object* v_jps_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2398_; 
v_vars_2388_ = lean_ctor_get(v_ctx_2384_, 0);
v_jps_2389_ = lean_ctor_get(v_ctx_2384_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_ctx_2384_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2391_ = v_ctx_2384_;
v_isShared_2392_ = v_isSharedCheck_2398_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_jps_2389_);
lean_inc(v_vars_2388_);
lean_dec(v_ctx_2384_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2398_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_t_2386_);
lean_ctor_set(v___x_2393_, 1, v_v_2387_);
v___x_2394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2385_, v___x_2393_, v_vars_2388_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2394_);
v___x_2396_ = v___x_2391_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_jps_2389_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* v_ctx_2399_, lean_object* v_j_2400_, lean_object* v_xs_2401_, lean_object* v_b_2402_){
_start:
{
lean_object* v_vars_2403_; lean_object* v_jps_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2413_; 
v_vars_2403_ = lean_ctor_get(v_ctx_2399_, 0);
v_jps_2404_ = lean_ctor_get(v_ctx_2399_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_ctx_2399_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2406_ = v_ctx_2399_;
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_jps_2404_);
lean_inc(v_vars_2403_);
lean_dec(v_ctx_2399_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_xs_2401_);
lean_ctor_set(v___x_2408_, 1, v_b_2402_);
v___x_2409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_j_2400_, v___x_2408_, v_jps_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 1, v___x_2409_);
v___x_2411_ = v___x_2406_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_vars_2403_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* v_ctx_2414_, lean_object* v_p_2415_){
_start:
{
lean_object* v_vars_2416_; lean_object* v_jps_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2428_; 
v_vars_2416_ = lean_ctor_get(v_ctx_2414_, 0);
v_jps_2417_ = lean_ctor_get(v_ctx_2414_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_ctx_2414_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2419_ = v_ctx_2414_;
v_isShared_2420_ = v_isSharedCheck_2428_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_jps_2417_);
lean_inc(v_vars_2416_);
lean_dec(v_ctx_2414_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2428_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_x_2421_; lean_object* v_ty_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v_x_2421_ = lean_ctor_get(v_p_2415_, 0);
lean_inc(v_x_2421_);
v_ty_2422_ = lean_ctor_get(v_p_2415_, 1);
lean_inc(v_ty_2422_);
lean_dec_ref(v_p_2415_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_ty_2422_);
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_2421_, v___x_2423_, v_vars_2416_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2424_);
v___x_2426_ = v___x_2419_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_jps_2417_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(lean_object* v_as_2429_, size_t v_i_2430_, size_t v_stop_2431_, lean_object* v_b_2432_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_usize_dec_eq(v_i_2430_, v_stop_2431_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; 
v___x_2434_ = lean_array_uget_borrowed(v_as_2429_, v_i_2430_);
lean_inc(v___x_2434_);
v___x_2435_ = l_Lean_IR_LocalContext_addParam(v_b_2432_, v___x_2434_);
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_add(v_i_2430_, v___x_2436_);
v_i_2430_ = v___x_2437_;
v_b_2432_ = v___x_2435_;
goto _start;
}
else
{
return v_b_2432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* v_as_2439_, lean_object* v_i_2440_, lean_object* v_stop_2441_, lean_object* v_b_2442_){
_start:
{
size_t v_i_boxed_2443_; size_t v_stop_boxed_2444_; lean_object* v_res_2445_; 
v_i_boxed_2443_ = lean_unbox_usize(v_i_2440_);
lean_dec(v_i_2440_);
v_stop_boxed_2444_ = lean_unbox_usize(v_stop_2441_);
lean_dec(v_stop_2441_);
v_res_2445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_2439_, v_i_boxed_2443_, v_stop_boxed_2444_, v_b_2442_);
lean_dec_ref(v_as_2439_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* v_ctx_2446_, lean_object* v_ps_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
v___x_2449_ = lean_array_get_size(v_ps_2447_);
v___x_2450_ = lean_nat_dec_lt(v___x_2448_, v___x_2449_);
if (v___x_2450_ == 0)
{
return v_ctx_2446_;
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = lean_usize_of_nat(v___x_2449_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2447_, v___x_2451_, v___x_2452_, v_ctx_2446_);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_2454_, lean_object* v_ps_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_IR_LocalContext_addParams(v_ctx_2454_, v_ps_2455_);
lean_dec_ref(v_ps_2455_);
return v_res_2456_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_2457_, lean_object* v_j_2458_){
_start:
{
lean_object* v_jps_2459_; uint8_t v___x_2460_; 
v_jps_2459_ = lean_ctor_get(v_ctx_2457_, 1);
v___x_2460_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_j_2458_, v_jps_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_2461_, lean_object* v_j_2462_){
_start:
{
uint8_t v_res_2463_; lean_object* v_r_2464_; 
v_res_2463_ = l_Lean_IR_LocalContext_isJP(v_ctx_2461_, v_j_2462_);
lean_dec(v_j_2462_);
lean_dec_ref(v_ctx_2461_);
v_r_2464_ = lean_box(v_res_2463_);
return v_r_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(lean_object* v_t_2465_, lean_object* v_k_2466_){
_start:
{
if (lean_obj_tag(v_t_2465_) == 0)
{
lean_object* v_k_2467_; lean_object* v_v_2468_; lean_object* v_l_2469_; lean_object* v_r_2470_; uint8_t v___x_2471_; 
v_k_2467_ = lean_ctor_get(v_t_2465_, 1);
v_v_2468_ = lean_ctor_get(v_t_2465_, 2);
v_l_2469_ = lean_ctor_get(v_t_2465_, 3);
v_r_2470_ = lean_ctor_get(v_t_2465_, 4);
v___x_2471_ = lean_nat_dec_lt(v_k_2466_, v_k_2467_);
if (v___x_2471_ == 0)
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_nat_dec_eq(v_k_2466_, v_k_2467_);
if (v___x_2472_ == 0)
{
v_t_2465_ = v_r_2470_;
goto _start;
}
else
{
lean_object* v___x_2474_; 
lean_inc(v_v_2468_);
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_v_2468_);
return v___x_2474_;
}
}
else
{
v_t_2465_ = v_l_2469_;
goto _start;
}
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg___boxed(lean_object* v_t_2477_, lean_object* v_k_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_2477_, v_k_2478_);
lean_dec(v_k_2478_);
lean_dec(v_t_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_2480_, lean_object* v_j_2481_){
_start:
{
lean_object* v_jps_2482_; lean_object* v___x_2483_; 
v_jps_2482_ = lean_ctor_get(v_ctx_2480_, 1);
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_2482_, v_j_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
else
{
lean_object* v_val_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2493_; 
v_val_2485_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2487_ = v___x_2483_;
v_isShared_2488_ = v_isSharedCheck_2493_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_val_2485_);
lean_dec(v___x_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2493_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_snd_2489_; lean_object* v___x_2491_; 
v_snd_2489_ = lean_ctor_get(v_val_2485_, 1);
lean_inc(v_snd_2489_);
lean_dec(v_val_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v_snd_2489_);
v___x_2491_ = v___x_2487_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_snd_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_2494_, lean_object* v_j_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_2494_, v_j_2495_);
lean_dec(v_j_2495_);
lean_dec_ref(v_ctx_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(lean_object* v_00_u03b4_2497_, lean_object* v_t_2498_, lean_object* v_k_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_2498_, v_k_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___boxed(lean_object* v_00_u03b4_2501_, lean_object* v_t_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(v_00_u03b4_2501_, v_t_2502_, v_k_2503_);
lean_dec(v_k_2503_);
lean_dec(v_t_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_2505_, lean_object* v_j_2506_){
_start:
{
lean_object* v_jps_2507_; lean_object* v___x_2508_; 
v_jps_2507_ = lean_ctor_get(v_ctx_2505_, 1);
v___x_2508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_2507_, v_j_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
else
{
lean_object* v_val_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2518_; 
v_val_2510_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2512_ = v___x_2508_;
v_isShared_2513_ = v_isSharedCheck_2518_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_val_2510_);
lean_dec(v___x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2518_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_fst_2514_; lean_object* v___x_2516_; 
v_fst_2514_ = lean_ctor_get(v_val_2510_, 0);
lean_inc(v_fst_2514_);
lean_dec(v_val_2510_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v_fst_2514_);
v___x_2516_ = v___x_2512_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_fst_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_2519_, lean_object* v_j_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_2519_, v_j_2520_);
lean_dec(v_j_2520_);
lean_dec_ref(v_ctx_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_2522_, lean_object* v_x_2523_){
_start:
{
lean_object* v_vars_2524_; lean_object* v___x_2525_; 
v_vars_2524_ = lean_ctor_get(v_ctx_2522_, 0);
v___x_2525_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_2524_, v_x_2523_);
if (lean_obj_tag(v___x_2525_) == 1)
{
lean_object* v_val_2526_; 
v_val_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_val_2526_);
lean_dec_ref_known(v___x_2525_, 1);
if (lean_obj_tag(v_val_2526_) == 0)
{
uint8_t v___x_2527_; 
lean_dec_ref_known(v_val_2526_, 1);
v___x_2527_ = 1;
return v___x_2527_;
}
else
{
uint8_t v___x_2528_; 
lean_dec(v_val_2526_);
v___x_2528_ = 0;
return v___x_2528_;
}
}
else
{
uint8_t v___x_2529_; 
lean_dec(v___x_2525_);
v___x_2529_ = 0;
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_2530_, lean_object* v_x_2531_){
_start:
{
uint8_t v_res_2532_; lean_object* v_r_2533_; 
v_res_2532_ = l_Lean_IR_LocalContext_isParam(v_ctx_2530_, v_x_2531_);
lean_dec(v_x_2531_);
lean_dec_ref(v_ctx_2530_);
v_r_2533_ = lean_box(v_res_2532_);
return v_r_2533_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v_vars_2536_; lean_object* v___x_2537_; 
v_vars_2536_ = lean_ctor_get(v_ctx_2534_, 0);
v___x_2537_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_2536_, v_x_2535_);
if (lean_obj_tag(v___x_2537_) == 1)
{
lean_object* v_val_2538_; 
v_val_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v___x_2537_, 1);
if (lean_obj_tag(v_val_2538_) == 1)
{
uint8_t v___x_2539_; 
lean_dec_ref_known(v_val_2538_, 2);
v___x_2539_ = 1;
return v___x_2539_;
}
else
{
uint8_t v___x_2540_; 
lean_dec(v_val_2538_);
v___x_2540_ = 0;
return v___x_2540_;
}
}
else
{
uint8_t v___x_2541_; 
lean_dec(v___x_2537_);
v___x_2541_ = 0;
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_2542_, lean_object* v_x_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_2542_, v_x_2543_);
lean_dec(v_x_2543_);
lean_dec_ref(v_ctx_2542_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_2546_, lean_object* v_t_2547_){
_start:
{
if (lean_obj_tag(v_t_2547_) == 0)
{
lean_object* v_k_2548_; lean_object* v_v_2549_; lean_object* v_l_2550_; lean_object* v_r_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_3206_; 
v_k_2548_ = lean_ctor_get(v_t_2547_, 1);
v_v_2549_ = lean_ctor_get(v_t_2547_, 2);
v_l_2550_ = lean_ctor_get(v_t_2547_, 3);
v_r_2551_ = lean_ctor_get(v_t_2547_, 4);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_t_2547_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v_t_2547_, 0);
lean_dec(v_unused_3207_);
v___x_2553_ = v_t_2547_;
v_isShared_2554_ = v_isSharedCheck_3206_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_r_2551_);
lean_inc(v_l_2550_);
lean_inc(v_v_2549_);
lean_inc(v_k_2548_);
lean_dec(v_t_2547_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_3206_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_nat_dec_lt(v_k_2546_, v_k_2548_);
if (v___x_2555_ == 0)
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_nat_dec_eq(v_k_2546_, v_k_2548_);
if (v___x_2556_ == 0)
{
lean_object* v_impl_2557_; lean_object* v___x_2558_; 
v_impl_2557_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2546_, v_r_2551_);
v___x_2558_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2557_) == 0)
{
if (lean_obj_tag(v_l_2550_) == 0)
{
lean_object* v_size_2559_; lean_object* v_size_2560_; lean_object* v_k_2561_; lean_object* v_v_2562_; lean_object* v_l_2563_; lean_object* v_r_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_size_2559_ = lean_ctor_get(v_impl_2557_, 0);
v_size_2560_ = lean_ctor_get(v_l_2550_, 0);
v_k_2561_ = lean_ctor_get(v_l_2550_, 1);
v_v_2562_ = lean_ctor_get(v_l_2550_, 2);
v_l_2563_ = lean_ctor_get(v_l_2550_, 3);
v_r_2564_ = lean_ctor_get(v_l_2550_, 4);
lean_inc(v_r_2564_);
v___x_2565_ = lean_unsigned_to_nat(3u);
v___x_2566_ = lean_nat_mul(v___x_2565_, v_size_2559_);
v___x_2567_ = lean_nat_dec_lt(v___x_2566_, v_size_2560_);
lean_dec(v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_dec(v_r_2564_);
v___x_2568_ = lean_nat_add(v___x_2558_, v_size_2560_);
v___x_2569_ = lean_nat_add(v___x_2568_, v_size_2559_);
lean_dec(v___x_2568_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_impl_2557_);
lean_ctor_set(v___x_2553_, 0, v___x_2569_);
v___x_2571_ = v___x_2553_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_l_2550_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_impl_2557_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
else
{
lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2638_; 
lean_inc(v_l_2563_);
lean_inc(v_v_2562_);
lean_inc(v_k_2561_);
lean_inc(v_size_2560_);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; lean_object* v_unused_2643_; 
v_unused_2639_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_l_2550_, 2);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_l_2550_, 1);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_2643_);
v___x_2574_ = v_l_2550_;
v_isShared_2575_ = v_isSharedCheck_2638_;
goto v_resetjp_2573_;
}
else
{
lean_dec(v_l_2550_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2638_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_size_2576_; lean_object* v_size_2577_; lean_object* v_k_2578_; lean_object* v_v_2579_; lean_object* v_l_2580_; lean_object* v_r_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_size_2576_ = lean_ctor_get(v_l_2563_, 0);
v_size_2577_ = lean_ctor_get(v_r_2564_, 0);
v_k_2578_ = lean_ctor_get(v_r_2564_, 1);
v_v_2579_ = lean_ctor_get(v_r_2564_, 2);
v_l_2580_ = lean_ctor_get(v_r_2564_, 3);
v_r_2581_ = lean_ctor_get(v_r_2564_, 4);
v___x_2582_ = lean_unsigned_to_nat(2u);
v___x_2583_ = lean_nat_mul(v___x_2582_, v_size_2576_);
v___x_2584_ = lean_nat_dec_lt(v_size_2577_, v___x_2583_);
lean_dec(v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2613_; 
lean_inc(v_r_2581_);
lean_inc(v_l_2580_);
lean_inc(v_v_2579_);
lean_inc(v_k_2578_);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_r_2564_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; lean_object* v_unused_2615_; lean_object* v_unused_2616_; lean_object* v_unused_2617_; lean_object* v_unused_2618_; 
v_unused_2614_ = lean_ctor_get(v_r_2564_, 4);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v_r_2564_, 3);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v_r_2564_, 2);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_r_2564_, 1);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_r_2564_, 0);
lean_dec(v_unused_2618_);
v___x_2586_ = v_r_2564_;
v_isShared_2587_ = v_isSharedCheck_2613_;
goto v_resetjp_2585_;
}
else
{
lean_dec(v_r_2564_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2613_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___x_2601_; lean_object* v___y_2603_; 
v___x_2588_ = lean_nat_add(v___x_2558_, v_size_2560_);
lean_dec(v_size_2560_);
v___x_2589_ = lean_nat_add(v___x_2588_, v_size_2559_);
lean_dec(v___x_2588_);
v___x_2601_ = lean_nat_add(v___x_2558_, v_size_2576_);
if (lean_obj_tag(v_l_2580_) == 0)
{
lean_object* v_size_2611_; 
v_size_2611_ = lean_ctor_get(v_l_2580_, 0);
lean_inc(v_size_2611_);
v___y_2603_ = v_size_2611_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_unsigned_to_nat(0u);
v___y_2603_ = v___x_2612_;
goto v___jp_2602_;
}
v___jp_2590_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_nat_add(v___y_2591_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec(v___y_2591_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 4, v_impl_2557_);
lean_ctor_set(v___x_2586_, 3, v_r_2581_);
lean_ctor_set(v___x_2586_, 2, v_v_2549_);
lean_ctor_set(v___x_2586_, 1, v_k_2548_);
lean_ctor_set(v___x_2586_, 0, v___x_2594_);
v___x_2596_ = v___x_2586_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_r_2581_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_impl_2557_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 4, v___x_2596_);
lean_ctor_set(v___x_2574_, 3, v___y_2592_);
lean_ctor_set(v___x_2574_, 2, v_v_2579_);
lean_ctor_set(v___x_2574_, 1, v_k_2578_);
lean_ctor_set(v___x_2574_, 0, v___x_2589_);
v___x_2598_ = v___x_2574_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v___y_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
v___jp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = lean_nat_add(v___x_2601_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec(v___x_2601_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_l_2580_);
lean_ctor_set(v___x_2553_, 3, v_l_2563_);
lean_ctor_set(v___x_2553_, 2, v_v_2562_);
lean_ctor_set(v___x_2553_, 1, v_k_2561_);
lean_ctor_set(v___x_2553_, 0, v___x_2604_);
v___x_2606_ = v___x_2553_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_k_2561_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_v_2562_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_l_2563_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_l_2580_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_nat_add(v___x_2558_, v_size_2559_);
if (lean_obj_tag(v_r_2581_) == 0)
{
lean_object* v_size_2608_; 
v_size_2608_ = lean_ctor_get(v_r_2581_, 0);
lean_inc(v_size_2608_);
v___y_2591_ = v___x_2607_;
v___y_2592_ = v___x_2606_;
v___y_2593_ = v_size_2608_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___y_2591_ = v___x_2607_;
v___y_2592_ = v___x_2606_;
v___y_2593_ = v___x_2609_;
goto v___jp_2590_;
}
}
}
}
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_del_object(v___x_2553_);
v___x_2619_ = lean_nat_add(v___x_2558_, v_size_2560_);
lean_dec(v_size_2560_);
v___x_2620_ = lean_nat_add(v___x_2619_, v_size_2559_);
lean_dec(v___x_2619_);
v___x_2621_ = lean_nat_add(v___x_2558_, v_size_2559_);
v___x_2622_ = lean_nat_add(v___x_2621_, v_size_2577_);
lean_dec(v___x_2621_);
lean_inc_ref(v_impl_2557_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 4, v_impl_2557_);
lean_ctor_set(v___x_2574_, 3, v_r_2564_);
lean_ctor_set(v___x_2574_, 2, v_v_2549_);
lean_ctor_set(v___x_2574_, 1, v_k_2548_);
lean_ctor_set(v___x_2574_, 0, v___x_2622_);
v___x_2624_ = v___x_2574_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_r_2564_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_impl_2557_);
v___x_2624_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
v_isSharedCheck_2631_ = !lean_is_exclusive(v_impl_2557_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; 
v_unused_2632_ = lean_ctor_get(v_impl_2557_, 4);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_impl_2557_, 3);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_impl_2557_, 2);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_impl_2557_, 1);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_impl_2557_, 0);
lean_dec(v_unused_2636_);
v___x_2626_ = v_impl_2557_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_dec(v_impl_2557_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 4, v___x_2624_);
lean_ctor_set(v___x_2626_, 3, v_l_2563_);
lean_ctor_set(v___x_2626_, 2, v_v_2562_);
lean_ctor_set(v___x_2626_, 1, v_k_2561_);
lean_ctor_set(v___x_2626_, 0, v___x_2620_);
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_k_2561_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_v_2562_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_l_2563_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v___x_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v_size_2644_ = lean_ctor_get(v_impl_2557_, 0);
v___x_2645_ = lean_nat_add(v___x_2558_, v_size_2644_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_impl_2557_);
lean_ctor_set(v___x_2553_, 0, v___x_2645_);
v___x_2647_ = v___x_2553_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_l_2550_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_impl_2557_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
else
{
if (lean_obj_tag(v_l_2550_) == 0)
{
lean_object* v_l_2649_; 
v_l_2649_ = lean_ctor_get(v_l_2550_, 3);
if (lean_obj_tag(v_l_2649_) == 0)
{
lean_object* v_r_2650_; 
lean_inc_ref(v_l_2649_);
v_r_2650_ = lean_ctor_get(v_l_2550_, 4);
lean_inc(v_r_2650_);
if (lean_obj_tag(v_r_2650_) == 0)
{
lean_object* v_size_2651_; lean_object* v_k_2652_; lean_object* v_v_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2666_; 
v_size_2651_ = lean_ctor_get(v_l_2550_, 0);
v_k_2652_ = lean_ctor_get(v_l_2550_, 1);
v_v_2653_ = lean_ctor_get(v_l_2550_, 2);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; lean_object* v_unused_2668_; 
v_unused_2667_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2667_);
v_unused_2668_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2668_);
v___x_2655_ = v_l_2550_;
v_isShared_2656_ = v_isSharedCheck_2666_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_v_2653_);
lean_inc(v_k_2652_);
lean_inc(v_size_2651_);
lean_dec(v_l_2550_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2666_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_size_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v_size_2657_ = lean_ctor_get(v_r_2650_, 0);
v___x_2658_ = lean_nat_add(v___x_2558_, v_size_2651_);
lean_dec(v_size_2651_);
v___x_2659_ = lean_nat_add(v___x_2558_, v_size_2657_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v_impl_2557_);
lean_ctor_set(v___x_2655_, 3, v_r_2650_);
lean_ctor_set(v___x_2655_, 2, v_v_2549_);
lean_ctor_set(v___x_2655_, 1, v_k_2548_);
lean_ctor_set(v___x_2655_, 0, v___x_2659_);
v___x_2661_ = v___x_2655_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v_r_2650_);
lean_ctor_set(v_reuseFailAlloc_2665_, 4, v_impl_2557_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___x_2661_);
lean_ctor_set(v___x_2553_, 3, v_l_2649_);
lean_ctor_set(v___x_2553_, 2, v_v_2653_);
lean_ctor_set(v___x_2553_, 1, v_k_2652_);
lean_ctor_set(v___x_2553_, 0, v___x_2658_);
v___x_2663_ = v___x_2553_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_k_2652_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_v_2653_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_l_2649_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v_k_2669_; lean_object* v_v_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2681_; 
v_k_2669_ = lean_ctor_get(v_l_2550_, 1);
v_v_2670_ = lean_ctor_get(v_l_2550_, 2);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; lean_object* v_unused_2683_; lean_object* v_unused_2684_; 
v_unused_2682_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2683_);
v_unused_2684_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_2684_);
v___x_2672_ = v_l_2550_;
v_isShared_2673_ = v_isSharedCheck_2681_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_v_2670_);
lean_inc(v_k_2669_);
lean_dec(v_l_2550_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2681_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = lean_unsigned_to_nat(3u);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 3, v_r_2650_);
lean_ctor_set(v___x_2672_, 2, v_v_2549_);
lean_ctor_set(v___x_2672_, 1, v_k_2548_);
lean_ctor_set(v___x_2672_, 0, v___x_2558_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_r_2650_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_r_2650_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___x_2676_);
lean_ctor_set(v___x_2553_, 3, v_l_2649_);
lean_ctor_set(v___x_2553_, 2, v_v_2670_);
lean_ctor_set(v___x_2553_, 1, v_k_2669_);
lean_ctor_set(v___x_2553_, 0, v___x_2674_);
v___x_2678_ = v___x_2553_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_k_2669_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_v_2670_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_l_2649_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
else
{
lean_object* v_r_2685_; 
v_r_2685_ = lean_ctor_get(v_l_2550_, 4);
lean_inc(v_r_2685_);
if (lean_obj_tag(v_r_2685_) == 0)
{
lean_object* v_k_2686_; lean_object* v_v_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2710_; 
lean_inc(v_l_2649_);
v_k_2686_ = lean_ctor_get(v_l_2550_, 1);
v_v_2687_ = lean_ctor_get(v_l_2550_, 2);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2711_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_2713_);
v___x_2689_ = v_l_2550_;
v_isShared_2690_ = v_isSharedCheck_2710_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_v_2687_);
lean_inc(v_k_2686_);
lean_dec(v_l_2550_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2710_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_k_2691_; lean_object* v_v_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2706_; 
v_k_2691_ = lean_ctor_get(v_r_2685_, 1);
v_v_2692_ = lean_ctor_get(v_r_2685_, 2);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_r_2685_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; lean_object* v_unused_2708_; lean_object* v_unused_2709_; 
v_unused_2707_ = lean_ctor_get(v_r_2685_, 4);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_r_2685_, 3);
lean_dec(v_unused_2708_);
v_unused_2709_ = lean_ctor_get(v_r_2685_, 0);
lean_dec(v_unused_2709_);
v___x_2694_ = v_r_2685_;
v_isShared_2695_ = v_isSharedCheck_2706_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_v_2692_);
lean_inc(v_k_2691_);
lean_dec(v_r_2685_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2706_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_unsigned_to_nat(3u);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 4, v_l_2649_);
lean_ctor_set(v___x_2694_, 3, v_l_2649_);
lean_ctor_set(v___x_2694_, 2, v_v_2687_);
lean_ctor_set(v___x_2694_, 1, v_k_2686_);
lean_ctor_set(v___x_2694_, 0, v___x_2558_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_k_2686_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_v_2687_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_l_2649_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_l_2649_);
v___x_2698_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 4, v_l_2649_);
lean_ctor_set(v___x_2689_, 2, v_v_2549_);
lean_ctor_set(v___x_2689_, 1, v_k_2548_);
lean_ctor_set(v___x_2689_, 0, v___x_2558_);
v___x_2700_ = v___x_2689_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_l_2649_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v_l_2649_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___x_2700_);
lean_ctor_set(v___x_2553_, 3, v___x_2698_);
lean_ctor_set(v___x_2553_, 2, v_v_2692_);
lean_ctor_set(v___x_2553_, 1, v_k_2691_);
lean_ctor_set(v___x_2553_, 0, v___x_2696_);
v___x_2702_ = v___x_2553_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_k_2691_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_v_2692_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v___x_2698_);
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
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2714_ = lean_unsigned_to_nat(2u);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_r_2685_);
lean_ctor_set(v___x_2553_, 0, v___x_2714_);
v___x_2716_ = v___x_2553_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_l_2550_);
lean_ctor_set(v_reuseFailAlloc_2717_, 4, v_r_2685_);
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
else
{
lean_object* v___x_2719_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_l_2550_);
lean_ctor_set(v___x_2553_, 0, v___x_2558_);
v___x_2719_ = v___x_2553_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2720_, 3, v_l_2550_);
lean_ctor_set(v_reuseFailAlloc_2720_, 4, v_l_2550_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_del_object(v___x_2553_);
lean_dec(v_v_2549_);
lean_dec(v_k_2548_);
if (lean_obj_tag(v_l_2550_) == 0)
{
if (lean_obj_tag(v_r_2551_) == 0)
{
lean_object* v_size_2721_; lean_object* v_k_2722_; lean_object* v_v_2723_; lean_object* v_l_2724_; lean_object* v_r_2725_; lean_object* v_size_2726_; lean_object* v_k_2727_; lean_object* v_v_2728_; lean_object* v_l_2729_; lean_object* v_r_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_size_2721_ = lean_ctor_get(v_l_2550_, 0);
v_k_2722_ = lean_ctor_get(v_l_2550_, 1);
v_v_2723_ = lean_ctor_get(v_l_2550_, 2);
v_l_2724_ = lean_ctor_get(v_l_2550_, 3);
v_r_2725_ = lean_ctor_get(v_l_2550_, 4);
lean_inc(v_r_2725_);
v_size_2726_ = lean_ctor_get(v_r_2551_, 0);
v_k_2727_ = lean_ctor_get(v_r_2551_, 1);
v_v_2728_ = lean_ctor_get(v_r_2551_, 2);
v_l_2729_ = lean_ctor_get(v_r_2551_, 3);
lean_inc(v_l_2729_);
v_r_2730_ = lean_ctor_get(v_r_2551_, 4);
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = lean_nat_dec_lt(v_size_2721_, v_size_2726_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2868_; 
lean_inc(v_l_2724_);
lean_inc(v_v_2723_);
lean_inc(v_k_2722_);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; lean_object* v_unused_2870_; lean_object* v_unused_2871_; lean_object* v_unused_2872_; lean_object* v_unused_2873_; 
v_unused_2869_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2869_);
v_unused_2870_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_l_2550_, 2);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_l_2550_, 1);
lean_dec(v_unused_2872_);
v_unused_2873_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_2873_);
v___x_2734_ = v_l_2550_;
v_isShared_2735_ = v_isSharedCheck_2868_;
goto v_resetjp_2733_;
}
else
{
lean_dec(v_l_2550_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2868_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v_tree_2737_; 
v___x_2736_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2722_, v_v_2723_, v_l_2724_, v_r_2725_);
v_tree_2737_ = lean_ctor_get(v___x_2736_, 2);
if (lean_obj_tag(v_tree_2737_) == 0)
{
lean_object* v_k_2738_; lean_object* v_v_2739_; lean_object* v_size_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
lean_inc_ref(v_tree_2737_);
v_k_2738_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_k_2738_);
v_v_2739_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_v_2739_);
lean_dec_ref(v___x_2736_);
v_size_2740_ = lean_ctor_get(v_tree_2737_, 0);
v___x_2741_ = lean_unsigned_to_nat(3u);
v___x_2742_ = lean_nat_mul(v___x_2741_, v_size_2740_);
v___x_2743_ = lean_nat_dec_lt(v___x_2742_, v_size_2726_);
lean_dec(v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_dec(v_l_2729_);
v___x_2744_ = lean_nat_add(v___x_2731_, v_size_2740_);
v___x_2745_ = lean_nat_add(v___x_2744_, v_size_2726_);
lean_dec(v___x_2744_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_2551_);
lean_ctor_set(v___x_2734_, 3, v_tree_2737_);
lean_ctor_set(v___x_2734_, 2, v_v_2739_);
lean_ctor_set(v___x_2734_, 1, v_k_2738_);
lean_ctor_set(v___x_2734_, 0, v___x_2745_);
v___x_2747_ = v___x_2734_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_tree_2737_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_r_2551_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2803_; 
lean_inc(v_r_2730_);
lean_inc(v_v_2728_);
lean_inc(v_k_2727_);
lean_inc(v_size_2726_);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2804_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_r_2551_, 2);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_r_2551_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_r_2551_, 0);
lean_dec(v_unused_2808_);
v___x_2750_ = v_r_2551_;
v_isShared_2751_ = v_isSharedCheck_2803_;
goto v_resetjp_2749_;
}
else
{
lean_dec(v_r_2551_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2803_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_size_2752_; lean_object* v_k_2753_; lean_object* v_v_2754_; lean_object* v_l_2755_; lean_object* v_r_2756_; lean_object* v_size_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_size_2752_ = lean_ctor_get(v_l_2729_, 0);
v_k_2753_ = lean_ctor_get(v_l_2729_, 1);
v_v_2754_ = lean_ctor_get(v_l_2729_, 2);
v_l_2755_ = lean_ctor_get(v_l_2729_, 3);
v_r_2756_ = lean_ctor_get(v_l_2729_, 4);
v_size_2757_ = lean_ctor_get(v_r_2730_, 0);
v___x_2758_ = lean_unsigned_to_nat(2u);
v___x_2759_ = lean_nat_mul(v___x_2758_, v_size_2757_);
v___x_2760_ = lean_nat_dec_lt(v_size_2752_, v___x_2759_);
lean_dec(v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2788_; 
lean_inc(v_r_2756_);
lean_inc(v_l_2755_);
lean_inc(v_v_2754_);
lean_inc(v_k_2753_);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_l_2729_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; lean_object* v_unused_2793_; 
v_unused_2789_ = lean_ctor_get(v_l_2729_, 4);
lean_dec(v_unused_2789_);
v_unused_2790_ = lean_ctor_get(v_l_2729_, 3);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_l_2729_, 2);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_l_2729_, 1);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_l_2729_, 0);
lean_dec(v_unused_2793_);
v___x_2762_ = v_l_2729_;
v_isShared_2763_ = v_isSharedCheck_2788_;
goto v_resetjp_2761_;
}
else
{
lean_dec(v_l_2729_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2788_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2778_; 
v___x_2764_ = lean_nat_add(v___x_2731_, v_size_2740_);
v___x_2765_ = lean_nat_add(v___x_2764_, v_size_2726_);
lean_dec(v_size_2726_);
if (lean_obj_tag(v_l_2755_) == 0)
{
lean_object* v_size_2786_; 
v_size_2786_ = lean_ctor_get(v_l_2755_, 0);
lean_inc(v_size_2786_);
v___y_2778_ = v_size_2786_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_unsigned_to_nat(0u);
v___y_2778_ = v___x_2787_;
goto v___jp_2777_;
}
v___jp_2766_:
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2770_ = lean_nat_add(v___y_2767_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec(v___y_2767_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 4, v_r_2730_);
lean_ctor_set(v___x_2762_, 3, v_r_2756_);
lean_ctor_set(v___x_2762_, 2, v_v_2728_);
lean_ctor_set(v___x_2762_, 1, v_k_2727_);
lean_ctor_set(v___x_2762_, 0, v___x_2770_);
v___x_2772_ = v___x_2762_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_r_2756_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_r_2730_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 4, v___x_2772_);
lean_ctor_set(v___x_2750_, 3, v___y_2768_);
lean_ctor_set(v___x_2750_, 2, v_v_2754_);
lean_ctor_set(v___x_2750_, 1, v_k_2753_);
lean_ctor_set(v___x_2750_, 0, v___x_2765_);
v___x_2774_ = v___x_2750_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_k_2753_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_v_2754_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v___y_2768_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
v___jp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_nat_add(v___x_2764_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec(v___x_2764_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_l_2755_);
lean_ctor_set(v___x_2734_, 3, v_tree_2737_);
lean_ctor_set(v___x_2734_, 2, v_v_2739_);
lean_ctor_set(v___x_2734_, 1, v_k_2738_);
lean_ctor_set(v___x_2734_, 0, v___x_2779_);
v___x_2781_ = v___x_2734_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_tree_2737_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_l_2755_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_nat_add(v___x_2731_, v_size_2757_);
if (lean_obj_tag(v_r_2756_) == 0)
{
lean_object* v_size_2783_; 
v_size_2783_ = lean_ctor_get(v_r_2756_, 0);
lean_inc(v_size_2783_);
v___y_2767_ = v___x_2782_;
v___y_2768_ = v___x_2781_;
v___y_2769_ = v_size_2783_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_unsigned_to_nat(0u);
v___y_2767_ = v___x_2782_;
v___y_2768_ = v___x_2781_;
v___y_2769_ = v___x_2784_;
goto v___jp_2766_;
}
}
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2794_ = lean_nat_add(v___x_2731_, v_size_2740_);
v___x_2795_ = lean_nat_add(v___x_2794_, v_size_2726_);
lean_dec(v_size_2726_);
v___x_2796_ = lean_nat_add(v___x_2794_, v_size_2752_);
lean_dec(v___x_2794_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 4, v_l_2729_);
lean_ctor_set(v___x_2750_, 3, v_tree_2737_);
lean_ctor_set(v___x_2750_, 2, v_v_2739_);
lean_ctor_set(v___x_2750_, 1, v_k_2738_);
lean_ctor_set(v___x_2750_, 0, v___x_2796_);
v___x_2798_ = v___x_2750_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_k_2738_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v_v_2739_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_tree_2737_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v_l_2729_);
v___x_2798_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_2730_);
lean_ctor_set(v___x_2734_, 3, v___x_2798_);
lean_ctor_set(v___x_2734_, 2, v_v_2728_);
lean_ctor_set(v___x_2734_, 1, v_k_2727_);
lean_ctor_set(v___x_2734_, 0, v___x_2795_);
v___x_2800_ = v___x_2734_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_r_2730_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
else
{
lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2862_; 
lean_inc(v_r_2730_);
lean_inc(v_v_2728_);
lean_inc(v_k_2727_);
lean_inc(v_size_2726_);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; lean_object* v_unused_2864_; lean_object* v_unused_2865_; lean_object* v_unused_2866_; lean_object* v_unused_2867_; 
v_unused_2863_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_r_2551_, 2);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v_r_2551_, 1);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v_r_2551_, 0);
lean_dec(v_unused_2867_);
v___x_2810_ = v_r_2551_;
v_isShared_2811_ = v_isSharedCheck_2862_;
goto v_resetjp_2809_;
}
else
{
lean_dec(v_r_2551_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2862_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
if (lean_obj_tag(v_l_2729_) == 0)
{
if (lean_obj_tag(v_r_2730_) == 0)
{
lean_object* v_k_2812_; lean_object* v_v_2813_; lean_object* v_size_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2818_; 
lean_inc(v_tree_2737_);
v_k_2812_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_k_2812_);
v_v_2813_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_v_2813_);
lean_dec_ref(v___x_2736_);
v_size_2814_ = lean_ctor_get(v_l_2729_, 0);
v___x_2815_ = lean_nat_add(v___x_2731_, v_size_2726_);
lean_dec(v_size_2726_);
v___x_2816_ = lean_nat_add(v___x_2731_, v_size_2814_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 4, v_l_2729_);
lean_ctor_set(v___x_2810_, 3, v_tree_2737_);
lean_ctor_set(v___x_2810_, 2, v_v_2813_);
lean_ctor_set(v___x_2810_, 1, v_k_2812_);
lean_ctor_set(v___x_2810_, 0, v___x_2816_);
v___x_2818_ = v___x_2810_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_k_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_v_2813_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_tree_2737_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_l_2729_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_2730_);
lean_ctor_set(v___x_2734_, 3, v___x_2818_);
lean_ctor_set(v___x_2734_, 2, v_v_2728_);
lean_ctor_set(v___x_2734_, 1, v_k_2727_);
lean_ctor_set(v___x_2734_, 0, v___x_2815_);
v___x_2820_ = v___x_2734_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v_r_2730_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
else
{
lean_object* v_k_2823_; lean_object* v_v_2824_; lean_object* v_k_2825_; lean_object* v_v_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_size_2726_);
v_k_2823_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_k_2823_);
v_v_2824_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_v_2824_);
lean_dec_ref(v___x_2736_);
v_k_2825_ = lean_ctor_get(v_l_2729_, 1);
v_v_2826_ = lean_ctor_get(v_l_2729_, 2);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_l_2729_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; lean_object* v_unused_2842_; lean_object* v_unused_2843_; 
v_unused_2841_ = lean_ctor_get(v_l_2729_, 4);
lean_dec(v_unused_2841_);
v_unused_2842_ = lean_ctor_get(v_l_2729_, 3);
lean_dec(v_unused_2842_);
v_unused_2843_ = lean_ctor_get(v_l_2729_, 0);
lean_dec(v_unused_2843_);
v___x_2828_ = v_l_2729_;
v_isShared_2829_ = v_isSharedCheck_2840_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_v_2826_);
lean_inc(v_k_2825_);
lean_dec(v_l_2729_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2840_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = lean_unsigned_to_nat(3u);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 4, v_r_2730_);
lean_ctor_set(v___x_2828_, 3, v_r_2730_);
lean_ctor_set(v___x_2828_, 2, v_v_2824_);
lean_ctor_set(v___x_2828_, 1, v_k_2823_);
lean_ctor_set(v___x_2828_, 0, v___x_2731_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_k_2823_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_v_2824_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_r_2730_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_r_2730_);
v___x_2832_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2834_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 3, v_r_2730_);
lean_ctor_set(v___x_2810_, 0, v___x_2731_);
v___x_2834_ = v___x_2810_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2838_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2838_, 3, v_r_2730_);
lean_ctor_set(v_reuseFailAlloc_2838_, 4, v_r_2730_);
v___x_2834_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2836_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_2834_);
lean_ctor_set(v___x_2734_, 3, v___x_2832_);
lean_ctor_set(v___x_2734_, 2, v_v_2826_);
lean_ctor_set(v___x_2734_, 1, v_k_2825_);
lean_ctor_set(v___x_2734_, 0, v___x_2830_);
v___x_2836_ = v___x_2734_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_k_2825_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_v_2826_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2730_) == 0)
{
lean_object* v_k_2844_; lean_object* v_v_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_dec(v_size_2726_);
v_k_2844_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_k_2844_);
v_v_2845_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_v_2845_);
lean_dec_ref(v___x_2736_);
v___x_2846_ = lean_unsigned_to_nat(3u);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 4, v_l_2729_);
lean_ctor_set(v___x_2810_, 2, v_v_2845_);
lean_ctor_set(v___x_2810_, 1, v_k_2844_);
lean_ctor_set(v___x_2810_, 0, v___x_2731_);
v___x_2848_ = v___x_2810_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_k_2844_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_v_2845_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_l_2729_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v_l_2729_);
v___x_2848_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2850_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_2730_);
lean_ctor_set(v___x_2734_, 3, v___x_2848_);
lean_ctor_set(v___x_2734_, 2, v_v_2728_);
lean_ctor_set(v___x_2734_, 1, v_k_2727_);
lean_ctor_set(v___x_2734_, 0, v___x_2846_);
v___x_2850_ = v___x_2734_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2846_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2851_, 3, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2851_, 4, v_r_2730_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
lean_object* v_k_2853_; lean_object* v_v_2854_; lean_object* v___x_2856_; 
v_k_2853_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_k_2853_);
v_v_2854_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_v_2854_);
lean_dec_ref(v___x_2736_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 3, v_r_2730_);
v___x_2856_ = v___x_2810_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_size_2726_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_r_2730_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_r_2730_);
v___x_2856_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_unsigned_to_nat(2u);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_2856_);
lean_ctor_set(v___x_2734_, 3, v_r_2730_);
lean_ctor_set(v___x_2734_, 2, v_v_2854_);
lean_ctor_set(v___x_2734_, 1, v_k_2853_);
lean_ctor_set(v___x_2734_, 0, v___x_2857_);
v___x_2859_ = v___x_2734_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_k_2853_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_v_2854_);
lean_ctor_set(v_reuseFailAlloc_2860_, 3, v_r_2730_);
lean_ctor_set(v_reuseFailAlloc_2860_, 4, v___x_2856_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
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
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_3026_; 
lean_inc(v_r_2730_);
lean_inc(v_v_2728_);
lean_inc(v_k_2727_);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; lean_object* v_unused_3028_; lean_object* v_unused_3029_; lean_object* v_unused_3030_; lean_object* v_unused_3031_; 
v_unused_3027_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_3027_);
v_unused_3028_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_3028_);
v_unused_3029_ = lean_ctor_get(v_r_2551_, 2);
lean_dec(v_unused_3029_);
v_unused_3030_ = lean_ctor_get(v_r_2551_, 1);
lean_dec(v_unused_3030_);
v_unused_3031_ = lean_ctor_get(v_r_2551_, 0);
lean_dec(v_unused_3031_);
v___x_2875_ = v_r_2551_;
v_isShared_2876_ = v_isSharedCheck_3026_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v_r_2551_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_3026_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v_tree_2878_; 
v___x_2877_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2727_, v_v_2728_, v_l_2729_, v_r_2730_);
v_tree_2878_ = lean_ctor_get(v___x_2877_, 2);
lean_inc(v_tree_2878_);
if (lean_obj_tag(v_tree_2878_) == 0)
{
lean_object* v_k_2879_; lean_object* v_v_2880_; lean_object* v_size_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v_k_2879_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_k_2879_);
v_v_2880_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_v_2880_);
lean_dec_ref(v___x_2877_);
v_size_2881_ = lean_ctor_get(v_tree_2878_, 0);
v___x_2882_ = lean_unsigned_to_nat(3u);
v___x_2883_ = lean_nat_mul(v___x_2882_, v_size_2881_);
v___x_2884_ = lean_nat_dec_lt(v___x_2883_, v_size_2721_);
lean_dec(v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec(v_r_2725_);
v___x_2885_ = lean_nat_add(v___x_2731_, v_size_2721_);
v___x_2886_ = lean_nat_add(v___x_2885_, v_size_2881_);
lean_dec(v___x_2885_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_tree_2878_);
lean_ctor_set(v___x_2875_, 3, v_l_2550_);
lean_ctor_set(v___x_2875_, 2, v_v_2880_);
lean_ctor_set(v___x_2875_, 1, v_k_2879_);
lean_ctor_set(v___x_2875_, 0, v___x_2886_);
v___x_2888_ = v___x_2875_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_k_2879_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_v_2880_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_l_2550_);
lean_ctor_set(v_reuseFailAlloc_2889_, 4, v_tree_2878_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
else
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2955_; 
lean_inc(v_l_2724_);
lean_inc(v_v_2723_);
lean_inc(v_k_2722_);
lean_inc(v_size_2721_);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; lean_object* v_unused_2957_; lean_object* v_unused_2958_; lean_object* v_unused_2959_; lean_object* v_unused_2960_; 
v_unused_2956_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2956_);
v_unused_2957_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2957_);
v_unused_2958_ = lean_ctor_get(v_l_2550_, 2);
lean_dec(v_unused_2958_);
v_unused_2959_ = lean_ctor_get(v_l_2550_, 1);
lean_dec(v_unused_2959_);
v_unused_2960_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_2960_);
v___x_2891_ = v_l_2550_;
v_isShared_2892_ = v_isSharedCheck_2955_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v_l_2550_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2955_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_size_2893_; lean_object* v_size_2894_; lean_object* v_k_2895_; lean_object* v_v_2896_; lean_object* v_l_2897_; lean_object* v_r_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v_size_2893_ = lean_ctor_get(v_l_2724_, 0);
v_size_2894_ = lean_ctor_get(v_r_2725_, 0);
v_k_2895_ = lean_ctor_get(v_r_2725_, 1);
v_v_2896_ = lean_ctor_get(v_r_2725_, 2);
v_l_2897_ = lean_ctor_get(v_r_2725_, 3);
v_r_2898_ = lean_ctor_get(v_r_2725_, 4);
v___x_2899_ = lean_unsigned_to_nat(2u);
v___x_2900_ = lean_nat_mul(v___x_2899_, v_size_2893_);
v___x_2901_ = lean_nat_dec_lt(v_size_2894_, v___x_2900_);
lean_dec(v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2939_; 
lean_inc(v_r_2898_);
lean_inc(v_l_2897_);
lean_inc(v_v_2896_);
lean_inc(v_k_2895_);
lean_del_object(v___x_2891_);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_r_2725_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; lean_object* v_unused_2941_; lean_object* v_unused_2942_; lean_object* v_unused_2943_; lean_object* v_unused_2944_; 
v_unused_2940_ = lean_ctor_get(v_r_2725_, 4);
lean_dec(v_unused_2940_);
v_unused_2941_ = lean_ctor_get(v_r_2725_, 3);
lean_dec(v_unused_2941_);
v_unused_2942_ = lean_ctor_get(v_r_2725_, 2);
lean_dec(v_unused_2942_);
v_unused_2943_ = lean_ctor_get(v_r_2725_, 1);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_r_2725_, 0);
lean_dec(v_unused_2944_);
v___x_2903_ = v_r_2725_;
v_isShared_2904_ = v_isSharedCheck_2939_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v_r_2725_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2939_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___x_2927_; lean_object* v___y_2929_; 
v___x_2905_ = lean_nat_add(v___x_2731_, v_size_2721_);
lean_dec(v_size_2721_);
v___x_2906_ = lean_nat_add(v___x_2905_, v_size_2881_);
lean_dec(v___x_2905_);
v___x_2927_ = lean_nat_add(v___x_2731_, v_size_2893_);
if (lean_obj_tag(v_l_2897_) == 0)
{
lean_object* v_size_2937_; 
v_size_2937_ = lean_ctor_get(v_l_2897_, 0);
lean_inc(v_size_2937_);
v___y_2929_ = v_size_2937_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_unsigned_to_nat(0u);
v___y_2929_ = v___x_2938_;
goto v___jp_2928_;
}
v___jp_2907_:
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2911_ = lean_nat_add(v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec(v___y_2909_);
lean_inc_ref(v_tree_2878_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 4, v_tree_2878_);
lean_ctor_set(v___x_2903_, 3, v_r_2898_);
lean_ctor_set(v___x_2903_, 2, v_v_2880_);
lean_ctor_set(v___x_2903_, 1, v_k_2879_);
lean_ctor_set(v___x_2903_, 0, v___x_2911_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_k_2879_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_v_2880_);
lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_r_2898_);
lean_ctor_set(v_reuseFailAlloc_2926_, 4, v_tree_2878_);
v___x_2913_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v_tree_2878_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2921_ = lean_ctor_get(v_tree_2878_, 4);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_tree_2878_, 3);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_tree_2878_, 2);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_tree_2878_, 1);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_tree_2878_, 0);
lean_dec(v_unused_2925_);
v___x_2915_ = v_tree_2878_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v_tree_2878_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 4, v___x_2913_);
lean_ctor_set(v___x_2915_, 3, v___y_2908_);
lean_ctor_set(v___x_2915_, 2, v_v_2896_);
lean_ctor_set(v___x_2915_, 1, v_k_2895_);
lean_ctor_set(v___x_2915_, 0, v___x_2906_);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_k_2895_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_v_2896_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v___y_2908_);
lean_ctor_set(v_reuseFailAlloc_2919_, 4, v___x_2913_);
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
v___jp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_nat_add(v___x_2927_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec(v___x_2927_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_l_2897_);
lean_ctor_set(v___x_2875_, 3, v_l_2724_);
lean_ctor_set(v___x_2875_, 2, v_v_2723_);
lean_ctor_set(v___x_2875_, 1, v_k_2722_);
lean_ctor_set(v___x_2875_, 0, v___x_2930_);
v___x_2932_ = v___x_2875_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_k_2722_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_v_2723_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_l_2724_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_l_2897_);
v___x_2932_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_nat_add(v___x_2731_, v_size_2881_);
if (lean_obj_tag(v_r_2898_) == 0)
{
lean_object* v_size_2934_; 
v_size_2934_ = lean_ctor_get(v_r_2898_, 0);
lean_inc(v_size_2934_);
v___y_2908_ = v___x_2932_;
v___y_2909_ = v___x_2933_;
v___y_2910_ = v_size_2934_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_unsigned_to_nat(0u);
v___y_2908_ = v___x_2932_;
v___y_2909_ = v___x_2933_;
v___y_2910_ = v___x_2935_;
goto v___jp_2907_;
}
}
}
}
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2945_ = lean_nat_add(v___x_2731_, v_size_2721_);
lean_dec(v_size_2721_);
v___x_2946_ = lean_nat_add(v___x_2945_, v_size_2881_);
lean_dec(v___x_2945_);
v___x_2947_ = lean_nat_add(v___x_2731_, v_size_2881_);
v___x_2948_ = lean_nat_add(v___x_2947_, v_size_2894_);
lean_dec(v___x_2947_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_tree_2878_);
lean_ctor_set(v___x_2875_, 3, v_r_2725_);
lean_ctor_set(v___x_2875_, 2, v_v_2880_);
lean_ctor_set(v___x_2875_, 1, v_k_2879_);
lean_ctor_set(v___x_2875_, 0, v___x_2948_);
v___x_2950_ = v___x_2875_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_k_2879_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_v_2880_);
lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_r_2725_);
lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_tree_2878_);
v___x_2950_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2952_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 4, v___x_2950_);
lean_ctor_set(v___x_2891_, 0, v___x_2946_);
v___x_2952_ = v___x_2891_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_k_2722_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_v_2723_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_l_2724_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2724_) == 0)
{
lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2984_; 
lean_inc_ref(v_l_2724_);
lean_inc(v_v_2723_);
lean_inc(v_k_2722_);
lean_inc(v_size_2721_);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; lean_object* v_unused_2987_; lean_object* v_unused_2988_; lean_object* v_unused_2989_; 
v_unused_2985_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_2986_);
v_unused_2987_ = lean_ctor_get(v_l_2550_, 2);
lean_dec(v_unused_2987_);
v_unused_2988_ = lean_ctor_get(v_l_2550_, 1);
lean_dec(v_unused_2988_);
v_unused_2989_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_2989_);
v___x_2962_ = v_l_2550_;
v_isShared_2963_ = v_isSharedCheck_2984_;
goto v_resetjp_2961_;
}
else
{
lean_dec(v_l_2550_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2984_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
if (lean_obj_tag(v_r_2725_) == 0)
{
lean_object* v_k_2964_; lean_object* v_v_2965_; lean_object* v_size_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v_k_2964_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_k_2964_);
v_v_2965_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_v_2965_);
lean_dec_ref(v___x_2877_);
v_size_2966_ = lean_ctor_get(v_r_2725_, 0);
v___x_2967_ = lean_nat_add(v___x_2731_, v_size_2721_);
lean_dec(v_size_2721_);
v___x_2968_ = lean_nat_add(v___x_2731_, v_size_2966_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_tree_2878_);
lean_ctor_set(v___x_2875_, 3, v_r_2725_);
lean_ctor_set(v___x_2875_, 2, v_v_2965_);
lean_ctor_set(v___x_2875_, 1, v_k_2964_);
lean_ctor_set(v___x_2875_, 0, v___x_2968_);
v___x_2970_ = v___x_2875_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_k_2964_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_v_2965_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_r_2725_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_tree_2878_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 4, v___x_2970_);
lean_ctor_set(v___x_2962_, 0, v___x_2967_);
v___x_2972_ = v___x_2962_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_k_2722_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_v_2723_);
lean_ctor_set(v_reuseFailAlloc_2973_, 3, v_l_2724_);
lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_object* v_k_2975_; lean_object* v_v_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
lean_dec(v_size_2721_);
v_k_2975_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_k_2975_);
v_v_2976_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_v_2976_);
lean_dec_ref(v___x_2877_);
v___x_2977_ = lean_unsigned_to_nat(3u);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_r_2725_);
lean_ctor_set(v___x_2875_, 3, v_r_2725_);
lean_ctor_set(v___x_2875_, 2, v_v_2976_);
lean_ctor_set(v___x_2875_, 1, v_k_2975_);
lean_ctor_set(v___x_2875_, 0, v___x_2731_);
v___x_2979_ = v___x_2875_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_k_2975_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v_v_2976_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v_r_2725_);
lean_ctor_set(v_reuseFailAlloc_2983_, 4, v_r_2725_);
v___x_2979_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 4, v___x_2979_);
lean_ctor_set(v___x_2962_, 0, v___x_2977_);
v___x_2981_ = v___x_2962_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_k_2722_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_v_2723_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_l_2724_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2725_) == 0)
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3014_; 
lean_inc(v_l_2724_);
lean_inc(v_v_2723_);
lean_inc(v_k_2722_);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_l_2550_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; lean_object* v_unused_3016_; lean_object* v_unused_3017_; lean_object* v_unused_3018_; lean_object* v_unused_3019_; 
v_unused_3015_ = lean_ctor_get(v_l_2550_, 4);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v_l_2550_, 3);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v_l_2550_, 2);
lean_dec(v_unused_3017_);
v_unused_3018_ = lean_ctor_get(v_l_2550_, 1);
lean_dec(v_unused_3018_);
v_unused_3019_ = lean_ctor_get(v_l_2550_, 0);
lean_dec(v_unused_3019_);
v___x_2991_ = v_l_2550_;
v_isShared_2992_ = v_isSharedCheck_3014_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v_l_2550_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3014_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v_k_2993_; lean_object* v_v_2994_; lean_object* v_k_2995_; lean_object* v_v_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3010_; 
v_k_2993_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_k_2993_);
v_v_2994_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_v_2994_);
lean_dec_ref(v___x_2877_);
v_k_2995_ = lean_ctor_get(v_r_2725_, 1);
v_v_2996_ = lean_ctor_get(v_r_2725_, 2);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_r_2725_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; lean_object* v_unused_3012_; lean_object* v_unused_3013_; 
v_unused_3011_ = lean_ctor_get(v_r_2725_, 4);
lean_dec(v_unused_3011_);
v_unused_3012_ = lean_ctor_get(v_r_2725_, 3);
lean_dec(v_unused_3012_);
v_unused_3013_ = lean_ctor_get(v_r_2725_, 0);
lean_dec(v_unused_3013_);
v___x_2998_ = v_r_2725_;
v_isShared_2999_ = v_isSharedCheck_3010_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_v_2996_);
lean_inc(v_k_2995_);
lean_dec(v_r_2725_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3010_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_3000_ = lean_unsigned_to_nat(3u);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 4, v_l_2724_);
lean_ctor_set(v___x_2998_, 3, v_l_2724_);
lean_ctor_set(v___x_2998_, 2, v_v_2723_);
lean_ctor_set(v___x_2998_, 1, v_k_2722_);
lean_ctor_set(v___x_2998_, 0, v___x_2731_);
v___x_3002_ = v___x_2998_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_k_2722_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v_v_2723_);
lean_ctor_set(v_reuseFailAlloc_3009_, 3, v_l_2724_);
lean_ctor_set(v_reuseFailAlloc_3009_, 4, v_l_2724_);
v___x_3002_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3004_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_l_2724_);
lean_ctor_set(v___x_2875_, 3, v_l_2724_);
lean_ctor_set(v___x_2875_, 2, v_v_2994_);
lean_ctor_set(v___x_2875_, 1, v_k_2993_);
lean_ctor_set(v___x_2875_, 0, v___x_2731_);
v___x_3004_ = v___x_2875_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_k_2993_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_v_2994_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_l_2724_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v_l_2724_);
v___x_3004_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3006_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 4, v___x_3004_);
lean_ctor_set(v___x_2991_, 3, v___x_3002_);
lean_ctor_set(v___x_2991_, 2, v_v_2996_);
lean_ctor_set(v___x_2991_, 1, v_k_2995_);
lean_ctor_set(v___x_2991_, 0, v___x_3000_);
v___x_3006_ = v___x_2991_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_k_2995_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_v_2996_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3007_, 4, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
}
else
{
lean_object* v_k_3020_; lean_object* v_v_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v_k_3020_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_k_3020_);
v_v_3021_ = lean_ctor_get(v___x_2877_, 1);
lean_inc(v_v_3021_);
lean_dec_ref(v___x_2877_);
v___x_3022_ = lean_unsigned_to_nat(2u);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v_r_2725_);
lean_ctor_set(v___x_2875_, 3, v_l_2550_);
lean_ctor_set(v___x_2875_, 2, v_v_3021_);
lean_ctor_set(v___x_2875_, 1, v_k_3020_);
lean_ctor_set(v___x_2875_, 0, v___x_3022_);
v___x_3024_ = v___x_2875_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_k_3020_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_v_3021_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_l_2550_);
lean_ctor_set(v_reuseFailAlloc_3025_, 4, v_r_2725_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
}
else
{
return v_l_2550_;
}
}
else
{
return v_r_2551_;
}
}
}
else
{
lean_object* v_impl_3032_; lean_object* v___x_3033_; 
v_impl_3032_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2546_, v_l_2550_);
v___x_3033_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3032_) == 0)
{
if (lean_obj_tag(v_r_2551_) == 0)
{
lean_object* v_size_3034_; lean_object* v_size_3035_; lean_object* v_k_3036_; lean_object* v_v_3037_; lean_object* v_l_3038_; lean_object* v_r_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v_size_3034_ = lean_ctor_get(v_impl_3032_, 0);
v_size_3035_ = lean_ctor_get(v_r_2551_, 0);
v_k_3036_ = lean_ctor_get(v_r_2551_, 1);
v_v_3037_ = lean_ctor_get(v_r_2551_, 2);
v_l_3038_ = lean_ctor_get(v_r_2551_, 3);
lean_inc(v_l_3038_);
v_r_3039_ = lean_ctor_get(v_r_2551_, 4);
v___x_3040_ = lean_unsigned_to_nat(3u);
v___x_3041_ = lean_nat_mul(v___x_3040_, v_size_3034_);
v___x_3042_ = lean_nat_dec_lt(v___x_3041_, v_size_3035_);
lean_dec(v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
lean_dec(v_l_3038_);
v___x_3043_ = lean_nat_add(v___x_3033_, v_size_3034_);
v___x_3044_ = lean_nat_add(v___x_3043_, v_size_3035_);
lean_dec(v___x_3043_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 3, v_impl_3032_);
lean_ctor_set(v___x_2553_, 0, v___x_3044_);
v___x_3046_ = v___x_2553_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_impl_3032_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_r_2551_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3111_; 
lean_inc(v_r_3039_);
lean_inc(v_v_3037_);
lean_inc(v_k_3036_);
lean_inc(v_size_3035_);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; lean_object* v_unused_3115_; lean_object* v_unused_3116_; 
v_unused_3112_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_r_2551_, 2);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_r_2551_, 1);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_r_2551_, 0);
lean_dec(v_unused_3116_);
v___x_3049_ = v_r_2551_;
v_isShared_3050_ = v_isSharedCheck_3111_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_r_2551_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3111_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_size_3051_; lean_object* v_k_3052_; lean_object* v_v_3053_; lean_object* v_l_3054_; lean_object* v_r_3055_; lean_object* v_size_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v_size_3051_ = lean_ctor_get(v_l_3038_, 0);
v_k_3052_ = lean_ctor_get(v_l_3038_, 1);
v_v_3053_ = lean_ctor_get(v_l_3038_, 2);
v_l_3054_ = lean_ctor_get(v_l_3038_, 3);
v_r_3055_ = lean_ctor_get(v_l_3038_, 4);
v_size_3056_ = lean_ctor_get(v_r_3039_, 0);
v___x_3057_ = lean_unsigned_to_nat(2u);
v___x_3058_ = lean_nat_mul(v___x_3057_, v_size_3056_);
v___x_3059_ = lean_nat_dec_lt(v_size_3051_, v___x_3058_);
lean_dec(v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3087_; 
lean_inc(v_r_3055_);
lean_inc(v_l_3054_);
lean_inc(v_v_3053_);
lean_inc(v_k_3052_);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_l_3038_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; lean_object* v_unused_3089_; lean_object* v_unused_3090_; lean_object* v_unused_3091_; lean_object* v_unused_3092_; 
v_unused_3088_ = lean_ctor_get(v_l_3038_, 4);
lean_dec(v_unused_3088_);
v_unused_3089_ = lean_ctor_get(v_l_3038_, 3);
lean_dec(v_unused_3089_);
v_unused_3090_ = lean_ctor_get(v_l_3038_, 2);
lean_dec(v_unused_3090_);
v_unused_3091_ = lean_ctor_get(v_l_3038_, 1);
lean_dec(v_unused_3091_);
v_unused_3092_ = lean_ctor_get(v_l_3038_, 0);
lean_dec(v_unused_3092_);
v___x_3061_ = v_l_3038_;
v_isShared_3062_ = v_isSharedCheck_3087_;
goto v_resetjp_3060_;
}
else
{
lean_dec(v_l_3038_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3087_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3077_; 
v___x_3063_ = lean_nat_add(v___x_3033_, v_size_3034_);
v___x_3064_ = lean_nat_add(v___x_3063_, v_size_3035_);
lean_dec(v_size_3035_);
if (lean_obj_tag(v_l_3054_) == 0)
{
lean_object* v_size_3085_; 
v_size_3085_ = lean_ctor_get(v_l_3054_, 0);
lean_inc(v_size_3085_);
v___y_3077_ = v_size_3085_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_unsigned_to_nat(0u);
v___y_3077_ = v___x_3086_;
goto v___jp_3076_;
}
v___jp_3065_:
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3069_ = lean_nat_add(v___y_3066_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec(v___y_3066_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 4, v_r_3039_);
lean_ctor_set(v___x_3061_, 3, v_r_3055_);
lean_ctor_set(v___x_3061_, 2, v_v_3037_);
lean_ctor_set(v___x_3061_, 1, v_k_3036_);
lean_ctor_set(v___x_3061_, 0, v___x_3069_);
v___x_3071_ = v___x_3061_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_k_3036_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_v_3037_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_r_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_r_3039_);
v___x_3071_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3073_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 4, v___x_3071_);
lean_ctor_set(v___x_3049_, 3, v___y_3067_);
lean_ctor_set(v___x_3049_, 2, v_v_3053_);
lean_ctor_set(v___x_3049_, 1, v_k_3052_);
lean_ctor_set(v___x_3049_, 0, v___x_3064_);
v___x_3073_ = v___x_3049_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3074_, 3, v___y_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 4, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
v___jp_3076_:
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3078_ = lean_nat_add(v___x_3063_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec(v___x_3063_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_l_3054_);
lean_ctor_set(v___x_2553_, 3, v_impl_3032_);
lean_ctor_set(v___x_2553_, 0, v___x_3078_);
v___x_3080_ = v___x_2553_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_impl_3032_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_l_3054_);
v___x_3080_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_nat_add(v___x_3033_, v_size_3056_);
if (lean_obj_tag(v_r_3055_) == 0)
{
lean_object* v_size_3082_; 
v_size_3082_ = lean_ctor_get(v_r_3055_, 0);
lean_inc(v_size_3082_);
v___y_3066_ = v___x_3081_;
v___y_3067_ = v___x_3080_;
v___y_3068_ = v_size_3082_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_unsigned_to_nat(0u);
v___y_3066_ = v___x_3081_;
v___y_3067_ = v___x_3080_;
v___y_3068_ = v___x_3083_;
goto v___jp_3065_;
}
}
}
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
lean_del_object(v___x_2553_);
v___x_3093_ = lean_nat_add(v___x_3033_, v_size_3034_);
v___x_3094_ = lean_nat_add(v___x_3093_, v_size_3035_);
lean_dec(v_size_3035_);
v___x_3095_ = lean_nat_add(v___x_3093_, v_size_3051_);
lean_dec(v___x_3093_);
lean_inc_ref(v_impl_3032_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 4, v_l_3038_);
lean_ctor_set(v___x_3049_, 3, v_impl_3032_);
lean_ctor_set(v___x_3049_, 2, v_v_2549_);
lean_ctor_set(v___x_3049_, 1, v_k_2548_);
lean_ctor_set(v___x_3049_, 0, v___x_3095_);
v___x_3097_ = v___x_3049_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_impl_3032_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_l_3038_);
v___x_3097_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_isSharedCheck_3104_ = !lean_is_exclusive(v_impl_3032_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; 
v_unused_3105_ = lean_ctor_get(v_impl_3032_, 4);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_impl_3032_, 3);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_impl_3032_, 2);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_impl_3032_, 1);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_impl_3032_, 0);
lean_dec(v_unused_3109_);
v___x_3099_ = v_impl_3032_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v_impl_3032_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 4, v_r_3039_);
lean_ctor_set(v___x_3099_, 3, v___x_3097_);
lean_ctor_set(v___x_3099_, 2, v_v_3037_);
lean_ctor_set(v___x_3099_, 1, v_k_3036_);
lean_ctor_set(v___x_3099_, 0, v___x_3094_);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_k_3036_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_v_3037_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3103_, 4, v_r_3039_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v_size_3117_ = lean_ctor_get(v_impl_3032_, 0);
v___x_3118_ = lean_nat_add(v___x_3033_, v_size_3117_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 3, v_impl_3032_);
lean_ctor_set(v___x_2553_, 0, v___x_3118_);
v___x_3120_ = v___x_2553_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_impl_3032_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_r_2551_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
if (lean_obj_tag(v_r_2551_) == 0)
{
lean_object* v_l_3122_; 
v_l_3122_ = lean_ctor_get(v_r_2551_, 3);
lean_inc(v_l_3122_);
if (lean_obj_tag(v_l_3122_) == 0)
{
lean_object* v_r_3123_; 
v_r_3123_ = lean_ctor_get(v_r_2551_, 4);
lean_inc(v_r_3123_);
if (lean_obj_tag(v_r_3123_) == 0)
{
lean_object* v_size_3124_; lean_object* v_k_3125_; lean_object* v_v_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3139_; 
v_size_3124_ = lean_ctor_get(v_r_2551_, 0);
v_k_3125_ = lean_ctor_get(v_r_2551_, 1);
v_v_3126_ = lean_ctor_get(v_r_2551_, 2);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; lean_object* v_unused_3141_; 
v_unused_3140_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_3141_);
v___x_3128_ = v_r_2551_;
v_isShared_3129_ = v_isSharedCheck_3139_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_v_3126_);
lean_inc(v_k_3125_);
lean_inc(v_size_3124_);
lean_dec(v_r_2551_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3139_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_size_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v_size_3130_ = lean_ctor_get(v_l_3122_, 0);
v___x_3131_ = lean_nat_add(v___x_3033_, v_size_3124_);
lean_dec(v_size_3124_);
v___x_3132_ = lean_nat_add(v___x_3033_, v_size_3130_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 4, v_l_3122_);
lean_ctor_set(v___x_3128_, 3, v_impl_3032_);
lean_ctor_set(v___x_3128_, 2, v_v_2549_);
lean_ctor_set(v___x_3128_, 1, v_k_2548_);
lean_ctor_set(v___x_3128_, 0, v___x_3132_);
v___x_3134_ = v___x_3128_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_impl_3032_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_l_3122_);
v___x_3134_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_r_3123_);
lean_ctor_set(v___x_2553_, 3, v___x_3134_);
lean_ctor_set(v___x_2553_, 2, v_v_3126_);
lean_ctor_set(v___x_2553_, 1, v_k_3125_);
lean_ctor_set(v___x_2553_, 0, v___x_3131_);
v___x_3136_ = v___x_2553_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_k_3125_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_v_3126_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_r_3123_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_k_3142_; lean_object* v_v_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3166_; 
v_k_3142_ = lean_ctor_get(v_r_2551_, 1);
v_v_3143_ = lean_ctor_get(v_r_2551_, 2);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3167_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_r_2551_, 0);
lean_dec(v_unused_3169_);
v___x_3145_ = v_r_2551_;
v_isShared_3146_ = v_isSharedCheck_3166_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_v_3143_);
lean_inc(v_k_3142_);
lean_dec(v_r_2551_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3166_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_k_3147_; lean_object* v_v_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3162_; 
v_k_3147_ = lean_ctor_get(v_l_3122_, 1);
v_v_3148_ = lean_ctor_get(v_l_3122_, 2);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_l_3122_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3163_ = lean_ctor_get(v_l_3122_, 4);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_l_3122_, 3);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_l_3122_, 0);
lean_dec(v_unused_3165_);
v___x_3150_ = v_l_3122_;
v_isShared_3151_ = v_isSharedCheck_3162_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_v_3148_);
lean_inc(v_k_3147_);
lean_dec(v_l_3122_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3162_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3152_ = lean_unsigned_to_nat(3u);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 4, v_r_3123_);
lean_ctor_set(v___x_3150_, 3, v_r_3123_);
lean_ctor_set(v___x_3150_, 2, v_v_2549_);
lean_ctor_set(v___x_3150_, 1, v_k_2548_);
lean_ctor_set(v___x_3150_, 0, v___x_3033_);
v___x_3154_ = v___x_3150_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3161_, 3, v_r_3123_);
lean_ctor_set(v_reuseFailAlloc_3161_, 4, v_r_3123_);
v___x_3154_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3156_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 3, v_r_3123_);
lean_ctor_set(v___x_3145_, 0, v___x_3033_);
v___x_3156_ = v___x_3145_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_k_3142_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_v_3143_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_r_3123_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_r_3123_);
v___x_3156_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___x_3156_);
lean_ctor_set(v___x_2553_, 3, v___x_3154_);
lean_ctor_set(v___x_2553_, 2, v_v_3148_);
lean_ctor_set(v___x_2553_, 1, v_k_3147_);
lean_ctor_set(v___x_2553_, 0, v___x_3152_);
v___x_3158_ = v___x_2553_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_k_3147_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_v_3148_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3170_; 
v_r_3170_ = lean_ctor_get(v_r_2551_, 4);
lean_inc(v_r_3170_);
if (lean_obj_tag(v_r_3170_) == 0)
{
lean_object* v_k_3171_; lean_object* v_v_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3183_; 
v_k_3171_ = lean_ctor_get(v_r_2551_, 1);
v_v_3172_ = lean_ctor_get(v_r_2551_, 2);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; lean_object* v_unused_3185_; lean_object* v_unused_3186_; 
v_unused_3184_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_3184_);
v_unused_3185_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v_r_2551_, 0);
lean_dec(v_unused_3186_);
v___x_3174_ = v_r_2551_;
v_isShared_3175_ = v_isSharedCheck_3183_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_v_3172_);
lean_inc(v_k_3171_);
lean_dec(v_r_2551_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3183_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = lean_unsigned_to_nat(3u);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_l_3122_);
lean_ctor_set(v___x_3174_, 2, v_v_2549_);
lean_ctor_set(v___x_3174_, 1, v_k_2548_);
lean_ctor_set(v___x_3174_, 0, v___x_3033_);
v___x_3178_ = v___x_3174_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_l_3122_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_l_3122_);
v___x_3178_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3180_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_r_3170_);
lean_ctor_set(v___x_2553_, 3, v___x_3178_);
lean_ctor_set(v___x_2553_, 2, v_v_3172_);
lean_ctor_set(v___x_2553_, 1, v_k_3171_);
lean_ctor_set(v___x_2553_, 0, v___x_3176_);
v___x_3180_ = v___x_2553_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_k_3171_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_v_3172_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_r_3170_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_object* v_size_3187_; lean_object* v_k_3188_; lean_object* v_v_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3200_; 
v_size_3187_ = lean_ctor_get(v_r_2551_, 0);
v_k_3188_ = lean_ctor_get(v_r_2551_, 1);
v_v_3189_ = lean_ctor_get(v_r_2551_, 2);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_r_2551_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; lean_object* v_unused_3202_; 
v_unused_3201_ = lean_ctor_get(v_r_2551_, 4);
lean_dec(v_unused_3201_);
v_unused_3202_ = lean_ctor_get(v_r_2551_, 3);
lean_dec(v_unused_3202_);
v___x_3191_ = v_r_2551_;
v_isShared_3192_ = v_isSharedCheck_3200_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_v_3189_);
lean_inc(v_k_3188_);
lean_inc(v_size_3187_);
lean_dec(v_r_2551_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3200_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 3, v_r_3170_);
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_size_3187_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_k_3188_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_v_3189_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_r_3170_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_r_3170_);
v___x_3194_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3195_ = lean_unsigned_to_nat(2u);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___x_3194_);
lean_ctor_set(v___x_2553_, 3, v_r_3170_);
lean_ctor_set(v___x_2553_, 0, v___x_3195_);
v___x_3197_ = v___x_2553_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_r_3170_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v___x_3194_);
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
lean_object* v___x_3204_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 3, v_r_2551_);
lean_ctor_set(v___x_2553_, 0, v___x_3033_);
v___x_3204_ = v___x_2553_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_r_2551_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_r_2551_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
else
{
return v_t_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3208_, lean_object* v_t_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3208_, v_t_3209_);
lean_dec(v_k_3208_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3211_, lean_object* v_j_3212_){
_start:
{
lean_object* v_vars_3213_; lean_object* v_jps_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3222_; 
v_vars_3213_ = lean_ctor_get(v_ctx_3211_, 0);
v_jps_3214_ = lean_ctor_get(v_ctx_3211_, 1);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_ctx_3211_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3216_ = v_ctx_3211_;
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_jps_3214_);
lean_inc(v_vars_3213_);
lean_dec(v_ctx_3211_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3212_, v_jps_3214_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3218_);
v___x_3220_ = v___x_3216_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_vars_3213_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3223_, lean_object* v_j_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3223_, v_j_3224_);
lean_dec(v_j_3224_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3226_, lean_object* v_k_3227_, lean_object* v_t_3228_, lean_object* v_h_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3227_, v_t_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3231_, lean_object* v_k_3232_, lean_object* v_t_3233_, lean_object* v_h_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3231_, v_k_3232_, v_t_3233_, v_h_3234_);
lean_dec(v_k_3232_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3236_, lean_object* v_x_3237_){
_start:
{
lean_object* v_vars_3238_; lean_object* v___x_3239_; 
v_vars_3238_ = lean_ctor_get(v_ctx_3236_, 0);
v___x_3239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3238_, v_x_3237_);
if (lean_obj_tag(v___x_3239_) == 1)
{
lean_object* v_val_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3248_; 
v_val_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3248_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_val_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3248_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_a_3244_; lean_object* v___x_3246_; 
v_a_3244_ = lean_ctor_get(v_val_3240_, 0);
lean_inc(v_a_3244_);
lean_dec(v_val_3240_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v_a_3244_);
v___x_3246_ = v___x_3242_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
else
{
lean_object* v___x_3249_; 
lean_dec(v___x_3239_);
v___x_3249_ = lean_box(0);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3250_, lean_object* v_x_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_IR_LocalContext_getType(v_ctx_3250_, v_x_3251_);
lean_dec(v_x_3251_);
lean_dec_ref(v_ctx_3250_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v_vars_3255_; lean_object* v___x_3256_; 
v_vars_3255_ = lean_ctor_get(v_ctx_3253_, 0);
v___x_3256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3255_, v_x_3254_);
if (lean_obj_tag(v___x_3256_) == 1)
{
lean_object* v_val_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3266_; 
v_val_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_val_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
if (lean_obj_tag(v_val_3257_) == 1)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; 
v_a_3261_ = lean_ctor_get(v_val_3257_, 1);
lean_inc_ref(v_a_3261_);
lean_dec_ref_known(v_val_3257_, 2);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v_a_3261_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
else
{
lean_object* v___x_3265_; 
lean_del_object(v___x_3259_);
lean_dec(v_val_3257_);
v___x_3265_ = lean_box(0);
return v___x_3265_;
}
}
}
else
{
lean_object* v___x_3267_; 
lean_dec(v___x_3256_);
v___x_3267_ = lean_box(0);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_IR_LocalContext_getValue(v_ctx_3268_, v_x_3269_);
lean_dec(v_x_3269_);
lean_dec_ref(v_ctx_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3271_, lean_object* v_v_u2081_3272_, lean_object* v_v_u2082_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_00_u03c1_3271_, v_v_u2081_3272_);
if (lean_obj_tag(v___x_3274_) == 0)
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_nat_dec_eq(v_v_u2081_3272_, v_v_u2082_3273_);
return v___x_3275_;
}
else
{
lean_object* v_val_3276_; uint8_t v___x_3277_; 
v_val_3276_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_val_3276_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3277_ = lean_nat_dec_eq(v_val_3276_, v_v_u2082_3273_);
lean_dec(v_val_3276_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3278_, lean_object* v_v_u2081_3279_, lean_object* v_v_u2082_3280_){
_start:
{
uint8_t v_res_3281_; lean_object* v_r_3282_; 
v_res_3281_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3278_, v_v_u2081_3279_, v_v_u2082_3280_);
lean_dec(v_v_u2082_3280_);
lean_dec(v_v_u2081_3279_);
lean_dec(v_00_u03c1_3278_);
v_r_3282_ = lean_box(v_res_3281_);
return v_r_3282_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
if (lean_obj_tag(v_x_3286_) == 0)
{
if (lean_obj_tag(v_x_3287_) == 0)
{
lean_object* v_id_3288_; lean_object* v_id_3289_; uint8_t v___x_3290_; 
v_id_3288_ = lean_ctor_get(v_x_3286_, 0);
v_id_3289_ = lean_ctor_get(v_x_3287_, 0);
v___x_3290_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3285_, v_id_3288_, v_id_3289_);
return v___x_3290_;
}
else
{
uint8_t v___x_3291_; 
v___x_3291_ = 0;
return v___x_3291_;
}
}
else
{
if (lean_obj_tag(v_x_3287_) == 1)
{
uint8_t v___x_3292_; 
v___x_3292_ = 1;
return v___x_3292_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = 0;
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_){
_start:
{
uint8_t v_res_3297_; lean_object* v_r_3298_; 
v_res_3297_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3294_, v_x_3295_, v_x_3296_);
lean_dec(v_x_3296_);
lean_dec(v_x_3295_);
lean_dec(v_00_u03c1_3294_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3301_, lean_object* v_xs_3302_, lean_object* v_ys_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_zero_3305_; uint8_t v_isZero_3306_; 
v_zero_3305_ = lean_unsigned_to_nat(0u);
v_isZero_3306_ = lean_nat_dec_eq(v_x_3304_, v_zero_3305_);
if (v_isZero_3306_ == 1)
{
lean_dec(v_x_3304_);
return v_isZero_3306_;
}
else
{
lean_object* v_one_3307_; lean_object* v_n_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v_one_3307_ = lean_unsigned_to_nat(1u);
v_n_3308_ = lean_nat_sub(v_x_3304_, v_one_3307_);
lean_dec(v_x_3304_);
v___x_3309_ = lean_array_fget_borrowed(v_xs_3302_, v_n_3308_);
v___x_3310_ = lean_array_fget_borrowed(v_ys_3303_, v_n_3308_);
v___x_3311_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3301_, v___x_3309_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_dec(v_n_3308_);
return v___x_3311_;
}
else
{
v_x_3304_ = v_n_3308_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3313_, lean_object* v_xs_3314_, lean_object* v_ys_3315_, lean_object* v_x_3316_){
_start:
{
uint8_t v_res_3317_; lean_object* v_r_3318_; 
v_res_3317_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3313_, v_xs_3314_, v_ys_3315_, v_x_3316_);
lean_dec_ref(v_ys_3315_);
lean_dec_ref(v_xs_3314_);
lean_dec(v_00_u03c1_3313_);
v_r_3318_ = lean_box(v_res_3317_);
return v_r_3318_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3319_, lean_object* v_args_u2081_3320_, lean_object* v_args_u2082_3321_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = lean_array_get_size(v_args_u2081_3320_);
v___x_3323_ = lean_array_get_size(v_args_u2082_3321_);
v___x_3324_ = lean_nat_dec_eq(v___x_3322_, v___x_3323_);
if (v___x_3324_ == 0)
{
return v___x_3324_;
}
else
{
uint8_t v___x_3325_; 
v___x_3325_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3319_, v_args_u2081_3320_, v_args_u2082_3321_, v___x_3322_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3326_, lean_object* v_args_u2081_3327_, lean_object* v_args_u2082_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3326_, v_args_u2081_3327_, v_args_u2082_3328_);
lean_dec_ref(v_args_u2082_3328_);
lean_dec_ref(v_args_u2081_3327_);
lean_dec(v_00_u03c1_3326_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3331_, lean_object* v_xs_3332_, lean_object* v_ys_3333_, lean_object* v_hsz_3334_, lean_object* v_x_3335_, lean_object* v_x_3336_){
_start:
{
uint8_t v___x_3337_; 
v___x_3337_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3331_, v_xs_3332_, v_ys_3333_, v_x_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3338_, lean_object* v_xs_3339_, lean_object* v_ys_3340_, lean_object* v_hsz_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_){
_start:
{
uint8_t v_res_3344_; lean_object* v_r_3345_; 
v_res_3344_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3338_, v_xs_3339_, v_ys_3340_, v_hsz_3341_, v_x_3342_, v_x_3343_);
lean_dec_ref(v_ys_3340_);
lean_dec_ref(v_xs_3339_);
lean_dec(v_00_u03c1_3338_);
v_r_3345_ = lean_box(v_res_3344_);
return v_r_3345_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* v_00_u03c1_3348_, lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
lean_object* v_n_u2081_3352_; lean_object* v_x_u2081_3353_; lean_object* v_n_u2082_3354_; lean_object* v_x_u2082_3355_; lean_object* v_c_u2081_3359_; lean_object* v_ys_u2081_3360_; lean_object* v_c_u2082_3361_; lean_object* v_ys_u2082_3362_; 
switch(lean_obj_tag(v_x_3349_))
{
case 0:
{
if (lean_obj_tag(v_x_3350_) == 0)
{
lean_object* v_i_3365_; lean_object* v_ys_3366_; lean_object* v_i_3367_; lean_object* v_ys_3368_; uint8_t v___x_3369_; 
v_i_3365_ = lean_ctor_get(v_x_3349_, 0);
v_ys_3366_ = lean_ctor_get(v_x_3349_, 1);
v_i_3367_ = lean_ctor_get(v_x_3350_, 0);
v_ys_3368_ = lean_ctor_get(v_x_3350_, 1);
v___x_3369_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3365_, v_i_3367_);
if (v___x_3369_ == 0)
{
return v___x_3369_;
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3348_, v_ys_3366_, v_ys_3368_);
return v___x_3370_;
}
}
else
{
uint8_t v___x_3371_; 
v___x_3371_ = 0;
return v___x_3371_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3350_) == 1)
{
lean_object* v_n_3372_; lean_object* v_x_3373_; lean_object* v_n_3374_; lean_object* v_x_3375_; 
v_n_3372_ = lean_ctor_get(v_x_3349_, 0);
v_x_3373_ = lean_ctor_get(v_x_3349_, 1);
v_n_3374_ = lean_ctor_get(v_x_3350_, 0);
v_x_3375_ = lean_ctor_get(v_x_3350_, 1);
v_n_u2081_3352_ = v_n_3372_;
v_x_u2081_3353_ = v_x_3373_;
v_n_u2082_3354_ = v_n_3374_;
v_x_u2082_3355_ = v_x_3375_;
goto v___jp_3351_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = 0;
return v___x_3376_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3350_) == 2)
{
lean_object* v_x_3377_; lean_object* v_i_3378_; uint8_t v_updtHeader_3379_; lean_object* v_ys_3380_; lean_object* v_x_3381_; lean_object* v_i_3382_; uint8_t v_updtHeader_3383_; lean_object* v_ys_3384_; uint8_t v___x_3385_; 
v_x_3377_ = lean_ctor_get(v_x_3349_, 0);
v_i_3378_ = lean_ctor_get(v_x_3349_, 1);
v_updtHeader_3379_ = lean_ctor_get_uint8(v_x_3349_, sizeof(void*)*3);
v_ys_3380_ = lean_ctor_get(v_x_3349_, 2);
v_x_3381_ = lean_ctor_get(v_x_3350_, 0);
v_i_3382_ = lean_ctor_get(v_x_3350_, 1);
v_updtHeader_3383_ = lean_ctor_get_uint8(v_x_3350_, sizeof(void*)*3);
v_ys_3384_ = lean_ctor_get(v_x_3350_, 2);
v___x_3385_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_3377_, v_x_3381_);
if (v___x_3385_ == 0)
{
return v___x_3385_;
}
else
{
uint8_t v___x_3386_; 
v___x_3386_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3378_, v_i_3382_);
if (v___x_3386_ == 0)
{
return v___x_3386_;
}
else
{
if (v_updtHeader_3383_ == 0)
{
if (v_updtHeader_3379_ == 0)
{
uint8_t v___x_3387_; 
v___x_3387_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3348_, v_ys_3380_, v_ys_3384_);
return v___x_3387_;
}
else
{
return v_updtHeader_3383_;
}
}
else
{
if (v_updtHeader_3379_ == 0)
{
return v_updtHeader_3379_;
}
else
{
uint8_t v___x_3388_; 
v___x_3388_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3348_, v_ys_3380_, v_ys_3384_);
return v___x_3388_;
}
}
}
}
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = 0;
return v___x_3389_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3350_) == 3)
{
lean_object* v_i_3390_; lean_object* v_x_3391_; lean_object* v_i_3392_; lean_object* v_x_3393_; 
v_i_3390_ = lean_ctor_get(v_x_3349_, 0);
v_x_3391_ = lean_ctor_get(v_x_3349_, 1);
v_i_3392_ = lean_ctor_get(v_x_3350_, 0);
v_x_3393_ = lean_ctor_get(v_x_3350_, 1);
v_n_u2081_3352_ = v_i_3390_;
v_x_u2081_3353_ = v_x_3391_;
v_n_u2082_3354_ = v_i_3392_;
v_x_u2082_3355_ = v_x_3393_;
goto v___jp_3351_;
}
else
{
uint8_t v___x_3394_; 
v___x_3394_ = 0;
return v___x_3394_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3350_) == 4)
{
lean_object* v_i_3395_; lean_object* v_x_3396_; lean_object* v_i_3397_; lean_object* v_x_3398_; 
v_i_3395_ = lean_ctor_get(v_x_3349_, 0);
v_x_3396_ = lean_ctor_get(v_x_3349_, 1);
v_i_3397_ = lean_ctor_get(v_x_3350_, 0);
v_x_3398_ = lean_ctor_get(v_x_3350_, 1);
v_n_u2081_3352_ = v_i_3395_;
v_x_u2081_3353_ = v_x_3396_;
v_n_u2082_3354_ = v_i_3397_;
v_x_u2082_3355_ = v_x_3398_;
goto v___jp_3351_;
}
else
{
uint8_t v___x_3399_; 
v___x_3399_ = 0;
return v___x_3399_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3350_) == 5)
{
lean_object* v_n_3400_; lean_object* v_offset_3401_; lean_object* v_x_3402_; lean_object* v_n_3403_; lean_object* v_offset_3404_; lean_object* v_x_3405_; uint8_t v___x_3406_; 
v_n_3400_ = lean_ctor_get(v_x_3349_, 0);
v_offset_3401_ = lean_ctor_get(v_x_3349_, 1);
v_x_3402_ = lean_ctor_get(v_x_3349_, 2);
v_n_3403_ = lean_ctor_get(v_x_3350_, 0);
v_offset_3404_ = lean_ctor_get(v_x_3350_, 1);
v_x_3405_ = lean_ctor_get(v_x_3350_, 2);
v___x_3406_ = lean_nat_dec_eq(v_n_3400_, v_n_3403_);
if (v___x_3406_ == 0)
{
return v___x_3406_;
}
else
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_nat_dec_eq(v_offset_3401_, v_offset_3404_);
if (v___x_3407_ == 0)
{
return v___x_3407_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_3402_, v_x_3405_);
return v___x_3408_;
}
}
}
else
{
uint8_t v___x_3409_; 
v___x_3409_ = 0;
return v___x_3409_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3350_) == 6)
{
lean_object* v_c_3410_; lean_object* v_ys_3411_; lean_object* v_c_3412_; lean_object* v_ys_3413_; 
v_c_3410_ = lean_ctor_get(v_x_3349_, 0);
v_ys_3411_ = lean_ctor_get(v_x_3349_, 1);
v_c_3412_ = lean_ctor_get(v_x_3350_, 0);
v_ys_3413_ = lean_ctor_get(v_x_3350_, 1);
v_c_u2081_3359_ = v_c_3410_;
v_ys_u2081_3360_ = v_ys_3411_;
v_c_u2082_3361_ = v_c_3412_;
v_ys_u2082_3362_ = v_ys_3413_;
goto v___jp_3358_;
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = 0;
return v___x_3414_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3350_) == 7)
{
lean_object* v_c_3415_; lean_object* v_ys_3416_; lean_object* v_c_3417_; lean_object* v_ys_3418_; 
v_c_3415_ = lean_ctor_get(v_x_3349_, 0);
v_ys_3416_ = lean_ctor_get(v_x_3349_, 1);
v_c_3417_ = lean_ctor_get(v_x_3350_, 0);
v_ys_3418_ = lean_ctor_get(v_x_3350_, 1);
v_c_u2081_3359_ = v_c_3415_;
v_ys_u2081_3360_ = v_ys_3416_;
v_c_u2082_3361_ = v_c_3417_;
v_ys_u2082_3362_ = v_ys_3418_;
goto v___jp_3358_;
}
else
{
uint8_t v___x_3419_; 
v___x_3419_ = 0;
return v___x_3419_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3350_) == 8)
{
lean_object* v_x_3420_; lean_object* v_ys_3421_; lean_object* v_x_3422_; lean_object* v_ys_3423_; uint8_t v___x_3424_; 
v_x_3420_ = lean_ctor_get(v_x_3349_, 0);
v_ys_3421_ = lean_ctor_get(v_x_3349_, 1);
v_x_3422_ = lean_ctor_get(v_x_3350_, 0);
v_ys_3423_ = lean_ctor_get(v_x_3350_, 1);
v___x_3424_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_3420_, v_x_3422_);
if (v___x_3424_ == 0)
{
return v___x_3424_;
}
else
{
uint8_t v___x_3425_; 
v___x_3425_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3348_, v_ys_3421_, v_ys_3423_);
return v___x_3425_;
}
}
else
{
uint8_t v___x_3426_; 
v___x_3426_ = 0;
return v___x_3426_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3350_) == 9)
{
lean_object* v_ty_3427_; lean_object* v_x_3428_; lean_object* v_ty_3429_; lean_object* v_x_3430_; uint8_t v___x_3431_; 
v_ty_3427_ = lean_ctor_get(v_x_3349_, 0);
v_x_3428_ = lean_ctor_get(v_x_3349_, 1);
v_ty_3429_ = lean_ctor_get(v_x_3350_, 0);
v_x_3430_ = lean_ctor_get(v_x_3350_, 1);
v___x_3431_ = l_Lean_IR_instBEqIRType_beq(v_ty_3427_, v_ty_3429_);
if (v___x_3431_ == 0)
{
return v___x_3431_;
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_3428_, v_x_3430_);
return v___x_3432_;
}
}
else
{
uint8_t v___x_3433_; 
v___x_3433_ = 0;
return v___x_3433_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3350_) == 10)
{
lean_object* v_x_3434_; lean_object* v_x_3435_; uint8_t v___x_3436_; 
v_x_3434_ = lean_ctor_get(v_x_3349_, 0);
v_x_3435_ = lean_ctor_get(v_x_3350_, 0);
v___x_3436_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_3434_, v_x_3435_);
return v___x_3436_;
}
else
{
uint8_t v___x_3437_; 
v___x_3437_ = 0;
return v___x_3437_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3350_) == 11)
{
lean_object* v_v_3438_; lean_object* v_v_3439_; uint8_t v___x_3440_; 
v_v_3438_ = lean_ctor_get(v_x_3349_, 0);
v_v_3439_ = lean_ctor_get(v_x_3350_, 0);
v___x_3440_ = l_Lean_IR_instBEqLitVal_beq(v_v_3438_, v_v_3439_);
return v___x_3440_;
}
else
{
uint8_t v___x_3441_; 
v___x_3441_ = 0;
return v___x_3441_;
}
}
default: 
{
if (lean_obj_tag(v_x_3350_) == 12)
{
lean_object* v_x_3442_; lean_object* v_x_3443_; uint8_t v___x_3444_; 
v_x_3442_ = lean_ctor_get(v_x_3349_, 0);
v_x_3443_ = lean_ctor_get(v_x_3350_, 0);
v___x_3444_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_3442_, v_x_3443_);
return v___x_3444_;
}
else
{
uint8_t v___x_3445_; 
v___x_3445_ = 0;
return v___x_3445_;
}
}
}
v___jp_3351_:
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_eq(v_n_u2081_3352_, v_n_u2082_3354_);
if (v___x_3356_ == 0)
{
return v___x_3356_;
}
else
{
uint8_t v___x_3357_; 
v___x_3357_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3348_, v_x_u2081_3353_, v_x_u2082_3355_);
return v___x_3357_;
}
}
v___jp_3358_:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_name_eq(v_c_u2081_3359_, v_c_u2082_3361_);
if (v___x_3363_ == 0)
{
return v___x_3363_;
}
else
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3348_, v_ys_u2081_3360_, v_ys_u2082_3362_);
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* v_00_u03c1_3446_, lean_object* v_x_3447_, lean_object* v_x_3448_){
_start:
{
uint8_t v_res_3449_; lean_object* v_r_3450_; 
v_res_3449_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_3446_, v_x_3447_, v_x_3448_);
lean_dec_ref(v_x_3448_);
lean_dec_ref(v_x_3447_);
lean_dec(v_00_u03c1_3446_);
v_r_3450_ = lean_box(v_res_3449_);
return v_r_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3453_, lean_object* v_x_u2081_3454_, lean_object* v_x_u2082_3455_){
_start:
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_nat_dec_eq(v_x_u2081_3454_, v_x_u2082_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3454_, v_x_u2082_3455_, v_00_u03c1_3453_);
return v___x_3457_;
}
else
{
lean_dec(v_x_u2082_3455_);
lean_dec(v_x_u2081_3454_);
return v_00_u03c1_3453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3458_, lean_object* v_p_u2081_3459_, lean_object* v_p_u2082_3460_){
_start:
{
lean_object* v_x_3461_; uint8_t v_borrow_3462_; lean_object* v_ty_3463_; lean_object* v_x_3464_; uint8_t v_borrow_3465_; lean_object* v_ty_3466_; uint8_t v___x_3470_; 
v_x_3461_ = lean_ctor_get(v_p_u2081_3459_, 0);
lean_inc(v_x_3461_);
v_borrow_3462_ = lean_ctor_get_uint8(v_p_u2081_3459_, sizeof(void*)*2);
v_ty_3463_ = lean_ctor_get(v_p_u2081_3459_, 1);
lean_inc(v_ty_3463_);
lean_dec_ref(v_p_u2081_3459_);
v_x_3464_ = lean_ctor_get(v_p_u2082_3460_, 0);
lean_inc(v_x_3464_);
v_borrow_3465_ = lean_ctor_get_uint8(v_p_u2082_3460_, sizeof(void*)*2);
v_ty_3466_ = lean_ctor_get(v_p_u2082_3460_, 1);
lean_inc(v_ty_3466_);
lean_dec_ref(v_p_u2082_3460_);
v___x_3470_ = l_Lean_IR_instBEqIRType_beq(v_ty_3463_, v_ty_3466_);
lean_dec(v_ty_3466_);
lean_dec(v_ty_3463_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec(v_x_3464_);
lean_dec(v_x_3461_);
lean_dec(v_00_u03c1_3458_);
v___x_3471_ = lean_box(0);
return v___x_3471_;
}
else
{
if (v_borrow_3465_ == 0)
{
if (v_borrow_3462_ == 0)
{
goto v___jp_3467_;
}
else
{
lean_object* v___x_3472_; 
lean_dec(v_x_3464_);
lean_dec(v_x_3461_);
lean_dec(v_00_u03c1_3458_);
v___x_3472_ = lean_box(0);
return v___x_3472_;
}
}
else
{
if (v_borrow_3462_ == 0)
{
lean_object* v___x_3473_; 
lean_dec(v_x_3464_);
lean_dec(v_x_3461_);
lean_dec(v_00_u03c1_3458_);
v___x_3473_ = lean_box(0);
return v___x_3473_;
}
else
{
goto v___jp_3467_;
}
}
}
v___jp_3467_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = l_Lean_IR_addVarRename(v_00_u03c1_3458_, v_x_3461_, v_x_3464_);
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3474_, lean_object* v_ps_u2081_3475_, lean_object* v_ps_u2082_3476_, lean_object* v_a_3477_, lean_object* v_b_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_nat_dec_lt(v_a_3477_, v_upperBound_3474_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec(v_a_3477_);
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_b_3478_);
return v___x_3480_;
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3481_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_3482_ = lean_array_get_borrowed(v___x_3481_, v_ps_u2081_3475_, v_a_3477_);
v___x_3483_ = lean_array_get_borrowed(v___x_3481_, v_ps_u2082_3476_, v_a_3477_);
lean_inc(v___x_3483_);
lean_inc(v___x_3482_);
v___x_3484_ = l_Lean_IR_addParamRename(v_b_3478_, v___x_3482_, v___x_3483_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_dec(v_a_3477_);
return v___x_3484_;
}
else
{
lean_object* v_val_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_val_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_val_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___x_3486_ = lean_unsigned_to_nat(1u);
v___x_3487_ = lean_nat_add(v_a_3477_, v___x_3486_);
lean_dec(v_a_3477_);
v_a_3477_ = v___x_3487_;
v_b_3478_ = v_val_3485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_3489_, lean_object* v_ps_u2081_3490_, lean_object* v_ps_u2082_3491_, lean_object* v_a_3492_, lean_object* v_b_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3489_, v_ps_u2081_3490_, v_ps_u2082_3491_, v_a_3492_, v_b_3493_);
lean_dec_ref(v_ps_u2082_3491_);
lean_dec_ref(v_ps_u2081_3490_);
lean_dec(v_upperBound_3489_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_3495_, lean_object* v_ps_u2081_3496_, lean_object* v_ps_u2082_3497_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3498_ = lean_array_get_size(v_ps_u2081_3496_);
v___x_3499_ = lean_array_get_size(v_ps_u2082_3497_);
v___x_3500_ = lean_nat_dec_eq(v___x_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v_00_u03c1_3495_);
v___x_3501_ = lean_box(0);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_3498_, v_ps_u2081_3496_, v_ps_u2082_3497_, v___x_3502_, v_00_u03c1_3495_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* v_00_u03c1_3504_, lean_object* v_ps_u2081_3505_, lean_object* v_ps_u2082_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_IR_addParamsRename(v_00_u03c1_3504_, v_ps_u2081_3505_, v_ps_u2082_3506_);
lean_dec_ref(v_ps_u2082_3506_);
lean_dec_ref(v_ps_u2081_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object* v_upperBound_3508_, lean_object* v_ps_u2081_3509_, lean_object* v_ps_u2082_3510_, lean_object* v_inst_3511_, lean_object* v_R_3512_, lean_object* v_a_3513_, lean_object* v_b_3514_, lean_object* v_c_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3508_, v_ps_u2081_3509_, v_ps_u2082_3510_, v_a_3513_, v_b_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object* v_upperBound_3517_, lean_object* v_ps_u2081_3518_, lean_object* v_ps_u2082_3519_, lean_object* v_inst_3520_, lean_object* v_R_3521_, lean_object* v_a_3522_, lean_object* v_b_3523_, lean_object* v_c_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(v_upperBound_3517_, v_ps_u2081_3518_, v_ps_u2082_3519_, v_inst_3520_, v_R_3521_, v_a_3522_, v_b_3523_, v_c_3524_);
lean_dec_ref(v_ps_u2082_3519_);
lean_dec_ref(v_ps_u2081_3518_);
lean_dec(v_upperBound_3517_);
return v_res_3525_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* v_x_3526_, lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
uint8_t v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v_00_u03c1_3538_; lean_object* v_x_u2081_3539_; lean_object* v_n_u2081_3540_; uint8_t v_c_u2081_3541_; uint8_t v_p_u2081_3542_; lean_object* v_b_u2081_3543_; lean_object* v_x_u2082_3544_; lean_object* v_n_u2082_3545_; uint8_t v_c_u2082_3546_; uint8_t v_p_u2082_3547_; lean_object* v_b_u2082_3548_; 
switch(lean_obj_tag(v_x_3527_))
{
case 0:
{
if (lean_obj_tag(v_x_3528_) == 0)
{
lean_object* v_x_3551_; lean_object* v_ty_3552_; lean_object* v_e_3553_; lean_object* v_b_3554_; lean_object* v_x_3555_; lean_object* v_ty_3556_; lean_object* v_e_3557_; lean_object* v_b_3558_; uint8_t v___x_3559_; 
v_x_3551_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3551_);
v_ty_3552_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_ty_3552_);
v_e_3553_ = lean_ctor_get(v_x_3527_, 2);
lean_inc_ref(v_e_3553_);
v_b_3554_ = lean_ctor_get(v_x_3527_, 3);
lean_inc(v_b_3554_);
lean_dec_ref_known(v_x_3527_, 4);
v_x_3555_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3555_);
v_ty_3556_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_ty_3556_);
v_e_3557_ = lean_ctor_get(v_x_3528_, 2);
lean_inc_ref(v_e_3557_);
v_b_3558_ = lean_ctor_get(v_x_3528_, 3);
lean_inc(v_b_3558_);
lean_dec_ref_known(v_x_3528_, 4);
v___x_3559_ = l_Lean_IR_instBEqIRType_beq(v_ty_3552_, v_ty_3556_);
lean_dec(v_ty_3556_);
lean_dec(v_ty_3552_);
if (v___x_3559_ == 0)
{
lean_dec(v_b_3558_);
lean_dec_ref(v_e_3557_);
lean_dec(v_x_3555_);
lean_dec(v_b_3554_);
lean_dec_ref(v_e_3553_);
lean_dec(v_x_3551_);
lean_dec(v_x_3526_);
return v___x_3559_;
}
else
{
uint8_t v___x_3560_; 
v___x_3560_ = l_Lean_IR_Expr_alphaEqv(v_x_3526_, v_e_3553_, v_e_3557_);
lean_dec_ref(v_e_3557_);
lean_dec_ref(v_e_3553_);
if (v___x_3560_ == 0)
{
lean_dec(v_b_3558_);
lean_dec(v_x_3555_);
lean_dec(v_b_3554_);
lean_dec(v_x_3551_);
lean_dec(v_x_3526_);
return v___x_3560_;
}
else
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Lean_IR_addVarRename(v_x_3526_, v_x_3551_, v_x_3555_);
v_x_3526_ = v___x_3561_;
v_x_3527_ = v_b_3554_;
v_x_3528_ = v_b_3558_;
goto _start;
}
}
}
else
{
uint8_t v___x_3563_; 
lean_dec_ref_known(v_x_3527_, 4);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3563_ = 0;
return v___x_3563_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3528_) == 1)
{
lean_object* v_j_3564_; lean_object* v_xs_3565_; lean_object* v_v_3566_; lean_object* v_b_3567_; lean_object* v_j_3568_; lean_object* v_xs_3569_; lean_object* v_v_3570_; lean_object* v_b_3571_; lean_object* v___x_3572_; 
v_j_3564_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_j_3564_);
v_xs_3565_ = lean_ctor_get(v_x_3527_, 1);
lean_inc_ref(v_xs_3565_);
v_v_3566_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_v_3566_);
v_b_3567_ = lean_ctor_get(v_x_3527_, 3);
lean_inc(v_b_3567_);
lean_dec_ref_known(v_x_3527_, 4);
v_j_3568_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_j_3568_);
v_xs_3569_ = lean_ctor_get(v_x_3528_, 1);
lean_inc_ref(v_xs_3569_);
v_v_3570_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_v_3570_);
v_b_3571_ = lean_ctor_get(v_x_3528_, 3);
lean_inc(v_b_3571_);
lean_dec_ref_known(v_x_3528_, 4);
lean_inc(v_x_3526_);
v___x_3572_ = l_Lean_IR_addParamsRename(v_x_3526_, v_xs_3565_, v_xs_3569_);
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
lean_dec(v_x_3526_);
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
lean_dec(v_x_3526_);
return v___x_3575_;
}
else
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_IR_addVarRename(v_x_3526_, v_j_3564_, v_j_3568_);
v_x_3526_ = v___x_3576_;
v_x_3527_ = v_b_3567_;
v_x_3528_ = v_b_3571_;
goto _start;
}
}
}
else
{
uint8_t v___x_3578_; 
lean_dec_ref_known(v_x_3527_, 4);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3578_ = 0;
return v___x_3578_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3528_) == 2)
{
lean_object* v_x_3579_; lean_object* v_i_3580_; lean_object* v_y_3581_; lean_object* v_b_3582_; lean_object* v_x_3583_; lean_object* v_i_3584_; lean_object* v_y_3585_; lean_object* v_b_3586_; uint8_t v___x_3587_; 
v_x_3579_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3579_);
v_i_3580_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_i_3580_);
v_y_3581_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_y_3581_);
v_b_3582_ = lean_ctor_get(v_x_3527_, 3);
lean_inc(v_b_3582_);
lean_dec_ref_known(v_x_3527_, 4);
v_x_3583_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3583_);
v_i_3584_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_i_3584_);
v_y_3585_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_y_3585_);
v_b_3586_ = lean_ctor_get(v_x_3528_, 3);
lean_inc(v_b_3586_);
lean_dec_ref_known(v_x_3528_, 4);
v___x_3587_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_x_3579_, v_x_3583_);
lean_dec(v_x_3583_);
lean_dec(v_x_3579_);
if (v___x_3587_ == 0)
{
lean_dec(v_b_3586_);
lean_dec(v_y_3585_);
lean_dec(v_i_3584_);
lean_dec(v_b_3582_);
lean_dec(v_y_3581_);
lean_dec(v_i_3580_);
lean_dec(v_x_3526_);
return v___x_3587_;
}
else
{
uint8_t v___x_3588_; 
v___x_3588_ = lean_nat_dec_eq(v_i_3580_, v_i_3584_);
lean_dec(v_i_3584_);
lean_dec(v_i_3580_);
if (v___x_3588_ == 0)
{
lean_dec(v_b_3586_);
lean_dec(v_y_3585_);
lean_dec(v_b_3582_);
lean_dec(v_y_3581_);
lean_dec(v_x_3526_);
return v___x_3588_;
}
else
{
uint8_t v___x_3589_; 
v___x_3589_ = l_Lean_IR_Arg_alphaEqv(v_x_3526_, v_y_3581_, v_y_3585_);
lean_dec(v_y_3585_);
lean_dec(v_y_3581_);
if (v___x_3589_ == 0)
{
lean_dec(v_b_3586_);
lean_dec(v_b_3582_);
lean_dec(v_x_3526_);
return v___x_3589_;
}
else
{
v_x_3527_ = v_b_3582_;
v_x_3528_ = v_b_3586_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3591_; 
lean_dec_ref_known(v_x_3527_, 4);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3591_ = 0;
return v___x_3591_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3528_) == 3)
{
lean_object* v_x_3592_; lean_object* v_cidx_3593_; lean_object* v_b_3594_; lean_object* v_x_3595_; lean_object* v_cidx_3596_; lean_object* v_b_3597_; uint8_t v___x_3598_; 
v_x_3592_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3592_);
v_cidx_3593_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_cidx_3593_);
v_b_3594_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_b_3594_);
lean_dec_ref_known(v_x_3527_, 3);
v_x_3595_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3595_);
v_cidx_3596_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_cidx_3596_);
v_b_3597_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_b_3597_);
lean_dec_ref_known(v_x_3528_, 3);
v___x_3598_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_x_3592_, v_x_3595_);
lean_dec(v_x_3595_);
lean_dec(v_x_3592_);
if (v___x_3598_ == 0)
{
lean_dec(v_b_3597_);
lean_dec(v_cidx_3596_);
lean_dec(v_b_3594_);
lean_dec(v_cidx_3593_);
lean_dec(v_x_3526_);
return v___x_3598_;
}
else
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_nat_dec_eq(v_cidx_3593_, v_cidx_3596_);
lean_dec(v_cidx_3596_);
lean_dec(v_cidx_3593_);
if (v___x_3599_ == 0)
{
lean_dec(v_b_3597_);
lean_dec(v_b_3594_);
lean_dec(v_x_3526_);
return v___x_3599_;
}
else
{
v_x_3527_ = v_b_3594_;
v_x_3528_ = v_b_3597_;
goto _start;
}
}
}
else
{
uint8_t v___x_3601_; 
lean_dec_ref_known(v_x_3527_, 3);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3601_ = 0;
return v___x_3601_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3528_) == 4)
{
lean_object* v_x_3602_; lean_object* v_i_3603_; lean_object* v_y_3604_; lean_object* v_b_3605_; lean_object* v_x_3606_; lean_object* v_i_3607_; lean_object* v_y_3608_; lean_object* v_b_3609_; uint8_t v___x_3610_; 
v_x_3602_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3602_);
v_i_3603_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_i_3603_);
v_y_3604_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_y_3604_);
v_b_3605_ = lean_ctor_get(v_x_3527_, 3);
lean_inc(v_b_3605_);
lean_dec_ref_known(v_x_3527_, 4);
v_x_3606_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3606_);
v_i_3607_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_i_3607_);
v_y_3608_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_y_3608_);
v_b_3609_ = lean_ctor_get(v_x_3528_, 3);
lean_inc(v_b_3609_);
lean_dec_ref_known(v_x_3528_, 4);
v___x_3610_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_x_3602_, v_x_3606_);
lean_dec(v_x_3606_);
lean_dec(v_x_3602_);
if (v___x_3610_ == 0)
{
lean_dec(v_b_3609_);
lean_dec(v_y_3608_);
lean_dec(v_i_3607_);
lean_dec(v_b_3605_);
lean_dec(v_y_3604_);
lean_dec(v_i_3603_);
lean_dec(v_x_3526_);
return v___x_3610_;
}
else
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_eq(v_i_3603_, v_i_3607_);
lean_dec(v_i_3607_);
lean_dec(v_i_3603_);
if (v___x_3611_ == 0)
{
lean_dec(v_b_3609_);
lean_dec(v_y_3608_);
lean_dec(v_b_3605_);
lean_dec(v_y_3604_);
lean_dec(v_x_3526_);
return v___x_3611_;
}
else
{
uint8_t v___x_3612_; 
v___x_3612_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_y_3604_, v_y_3608_);
lean_dec(v_y_3608_);
lean_dec(v_y_3604_);
if (v___x_3612_ == 0)
{
lean_dec(v_b_3609_);
lean_dec(v_b_3605_);
lean_dec(v_x_3526_);
return v___x_3612_;
}
else
{
v_x_3527_ = v_b_3605_;
v_x_3528_ = v_b_3609_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3614_; 
lean_dec_ref_known(v_x_3527_, 4);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3614_ = 0;
return v___x_3614_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3528_) == 5)
{
lean_object* v_x_3615_; lean_object* v_i_3616_; lean_object* v_offset_3617_; lean_object* v_y_3618_; lean_object* v_ty_3619_; lean_object* v_b_3620_; lean_object* v_x_3621_; lean_object* v_i_3622_; lean_object* v_offset_3623_; lean_object* v_y_3624_; lean_object* v_ty_3625_; lean_object* v_b_3626_; uint8_t v___x_3627_; 
v_x_3615_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3615_);
v_i_3616_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_i_3616_);
v_offset_3617_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_offset_3617_);
v_y_3618_ = lean_ctor_get(v_x_3527_, 3);
lean_inc(v_y_3618_);
v_ty_3619_ = lean_ctor_get(v_x_3527_, 4);
lean_inc(v_ty_3619_);
v_b_3620_ = lean_ctor_get(v_x_3527_, 5);
lean_inc(v_b_3620_);
lean_dec_ref_known(v_x_3527_, 6);
v_x_3621_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3621_);
v_i_3622_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_i_3622_);
v_offset_3623_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_offset_3623_);
v_y_3624_ = lean_ctor_get(v_x_3528_, 3);
lean_inc(v_y_3624_);
v_ty_3625_ = lean_ctor_get(v_x_3528_, 4);
lean_inc(v_ty_3625_);
v_b_3626_ = lean_ctor_get(v_x_3528_, 5);
lean_inc(v_b_3626_);
lean_dec_ref_known(v_x_3528_, 6);
v___x_3627_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_x_3615_, v_x_3621_);
lean_dec(v_x_3621_);
lean_dec(v_x_3615_);
if (v___x_3627_ == 0)
{
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_y_3624_);
lean_dec(v_offset_3623_);
lean_dec(v_i_3622_);
lean_dec(v_b_3620_);
lean_dec(v_ty_3619_);
lean_dec(v_y_3618_);
lean_dec(v_offset_3617_);
lean_dec(v_i_3616_);
lean_dec(v_x_3526_);
return v___x_3627_;
}
else
{
uint8_t v___x_3628_; 
v___x_3628_ = lean_nat_dec_eq(v_i_3616_, v_i_3622_);
lean_dec(v_i_3622_);
lean_dec(v_i_3616_);
if (v___x_3628_ == 0)
{
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_y_3624_);
lean_dec(v_offset_3623_);
lean_dec(v_b_3620_);
lean_dec(v_ty_3619_);
lean_dec(v_y_3618_);
lean_dec(v_offset_3617_);
lean_dec(v_x_3526_);
return v___x_3628_;
}
else
{
uint8_t v___x_3629_; 
v___x_3629_ = lean_nat_dec_eq(v_offset_3617_, v_offset_3623_);
lean_dec(v_offset_3623_);
lean_dec(v_offset_3617_);
if (v___x_3629_ == 0)
{
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_y_3624_);
lean_dec(v_b_3620_);
lean_dec(v_ty_3619_);
lean_dec(v_y_3618_);
lean_dec(v_x_3526_);
return v___x_3629_;
}
else
{
uint8_t v___x_3630_; 
v___x_3630_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_y_3618_, v_y_3624_);
lean_dec(v_y_3624_);
lean_dec(v_y_3618_);
if (v___x_3630_ == 0)
{
lean_dec(v_b_3626_);
lean_dec(v_ty_3625_);
lean_dec(v_b_3620_);
lean_dec(v_ty_3619_);
lean_dec(v_x_3526_);
return v___x_3630_;
}
else
{
uint8_t v___x_3631_; 
v___x_3631_ = l_Lean_IR_instBEqIRType_beq(v_ty_3619_, v_ty_3625_);
lean_dec(v_ty_3625_);
lean_dec(v_ty_3619_);
if (v___x_3631_ == 0)
{
lean_dec(v_b_3626_);
lean_dec(v_b_3620_);
lean_dec(v_x_3526_);
return v___x_3631_;
}
else
{
v_x_3527_ = v_b_3620_;
v_x_3528_ = v_b_3626_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_3633_; 
lean_dec_ref_known(v_x_3527_, 6);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3633_ = 0;
return v___x_3633_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3528_) == 6)
{
lean_object* v_x_3634_; lean_object* v_n_3635_; uint8_t v_c_3636_; uint8_t v_persistent_3637_; lean_object* v_b_3638_; lean_object* v_x_3639_; lean_object* v_n_3640_; uint8_t v_c_3641_; uint8_t v_persistent_3642_; lean_object* v_b_3643_; 
v_x_3634_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3634_);
v_n_3635_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_n_3635_);
v_c_3636_ = lean_ctor_get_uint8(v_x_3527_, sizeof(void*)*3);
v_persistent_3637_ = lean_ctor_get_uint8(v_x_3527_, sizeof(void*)*3 + 1);
v_b_3638_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_b_3638_);
lean_dec_ref_known(v_x_3527_, 3);
v_x_3639_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3639_);
v_n_3640_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_n_3640_);
v_c_3641_ = lean_ctor_get_uint8(v_x_3528_, sizeof(void*)*3);
v_persistent_3642_ = lean_ctor_get_uint8(v_x_3528_, sizeof(void*)*3 + 1);
v_b_3643_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_b_3643_);
lean_dec_ref_known(v_x_3528_, 3);
v_00_u03c1_3538_ = v_x_3526_;
v_x_u2081_3539_ = v_x_3634_;
v_n_u2081_3540_ = v_n_3635_;
v_c_u2081_3541_ = v_c_3636_;
v_p_u2081_3542_ = v_persistent_3637_;
v_b_u2081_3543_ = v_b_3638_;
v_x_u2082_3544_ = v_x_3639_;
v_n_u2082_3545_ = v_n_3640_;
v_c_u2082_3546_ = v_c_3641_;
v_p_u2082_3547_ = v_persistent_3642_;
v_b_u2082_3548_ = v_b_3643_;
goto v___jp_3537_;
}
else
{
uint8_t v___x_3644_; 
lean_dec_ref_known(v_x_3527_, 3);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3644_ = 0;
return v___x_3644_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3528_) == 7)
{
lean_object* v_x_3645_; lean_object* v_n_3646_; uint8_t v_c_3647_; uint8_t v_persistent_3648_; lean_object* v_b_3649_; lean_object* v_x_3650_; lean_object* v_n_3651_; uint8_t v_c_3652_; uint8_t v_persistent_3653_; lean_object* v_b_3654_; 
v_x_3645_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3645_);
v_n_3646_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_n_3646_);
v_c_3647_ = lean_ctor_get_uint8(v_x_3527_, sizeof(void*)*3);
v_persistent_3648_ = lean_ctor_get_uint8(v_x_3527_, sizeof(void*)*3 + 1);
v_b_3649_ = lean_ctor_get(v_x_3527_, 2);
lean_inc(v_b_3649_);
lean_dec_ref_known(v_x_3527_, 3);
v_x_3650_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3650_);
v_n_3651_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_n_3651_);
v_c_3652_ = lean_ctor_get_uint8(v_x_3528_, sizeof(void*)*3);
v_persistent_3653_ = lean_ctor_get_uint8(v_x_3528_, sizeof(void*)*3 + 1);
v_b_3654_ = lean_ctor_get(v_x_3528_, 2);
lean_inc(v_b_3654_);
lean_dec_ref_known(v_x_3528_, 3);
v_00_u03c1_3538_ = v_x_3526_;
v_x_u2081_3539_ = v_x_3645_;
v_n_u2081_3540_ = v_n_3646_;
v_c_u2081_3541_ = v_c_3647_;
v_p_u2081_3542_ = v_persistent_3648_;
v_b_u2081_3543_ = v_b_3649_;
v_x_u2082_3544_ = v_x_3650_;
v_n_u2082_3545_ = v_n_3651_;
v_c_u2082_3546_ = v_c_3652_;
v_p_u2082_3547_ = v_persistent_3653_;
v_b_u2082_3548_ = v_b_3654_;
goto v___jp_3537_;
}
else
{
uint8_t v___x_3655_; 
lean_dec_ref_known(v_x_3527_, 3);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3655_ = 0;
return v___x_3655_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3528_) == 8)
{
lean_object* v_x_3656_; lean_object* v_b_3657_; lean_object* v_x_3658_; lean_object* v_b_3659_; uint8_t v___x_3660_; 
v_x_3656_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3656_);
v_b_3657_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_b_3657_);
lean_dec_ref_known(v_x_3527_, 2);
v_x_3658_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3658_);
v_b_3659_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_b_3659_);
lean_dec_ref_known(v_x_3528_, 2);
v___x_3660_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_x_3656_, v_x_3658_);
lean_dec(v_x_3658_);
lean_dec(v_x_3656_);
if (v___x_3660_ == 0)
{
lean_dec(v_b_3659_);
lean_dec(v_b_3657_);
lean_dec(v_x_3526_);
return v___x_3660_;
}
else
{
v_x_3527_ = v_b_3657_;
v_x_3528_ = v_b_3659_;
goto _start;
}
}
else
{
uint8_t v___x_3662_; 
lean_dec_ref_known(v_x_3527_, 2);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3662_ = 0;
return v___x_3662_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3528_) == 9)
{
lean_object* v_tid_3663_; lean_object* v_x_3664_; lean_object* v_cs_3665_; lean_object* v_tid_3666_; lean_object* v_x_3667_; lean_object* v_cs_3668_; uint8_t v___x_3669_; 
v_tid_3663_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_tid_3663_);
v_x_3664_ = lean_ctor_get(v_x_3527_, 1);
lean_inc(v_x_3664_);
v_cs_3665_ = lean_ctor_get(v_x_3527_, 3);
lean_inc_ref(v_cs_3665_);
lean_dec_ref_known(v_x_3527_, 4);
v_tid_3666_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_tid_3666_);
v_x_3667_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_x_3667_);
v_cs_3668_ = lean_ctor_get(v_x_3528_, 3);
lean_inc_ref(v_cs_3668_);
lean_dec_ref_known(v_x_3528_, 4);
v___x_3669_ = lean_name_eq(v_tid_3663_, v_tid_3666_);
lean_dec(v_tid_3666_);
lean_dec(v_tid_3663_);
if (v___x_3669_ == 0)
{
lean_dec_ref(v_cs_3668_);
lean_dec(v_x_3667_);
lean_dec_ref(v_cs_3665_);
lean_dec(v_x_3664_);
lean_dec(v_x_3526_);
return v___x_3669_;
}
else
{
uint8_t v___x_3670_; 
v___x_3670_ = l_Lean_IR_VarId_alphaEqv(v_x_3526_, v_x_3664_, v_x_3667_);
lean_dec(v_x_3667_);
lean_dec(v_x_3664_);
if (v___x_3670_ == 0)
{
lean_dec_ref(v_cs_3668_);
lean_dec_ref(v_cs_3665_);
lean_dec(v_x_3526_);
return v___x_3670_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v___x_3671_ = lean_array_get_size(v_cs_3665_);
v___x_3672_ = lean_array_get_size(v_cs_3668_);
v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_dec_ref(v_cs_3668_);
lean_dec_ref(v_cs_3665_);
lean_dec(v_x_3526_);
return v___x_3673_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3526_, v_cs_3665_, v_cs_3668_, v___x_3671_);
lean_dec_ref(v_cs_3668_);
lean_dec_ref(v_cs_3665_);
return v___x_3674_;
}
}
}
}
else
{
uint8_t v___x_3675_; 
lean_dec_ref_known(v_x_3527_, 4);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3675_ = 0;
return v___x_3675_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3528_) == 10)
{
lean_object* v_x_3676_; lean_object* v_x_3677_; uint8_t v___x_3678_; 
v_x_3676_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_x_3676_);
lean_dec_ref_known(v_x_3527_, 1);
v_x_3677_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_x_3677_);
lean_dec_ref_known(v_x_3528_, 1);
v___x_3678_ = l_Lean_IR_Arg_alphaEqv(v_x_3526_, v_x_3676_, v_x_3677_);
lean_dec(v_x_3677_);
lean_dec(v_x_3676_);
lean_dec(v_x_3526_);
return v___x_3678_;
}
else
{
uint8_t v___x_3679_; 
lean_dec_ref_known(v_x_3527_, 1);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3679_ = 0;
return v___x_3679_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3528_) == 11)
{
lean_object* v_j_3680_; lean_object* v_ys_3681_; lean_object* v_j_3682_; lean_object* v_ys_3683_; uint8_t v___x_3684_; 
v_j_3680_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_j_3680_);
v_ys_3681_ = lean_ctor_get(v_x_3527_, 1);
lean_inc_ref(v_ys_3681_);
lean_dec_ref_known(v_x_3527_, 2);
v_j_3682_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_j_3682_);
v_ys_3683_ = lean_ctor_get(v_x_3528_, 1);
lean_inc_ref(v_ys_3683_);
lean_dec_ref_known(v_x_3528_, 2);
v___x_3684_ = lean_nat_dec_eq(v_j_3680_, v_j_3682_);
lean_dec(v_j_3682_);
lean_dec(v_j_3680_);
if (v___x_3684_ == 0)
{
lean_dec_ref(v_ys_3683_);
lean_dec_ref(v_ys_3681_);
lean_dec(v_x_3526_);
return v___x_3684_;
}
else
{
uint8_t v___x_3685_; 
v___x_3685_ = l_Lean_IR_args_alphaEqv(v_x_3526_, v_ys_3681_, v_ys_3683_);
lean_dec_ref(v_ys_3683_);
lean_dec_ref(v_ys_3681_);
lean_dec(v_x_3526_);
return v___x_3685_;
}
}
else
{
uint8_t v___x_3686_; 
lean_dec_ref_known(v_x_3527_, 2);
lean_dec(v_x_3528_);
lean_dec(v_x_3526_);
v___x_3686_ = 0;
return v___x_3686_;
}
}
default: 
{
lean_dec(v_x_3526_);
if (lean_obj_tag(v_x_3528_) == 12)
{
uint8_t v___x_3687_; 
v___x_3687_ = 1;
return v___x_3687_;
}
else
{
uint8_t v___x_3688_; 
lean_dec(v_x_3528_);
v___x_3688_ = 0;
return v___x_3688_;
}
}
}
v___jp_3529_:
{
if (v___y_3530_ == 0)
{
if (v___y_3534_ == 0)
{
v_x_3526_ = v___y_3531_;
v_x_3527_ = v___y_3533_;
v_x_3528_ = v___y_3532_;
goto _start;
}
else
{
lean_dec(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec(v___y_3531_);
return v___y_3530_;
}
}
else
{
if (v___y_3534_ == 0)
{
lean_dec(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec(v___y_3531_);
return v___y_3534_;
}
else
{
v_x_3526_ = v___y_3531_;
v_x_3527_ = v___y_3533_;
v_x_3528_ = v___y_3532_;
goto _start;
}
}
}
v___jp_3537_:
{
uint8_t v___x_3549_; 
v___x_3549_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3538_, v_x_u2081_3539_, v_x_u2082_3544_);
lean_dec(v_x_u2082_3544_);
lean_dec(v_x_u2081_3539_);
if (v___x_3549_ == 0)
{
lean_dec(v_b_u2082_3548_);
lean_dec(v_n_u2082_3545_);
lean_dec(v_b_u2081_3543_);
lean_dec(v_n_u2081_3540_);
lean_dec(v_00_u03c1_3538_);
return v___x_3549_;
}
else
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_nat_dec_eq(v_n_u2081_3540_, v_n_u2082_3545_);
lean_dec(v_n_u2082_3545_);
lean_dec(v_n_u2081_3540_);
if (v___x_3550_ == 0)
{
lean_dec(v_b_u2082_3548_);
lean_dec(v_b_u2081_3543_);
lean_dec(v_00_u03c1_3538_);
return v___x_3550_;
}
else
{
if (v_c_u2082_3546_ == 0)
{
if (v_c_u2081_3541_ == 0)
{
v___y_3530_ = v_p_u2082_3547_;
v___y_3531_ = v_00_u03c1_3538_;
v___y_3532_ = v_b_u2082_3548_;
v___y_3533_ = v_b_u2081_3543_;
v___y_3534_ = v_p_u2081_3542_;
goto v___jp_3529_;
}
else
{
lean_dec(v_b_u2082_3548_);
lean_dec(v_b_u2081_3543_);
lean_dec(v_00_u03c1_3538_);
return v_c_u2082_3546_;
}
}
else
{
if (v_c_u2081_3541_ == 0)
{
lean_dec(v_b_u2082_3548_);
lean_dec(v_b_u2081_3543_);
lean_dec(v_00_u03c1_3538_);
return v_c_u2081_3541_;
}
else
{
v___y_3530_ = v_p_u2082_3547_;
v___y_3531_ = v_00_u03c1_3538_;
v___y_3532_ = v_b_u2082_3548_;
v___y_3533_ = v_b_u2081_3543_;
v___y_3534_ = v_p_u2081_3542_;
goto v___jp_3529_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* v_x_3689_, lean_object* v_xs_3690_, lean_object* v_ys_3691_, lean_object* v_x_3692_){
_start:
{
lean_object* v_zero_3693_; uint8_t v_isZero_3694_; 
v_zero_3693_ = lean_unsigned_to_nat(0u);
v_isZero_3694_ = lean_nat_dec_eq(v_x_3692_, v_zero_3693_);
if (v_isZero_3694_ == 1)
{
lean_dec(v_x_3692_);
lean_dec(v_x_3689_);
return v_isZero_3694_;
}
else
{
lean_object* v_one_3695_; lean_object* v_n_3696_; uint8_t v___y_3698_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_one_3695_ = lean_unsigned_to_nat(1u);
v_n_3696_ = lean_nat_sub(v_x_3692_, v_one_3695_);
lean_dec(v_x_3692_);
v___x_3700_ = lean_array_fget_borrowed(v_xs_3690_, v_n_3696_);
v___x_3701_ = lean_array_fget_borrowed(v_ys_3691_, v_n_3696_);
if (lean_obj_tag(v___x_3700_) == 0)
{
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_info_3702_; lean_object* v_b_3703_; lean_object* v_info_3704_; lean_object* v_b_3705_; uint8_t v___x_3706_; 
v_info_3702_ = lean_ctor_get(v___x_3700_, 0);
v_b_3703_ = lean_ctor_get(v___x_3700_, 1);
v_info_3704_ = lean_ctor_get(v___x_3701_, 0);
v_b_3705_ = lean_ctor_get(v___x_3701_, 1);
v___x_3706_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_3702_, v_info_3704_);
if (v___x_3706_ == 0)
{
lean_dec(v_n_3696_);
lean_dec(v_x_3689_);
return v___x_3706_;
}
else
{
uint8_t v___x_3707_; 
lean_inc(v_b_3705_);
lean_inc(v_b_3703_);
lean_inc(v_x_3689_);
v___x_3707_ = l_Lean_IR_FnBody_alphaEqv(v_x_3689_, v_b_3703_, v_b_3705_);
v___y_3698_ = v___x_3707_;
goto v___jp_3697_;
}
}
else
{
lean_dec(v_n_3696_);
lean_dec(v_x_3689_);
return v_isZero_3694_;
}
}
else
{
if (lean_obj_tag(v___x_3701_) == 1)
{
lean_object* v_b_3708_; lean_object* v_b_3709_; uint8_t v___x_3710_; 
v_b_3708_ = lean_ctor_get(v___x_3700_, 0);
v_b_3709_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_b_3709_);
lean_inc(v_b_3708_);
lean_inc(v_x_3689_);
v___x_3710_ = l_Lean_IR_FnBody_alphaEqv(v_x_3689_, v_b_3708_, v_b_3709_);
v___y_3698_ = v___x_3710_;
goto v___jp_3697_;
}
else
{
lean_dec(v_n_3696_);
lean_dec(v_x_3689_);
return v_isZero_3694_;
}
}
v___jp_3697_:
{
if (v___y_3698_ == 0)
{
lean_dec(v_n_3696_);
lean_dec(v_x_3689_);
return v___y_3698_;
}
else
{
v_x_3692_ = v_n_3696_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* v_x_3711_, lean_object* v_xs_3712_, lean_object* v_ys_3713_, lean_object* v_x_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3711_, v_xs_3712_, v_ys_3713_, v_x_3714_);
lean_dec_ref(v_ys_3713_);
lean_dec_ref(v_xs_3712_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* v_x_3717_, lean_object* v_x_3718_, lean_object* v_x_3719_){
_start:
{
uint8_t v_res_3720_; lean_object* v_r_3721_; 
v_res_3720_ = l_Lean_IR_FnBody_alphaEqv(v_x_3717_, v_x_3718_, v_x_3719_);
v_r_3721_ = lean_box(v_res_3720_);
return v_r_3721_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object* v_x_3722_, lean_object* v_xs_3723_, lean_object* v_ys_3724_, lean_object* v_hsz_3725_, lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3722_, v_xs_3723_, v_ys_3724_, v_x_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* v_x_3729_, lean_object* v_xs_3730_, lean_object* v_ys_3731_, lean_object* v_hsz_3732_, lean_object* v_x_3733_, lean_object* v_x_3734_){
_start:
{
uint8_t v_res_3735_; lean_object* v_r_3736_; 
v_res_3735_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(v_x_3729_, v_xs_3730_, v_ys_3731_, v_hsz_3732_, v_x_3733_, v_x_3734_);
lean_dec_ref(v_ys_3731_);
lean_dec_ref(v_xs_3730_);
v_r_3736_ = lean_box(v_res_3735_);
return v_r_3736_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* v_b_u2081_3737_, lean_object* v_b_u2082_3738_){
_start:
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = lean_box(1);
v___x_3740_ = l_Lean_IR_FnBody_alphaEqv(v___x_3739_, v_b_u2081_3737_, v_b_u2082_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* v_b_u2081_3741_, lean_object* v_b_u2082_3742_){
_start:
{
uint8_t v_res_3743_; lean_object* v_r_3744_; 
v_res_3743_ = l_Lean_IR_FnBody_beq(v_b_u2081_3741_, v_b_u2082_3742_);
v_r_3744_ = lean_box(v_res_3743_);
return v_r_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* v_x_3765_, lean_object* v_t_3766_, lean_object* v_e_3767_){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3768_ = ((lean_object*)(l_Lean_IR_mkIf___closed__1));
v___x_3769_ = lean_box(1);
v___x_3770_ = ((lean_object*)(l_Lean_IR_mkIf___closed__4));
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v_e_3767_);
v___x_3772_ = ((lean_object*)(l_Lean_IR_mkIf___closed__7));
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v_t_3766_);
v___x_3774_ = lean_unsigned_to_nat(2u);
v___x_3775_ = lean_mk_empty_array_with_capacity(v___x_3774_);
v___x_3776_ = lean_array_push(v___x_3775_, v___x_3771_);
v___x_3777_ = lean_array_push(v___x_3776_, v___x_3773_);
v___x_3778_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3768_);
lean_ctor_set(v___x_3778_, 1, v_x_3765_);
lean_ctor_set(v___x_3778_, 2, v___x_3769_);
lean_ctor_set(v___x_3778_, 3, v___x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* v_t_3785_){
_start:
{
switch(lean_obj_tag(v_t_3785_))
{
case 5:
{
lean_object* v___x_3786_; 
v___x_3786_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__0));
return v___x_3786_;
}
case 3:
{
lean_object* v___x_3787_; 
v___x_3787_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__1));
return v___x_3787_;
}
case 4:
{
lean_object* v___x_3788_; 
v___x_3788_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__2));
return v___x_3788_;
}
case 0:
{
lean_object* v___x_3789_; 
v___x_3789_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__3));
return v___x_3789_;
}
case 9:
{
lean_object* v___x_3790_; 
v___x_3790_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__4));
return v___x_3790_;
}
default: 
{
lean_object* v___x_3791_; 
v___x_3791_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__5));
return v___x_3791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* v_t_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_IR_getUnboxOpName(v_t_3792_);
lean_dec(v_t_3792_);
return v_res_3793_;
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
