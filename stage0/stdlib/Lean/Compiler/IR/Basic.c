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
v___x_2208_ = lean_nat_add(v___y_2205_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec(v___y_2205_);
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
lean_ctor_set(v___x_2188_, 3, v___y_2206_);
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
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v___y_2206_);
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
v___y_2205_ = v___x_2221_;
v___y_2206_ = v___x_2220_;
v___y_2207_ = v_size_2222_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___y_2205_ = v___x_2221_;
v___y_2206_ = v___x_2220_;
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
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_le(v___x_2449_, v___x_2449_);
if (v___x_2451_ == 0)
{
if (v___x_2450_ == 0)
{
return v_ctx_2446_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2449_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2447_, v___x_2452_, v___x_2453_, v_ctx_2446_);
return v___x_2454_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2449_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_2447_, v___x_2455_, v___x_2456_, v_ctx_2446_);
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* v_ctx_2458_, lean_object* v_ps_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_IR_LocalContext_addParams(v_ctx_2458_, v_ps_2459_);
lean_dec_ref(v_ps_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* v_ctx_2461_, lean_object* v_j_2462_){
_start:
{
lean_object* v_jps_2463_; uint8_t v___x_2464_; 
v_jps_2463_ = lean_ctor_get(v_ctx_2461_, 1);
v___x_2464_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(v_j_2462_, v_jps_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* v_ctx_2465_, lean_object* v_j_2466_){
_start:
{
uint8_t v_res_2467_; lean_object* v_r_2468_; 
v_res_2467_ = l_Lean_IR_LocalContext_isJP(v_ctx_2465_, v_j_2466_);
lean_dec(v_j_2466_);
lean_dec_ref(v_ctx_2465_);
v_r_2468_ = lean_box(v_res_2467_);
return v_r_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(lean_object* v_t_2469_, lean_object* v_k_2470_){
_start:
{
if (lean_obj_tag(v_t_2469_) == 0)
{
lean_object* v_k_2471_; lean_object* v_v_2472_; lean_object* v_l_2473_; lean_object* v_r_2474_; uint8_t v___x_2475_; 
v_k_2471_ = lean_ctor_get(v_t_2469_, 1);
v_v_2472_ = lean_ctor_get(v_t_2469_, 2);
v_l_2473_ = lean_ctor_get(v_t_2469_, 3);
v_r_2474_ = lean_ctor_get(v_t_2469_, 4);
v___x_2475_ = lean_nat_dec_lt(v_k_2470_, v_k_2471_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_nat_dec_eq(v_k_2470_, v_k_2471_);
if (v___x_2476_ == 0)
{
v_t_2469_ = v_r_2474_;
goto _start;
}
else
{
lean_object* v___x_2478_; 
lean_inc(v_v_2472_);
v___x_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_v_2472_);
return v___x_2478_;
}
}
else
{
v_t_2469_ = v_l_2473_;
goto _start;
}
}
else
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_box(0);
return v___x_2480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg___boxed(lean_object* v_t_2481_, lean_object* v_k_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_2481_, v_k_2482_);
lean_dec(v_k_2482_);
lean_dec(v_t_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* v_ctx_2484_, lean_object* v_j_2485_){
_start:
{
lean_object* v_jps_2486_; lean_object* v___x_2487_; 
v_jps_2486_ = lean_ctor_get(v_ctx_2484_, 1);
v___x_2487_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_2486_, v_j_2485_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_box(0);
return v___x_2488_;
}
else
{
lean_object* v_val_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
v_val_2489_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v___x_2487_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_val_2489_);
lean_dec(v___x_2487_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_snd_2493_; lean_object* v___x_2495_; 
v_snd_2493_ = lean_ctor_get(v_val_2489_, 1);
lean_inc(v_snd_2493_);
lean_dec(v_val_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v_snd_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_snd_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* v_ctx_2498_, lean_object* v_j_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_2498_, v_j_2499_);
lean_dec(v_j_2499_);
lean_dec_ref(v_ctx_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(lean_object* v_00_u03b4_2501_, lean_object* v_t_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_t_2502_, v_k_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___boxed(lean_object* v_00_u03b4_2505_, lean_object* v_t_2506_, lean_object* v_k_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0(v_00_u03b4_2505_, v_t_2506_, v_k_2507_);
lean_dec(v_k_2507_);
lean_dec(v_t_2506_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* v_ctx_2509_, lean_object* v_j_2510_){
_start:
{
lean_object* v_jps_2511_; lean_object* v___x_2512_; 
v_jps_2511_ = lean_ctor_get(v_ctx_2509_, 1);
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_jps_2511_, v_j_2510_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
else
{
lean_object* v_val_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
v_val_2514_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v___x_2512_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_val_2514_);
lean_dec(v___x_2512_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_fst_2518_; lean_object* v___x_2520_; 
v_fst_2518_ = lean_ctor_get(v_val_2514_, 0);
lean_inc(v_fst_2518_);
lean_dec(v_val_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v_fst_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_fst_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* v_ctx_2523_, lean_object* v_j_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_2523_, v_j_2524_);
lean_dec(v_j_2524_);
lean_dec_ref(v_ctx_2523_);
return v_res_2525_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* v_ctx_2526_, lean_object* v_x_2527_){
_start:
{
lean_object* v_vars_2528_; lean_object* v___x_2529_; 
v_vars_2528_ = lean_ctor_get(v_ctx_2526_, 0);
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_2528_, v_x_2527_);
if (lean_obj_tag(v___x_2529_) == 1)
{
lean_object* v_val_2530_; 
v_val_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v___x_2529_, 1);
if (lean_obj_tag(v_val_2530_) == 0)
{
uint8_t v___x_2531_; 
lean_dec_ref_known(v_val_2530_, 1);
v___x_2531_ = 1;
return v___x_2531_;
}
else
{
uint8_t v___x_2532_; 
lean_dec(v_val_2530_);
v___x_2532_ = 0;
return v___x_2532_;
}
}
else
{
uint8_t v___x_2533_; 
lean_dec(v___x_2529_);
v___x_2533_ = 0;
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* v_ctx_2534_, lean_object* v_x_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_Lean_IR_LocalContext_isParam(v_ctx_2534_, v_x_2535_);
lean_dec(v_x_2535_);
lean_dec_ref(v_ctx_2534_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* v_ctx_2538_, lean_object* v_x_2539_){
_start:
{
lean_object* v_vars_2540_; lean_object* v___x_2541_; 
v_vars_2540_ = lean_ctor_get(v_ctx_2538_, 0);
v___x_2541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_2540_, v_x_2539_);
if (lean_obj_tag(v___x_2541_) == 1)
{
lean_object* v_val_2542_; 
v_val_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_val_2542_);
lean_dec_ref_known(v___x_2541_, 1);
if (lean_obj_tag(v_val_2542_) == 1)
{
uint8_t v___x_2543_; 
lean_dec_ref_known(v_val_2542_, 2);
v___x_2543_ = 1;
return v___x_2543_;
}
else
{
uint8_t v___x_2544_; 
lean_dec(v_val_2542_);
v___x_2544_ = 0;
return v___x_2544_;
}
}
else
{
uint8_t v___x_2545_; 
lean_dec(v___x_2541_);
v___x_2545_ = 0;
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* v_ctx_2546_, lean_object* v_x_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_2546_, v_x_2547_);
lean_dec(v_x_2547_);
lean_dec_ref(v_ctx_2546_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* v_k_2550_, lean_object* v_t_2551_){
_start:
{
if (lean_obj_tag(v_t_2551_) == 0)
{
lean_object* v_k_2552_; lean_object* v_v_2553_; lean_object* v_l_2554_; lean_object* v_r_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_3210_; 
v_k_2552_ = lean_ctor_get(v_t_2551_, 1);
v_v_2553_ = lean_ctor_get(v_t_2551_, 2);
v_l_2554_ = lean_ctor_get(v_t_2551_, 3);
v_r_2555_ = lean_ctor_get(v_t_2551_, 4);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_t_2551_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_t_2551_, 0);
lean_dec(v_unused_3211_);
v___x_2557_ = v_t_2551_;
v_isShared_2558_ = v_isSharedCheck_3210_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_r_2555_);
lean_inc(v_l_2554_);
lean_inc(v_v_2553_);
lean_inc(v_k_2552_);
lean_dec(v_t_2551_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_3210_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_nat_dec_lt(v_k_2550_, v_k_2552_);
if (v___x_2559_ == 0)
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_nat_dec_eq(v_k_2550_, v_k_2552_);
if (v___x_2560_ == 0)
{
lean_object* v_impl_2561_; lean_object* v___x_2562_; 
v_impl_2561_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2550_, v_r_2555_);
v___x_2562_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2561_) == 0)
{
if (lean_obj_tag(v_l_2554_) == 0)
{
lean_object* v_size_2563_; lean_object* v_size_2564_; lean_object* v_k_2565_; lean_object* v_v_2566_; lean_object* v_l_2567_; lean_object* v_r_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_size_2563_ = lean_ctor_get(v_impl_2561_, 0);
v_size_2564_ = lean_ctor_get(v_l_2554_, 0);
v_k_2565_ = lean_ctor_get(v_l_2554_, 1);
v_v_2566_ = lean_ctor_get(v_l_2554_, 2);
v_l_2567_ = lean_ctor_get(v_l_2554_, 3);
v_r_2568_ = lean_ctor_get(v_l_2554_, 4);
lean_inc(v_r_2568_);
v___x_2569_ = lean_unsigned_to_nat(3u);
v___x_2570_ = lean_nat_mul(v___x_2569_, v_size_2563_);
v___x_2571_ = lean_nat_dec_lt(v___x_2570_, v_size_2564_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
lean_dec(v_r_2568_);
v___x_2572_ = lean_nat_add(v___x_2562_, v_size_2564_);
v___x_2573_ = lean_nat_add(v___x_2572_, v_size_2563_);
lean_dec(v___x_2572_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_impl_2561_);
lean_ctor_set(v___x_2557_, 0, v___x_2573_);
v___x_2575_ = v___x_2557_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_impl_2561_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
else
{
lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2642_; 
lean_inc(v_l_2567_);
lean_inc(v_v_2566_);
lean_inc(v_k_2565_);
lean_inc(v_size_2564_);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2643_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_l_2554_, 2);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_l_2554_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_2647_);
v___x_2578_ = v_l_2554_;
v_isShared_2579_ = v_isSharedCheck_2642_;
goto v_resetjp_2577_;
}
else
{
lean_dec(v_l_2554_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2642_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_size_2580_; lean_object* v_size_2581_; lean_object* v_k_2582_; lean_object* v_v_2583_; lean_object* v_l_2584_; lean_object* v_r_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v_size_2580_ = lean_ctor_get(v_l_2567_, 0);
v_size_2581_ = lean_ctor_get(v_r_2568_, 0);
v_k_2582_ = lean_ctor_get(v_r_2568_, 1);
v_v_2583_ = lean_ctor_get(v_r_2568_, 2);
v_l_2584_ = lean_ctor_get(v_r_2568_, 3);
v_r_2585_ = lean_ctor_get(v_r_2568_, 4);
v___x_2586_ = lean_unsigned_to_nat(2u);
v___x_2587_ = lean_nat_mul(v___x_2586_, v_size_2580_);
v___x_2588_ = lean_nat_dec_lt(v_size_2581_, v___x_2587_);
lean_dec(v___x_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2617_; 
lean_inc(v_r_2585_);
lean_inc(v_l_2584_);
lean_inc(v_v_2583_);
lean_inc(v_k_2582_);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_r_2568_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; lean_object* v_unused_2619_; lean_object* v_unused_2620_; lean_object* v_unused_2621_; lean_object* v_unused_2622_; 
v_unused_2618_ = lean_ctor_get(v_r_2568_, 4);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_r_2568_, 3);
lean_dec(v_unused_2619_);
v_unused_2620_ = lean_ctor_get(v_r_2568_, 2);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_r_2568_, 1);
lean_dec(v_unused_2621_);
v_unused_2622_ = lean_ctor_get(v_r_2568_, 0);
lean_dec(v_unused_2622_);
v___x_2590_ = v_r_2568_;
v_isShared_2591_ = v_isSharedCheck_2617_;
goto v_resetjp_2589_;
}
else
{
lean_dec(v_r_2568_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2617_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___x_2605_; lean_object* v___y_2607_; 
v___x_2592_ = lean_nat_add(v___x_2562_, v_size_2564_);
lean_dec(v_size_2564_);
v___x_2593_ = lean_nat_add(v___x_2592_, v_size_2563_);
lean_dec(v___x_2592_);
v___x_2605_ = lean_nat_add(v___x_2562_, v_size_2580_);
if (lean_obj_tag(v_l_2584_) == 0)
{
lean_object* v_size_2615_; 
v_size_2615_ = lean_ctor_get(v_l_2584_, 0);
lean_inc(v_size_2615_);
v___y_2607_ = v_size_2615_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_unsigned_to_nat(0u);
v___y_2607_ = v___x_2616_;
goto v___jp_2606_;
}
v___jp_2594_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_nat_add(v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 4, v_impl_2561_);
lean_ctor_set(v___x_2590_, 3, v_r_2585_);
lean_ctor_set(v___x_2590_, 2, v_v_2553_);
lean_ctor_set(v___x_2590_, 1, v_k_2552_);
lean_ctor_set(v___x_2590_, 0, v___x_2598_);
v___x_2600_ = v___x_2590_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_r_2585_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_impl_2561_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v___x_2600_);
lean_ctor_set(v___x_2578_, 3, v___y_2595_);
lean_ctor_set(v___x_2578_, 2, v_v_2583_);
lean_ctor_set(v___x_2578_, 1, v_k_2582_);
lean_ctor_set(v___x_2578_, 0, v___x_2593_);
v___x_2602_ = v___x_2578_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2582_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_v_2583_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v___y_2595_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
v___jp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_nat_add(v___x_2605_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec(v___x_2605_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_l_2584_);
lean_ctor_set(v___x_2557_, 3, v_l_2567_);
lean_ctor_set(v___x_2557_, 2, v_v_2566_);
lean_ctor_set(v___x_2557_, 1, v_k_2565_);
lean_ctor_set(v___x_2557_, 0, v___x_2608_);
v___x_2610_ = v___x_2557_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_k_2565_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_v_2566_);
lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_l_2567_);
lean_ctor_set(v_reuseFailAlloc_2614_, 4, v_l_2584_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_nat_add(v___x_2562_, v_size_2563_);
if (lean_obj_tag(v_r_2585_) == 0)
{
lean_object* v_size_2612_; 
v_size_2612_ = lean_ctor_get(v_r_2585_, 0);
lean_inc(v_size_2612_);
v___y_2595_ = v___x_2610_;
v___y_2596_ = v___x_2611_;
v___y_2597_ = v_size_2612_;
goto v___jp_2594_;
}
else
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_unsigned_to_nat(0u);
v___y_2595_ = v___x_2610_;
v___y_2596_ = v___x_2611_;
v___y_2597_ = v___x_2613_;
goto v___jp_2594_;
}
}
}
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_del_object(v___x_2557_);
v___x_2623_ = lean_nat_add(v___x_2562_, v_size_2564_);
lean_dec(v_size_2564_);
v___x_2624_ = lean_nat_add(v___x_2623_, v_size_2563_);
lean_dec(v___x_2623_);
v___x_2625_ = lean_nat_add(v___x_2562_, v_size_2563_);
v___x_2626_ = lean_nat_add(v___x_2625_, v_size_2581_);
lean_dec(v___x_2625_);
lean_inc_ref(v_impl_2561_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v_impl_2561_);
lean_ctor_set(v___x_2578_, 3, v_r_2568_);
lean_ctor_set(v___x_2578_, 2, v_v_2553_);
lean_ctor_set(v___x_2578_, 1, v_k_2552_);
lean_ctor_set(v___x_2578_, 0, v___x_2626_);
v___x_2628_ = v___x_2578_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_r_2568_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_impl_2561_);
v___x_2628_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
v_isSharedCheck_2635_ = !lean_is_exclusive(v_impl_2561_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; lean_object* v_unused_2637_; lean_object* v_unused_2638_; lean_object* v_unused_2639_; lean_object* v_unused_2640_; 
v_unused_2636_ = lean_ctor_get(v_impl_2561_, 4);
lean_dec(v_unused_2636_);
v_unused_2637_ = lean_ctor_get(v_impl_2561_, 3);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v_impl_2561_, 2);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_impl_2561_, 1);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_impl_2561_, 0);
lean_dec(v_unused_2640_);
v___x_2630_ = v_impl_2561_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_dec(v_impl_2561_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 4, v___x_2628_);
lean_ctor_set(v___x_2630_, 3, v_l_2567_);
lean_ctor_set(v___x_2630_, 2, v_v_2566_);
lean_ctor_set(v___x_2630_, 1, v_k_2565_);
lean_ctor_set(v___x_2630_, 0, v___x_2624_);
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_k_2565_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v_v_2566_);
lean_ctor_set(v_reuseFailAlloc_2634_, 3, v_l_2567_);
lean_ctor_set(v_reuseFailAlloc_2634_, 4, v___x_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v_size_2648_ = lean_ctor_get(v_impl_2561_, 0);
v___x_2649_ = lean_nat_add(v___x_2562_, v_size_2648_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_impl_2561_);
lean_ctor_set(v___x_2557_, 0, v___x_2649_);
v___x_2651_ = v___x_2557_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_impl_2561_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
if (lean_obj_tag(v_l_2554_) == 0)
{
lean_object* v_l_2653_; 
v_l_2653_ = lean_ctor_get(v_l_2554_, 3);
if (lean_obj_tag(v_l_2653_) == 0)
{
lean_object* v_r_2654_; 
lean_inc_ref(v_l_2653_);
v_r_2654_ = lean_ctor_get(v_l_2554_, 4);
lean_inc(v_r_2654_);
if (lean_obj_tag(v_r_2654_) == 0)
{
lean_object* v_size_2655_; lean_object* v_k_2656_; lean_object* v_v_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2670_; 
v_size_2655_ = lean_ctor_get(v_l_2554_, 0);
v_k_2656_ = lean_ctor_get(v_l_2554_, 1);
v_v_2657_ = lean_ctor_get(v_l_2554_, 2);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; lean_object* v_unused_2672_; 
v_unused_2671_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2672_);
v___x_2659_ = v_l_2554_;
v_isShared_2660_ = v_isSharedCheck_2670_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_v_2657_);
lean_inc(v_k_2656_);
lean_inc(v_size_2655_);
lean_dec(v_l_2554_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2670_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_size_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v_size_2661_ = lean_ctor_get(v_r_2654_, 0);
v___x_2662_ = lean_nat_add(v___x_2562_, v_size_2655_);
lean_dec(v_size_2655_);
v___x_2663_ = lean_nat_add(v___x_2562_, v_size_2661_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 4, v_impl_2561_);
lean_ctor_set(v___x_2659_, 3, v_r_2654_);
lean_ctor_set(v___x_2659_, 2, v_v_2553_);
lean_ctor_set(v___x_2659_, 1, v_k_2552_);
lean_ctor_set(v___x_2659_, 0, v___x_2663_);
v___x_2665_ = v___x_2659_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_r_2654_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v_impl_2561_);
v___x_2665_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v___x_2665_);
lean_ctor_set(v___x_2557_, 3, v_l_2653_);
lean_ctor_set(v___x_2557_, 2, v_v_2657_);
lean_ctor_set(v___x_2557_, 1, v_k_2656_);
lean_ctor_set(v___x_2557_, 0, v___x_2662_);
v___x_2667_ = v___x_2557_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_k_2656_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_v_2657_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_l_2653_);
lean_ctor_set(v_reuseFailAlloc_2668_, 4, v___x_2665_);
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
else
{
lean_object* v_k_2673_; lean_object* v_v_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2685_; 
v_k_2673_ = lean_ctor_get(v_l_2554_, 1);
v_v_2674_ = lean_ctor_get(v_l_2554_, 2);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; 
v_unused_2686_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_2688_);
v___x_2676_ = v_l_2554_;
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_v_2674_);
lean_inc(v_k_2673_);
lean_dec(v_l_2554_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = lean_unsigned_to_nat(3u);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 3, v_r_2654_);
lean_ctor_set(v___x_2676_, 2, v_v_2553_);
lean_ctor_set(v___x_2676_, 1, v_k_2552_);
lean_ctor_set(v___x_2676_, 0, v___x_2562_);
v___x_2680_ = v___x_2676_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_r_2654_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_r_2654_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v___x_2680_);
lean_ctor_set(v___x_2557_, 3, v_l_2653_);
lean_ctor_set(v___x_2557_, 2, v_v_2674_);
lean_ctor_set(v___x_2557_, 1, v_k_2673_);
lean_ctor_set(v___x_2557_, 0, v___x_2678_);
v___x_2682_ = v___x_2557_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2673_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2674_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_l_2653_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
lean_object* v_r_2689_; 
v_r_2689_ = lean_ctor_get(v_l_2554_, 4);
lean_inc(v_r_2689_);
if (lean_obj_tag(v_r_2689_) == 0)
{
lean_object* v_k_2690_; lean_object* v_v_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2714_; 
lean_inc(v_l_2653_);
v_k_2690_ = lean_ctor_get(v_l_2554_, 1);
v_v_2691_ = lean_ctor_get(v_l_2554_, 2);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; 
v_unused_2715_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_2717_);
v___x_2693_ = v_l_2554_;
v_isShared_2694_ = v_isSharedCheck_2714_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_v_2691_);
lean_inc(v_k_2690_);
lean_dec(v_l_2554_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2714_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_k_2695_; lean_object* v_v_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2710_; 
v_k_2695_ = lean_ctor_get(v_r_2689_, 1);
v_v_2696_ = lean_ctor_get(v_r_2689_, 2);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_r_2689_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2711_ = lean_ctor_get(v_r_2689_, 4);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_r_2689_, 3);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_r_2689_, 0);
lean_dec(v_unused_2713_);
v___x_2698_ = v_r_2689_;
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_v_2696_);
lean_inc(v_k_2695_);
lean_dec(v_r_2689_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_unsigned_to_nat(3u);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 4, v_l_2653_);
lean_ctor_set(v___x_2698_, 3, v_l_2653_);
lean_ctor_set(v___x_2698_, 2, v_v_2691_);
lean_ctor_set(v___x_2698_, 1, v_k_2690_);
lean_ctor_set(v___x_2698_, 0, v___x_2562_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_k_2690_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_v_2691_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_l_2653_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_l_2653_);
v___x_2702_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 4, v_l_2653_);
lean_ctor_set(v___x_2693_, 2, v_v_2553_);
lean_ctor_set(v___x_2693_, 1, v_k_2552_);
lean_ctor_set(v___x_2693_, 0, v___x_2562_);
v___x_2704_ = v___x_2693_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_l_2653_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_l_2653_);
v___x_2704_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v___x_2704_);
lean_ctor_set(v___x_2557_, 3, v___x_2702_);
lean_ctor_set(v___x_2557_, 2, v_v_2696_);
lean_ctor_set(v___x_2557_, 1, v_k_2695_);
lean_ctor_set(v___x_2557_, 0, v___x_2700_);
v___x_2706_ = v___x_2557_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2695_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2696_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_unsigned_to_nat(2u);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_r_2689_);
lean_ctor_set(v___x_2557_, 0, v___x_2718_);
v___x_2720_ = v___x_2557_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2721_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2721_, 4, v_r_2689_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v___x_2723_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_l_2554_);
lean_ctor_set(v___x_2557_, 0, v___x_2562_);
v___x_2723_ = v___x_2557_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_l_2554_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_del_object(v___x_2557_);
lean_dec(v_v_2553_);
lean_dec(v_k_2552_);
if (lean_obj_tag(v_l_2554_) == 0)
{
if (lean_obj_tag(v_r_2555_) == 0)
{
lean_object* v_size_2725_; lean_object* v_k_2726_; lean_object* v_v_2727_; lean_object* v_l_2728_; lean_object* v_r_2729_; lean_object* v_size_2730_; lean_object* v_k_2731_; lean_object* v_v_2732_; lean_object* v_l_2733_; lean_object* v_r_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_size_2725_ = lean_ctor_get(v_l_2554_, 0);
v_k_2726_ = lean_ctor_get(v_l_2554_, 1);
v_v_2727_ = lean_ctor_get(v_l_2554_, 2);
v_l_2728_ = lean_ctor_get(v_l_2554_, 3);
v_r_2729_ = lean_ctor_get(v_l_2554_, 4);
lean_inc(v_r_2729_);
v_size_2730_ = lean_ctor_get(v_r_2555_, 0);
v_k_2731_ = lean_ctor_get(v_r_2555_, 1);
v_v_2732_ = lean_ctor_get(v_r_2555_, 2);
v_l_2733_ = lean_ctor_get(v_r_2555_, 3);
lean_inc(v_l_2733_);
v_r_2734_ = lean_ctor_get(v_r_2555_, 4);
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_dec_lt(v_size_2725_, v_size_2730_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2872_; 
lean_inc(v_l_2728_);
lean_inc(v_v_2727_);
lean_inc(v_k_2726_);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; lean_object* v_unused_2874_; lean_object* v_unused_2875_; lean_object* v_unused_2876_; lean_object* v_unused_2877_; 
v_unused_2873_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2873_);
v_unused_2874_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2874_);
v_unused_2875_ = lean_ctor_get(v_l_2554_, 2);
lean_dec(v_unused_2875_);
v_unused_2876_ = lean_ctor_get(v_l_2554_, 1);
lean_dec(v_unused_2876_);
v_unused_2877_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_2877_);
v___x_2738_ = v_l_2554_;
v_isShared_2739_ = v_isSharedCheck_2872_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_l_2554_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2872_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v_tree_2741_; 
v___x_2740_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2726_, v_v_2727_, v_l_2728_, v_r_2729_);
v_tree_2741_ = lean_ctor_get(v___x_2740_, 2);
if (lean_obj_tag(v_tree_2741_) == 0)
{
lean_object* v_k_2742_; lean_object* v_v_2743_; lean_object* v_size_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
lean_inc_ref(v_tree_2741_);
v_k_2742_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_k_2742_);
v_v_2743_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_v_2743_);
lean_dec_ref(v___x_2740_);
v_size_2744_ = lean_ctor_get(v_tree_2741_, 0);
v___x_2745_ = lean_unsigned_to_nat(3u);
v___x_2746_ = lean_nat_mul(v___x_2745_, v_size_2744_);
v___x_2747_ = lean_nat_dec_lt(v___x_2746_, v_size_2730_);
lean_dec(v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec(v_l_2733_);
v___x_2748_ = lean_nat_add(v___x_2735_, v_size_2744_);
v___x_2749_ = lean_nat_add(v___x_2748_, v_size_2730_);
lean_dec(v___x_2748_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v_r_2555_);
lean_ctor_set(v___x_2738_, 3, v_tree_2741_);
lean_ctor_set(v___x_2738_, 2, v_v_2743_);
lean_ctor_set(v___x_2738_, 1, v_k_2742_);
lean_ctor_set(v___x_2738_, 0, v___x_2749_);
v___x_2751_ = v___x_2738_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2752_, 3, v_tree_2741_);
lean_ctor_set(v_reuseFailAlloc_2752_, 4, v_r_2555_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2807_; 
lean_inc(v_r_2734_);
lean_inc(v_v_2732_);
lean_inc(v_k_2731_);
lean_inc(v_size_2730_);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; 
v_unused_2808_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_r_2555_, 2);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_r_2555_, 1);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_2812_);
v___x_2754_ = v_r_2555_;
v_isShared_2755_ = v_isSharedCheck_2807_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v_r_2555_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2807_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_size_2756_; lean_object* v_k_2757_; lean_object* v_v_2758_; lean_object* v_l_2759_; lean_object* v_r_2760_; lean_object* v_size_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v_size_2756_ = lean_ctor_get(v_l_2733_, 0);
v_k_2757_ = lean_ctor_get(v_l_2733_, 1);
v_v_2758_ = lean_ctor_get(v_l_2733_, 2);
v_l_2759_ = lean_ctor_get(v_l_2733_, 3);
v_r_2760_ = lean_ctor_get(v_l_2733_, 4);
v_size_2761_ = lean_ctor_get(v_r_2734_, 0);
v___x_2762_ = lean_unsigned_to_nat(2u);
v___x_2763_ = lean_nat_mul(v___x_2762_, v_size_2761_);
v___x_2764_ = lean_nat_dec_lt(v_size_2756_, v___x_2763_);
lean_dec(v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2792_; 
lean_inc(v_r_2760_);
lean_inc(v_l_2759_);
lean_inc(v_v_2758_);
lean_inc(v_k_2757_);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_l_2733_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; lean_object* v_unused_2794_; lean_object* v_unused_2795_; lean_object* v_unused_2796_; lean_object* v_unused_2797_; 
v_unused_2793_ = lean_ctor_get(v_l_2733_, 4);
lean_dec(v_unused_2793_);
v_unused_2794_ = lean_ctor_get(v_l_2733_, 3);
lean_dec(v_unused_2794_);
v_unused_2795_ = lean_ctor_get(v_l_2733_, 2);
lean_dec(v_unused_2795_);
v_unused_2796_ = lean_ctor_get(v_l_2733_, 1);
lean_dec(v_unused_2796_);
v_unused_2797_ = lean_ctor_get(v_l_2733_, 0);
lean_dec(v_unused_2797_);
v___x_2766_ = v_l_2733_;
v_isShared_2767_ = v_isSharedCheck_2792_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v_l_2733_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2792_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2782_; 
v___x_2768_ = lean_nat_add(v___x_2735_, v_size_2744_);
v___x_2769_ = lean_nat_add(v___x_2768_, v_size_2730_);
lean_dec(v_size_2730_);
if (lean_obj_tag(v_l_2759_) == 0)
{
lean_object* v_size_2790_; 
v_size_2790_ = lean_ctor_get(v_l_2759_, 0);
lean_inc(v_size_2790_);
v___y_2782_ = v_size_2790_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_unsigned_to_nat(0u);
v___y_2782_ = v___x_2791_;
goto v___jp_2781_;
}
v___jp_2770_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_nat_add(v___y_2771_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec(v___y_2771_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_r_2734_);
lean_ctor_set(v___x_2766_, 3, v_r_2760_);
lean_ctor_set(v___x_2766_, 2, v_v_2732_);
lean_ctor_set(v___x_2766_, 1, v_k_2731_);
lean_ctor_set(v___x_2766_, 0, v___x_2774_);
v___x_2776_ = v___x_2766_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_r_2760_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_r_2734_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 4, v___x_2776_);
lean_ctor_set(v___x_2754_, 3, v___y_2772_);
lean_ctor_set(v___x_2754_, 2, v_v_2758_);
lean_ctor_set(v___x_2754_, 1, v_k_2757_);
lean_ctor_set(v___x_2754_, 0, v___x_2769_);
v___x_2778_ = v___x_2754_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_k_2757_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_v_2758_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v___y_2772_);
lean_ctor_set(v_reuseFailAlloc_2779_, 4, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
v___jp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2783_ = lean_nat_add(v___x_2768_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec(v___x_2768_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v_l_2759_);
lean_ctor_set(v___x_2738_, 3, v_tree_2741_);
lean_ctor_set(v___x_2738_, 2, v_v_2743_);
lean_ctor_set(v___x_2738_, 1, v_k_2742_);
lean_ctor_set(v___x_2738_, 0, v___x_2783_);
v___x_2785_ = v___x_2738_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_tree_2741_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_l_2759_);
v___x_2785_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_nat_add(v___x_2735_, v_size_2761_);
if (lean_obj_tag(v_r_2760_) == 0)
{
lean_object* v_size_2787_; 
v_size_2787_ = lean_ctor_get(v_r_2760_, 0);
lean_inc(v_size_2787_);
v___y_2771_ = v___x_2786_;
v___y_2772_ = v___x_2785_;
v___y_2773_ = v_size_2787_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_unsigned_to_nat(0u);
v___y_2771_ = v___x_2786_;
v___y_2772_ = v___x_2785_;
v___y_2773_ = v___x_2788_;
goto v___jp_2770_;
}
}
}
}
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2798_ = lean_nat_add(v___x_2735_, v_size_2744_);
v___x_2799_ = lean_nat_add(v___x_2798_, v_size_2730_);
lean_dec(v_size_2730_);
v___x_2800_ = lean_nat_add(v___x_2798_, v_size_2756_);
lean_dec(v___x_2798_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 4, v_l_2733_);
lean_ctor_set(v___x_2754_, 3, v_tree_2741_);
lean_ctor_set(v___x_2754_, 2, v_v_2743_);
lean_ctor_set(v___x_2754_, 1, v_k_2742_);
lean_ctor_set(v___x_2754_, 0, v___x_2800_);
v___x_2802_ = v___x_2754_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_tree_2741_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_l_2733_);
v___x_2802_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v_r_2734_);
lean_ctor_set(v___x_2738_, 3, v___x_2802_);
lean_ctor_set(v___x_2738_, 2, v_v_2732_);
lean_ctor_set(v___x_2738_, 1, v_k_2731_);
lean_ctor_set(v___x_2738_, 0, v___x_2799_);
v___x_2804_ = v___x_2738_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_r_2734_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
else
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2866_; 
lean_inc(v_r_2734_);
lean_inc(v_v_2732_);
lean_inc(v_k_2731_);
lean_inc(v_size_2730_);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; lean_object* v_unused_2868_; lean_object* v_unused_2869_; lean_object* v_unused_2870_; lean_object* v_unused_2871_; 
v_unused_2867_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_2867_);
v_unused_2868_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_2868_);
v_unused_2869_ = lean_ctor_get(v_r_2555_, 2);
lean_dec(v_unused_2869_);
v_unused_2870_ = lean_ctor_get(v_r_2555_, 1);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_2871_);
v___x_2814_ = v_r_2555_;
v_isShared_2815_ = v_isSharedCheck_2866_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v_r_2555_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2866_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_l_2733_) == 0)
{
if (lean_obj_tag(v_r_2734_) == 0)
{
lean_object* v_k_2816_; lean_object* v_v_2817_; lean_object* v_size_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_inc(v_tree_2741_);
v_k_2816_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_k_2816_);
v_v_2817_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_v_2817_);
lean_dec_ref(v___x_2740_);
v_size_2818_ = lean_ctor_get(v_l_2733_, 0);
v___x_2819_ = lean_nat_add(v___x_2735_, v_size_2730_);
lean_dec(v_size_2730_);
v___x_2820_ = lean_nat_add(v___x_2735_, v_size_2818_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v_l_2733_);
lean_ctor_set(v___x_2814_, 3, v_tree_2741_);
lean_ctor_set(v___x_2814_, 2, v_v_2817_);
lean_ctor_set(v___x_2814_, 1, v_k_2816_);
lean_ctor_set(v___x_2814_, 0, v___x_2820_);
v___x_2822_ = v___x_2814_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_k_2816_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_v_2817_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_tree_2741_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_l_2733_);
v___x_2822_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v_r_2734_);
lean_ctor_set(v___x_2738_, 3, v___x_2822_);
lean_ctor_set(v___x_2738_, 2, v_v_2732_);
lean_ctor_set(v___x_2738_, 1, v_k_2731_);
lean_ctor_set(v___x_2738_, 0, v___x_2819_);
v___x_2824_ = v___x_2738_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_r_2734_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_k_2827_; lean_object* v_v_2828_; lean_object* v_k_2829_; lean_object* v_v_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_size_2730_);
v_k_2827_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_k_2827_);
v_v_2828_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_v_2828_);
lean_dec_ref(v___x_2740_);
v_k_2829_ = lean_ctor_get(v_l_2733_, 1);
v_v_2830_ = lean_ctor_get(v_l_2733_, 2);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_l_2733_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; lean_object* v_unused_2846_; lean_object* v_unused_2847_; 
v_unused_2845_ = lean_ctor_get(v_l_2733_, 4);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_l_2733_, 3);
lean_dec(v_unused_2846_);
v_unused_2847_ = lean_ctor_get(v_l_2733_, 0);
lean_dec(v_unused_2847_);
v___x_2832_ = v_l_2733_;
v_isShared_2833_ = v_isSharedCheck_2844_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_v_2830_);
lean_inc(v_k_2829_);
lean_dec(v_l_2733_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2844_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2834_ = lean_unsigned_to_nat(3u);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 4, v_r_2734_);
lean_ctor_set(v___x_2832_, 3, v_r_2734_);
lean_ctor_set(v___x_2832_, 2, v_v_2828_);
lean_ctor_set(v___x_2832_, 1, v_k_2827_);
lean_ctor_set(v___x_2832_, 0, v___x_2735_);
v___x_2836_ = v___x_2832_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_r_2734_);
lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_r_2734_);
v___x_2836_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2838_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 3, v_r_2734_);
lean_ctor_set(v___x_2814_, 0, v___x_2735_);
v___x_2838_ = v___x_2814_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_r_2734_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_r_2734_);
v___x_2838_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2840_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v___x_2838_);
lean_ctor_set(v___x_2738_, 3, v___x_2836_);
lean_ctor_set(v___x_2738_, 2, v_v_2830_);
lean_ctor_set(v___x_2738_, 1, v_k_2829_);
lean_ctor_set(v___x_2738_, 0, v___x_2834_);
v___x_2840_ = v___x_2738_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2829_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2830_);
lean_ctor_set(v_reuseFailAlloc_2841_, 3, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2841_, 4, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2734_) == 0)
{
lean_object* v_k_2848_; lean_object* v_v_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_dec(v_size_2730_);
v_k_2848_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_k_2848_);
v_v_2849_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_v_2849_);
lean_dec_ref(v___x_2740_);
v___x_2850_ = lean_unsigned_to_nat(3u);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v_l_2733_);
lean_ctor_set(v___x_2814_, 2, v_v_2849_);
lean_ctor_set(v___x_2814_, 1, v_k_2848_);
lean_ctor_set(v___x_2814_, 0, v___x_2735_);
v___x_2852_ = v___x_2814_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_k_2848_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_v_2849_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_l_2733_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_l_2733_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2854_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v_r_2734_);
lean_ctor_set(v___x_2738_, 3, v___x_2852_);
lean_ctor_set(v___x_2738_, 2, v_v_2732_);
lean_ctor_set(v___x_2738_, 1, v_k_2731_);
lean_ctor_set(v___x_2738_, 0, v___x_2850_);
v___x_2854_ = v___x_2738_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_r_2734_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
else
{
lean_object* v_k_2857_; lean_object* v_v_2858_; lean_object* v___x_2860_; 
v_k_2857_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_k_2857_);
v_v_2858_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_v_2858_);
lean_dec_ref(v___x_2740_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 3, v_r_2734_);
v___x_2860_ = v___x_2814_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_size_2730_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_r_2734_);
lean_ctor_set(v_reuseFailAlloc_2865_, 4, v_r_2734_);
v___x_2860_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = lean_unsigned_to_nat(2u);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 4, v___x_2860_);
lean_ctor_set(v___x_2738_, 3, v_r_2734_);
lean_ctor_set(v___x_2738_, 2, v_v_2858_);
lean_ctor_set(v___x_2738_, 1, v_k_2857_);
lean_ctor_set(v___x_2738_, 0, v___x_2861_);
v___x_2863_ = v___x_2738_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_k_2857_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_v_2858_);
lean_ctor_set(v_reuseFailAlloc_2864_, 3, v_r_2734_);
lean_ctor_set(v_reuseFailAlloc_2864_, 4, v___x_2860_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
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
lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_3030_; 
lean_inc(v_r_2734_);
lean_inc(v_v_2732_);
lean_inc(v_k_2731_);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; lean_object* v_unused_3032_; lean_object* v_unused_3033_; lean_object* v_unused_3034_; lean_object* v_unused_3035_; 
v_unused_3031_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_3031_);
v_unused_3032_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_3032_);
v_unused_3033_ = lean_ctor_get(v_r_2555_, 2);
lean_dec(v_unused_3033_);
v_unused_3034_ = lean_ctor_get(v_r_2555_, 1);
lean_dec(v_unused_3034_);
v_unused_3035_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_3035_);
v___x_2879_ = v_r_2555_;
v_isShared_2880_ = v_isSharedCheck_3030_;
goto v_resetjp_2878_;
}
else
{
lean_dec(v_r_2555_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_3030_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v_tree_2882_; 
v___x_2881_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2731_, v_v_2732_, v_l_2733_, v_r_2734_);
v_tree_2882_ = lean_ctor_get(v___x_2881_, 2);
lean_inc(v_tree_2882_);
if (lean_obj_tag(v_tree_2882_) == 0)
{
lean_object* v_k_2883_; lean_object* v_v_2884_; lean_object* v_size_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_k_2883_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_k_2883_);
v_v_2884_ = lean_ctor_get(v___x_2881_, 1);
lean_inc(v_v_2884_);
lean_dec_ref(v___x_2881_);
v_size_2885_ = lean_ctor_get(v_tree_2882_, 0);
v___x_2886_ = lean_unsigned_to_nat(3u);
v___x_2887_ = lean_nat_mul(v___x_2886_, v_size_2885_);
v___x_2888_ = lean_nat_dec_lt(v___x_2887_, v_size_2725_);
lean_dec(v___x_2887_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
lean_dec(v_r_2729_);
v___x_2889_ = lean_nat_add(v___x_2735_, v_size_2725_);
v___x_2890_ = lean_nat_add(v___x_2889_, v_size_2885_);
lean_dec(v___x_2889_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_tree_2882_);
lean_ctor_set(v___x_2879_, 3, v_l_2554_);
lean_ctor_set(v___x_2879_, 2, v_v_2884_);
lean_ctor_set(v___x_2879_, 1, v_k_2883_);
lean_ctor_set(v___x_2879_, 0, v___x_2890_);
v___x_2892_ = v___x_2879_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_k_2883_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_v_2884_);
lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_tree_2882_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
else
{
lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2959_; 
lean_inc(v_l_2728_);
lean_inc(v_v_2727_);
lean_inc(v_k_2726_);
lean_inc(v_size_2725_);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; lean_object* v_unused_2961_; lean_object* v_unused_2962_; lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2960_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2960_);
v_unused_2961_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v_l_2554_, 2);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_l_2554_, 1);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_2964_);
v___x_2895_ = v_l_2554_;
v_isShared_2896_ = v_isSharedCheck_2959_;
goto v_resetjp_2894_;
}
else
{
lean_dec(v_l_2554_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2959_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v_size_2897_; lean_object* v_size_2898_; lean_object* v_k_2899_; lean_object* v_v_2900_; lean_object* v_l_2901_; lean_object* v_r_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_size_2897_ = lean_ctor_get(v_l_2728_, 0);
v_size_2898_ = lean_ctor_get(v_r_2729_, 0);
v_k_2899_ = lean_ctor_get(v_r_2729_, 1);
v_v_2900_ = lean_ctor_get(v_r_2729_, 2);
v_l_2901_ = lean_ctor_get(v_r_2729_, 3);
v_r_2902_ = lean_ctor_get(v_r_2729_, 4);
v___x_2903_ = lean_unsigned_to_nat(2u);
v___x_2904_ = lean_nat_mul(v___x_2903_, v_size_2897_);
v___x_2905_ = lean_nat_dec_lt(v_size_2898_, v___x_2904_);
lean_dec(v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2943_; 
lean_inc(v_r_2902_);
lean_inc(v_l_2901_);
lean_inc(v_v_2900_);
lean_inc(v_k_2899_);
lean_del_object(v___x_2895_);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_r_2729_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; lean_object* v_unused_2945_; lean_object* v_unused_2946_; lean_object* v_unused_2947_; lean_object* v_unused_2948_; 
v_unused_2944_ = lean_ctor_get(v_r_2729_, 4);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_r_2729_, 3);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_r_2729_, 2);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_r_2729_, 1);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v_r_2729_, 0);
lean_dec(v_unused_2948_);
v___x_2907_ = v_r_2729_;
v_isShared_2908_ = v_isSharedCheck_2943_;
goto v_resetjp_2906_;
}
else
{
lean_dec(v_r_2729_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2943_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___x_2931_; lean_object* v___y_2933_; 
v___x_2909_ = lean_nat_add(v___x_2735_, v_size_2725_);
lean_dec(v_size_2725_);
v___x_2910_ = lean_nat_add(v___x_2909_, v_size_2885_);
lean_dec(v___x_2909_);
v___x_2931_ = lean_nat_add(v___x_2735_, v_size_2897_);
if (lean_obj_tag(v_l_2901_) == 0)
{
lean_object* v_size_2941_; 
v_size_2941_ = lean_ctor_get(v_l_2901_, 0);
lean_inc(v_size_2941_);
v___y_2933_ = v_size_2941_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_unsigned_to_nat(0u);
v___y_2933_ = v___x_2942_;
goto v___jp_2932_;
}
v___jp_2911_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = lean_nat_add(v___y_2912_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec(v___y_2912_);
lean_inc_ref(v_tree_2882_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 4, v_tree_2882_);
lean_ctor_set(v___x_2907_, 3, v_r_2902_);
lean_ctor_set(v___x_2907_, 2, v_v_2884_);
lean_ctor_set(v___x_2907_, 1, v_k_2883_);
lean_ctor_set(v___x_2907_, 0, v___x_2915_);
v___x_2917_ = v___x_2907_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2883_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2884_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_r_2902_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_tree_2882_);
v___x_2917_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_isSharedCheck_2924_ = !lean_is_exclusive(v_tree_2882_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; lean_object* v_unused_2926_; lean_object* v_unused_2927_; lean_object* v_unused_2928_; lean_object* v_unused_2929_; 
v_unused_2925_ = lean_ctor_get(v_tree_2882_, 4);
lean_dec(v_unused_2925_);
v_unused_2926_ = lean_ctor_get(v_tree_2882_, 3);
lean_dec(v_unused_2926_);
v_unused_2927_ = lean_ctor_get(v_tree_2882_, 2);
lean_dec(v_unused_2927_);
v_unused_2928_ = lean_ctor_get(v_tree_2882_, 1);
lean_dec(v_unused_2928_);
v_unused_2929_ = lean_ctor_get(v_tree_2882_, 0);
lean_dec(v_unused_2929_);
v___x_2919_ = v_tree_2882_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v_tree_2882_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 4, v___x_2917_);
lean_ctor_set(v___x_2919_, 3, v___y_2913_);
lean_ctor_set(v___x_2919_, 2, v_v_2900_);
lean_ctor_set(v___x_2919_, 1, v_k_2899_);
lean_ctor_set(v___x_2919_, 0, v___x_2910_);
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_k_2899_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_v_2900_);
lean_ctor_set(v_reuseFailAlloc_2923_, 3, v___y_2913_);
lean_ctor_set(v_reuseFailAlloc_2923_, 4, v___x_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = lean_nat_add(v___x_2931_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec(v___x_2931_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_l_2901_);
lean_ctor_set(v___x_2879_, 3, v_l_2728_);
lean_ctor_set(v___x_2879_, 2, v_v_2727_);
lean_ctor_set(v___x_2879_, 1, v_k_2726_);
lean_ctor_set(v___x_2879_, 0, v___x_2934_);
v___x_2936_ = v___x_2879_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_k_2726_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_v_2727_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_l_2728_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_l_2901_);
v___x_2936_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_nat_add(v___x_2735_, v_size_2885_);
if (lean_obj_tag(v_r_2902_) == 0)
{
lean_object* v_size_2938_; 
v_size_2938_ = lean_ctor_get(v_r_2902_, 0);
lean_inc(v_size_2938_);
v___y_2912_ = v___x_2937_;
v___y_2913_ = v___x_2936_;
v___y_2914_ = v_size_2938_;
goto v___jp_2911_;
}
else
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___y_2912_ = v___x_2937_;
v___y_2913_ = v___x_2936_;
v___y_2914_ = v___x_2939_;
goto v___jp_2911_;
}
}
}
}
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2949_ = lean_nat_add(v___x_2735_, v_size_2725_);
lean_dec(v_size_2725_);
v___x_2950_ = lean_nat_add(v___x_2949_, v_size_2885_);
lean_dec(v___x_2949_);
v___x_2951_ = lean_nat_add(v___x_2735_, v_size_2885_);
v___x_2952_ = lean_nat_add(v___x_2951_, v_size_2898_);
lean_dec(v___x_2951_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_tree_2882_);
lean_ctor_set(v___x_2879_, 3, v_r_2729_);
lean_ctor_set(v___x_2879_, 2, v_v_2884_);
lean_ctor_set(v___x_2879_, 1, v_k_2883_);
lean_ctor_set(v___x_2879_, 0, v___x_2952_);
v___x_2954_ = v___x_2879_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_k_2883_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_v_2884_);
lean_ctor_set(v_reuseFailAlloc_2958_, 3, v_r_2729_);
lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_tree_2882_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 4, v___x_2954_);
lean_ctor_set(v___x_2895_, 0, v___x_2950_);
v___x_2956_ = v___x_2895_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_k_2726_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_v_2727_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_l_2728_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v___x_2954_);
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
}
}
else
{
if (lean_obj_tag(v_l_2728_) == 0)
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2988_; 
lean_inc_ref(v_l_2728_);
lean_inc(v_v_2727_);
lean_inc(v_k_2726_);
lean_inc(v_size_2725_);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; lean_object* v_unused_2990_; lean_object* v_unused_2991_; lean_object* v_unused_2992_; lean_object* v_unused_2993_; 
v_unused_2989_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_2989_);
v_unused_2990_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_2990_);
v_unused_2991_ = lean_ctor_get(v_l_2554_, 2);
lean_dec(v_unused_2991_);
v_unused_2992_ = lean_ctor_get(v_l_2554_, 1);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_2993_);
v___x_2966_ = v_l_2554_;
v_isShared_2967_ = v_isSharedCheck_2988_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_l_2554_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2988_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
if (lean_obj_tag(v_r_2729_) == 0)
{
lean_object* v_k_2968_; lean_object* v_v_2969_; lean_object* v_size_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v_k_2968_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_k_2968_);
v_v_2969_ = lean_ctor_get(v___x_2881_, 1);
lean_inc(v_v_2969_);
lean_dec_ref(v___x_2881_);
v_size_2970_ = lean_ctor_get(v_r_2729_, 0);
v___x_2971_ = lean_nat_add(v___x_2735_, v_size_2725_);
lean_dec(v_size_2725_);
v___x_2972_ = lean_nat_add(v___x_2735_, v_size_2970_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_tree_2882_);
lean_ctor_set(v___x_2879_, 3, v_r_2729_);
lean_ctor_set(v___x_2879_, 2, v_v_2969_);
lean_ctor_set(v___x_2879_, 1, v_k_2968_);
lean_ctor_set(v___x_2879_, 0, v___x_2972_);
v___x_2974_ = v___x_2879_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_k_2968_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v_v_2969_);
lean_ctor_set(v_reuseFailAlloc_2978_, 3, v_r_2729_);
lean_ctor_set(v_reuseFailAlloc_2978_, 4, v_tree_2882_);
v___x_2974_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 4, v___x_2974_);
lean_ctor_set(v___x_2966_, 0, v___x_2971_);
v___x_2976_ = v___x_2966_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_k_2726_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_v_2727_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_l_2728_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
else
{
lean_object* v_k_2979_; lean_object* v_v_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_dec(v_size_2725_);
v_k_2979_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_k_2979_);
v_v_2980_ = lean_ctor_get(v___x_2881_, 1);
lean_inc(v_v_2980_);
lean_dec_ref(v___x_2881_);
v___x_2981_ = lean_unsigned_to_nat(3u);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_r_2729_);
lean_ctor_set(v___x_2879_, 3, v_r_2729_);
lean_ctor_set(v___x_2879_, 2, v_v_2980_);
lean_ctor_set(v___x_2879_, 1, v_k_2979_);
lean_ctor_set(v___x_2879_, 0, v___x_2735_);
v___x_2983_ = v___x_2879_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_k_2979_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_v_2980_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_r_2729_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_r_2729_);
v___x_2983_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2985_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 4, v___x_2983_);
lean_ctor_set(v___x_2966_, 0, v___x_2981_);
v___x_2985_ = v___x_2966_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_k_2726_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_v_2727_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_l_2728_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2729_) == 0)
{
lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3018_; 
lean_inc(v_l_2728_);
lean_inc(v_v_2727_);
lean_inc(v_k_2726_);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_l_2554_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; lean_object* v_unused_3020_; lean_object* v_unused_3021_; lean_object* v_unused_3022_; lean_object* v_unused_3023_; 
v_unused_3019_ = lean_ctor_get(v_l_2554_, 4);
lean_dec(v_unused_3019_);
v_unused_3020_ = lean_ctor_get(v_l_2554_, 3);
lean_dec(v_unused_3020_);
v_unused_3021_ = lean_ctor_get(v_l_2554_, 2);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v_l_2554_, 1);
lean_dec(v_unused_3022_);
v_unused_3023_ = lean_ctor_get(v_l_2554_, 0);
lean_dec(v_unused_3023_);
v___x_2995_ = v_l_2554_;
v_isShared_2996_ = v_isSharedCheck_3018_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v_l_2554_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3018_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v_k_2997_; lean_object* v_v_2998_; lean_object* v_k_2999_; lean_object* v_v_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3014_; 
v_k_2997_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_k_2997_);
v_v_2998_ = lean_ctor_get(v___x_2881_, 1);
lean_inc(v_v_2998_);
lean_dec_ref(v___x_2881_);
v_k_2999_ = lean_ctor_get(v_r_2729_, 1);
v_v_3000_ = lean_ctor_get(v_r_2729_, 2);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_r_2729_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; lean_object* v_unused_3016_; lean_object* v_unused_3017_; 
v_unused_3015_ = lean_ctor_get(v_r_2729_, 4);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v_r_2729_, 3);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v_r_2729_, 0);
lean_dec(v_unused_3017_);
v___x_3002_ = v_r_2729_;
v_isShared_3003_ = v_isSharedCheck_3014_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_v_3000_);
lean_inc(v_k_2999_);
lean_dec(v_r_2729_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3014_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(3u);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 4, v_l_2728_);
lean_ctor_set(v___x_3002_, 3, v_l_2728_);
lean_ctor_set(v___x_3002_, 2, v_v_2727_);
lean_ctor_set(v___x_3002_, 1, v_k_2726_);
lean_ctor_set(v___x_3002_, 0, v___x_2735_);
v___x_3006_ = v___x_3002_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_2726_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_2727_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_l_2728_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_l_2728_);
v___x_3006_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3008_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_l_2728_);
lean_ctor_set(v___x_2879_, 3, v_l_2728_);
lean_ctor_set(v___x_2879_, 2, v_v_2998_);
lean_ctor_set(v___x_2879_, 1, v_k_2997_);
lean_ctor_set(v___x_2879_, 0, v___x_2735_);
v___x_3008_ = v___x_2879_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_2997_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_2998_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_l_2728_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_l_2728_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 4, v___x_3008_);
lean_ctor_set(v___x_2995_, 3, v___x_3006_);
lean_ctor_set(v___x_2995_, 2, v_v_3000_);
lean_ctor_set(v___x_2995_, 1, v_k_2999_);
lean_ctor_set(v___x_2995_, 0, v___x_3004_);
v___x_3010_ = v___x_2995_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_2999_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_3000_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v___x_3006_);
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
}
}
}
else
{
lean_object* v_k_3024_; lean_object* v_v_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
v_k_3024_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_k_3024_);
v_v_3025_ = lean_ctor_get(v___x_2881_, 1);
lean_inc(v_v_3025_);
lean_dec_ref(v___x_2881_);
v___x_3026_ = lean_unsigned_to_nat(2u);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_r_2729_);
lean_ctor_set(v___x_2879_, 3, v_l_2554_);
lean_ctor_set(v___x_2879_, 2, v_v_3025_);
lean_ctor_set(v___x_2879_, 1, v_k_3024_);
lean_ctor_set(v___x_2879_, 0, v___x_3026_);
v___x_3028_ = v___x_2879_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_k_3024_);
lean_ctor_set(v_reuseFailAlloc_3029_, 2, v_v_3025_);
lean_ctor_set(v_reuseFailAlloc_3029_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_3029_, 4, v_r_2729_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
}
else
{
return v_l_2554_;
}
}
else
{
return v_r_2555_;
}
}
}
else
{
lean_object* v_impl_3036_; lean_object* v___x_3037_; 
v_impl_3036_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_2550_, v_l_2554_);
v___x_3037_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3036_) == 0)
{
if (lean_obj_tag(v_r_2555_) == 0)
{
lean_object* v_size_3038_; lean_object* v_size_3039_; lean_object* v_k_3040_; lean_object* v_v_3041_; lean_object* v_l_3042_; lean_object* v_r_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v_size_3038_ = lean_ctor_get(v_impl_3036_, 0);
v_size_3039_ = lean_ctor_get(v_r_2555_, 0);
v_k_3040_ = lean_ctor_get(v_r_2555_, 1);
v_v_3041_ = lean_ctor_get(v_r_2555_, 2);
v_l_3042_ = lean_ctor_get(v_r_2555_, 3);
lean_inc(v_l_3042_);
v_r_3043_ = lean_ctor_get(v_r_2555_, 4);
v___x_3044_ = lean_unsigned_to_nat(3u);
v___x_3045_ = lean_nat_mul(v___x_3044_, v_size_3038_);
v___x_3046_ = lean_nat_dec_lt(v___x_3045_, v_size_3039_);
lean_dec(v___x_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_dec(v_l_3042_);
v___x_3047_ = lean_nat_add(v___x_3037_, v_size_3038_);
v___x_3048_ = lean_nat_add(v___x_3047_, v_size_3039_);
lean_dec(v___x_3047_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 3, v_impl_3036_);
lean_ctor_set(v___x_2557_, 0, v___x_3048_);
v___x_3050_ = v___x_2557_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3051_, 3, v_impl_3036_);
lean_ctor_set(v_reuseFailAlloc_3051_, 4, v_r_2555_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
else
{
lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3115_; 
lean_inc(v_r_3043_);
lean_inc(v_v_3041_);
lean_inc(v_k_3040_);
lean_inc(v_size_3039_);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; lean_object* v_unused_3120_; 
v_unused_3116_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_r_2555_, 2);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_r_2555_, 1);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_3120_);
v___x_3053_ = v_r_2555_;
v_isShared_3054_ = v_isSharedCheck_3115_;
goto v_resetjp_3052_;
}
else
{
lean_dec(v_r_2555_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3115_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v_size_3055_; lean_object* v_k_3056_; lean_object* v_v_3057_; lean_object* v_l_3058_; lean_object* v_r_3059_; lean_object* v_size_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_size_3055_ = lean_ctor_get(v_l_3042_, 0);
v_k_3056_ = lean_ctor_get(v_l_3042_, 1);
v_v_3057_ = lean_ctor_get(v_l_3042_, 2);
v_l_3058_ = lean_ctor_get(v_l_3042_, 3);
v_r_3059_ = lean_ctor_get(v_l_3042_, 4);
v_size_3060_ = lean_ctor_get(v_r_3043_, 0);
v___x_3061_ = lean_unsigned_to_nat(2u);
v___x_3062_ = lean_nat_mul(v___x_3061_, v_size_3060_);
v___x_3063_ = lean_nat_dec_lt(v_size_3055_, v___x_3062_);
lean_dec(v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3091_; 
lean_inc(v_r_3059_);
lean_inc(v_l_3058_);
lean_inc(v_v_3057_);
lean_inc(v_k_3056_);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_l_3042_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; lean_object* v_unused_3093_; lean_object* v_unused_3094_; lean_object* v_unused_3095_; lean_object* v_unused_3096_; 
v_unused_3092_ = lean_ctor_get(v_l_3042_, 4);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_l_3042_, 3);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_l_3042_, 2);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_l_3042_, 1);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_l_3042_, 0);
lean_dec(v_unused_3096_);
v___x_3065_ = v_l_3042_;
v_isShared_3066_ = v_isSharedCheck_3091_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v_l_3042_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3091_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3081_; 
v___x_3067_ = lean_nat_add(v___x_3037_, v_size_3038_);
v___x_3068_ = lean_nat_add(v___x_3067_, v_size_3039_);
lean_dec(v_size_3039_);
if (lean_obj_tag(v_l_3058_) == 0)
{
lean_object* v_size_3089_; 
v_size_3089_ = lean_ctor_get(v_l_3058_, 0);
lean_inc(v_size_3089_);
v___y_3081_ = v_size_3089_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_unsigned_to_nat(0u);
v___y_3081_ = v___x_3090_;
goto v___jp_3080_;
}
v___jp_3069_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_nat_add(v___y_3070_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec(v___y_3070_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_r_3043_);
lean_ctor_set(v___x_3065_, 3, v_r_3059_);
lean_ctor_set(v___x_3065_, 2, v_v_3041_);
lean_ctor_set(v___x_3065_, 1, v_k_3040_);
lean_ctor_set(v___x_3065_, 0, v___x_3073_);
v___x_3075_ = v___x_3065_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_k_3040_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_v_3041_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_r_3059_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_r_3043_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3077_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 4, v___x_3075_);
lean_ctor_set(v___x_3053_, 3, v___y_3071_);
lean_ctor_set(v___x_3053_, 2, v_v_3057_);
lean_ctor_set(v___x_3053_, 1, v_k_3056_);
lean_ctor_set(v___x_3053_, 0, v___x_3068_);
v___x_3077_ = v___x_3053_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_k_3056_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v_v_3057_);
lean_ctor_set(v_reuseFailAlloc_3078_, 3, v___y_3071_);
lean_ctor_set(v_reuseFailAlloc_3078_, 4, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = lean_nat_add(v___x_3067_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec(v___x_3067_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_l_3058_);
lean_ctor_set(v___x_2557_, 3, v_impl_3036_);
lean_ctor_set(v___x_2557_, 0, v___x_3082_);
v___x_3084_ = v___x_2557_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_impl_3036_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_l_3058_);
v___x_3084_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_nat_add(v___x_3037_, v_size_3060_);
if (lean_obj_tag(v_r_3059_) == 0)
{
lean_object* v_size_3086_; 
v_size_3086_ = lean_ctor_get(v_r_3059_, 0);
lean_inc(v_size_3086_);
v___y_3070_ = v___x_3085_;
v___y_3071_ = v___x_3084_;
v___y_3072_ = v_size_3086_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_unsigned_to_nat(0u);
v___y_3070_ = v___x_3085_;
v___y_3071_ = v___x_3084_;
v___y_3072_ = v___x_3087_;
goto v___jp_3069_;
}
}
}
}
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_del_object(v___x_2557_);
v___x_3097_ = lean_nat_add(v___x_3037_, v_size_3038_);
v___x_3098_ = lean_nat_add(v___x_3097_, v_size_3039_);
lean_dec(v_size_3039_);
v___x_3099_ = lean_nat_add(v___x_3097_, v_size_3055_);
lean_dec(v___x_3097_);
lean_inc_ref(v_impl_3036_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 4, v_l_3042_);
lean_ctor_set(v___x_3053_, 3, v_impl_3036_);
lean_ctor_set(v___x_3053_, 2, v_v_2553_);
lean_ctor_set(v___x_3053_, 1, v_k_2552_);
lean_ctor_set(v___x_3053_, 0, v___x_3099_);
v___x_3101_ = v___x_3053_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_impl_3036_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_l_3042_);
v___x_3101_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_isSharedCheck_3108_ = !lean_is_exclusive(v_impl_3036_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; lean_object* v_unused_3110_; lean_object* v_unused_3111_; lean_object* v_unused_3112_; lean_object* v_unused_3113_; 
v_unused_3109_ = lean_ctor_get(v_impl_3036_, 4);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v_impl_3036_, 3);
lean_dec(v_unused_3110_);
v_unused_3111_ = lean_ctor_get(v_impl_3036_, 2);
lean_dec(v_unused_3111_);
v_unused_3112_ = lean_ctor_get(v_impl_3036_, 1);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_impl_3036_, 0);
lean_dec(v_unused_3113_);
v___x_3103_ = v_impl_3036_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_dec(v_impl_3036_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 4, v_r_3043_);
lean_ctor_set(v___x_3103_, 3, v___x_3101_);
lean_ctor_set(v___x_3103_, 2, v_v_3041_);
lean_ctor_set(v___x_3103_, 1, v_k_3040_);
lean_ctor_set(v___x_3103_, 0, v___x_3098_);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_k_3040_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_v_3041_);
lean_ctor_set(v_reuseFailAlloc_3107_, 3, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3107_, 4, v_r_3043_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v_size_3121_ = lean_ctor_get(v_impl_3036_, 0);
v___x_3122_ = lean_nat_add(v___x_3037_, v_size_3121_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 3, v_impl_3036_);
lean_ctor_set(v___x_2557_, 0, v___x_3122_);
v___x_3124_ = v___x_2557_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_impl_3036_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_r_2555_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
if (lean_obj_tag(v_r_2555_) == 0)
{
lean_object* v_l_3126_; 
v_l_3126_ = lean_ctor_get(v_r_2555_, 3);
lean_inc(v_l_3126_);
if (lean_obj_tag(v_l_3126_) == 0)
{
lean_object* v_r_3127_; 
v_r_3127_ = lean_ctor_get(v_r_2555_, 4);
lean_inc(v_r_3127_);
if (lean_obj_tag(v_r_3127_) == 0)
{
lean_object* v_size_3128_; lean_object* v_k_3129_; lean_object* v_v_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3143_; 
v_size_3128_ = lean_ctor_get(v_r_2555_, 0);
v_k_3129_ = lean_ctor_get(v_r_2555_, 1);
v_v_3130_ = lean_ctor_get(v_r_2555_, 2);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; lean_object* v_unused_3145_; 
v_unused_3144_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_3145_);
v___x_3132_ = v_r_2555_;
v_isShared_3133_ = v_isSharedCheck_3143_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_v_3130_);
lean_inc(v_k_3129_);
lean_inc(v_size_3128_);
lean_dec(v_r_2555_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3143_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v_size_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3138_; 
v_size_3134_ = lean_ctor_get(v_l_3126_, 0);
v___x_3135_ = lean_nat_add(v___x_3037_, v_size_3128_);
lean_dec(v_size_3128_);
v___x_3136_ = lean_nat_add(v___x_3037_, v_size_3134_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 4, v_l_3126_);
lean_ctor_set(v___x_3132_, 3, v_impl_3036_);
lean_ctor_set(v___x_3132_, 2, v_v_2553_);
lean_ctor_set(v___x_3132_, 1, v_k_2552_);
lean_ctor_set(v___x_3132_, 0, v___x_3136_);
v___x_3138_ = v___x_3132_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_impl_3036_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_l_3126_);
v___x_3138_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_r_3127_);
lean_ctor_set(v___x_2557_, 3, v___x_3138_);
lean_ctor_set(v___x_2557_, 2, v_v_3130_);
lean_ctor_set(v___x_2557_, 1, v_k_3129_);
lean_ctor_set(v___x_2557_, 0, v___x_3135_);
v___x_3140_ = v___x_2557_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_k_3129_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_v_3130_);
lean_ctor_set(v_reuseFailAlloc_3141_, 3, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3141_, 4, v_r_3127_);
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
else
{
lean_object* v_k_3146_; lean_object* v_v_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3170_; 
v_k_3146_ = lean_ctor_get(v_r_2555_, 1);
v_v_3147_ = lean_ctor_get(v_r_2555_, 2);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; lean_object* v_unused_3172_; lean_object* v_unused_3173_; 
v_unused_3171_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_3173_);
v___x_3149_ = v_r_2555_;
v_isShared_3150_ = v_isSharedCheck_3170_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_v_3147_);
lean_inc(v_k_3146_);
lean_dec(v_r_2555_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3170_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_k_3151_; lean_object* v_v_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3166_; 
v_k_3151_ = lean_ctor_get(v_l_3126_, 1);
v_v_3152_ = lean_ctor_get(v_l_3126_, 2);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_l_3126_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3167_ = lean_ctor_get(v_l_3126_, 4);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_l_3126_, 3);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_l_3126_, 0);
lean_dec(v_unused_3169_);
v___x_3154_ = v_l_3126_;
v_isShared_3155_ = v_isSharedCheck_3166_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_v_3152_);
lean_inc(v_k_3151_);
lean_dec(v_l_3126_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3166_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = lean_unsigned_to_nat(3u);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 4, v_r_3127_);
lean_ctor_set(v___x_3154_, 3, v_r_3127_);
lean_ctor_set(v___x_3154_, 2, v_v_2553_);
lean_ctor_set(v___x_3154_, 1, v_k_2552_);
lean_ctor_set(v___x_3154_, 0, v___x_3037_);
v___x_3158_ = v___x_3154_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_r_3127_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_r_3127_);
v___x_3158_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3160_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 3, v_r_3127_);
lean_ctor_set(v___x_3149_, 0, v___x_3037_);
v___x_3160_ = v___x_3149_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_k_3146_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_v_3147_);
lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_r_3127_);
lean_ctor_set(v_reuseFailAlloc_3164_, 4, v_r_3127_);
v___x_3160_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3162_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v___x_3160_);
lean_ctor_set(v___x_2557_, 3, v___x_3158_);
lean_ctor_set(v___x_2557_, 2, v_v_3152_);
lean_ctor_set(v___x_2557_, 1, v_k_3151_);
lean_ctor_set(v___x_2557_, 0, v___x_3156_);
v___x_3162_ = v___x_2557_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_k_3151_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_v_3152_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3163_, 4, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3174_; 
v_r_3174_ = lean_ctor_get(v_r_2555_, 4);
lean_inc(v_r_3174_);
if (lean_obj_tag(v_r_3174_) == 0)
{
lean_object* v_k_3175_; lean_object* v_v_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3187_; 
v_k_3175_ = lean_ctor_get(v_r_2555_, 1);
v_v_3176_ = lean_ctor_get(v_r_2555_, 2);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; lean_object* v_unused_3189_; lean_object* v_unused_3190_; 
v_unused_3188_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_3189_);
v_unused_3190_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_3190_);
v___x_3178_ = v_r_2555_;
v_isShared_3179_ = v_isSharedCheck_3187_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_v_3176_);
lean_inc(v_k_3175_);
lean_dec(v_r_2555_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3187_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_unsigned_to_nat(3u);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 4, v_l_3126_);
lean_ctor_set(v___x_3178_, 2, v_v_2553_);
lean_ctor_set(v___x_3178_, 1, v_k_2552_);
lean_ctor_set(v___x_3178_, 0, v___x_3037_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3186_, 3, v_l_3126_);
lean_ctor_set(v_reuseFailAlloc_3186_, 4, v_l_3126_);
v___x_3182_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3184_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v_r_3174_);
lean_ctor_set(v___x_2557_, 3, v___x_3182_);
lean_ctor_set(v___x_2557_, 2, v_v_3176_);
lean_ctor_set(v___x_2557_, 1, v_k_3175_);
lean_ctor_set(v___x_2557_, 0, v___x_3180_);
v___x_3184_ = v___x_2557_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_k_3175_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_v_3176_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_r_3174_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_size_3191_; lean_object* v_k_3192_; lean_object* v_v_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3204_; 
v_size_3191_ = lean_ctor_get(v_r_2555_, 0);
v_k_3192_ = lean_ctor_get(v_r_2555_, 1);
v_v_3193_ = lean_ctor_get(v_r_2555_, 2);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; 
v_unused_3205_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_3206_);
v___x_3195_ = v_r_2555_;
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_v_3193_);
lean_inc(v_k_3192_);
lean_inc(v_size_3191_);
lean_dec(v_r_2555_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 3, v_r_3174_);
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_size_3191_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_k_3192_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_v_3193_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v_r_3174_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v_r_3174_);
v___x_3198_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_unsigned_to_nat(2u);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 4, v___x_3198_);
lean_ctor_set(v___x_2557_, 3, v_r_3174_);
lean_ctor_set(v___x_2557_, 0, v___x_3199_);
v___x_3201_ = v___x_2557_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_r_3174_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v___x_3198_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
}
else
{
lean_object* v___x_3208_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 3, v_r_2555_);
lean_ctor_set(v___x_2557_, 0, v___x_3037_);
v___x_3208_ = v___x_2557_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v_r_2555_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v_r_2555_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
}
}
else
{
return v_t_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* v_k_3212_, lean_object* v_t_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3212_, v_t_3213_);
lean_dec(v_k_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* v_ctx_3215_, lean_object* v_j_3216_){
_start:
{
lean_object* v_vars_3217_; lean_object* v_jps_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3226_; 
v_vars_3217_ = lean_ctor_get(v_ctx_3215_, 0);
v_jps_3218_ = lean_ctor_get(v_ctx_3215_, 1);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_ctx_3215_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3220_ = v_ctx_3215_;
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_jps_3218_);
lean_inc(v_vars_3217_);
lean_dec(v_ctx_3215_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_3216_, v_jps_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v___x_3222_);
v___x_3224_ = v___x_3220_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_vars_3217_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* v_ctx_3227_, lean_object* v_j_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_3227_, v_j_3228_);
lean_dec(v_j_3228_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* v_00_u03b2_3230_, lean_object* v_k_3231_, lean_object* v_t_3232_, lean_object* v_h_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_3231_, v_t_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* v_00_u03b2_3235_, lean_object* v_k_3236_, lean_object* v_t_3237_, lean_object* v_h_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(v_00_u03b2_3235_, v_k_3236_, v_t_3237_, v_h_3238_);
lean_dec(v_k_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* v_ctx_3240_, lean_object* v_x_3241_){
_start:
{
lean_object* v_vars_3242_; lean_object* v___x_3243_; 
v_vars_3242_ = lean_ctor_get(v_ctx_3240_, 0);
v___x_3243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3242_, v_x_3241_);
if (lean_obj_tag(v___x_3243_) == 1)
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3252_; 
v_val_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_a_3248_; lean_object* v___x_3250_; 
v_a_3248_ = lean_ctor_get(v_val_3244_, 0);
lean_inc(v_a_3248_);
lean_dec(v_val_3244_);
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
}
else
{
lean_object* v___x_3253_; 
lean_dec(v___x_3243_);
v___x_3253_ = lean_box(0);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* v_ctx_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_IR_LocalContext_getType(v_ctx_3254_, v_x_3255_);
lean_dec(v_x_3255_);
lean_dec_ref(v_ctx_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* v_ctx_3257_, lean_object* v_x_3258_){
_start:
{
lean_object* v_vars_3259_; lean_object* v___x_3260_; 
v_vars_3259_ = lean_ctor_get(v_ctx_3257_, 0);
v___x_3260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_vars_3259_, v_x_3258_);
if (lean_obj_tag(v___x_3260_) == 1)
{
lean_object* v_val_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3270_; 
v_val_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3270_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_val_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3270_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
if (lean_obj_tag(v_val_3261_) == 1)
{
lean_object* v_a_3265_; lean_object* v___x_3267_; 
v_a_3265_ = lean_ctor_get(v_val_3261_, 1);
lean_inc_ref(v_a_3265_);
lean_dec_ref_known(v_val_3261_, 2);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_a_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
else
{
lean_object* v___x_3269_; 
lean_del_object(v___x_3263_);
lean_dec(v_val_3261_);
v___x_3269_ = lean_box(0);
return v___x_3269_;
}
}
}
else
{
lean_object* v___x_3271_; 
lean_dec(v___x_3260_);
v___x_3271_ = lean_box(0);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* v_ctx_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_IR_LocalContext_getValue(v_ctx_3272_, v_x_3273_);
lean_dec(v_x_3273_);
lean_dec_ref(v_ctx_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* v_00_u03c1_3275_, lean_object* v_v_u2081_3276_, lean_object* v_v_u2082_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_getJPBody_spec__0___redArg(v_00_u03c1_3275_, v_v_u2081_3276_);
if (lean_obj_tag(v___x_3278_) == 0)
{
uint8_t v___x_3279_; 
v___x_3279_ = lean_nat_dec_eq(v_v_u2081_3276_, v_v_u2082_3277_);
return v___x_3279_;
}
else
{
lean_object* v_val_3280_; uint8_t v___x_3281_; 
v_val_3280_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_val_3280_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3281_ = lean_nat_dec_eq(v_val_3280_, v_v_u2082_3277_);
lean_dec(v_val_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* v_00_u03c1_3282_, lean_object* v_v_u2081_3283_, lean_object* v_v_u2082_3284_){
_start:
{
uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_res_3285_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3282_, v_v_u2081_3283_, v_v_u2082_3284_);
lean_dec(v_v_u2082_3284_);
lean_dec(v_v_u2081_3283_);
lean_dec(v_00_u03c1_3282_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* v_00_u03c1_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
if (lean_obj_tag(v_x_3290_) == 0)
{
if (lean_obj_tag(v_x_3291_) == 0)
{
lean_object* v_id_3292_; lean_object* v_id_3293_; uint8_t v___x_3294_; 
v_id_3292_ = lean_ctor_get(v_x_3290_, 0);
v_id_3293_ = lean_ctor_get(v_x_3291_, 0);
v___x_3294_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3289_, v_id_3292_, v_id_3293_);
return v___x_3294_;
}
else
{
uint8_t v___x_3295_; 
v___x_3295_ = 0;
return v___x_3295_;
}
}
else
{
if (lean_obj_tag(v_x_3291_) == 1)
{
uint8_t v___x_3296_; 
v___x_3296_ = 1;
return v___x_3296_;
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = 0;
return v___x_3297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* v_00_u03c1_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3298_, v_x_3299_, v_x_3300_);
lean_dec(v_x_3300_);
lean_dec(v_x_3299_);
lean_dec(v_00_u03c1_3298_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* v_00_u03c1_3305_, lean_object* v_xs_3306_, lean_object* v_ys_3307_, lean_object* v_x_3308_){
_start:
{
lean_object* v_zero_3309_; uint8_t v_isZero_3310_; 
v_zero_3309_ = lean_unsigned_to_nat(0u);
v_isZero_3310_ = lean_nat_dec_eq(v_x_3308_, v_zero_3309_);
if (v_isZero_3310_ == 1)
{
lean_dec(v_x_3308_);
return v_isZero_3310_;
}
else
{
lean_object* v_one_3311_; lean_object* v_n_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; uint8_t v___x_3315_; 
v_one_3311_ = lean_unsigned_to_nat(1u);
v_n_3312_ = lean_nat_sub(v_x_3308_, v_one_3311_);
lean_dec(v_x_3308_);
v___x_3313_ = lean_array_fget_borrowed(v_xs_3306_, v_n_3312_);
v___x_3314_ = lean_array_fget_borrowed(v_ys_3307_, v_n_3312_);
v___x_3315_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_3305_, v___x_3313_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_dec(v_n_3312_);
return v___x_3315_;
}
else
{
v_x_3308_ = v_n_3312_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* v_00_u03c1_3317_, lean_object* v_xs_3318_, lean_object* v_ys_3319_, lean_object* v_x_3320_){
_start:
{
uint8_t v_res_3321_; lean_object* v_r_3322_; 
v_res_3321_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3317_, v_xs_3318_, v_ys_3319_, v_x_3320_);
lean_dec_ref(v_ys_3319_);
lean_dec_ref(v_xs_3318_);
lean_dec(v_00_u03c1_3317_);
v_r_3322_ = lean_box(v_res_3321_);
return v_r_3322_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* v_00_u03c1_3323_, lean_object* v_args_u2081_3324_, lean_object* v_args_u2082_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3326_ = lean_array_get_size(v_args_u2081_3324_);
v___x_3327_ = lean_array_get_size(v_args_u2082_3325_);
v___x_3328_ = lean_nat_dec_eq(v___x_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
return v___x_3328_;
}
else
{
uint8_t v___x_3329_; 
v___x_3329_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3323_, v_args_u2081_3324_, v_args_u2082_3325_, v___x_3326_);
return v___x_3329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* v_00_u03c1_3330_, lean_object* v_args_u2081_3331_, lean_object* v_args_u2082_3332_){
_start:
{
uint8_t v_res_3333_; lean_object* v_r_3334_; 
v_res_3333_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3330_, v_args_u2081_3331_, v_args_u2082_3332_);
lean_dec_ref(v_args_u2082_3332_);
lean_dec_ref(v_args_u2081_3331_);
lean_dec(v_00_u03c1_3330_);
v_r_3334_ = lean_box(v_res_3333_);
return v_r_3334_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(lean_object* v_00_u03c1_3335_, lean_object* v_xs_3336_, lean_object* v_ys_3337_, lean_object* v_hsz_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_){
_start:
{
uint8_t v___x_3341_; 
v___x_3341_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(v_00_u03c1_3335_, v_xs_3336_, v_ys_3337_, v_x_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* v_00_u03c1_3342_, lean_object* v_xs_3343_, lean_object* v_ys_3344_, lean_object* v_hsz_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_){
_start:
{
uint8_t v_res_3348_; lean_object* v_r_3349_; 
v_res_3348_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(v_00_u03c1_3342_, v_xs_3343_, v_ys_3344_, v_hsz_3345_, v_x_3346_, v_x_3347_);
lean_dec_ref(v_ys_3344_);
lean_dec_ref(v_xs_3343_);
lean_dec(v_00_u03c1_3342_);
v_r_3349_ = lean_box(v_res_3348_);
return v_r_3349_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* v_00_u03c1_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_){
_start:
{
lean_object* v_c_u2081_3356_; lean_object* v_ys_u2081_3357_; lean_object* v_c_u2082_3358_; lean_object* v_ys_u2082_3359_; lean_object* v_n_u2081_3363_; lean_object* v_x_u2081_3364_; lean_object* v_n_u2082_3365_; lean_object* v_x_u2082_3366_; 
switch(lean_obj_tag(v_x_3353_))
{
case 0:
{
if (lean_obj_tag(v_x_3354_) == 0)
{
lean_object* v_i_3369_; lean_object* v_ys_3370_; lean_object* v_i_3371_; lean_object* v_ys_3372_; uint8_t v___x_3373_; 
v_i_3369_ = lean_ctor_get(v_x_3353_, 0);
v_ys_3370_ = lean_ctor_get(v_x_3353_, 1);
v_i_3371_ = lean_ctor_get(v_x_3354_, 0);
v_ys_3372_ = lean_ctor_get(v_x_3354_, 1);
v___x_3373_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3369_, v_i_3371_);
if (v___x_3373_ == 0)
{
return v___x_3373_;
}
else
{
uint8_t v___x_3374_; 
v___x_3374_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3352_, v_ys_3370_, v_ys_3372_);
return v___x_3374_;
}
}
else
{
uint8_t v___x_3375_; 
v___x_3375_ = 0;
return v___x_3375_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3354_) == 1)
{
lean_object* v_n_3376_; lean_object* v_x_3377_; lean_object* v_n_3378_; lean_object* v_x_3379_; 
v_n_3376_ = lean_ctor_get(v_x_3353_, 0);
v_x_3377_ = lean_ctor_get(v_x_3353_, 1);
v_n_3378_ = lean_ctor_get(v_x_3354_, 0);
v_x_3379_ = lean_ctor_get(v_x_3354_, 1);
v_n_u2081_3363_ = v_n_3376_;
v_x_u2081_3364_ = v_x_3377_;
v_n_u2082_3365_ = v_n_3378_;
v_x_u2082_3366_ = v_x_3379_;
goto v___jp_3362_;
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = 0;
return v___x_3380_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3354_) == 2)
{
lean_object* v_x_3381_; lean_object* v_i_3382_; uint8_t v_updtHeader_3383_; lean_object* v_ys_3384_; lean_object* v_x_3385_; lean_object* v_i_3386_; uint8_t v_updtHeader_3387_; lean_object* v_ys_3388_; uint8_t v___y_3390_; uint8_t v___x_3393_; 
v_x_3381_ = lean_ctor_get(v_x_3353_, 0);
v_i_3382_ = lean_ctor_get(v_x_3353_, 1);
v_updtHeader_3383_ = lean_ctor_get_uint8(v_x_3353_, sizeof(void*)*3);
v_ys_3384_ = lean_ctor_get(v_x_3353_, 2);
v_x_3385_ = lean_ctor_get(v_x_3354_, 0);
v_i_3386_ = lean_ctor_get(v_x_3354_, 1);
v_updtHeader_3387_ = lean_ctor_get_uint8(v_x_3354_, sizeof(void*)*3);
v_ys_3388_ = lean_ctor_get(v_x_3354_, 2);
v___x_3393_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_3381_, v_x_3385_);
if (v___x_3393_ == 0)
{
v___y_3390_ = v___x_3393_;
goto v___jp_3389_;
}
else
{
uint8_t v___x_3394_; 
v___x_3394_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_3382_, v_i_3386_);
v___y_3390_ = v___x_3394_;
goto v___jp_3389_;
}
v___jp_3389_:
{
if (v___y_3390_ == 0)
{
return v___y_3390_;
}
else
{
if (v_updtHeader_3387_ == 0)
{
if (v_updtHeader_3383_ == 0)
{
uint8_t v___x_3391_; 
v___x_3391_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3352_, v_ys_3384_, v_ys_3388_);
return v___x_3391_;
}
else
{
return v_updtHeader_3387_;
}
}
else
{
if (v_updtHeader_3383_ == 0)
{
return v_updtHeader_3383_;
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3352_, v_ys_3384_, v_ys_3388_);
return v___x_3392_;
}
}
}
}
}
else
{
uint8_t v___x_3395_; 
v___x_3395_ = 0;
return v___x_3395_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3354_) == 3)
{
lean_object* v_i_3396_; lean_object* v_x_3397_; lean_object* v_i_3398_; lean_object* v_x_3399_; 
v_i_3396_ = lean_ctor_get(v_x_3353_, 0);
v_x_3397_ = lean_ctor_get(v_x_3353_, 1);
v_i_3398_ = lean_ctor_get(v_x_3354_, 0);
v_x_3399_ = lean_ctor_get(v_x_3354_, 1);
v_n_u2081_3363_ = v_i_3396_;
v_x_u2081_3364_ = v_x_3397_;
v_n_u2082_3365_ = v_i_3398_;
v_x_u2082_3366_ = v_x_3399_;
goto v___jp_3362_;
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = 0;
return v___x_3400_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3354_) == 4)
{
lean_object* v_i_3401_; lean_object* v_x_3402_; lean_object* v_i_3403_; lean_object* v_x_3404_; 
v_i_3401_ = lean_ctor_get(v_x_3353_, 0);
v_x_3402_ = lean_ctor_get(v_x_3353_, 1);
v_i_3403_ = lean_ctor_get(v_x_3354_, 0);
v_x_3404_ = lean_ctor_get(v_x_3354_, 1);
v_n_u2081_3363_ = v_i_3401_;
v_x_u2081_3364_ = v_x_3402_;
v_n_u2082_3365_ = v_i_3403_;
v_x_u2082_3366_ = v_x_3404_;
goto v___jp_3362_;
}
else
{
uint8_t v___x_3405_; 
v___x_3405_ = 0;
return v___x_3405_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3354_) == 5)
{
lean_object* v_n_3406_; lean_object* v_offset_3407_; lean_object* v_x_3408_; lean_object* v_n_3409_; lean_object* v_offset_3410_; lean_object* v_x_3411_; uint8_t v___x_3412_; 
v_n_3406_ = lean_ctor_get(v_x_3353_, 0);
v_offset_3407_ = lean_ctor_get(v_x_3353_, 1);
v_x_3408_ = lean_ctor_get(v_x_3353_, 2);
v_n_3409_ = lean_ctor_get(v_x_3354_, 0);
v_offset_3410_ = lean_ctor_get(v_x_3354_, 1);
v_x_3411_ = lean_ctor_get(v_x_3354_, 2);
v___x_3412_ = lean_nat_dec_eq(v_n_3406_, v_n_3409_);
if (v___x_3412_ == 0)
{
return v___x_3412_;
}
else
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_nat_dec_eq(v_offset_3407_, v_offset_3410_);
if (v___x_3413_ == 0)
{
return v___x_3413_;
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_3408_, v_x_3411_);
return v___x_3414_;
}
}
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = 0;
return v___x_3415_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3354_) == 6)
{
lean_object* v_c_3416_; lean_object* v_ys_3417_; lean_object* v_c_3418_; lean_object* v_ys_3419_; 
v_c_3416_ = lean_ctor_get(v_x_3353_, 0);
v_ys_3417_ = lean_ctor_get(v_x_3353_, 1);
v_c_3418_ = lean_ctor_get(v_x_3354_, 0);
v_ys_3419_ = lean_ctor_get(v_x_3354_, 1);
v_c_u2081_3356_ = v_c_3416_;
v_ys_u2081_3357_ = v_ys_3417_;
v_c_u2082_3358_ = v_c_3418_;
v_ys_u2082_3359_ = v_ys_3419_;
goto v___jp_3355_;
}
else
{
uint8_t v___x_3420_; 
v___x_3420_ = 0;
return v___x_3420_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3354_) == 7)
{
lean_object* v_c_3421_; lean_object* v_ys_3422_; lean_object* v_c_3423_; lean_object* v_ys_3424_; 
v_c_3421_ = lean_ctor_get(v_x_3353_, 0);
v_ys_3422_ = lean_ctor_get(v_x_3353_, 1);
v_c_3423_ = lean_ctor_get(v_x_3354_, 0);
v_ys_3424_ = lean_ctor_get(v_x_3354_, 1);
v_c_u2081_3356_ = v_c_3421_;
v_ys_u2081_3357_ = v_ys_3422_;
v_c_u2082_3358_ = v_c_3423_;
v_ys_u2082_3359_ = v_ys_3424_;
goto v___jp_3355_;
}
else
{
uint8_t v___x_3425_; 
v___x_3425_ = 0;
return v___x_3425_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3354_) == 8)
{
lean_object* v_x_3426_; lean_object* v_ys_3427_; lean_object* v_x_3428_; lean_object* v_ys_3429_; uint8_t v___x_3430_; 
v_x_3426_ = lean_ctor_get(v_x_3353_, 0);
v_ys_3427_ = lean_ctor_get(v_x_3353_, 1);
v_x_3428_ = lean_ctor_get(v_x_3354_, 0);
v_ys_3429_ = lean_ctor_get(v_x_3354_, 1);
v___x_3430_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_3426_, v_x_3428_);
if (v___x_3430_ == 0)
{
return v___x_3430_;
}
else
{
uint8_t v___x_3431_; 
v___x_3431_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3352_, v_ys_3427_, v_ys_3429_);
return v___x_3431_;
}
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = 0;
return v___x_3432_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3354_) == 9)
{
lean_object* v_ty_3433_; lean_object* v_x_3434_; lean_object* v_ty_3435_; lean_object* v_x_3436_; uint8_t v___x_3437_; 
v_ty_3433_ = lean_ctor_get(v_x_3353_, 0);
v_x_3434_ = lean_ctor_get(v_x_3353_, 1);
v_ty_3435_ = lean_ctor_get(v_x_3354_, 0);
v_x_3436_ = lean_ctor_get(v_x_3354_, 1);
v___x_3437_ = l_Lean_IR_instBEqIRType_beq(v_ty_3433_, v_ty_3435_);
if (v___x_3437_ == 0)
{
return v___x_3437_;
}
else
{
uint8_t v___x_3438_; 
v___x_3438_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_3434_, v_x_3436_);
return v___x_3438_;
}
}
else
{
uint8_t v___x_3439_; 
v___x_3439_ = 0;
return v___x_3439_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3354_) == 10)
{
lean_object* v_x_3440_; lean_object* v_x_3441_; uint8_t v___x_3442_; 
v_x_3440_ = lean_ctor_get(v_x_3353_, 0);
v_x_3441_ = lean_ctor_get(v_x_3354_, 0);
v___x_3442_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_3440_, v_x_3441_);
return v___x_3442_;
}
else
{
uint8_t v___x_3443_; 
v___x_3443_ = 0;
return v___x_3443_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3354_) == 11)
{
lean_object* v_v_3444_; lean_object* v_v_3445_; uint8_t v___x_3446_; 
v_v_3444_ = lean_ctor_get(v_x_3353_, 0);
v_v_3445_ = lean_ctor_get(v_x_3354_, 0);
v___x_3446_ = l_Lean_IR_instBEqLitVal_beq(v_v_3444_, v_v_3445_);
return v___x_3446_;
}
else
{
uint8_t v___x_3447_; 
v___x_3447_ = 0;
return v___x_3447_;
}
}
default: 
{
if (lean_obj_tag(v_x_3354_) == 12)
{
lean_object* v_x_3448_; lean_object* v_x_3449_; uint8_t v___x_3450_; 
v_x_3448_ = lean_ctor_get(v_x_3353_, 0);
v_x_3449_ = lean_ctor_get(v_x_3354_, 0);
v___x_3450_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_3448_, v_x_3449_);
return v___x_3450_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = 0;
return v___x_3451_;
}
}
}
v___jp_3355_:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_name_eq(v_c_u2081_3356_, v_c_u2082_3358_);
if (v___x_3360_ == 0)
{
return v___x_3360_;
}
else
{
uint8_t v___x_3361_; 
v___x_3361_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_3352_, v_ys_u2081_3357_, v_ys_u2082_3359_);
return v___x_3361_;
}
}
v___jp_3362_:
{
uint8_t v___x_3367_; 
v___x_3367_ = lean_nat_dec_eq(v_n_u2081_3363_, v_n_u2082_3365_);
if (v___x_3367_ == 0)
{
return v___x_3367_;
}
else
{
uint8_t v___x_3368_; 
v___x_3368_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3352_, v_x_u2081_3364_, v_x_u2082_3366_);
return v___x_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* v_00_u03c1_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_){
_start:
{
uint8_t v_res_3455_; lean_object* v_r_3456_; 
v_res_3455_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_3452_, v_x_3453_, v_x_3454_);
lean_dec_ref(v_x_3454_);
lean_dec_ref(v_x_3453_);
lean_dec(v_00_u03c1_3452_);
v_r_3456_ = lean_box(v_res_3455_);
return v_r_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* v_00_u03c1_3459_, lean_object* v_x_u2081_3460_, lean_object* v_x_u2082_3461_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_nat_dec_eq(v_x_u2081_3460_, v_x_u2082_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_x_u2081_3460_, v_x_u2082_3461_, v_00_u03c1_3459_);
return v___x_3463_;
}
else
{
lean_dec(v_x_u2082_3461_);
lean_dec(v_x_u2081_3460_);
return v_00_u03c1_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* v_00_u03c1_3464_, lean_object* v_p_u2081_3465_, lean_object* v_p_u2082_3466_){
_start:
{
lean_object* v_x_3467_; uint8_t v_borrow_3468_; lean_object* v_ty_3469_; lean_object* v_x_3470_; uint8_t v_borrow_3471_; lean_object* v_ty_3472_; uint8_t v___y_3474_; uint8_t v___x_3478_; 
v_x_3467_ = lean_ctor_get(v_p_u2081_3465_, 0);
lean_inc(v_x_3467_);
v_borrow_3468_ = lean_ctor_get_uint8(v_p_u2081_3465_, sizeof(void*)*2);
v_ty_3469_ = lean_ctor_get(v_p_u2081_3465_, 1);
lean_inc(v_ty_3469_);
lean_dec_ref(v_p_u2081_3465_);
v_x_3470_ = lean_ctor_get(v_p_u2082_3466_, 0);
lean_inc(v_x_3470_);
v_borrow_3471_ = lean_ctor_get_uint8(v_p_u2082_3466_, sizeof(void*)*2);
v_ty_3472_ = lean_ctor_get(v_p_u2082_3466_, 1);
lean_inc(v_ty_3472_);
lean_dec_ref(v_p_u2082_3466_);
v___x_3478_ = l_Lean_IR_instBEqIRType_beq(v_ty_3469_, v_ty_3472_);
lean_dec(v_ty_3472_);
lean_dec(v_ty_3469_);
if (v___x_3478_ == 0)
{
v___y_3474_ = v___x_3478_;
goto v___jp_3473_;
}
else
{
if (v_borrow_3471_ == 0)
{
if (v_borrow_3468_ == 0)
{
v___y_3474_ = v___x_3478_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3479_; 
lean_dec(v_x_3470_);
lean_dec(v_x_3467_);
lean_dec(v_00_u03c1_3464_);
v___x_3479_ = lean_box(0);
return v___x_3479_;
}
}
else
{
v___y_3474_ = v_borrow_3468_;
goto v___jp_3473_;
}
}
v___jp_3473_:
{
if (v___y_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec(v_x_3470_);
lean_dec(v_x_3467_);
lean_dec(v_00_u03c1_3464_);
v___x_3475_ = lean_box(0);
return v___x_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = l_Lean_IR_addVarRename(v_00_u03c1_3464_, v_x_3467_, v_x_3470_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(lean_object* v_upperBound_3480_, lean_object* v_ps_u2081_3481_, lean_object* v_ps_u2082_3482_, lean_object* v_a_3483_, lean_object* v_b_3484_){
_start:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_nat_dec_lt(v_a_3483_, v_upperBound_3480_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec(v_a_3483_);
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v_b_3484_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3487_ = ((lean_object*)(l_Lean_IR_instInhabitedParam_default));
v___x_3488_ = lean_array_get_borrowed(v___x_3487_, v_ps_u2081_3481_, v_a_3483_);
v___x_3489_ = lean_array_get_borrowed(v___x_3487_, v_ps_u2082_3482_, v_a_3483_);
lean_inc(v___x_3489_);
lean_inc(v___x_3488_);
v___x_3490_ = l_Lean_IR_addParamRename(v_b_3484_, v___x_3488_, v___x_3489_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_dec(v_a_3483_);
return v___x_3490_;
}
else
{
lean_object* v_val_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_val_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_val_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_nat_add(v_a_3483_, v___x_3492_);
lean_dec(v_a_3483_);
v_a_3483_ = v___x_3493_;
v_b_3484_ = v_val_3491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* v_upperBound_3495_, lean_object* v_ps_u2081_3496_, lean_object* v_ps_u2082_3497_, lean_object* v_a_3498_, lean_object* v_b_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3495_, v_ps_u2081_3496_, v_ps_u2082_3497_, v_a_3498_, v_b_3499_);
lean_dec_ref(v_ps_u2082_3497_);
lean_dec_ref(v_ps_u2081_3496_);
lean_dec(v_upperBound_3495_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* v_00_u03c1_3501_, lean_object* v_ps_u2081_3502_, lean_object* v_ps_u2082_3503_){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3504_ = lean_array_get_size(v_ps_u2081_3502_);
v___x_3505_ = lean_array_get_size(v_ps_u2082_3503_);
v___x_3506_ = lean_nat_dec_eq(v___x_3504_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v_00_u03c1_3501_);
v___x_3507_ = lean_box(0);
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_unsigned_to_nat(0u);
v___x_3509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v___x_3504_, v_ps_u2081_3502_, v_ps_u2082_3503_, v___x_3508_, v_00_u03c1_3501_);
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* v_00_u03c1_3510_, lean_object* v_ps_u2081_3511_, lean_object* v_ps_u2082_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_IR_addParamsRename(v_00_u03c1_3510_, v_ps_u2081_3511_, v_ps_u2082_3512_);
lean_dec_ref(v_ps_u2082_3512_);
lean_dec_ref(v_ps_u2081_3511_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(lean_object* v_upperBound_3514_, lean_object* v_ps_u2081_3515_, lean_object* v_ps_u2082_3516_, lean_object* v_inst_3517_, lean_object* v_R_3518_, lean_object* v_a_3519_, lean_object* v_b_3520_, lean_object* v_c_3521_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(v_upperBound_3514_, v_ps_u2081_3515_, v_ps_u2082_3516_, v_a_3519_, v_b_3520_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(lean_object* v_upperBound_3523_, lean_object* v_ps_u2081_3524_, lean_object* v_ps_u2082_3525_, lean_object* v_inst_3526_, lean_object* v_R_3527_, lean_object* v_a_3528_, lean_object* v_b_3529_, lean_object* v_c_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(v_upperBound_3523_, v_ps_u2081_3524_, v_ps_u2082_3525_, v_inst_3526_, v_R_3527_, v_a_3528_, v_b_3529_, v_c_3530_);
lean_dec_ref(v_ps_u2082_3525_);
lean_dec_ref(v_ps_u2081_3524_);
lean_dec(v_upperBound_3523_);
return v_res_3531_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3546_; uint8_t v___y_3547_; uint8_t v___y_3548_; uint8_t v___y_3549_; lean_object* v___y_3550_; uint8_t v___y_3551_; lean_object* v_00_u03c1_3553_; lean_object* v_x_u2081_3554_; lean_object* v_n_u2081_3555_; uint8_t v_c_u2081_3556_; uint8_t v_p_u2081_3557_; lean_object* v_b_u2081_3558_; lean_object* v_x_u2082_3559_; lean_object* v_n_u2082_3560_; uint8_t v_c_u2082_3561_; uint8_t v_p_u2082_3562_; lean_object* v_b_u2082_3563_; 
switch(lean_obj_tag(v_x_3533_))
{
case 0:
{
if (lean_obj_tag(v_x_3534_) == 0)
{
lean_object* v_x_3566_; lean_object* v_ty_3567_; lean_object* v_e_3568_; lean_object* v_b_3569_; lean_object* v_x_3570_; lean_object* v_ty_3571_; lean_object* v_e_3572_; lean_object* v_b_3573_; uint8_t v___y_3575_; uint8_t v___x_3578_; 
v_x_3566_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3566_);
v_ty_3567_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_ty_3567_);
v_e_3568_ = lean_ctor_get(v_x_3533_, 2);
lean_inc_ref(v_e_3568_);
v_b_3569_ = lean_ctor_get(v_x_3533_, 3);
lean_inc(v_b_3569_);
lean_dec_ref_known(v_x_3533_, 4);
v_x_3570_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3570_);
v_ty_3571_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_ty_3571_);
v_e_3572_ = lean_ctor_get(v_x_3534_, 2);
lean_inc_ref(v_e_3572_);
v_b_3573_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_b_3573_);
lean_dec_ref_known(v_x_3534_, 4);
v___x_3578_ = l_Lean_IR_instBEqIRType_beq(v_ty_3567_, v_ty_3571_);
lean_dec(v_ty_3571_);
lean_dec(v_ty_3567_);
if (v___x_3578_ == 0)
{
lean_dec_ref(v_e_3572_);
lean_dec_ref(v_e_3568_);
v___y_3575_ = v___x_3578_;
goto v___jp_3574_;
}
else
{
uint8_t v___x_3579_; 
v___x_3579_ = l_Lean_IR_Expr_alphaEqv(v_x_3532_, v_e_3568_, v_e_3572_);
lean_dec_ref(v_e_3572_);
lean_dec_ref(v_e_3568_);
v___y_3575_ = v___x_3579_;
goto v___jp_3574_;
}
v___jp_3574_:
{
if (v___y_3575_ == 0)
{
lean_dec(v_b_3573_);
lean_dec(v_x_3570_);
lean_dec(v_b_3569_);
lean_dec(v_x_3566_);
lean_dec(v_x_3532_);
return v___y_3575_;
}
else
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_IR_addVarRename(v_x_3532_, v_x_3566_, v_x_3570_);
v_x_3532_ = v___x_3576_;
v_x_3533_ = v_b_3569_;
v_x_3534_ = v_b_3573_;
goto _start;
}
}
}
else
{
uint8_t v___x_3580_; 
lean_dec_ref_known(v_x_3533_, 4);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3580_ = 0;
return v___x_3580_;
}
}
case 1:
{
if (lean_obj_tag(v_x_3534_) == 1)
{
lean_object* v_j_3581_; lean_object* v_xs_3582_; lean_object* v_v_3583_; lean_object* v_b_3584_; lean_object* v_j_3585_; lean_object* v_xs_3586_; lean_object* v_v_3587_; lean_object* v_b_3588_; lean_object* v___x_3589_; 
v_j_3581_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_j_3581_);
v_xs_3582_ = lean_ctor_get(v_x_3533_, 1);
lean_inc_ref(v_xs_3582_);
v_v_3583_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_v_3583_);
v_b_3584_ = lean_ctor_get(v_x_3533_, 3);
lean_inc(v_b_3584_);
lean_dec_ref_known(v_x_3533_, 4);
v_j_3585_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_j_3585_);
v_xs_3586_ = lean_ctor_get(v_x_3534_, 1);
lean_inc_ref(v_xs_3586_);
v_v_3587_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_v_3587_);
v_b_3588_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_b_3588_);
lean_dec_ref_known(v_x_3534_, 4);
lean_inc(v_x_3532_);
v___x_3589_ = l_Lean_IR_addParamsRename(v_x_3532_, v_xs_3582_, v_xs_3586_);
lean_dec_ref(v_xs_3586_);
lean_dec_ref(v_xs_3582_);
if (lean_obj_tag(v___x_3589_) == 0)
{
uint8_t v___x_3590_; 
lean_dec(v_b_3588_);
lean_dec(v_v_3587_);
lean_dec(v_j_3585_);
lean_dec(v_b_3584_);
lean_dec(v_v_3583_);
lean_dec(v_j_3581_);
lean_dec(v_x_3532_);
v___x_3590_ = 0;
return v___x_3590_;
}
else
{
lean_object* v_val_3591_; uint8_t v___x_3592_; 
v_val_3591_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_val_3591_);
lean_dec_ref_known(v___x_3589_, 1);
v___x_3592_ = l_Lean_IR_FnBody_alphaEqv(v_val_3591_, v_v_3583_, v_v_3587_);
if (v___x_3592_ == 0)
{
lean_dec(v_b_3588_);
lean_dec(v_j_3585_);
lean_dec(v_b_3584_);
lean_dec(v_j_3581_);
lean_dec(v_x_3532_);
return v___x_3592_;
}
else
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_IR_addVarRename(v_x_3532_, v_j_3581_, v_j_3585_);
v_x_3532_ = v___x_3593_;
v_x_3533_ = v_b_3584_;
v_x_3534_ = v_b_3588_;
goto _start;
}
}
}
else
{
uint8_t v___x_3595_; 
lean_dec_ref_known(v_x_3533_, 4);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3595_ = 0;
return v___x_3595_;
}
}
case 2:
{
if (lean_obj_tag(v_x_3534_) == 2)
{
lean_object* v_x_3596_; lean_object* v_i_3597_; lean_object* v_y_3598_; lean_object* v_b_3599_; lean_object* v_x_3600_; lean_object* v_i_3601_; lean_object* v_y_3602_; lean_object* v_b_3603_; uint8_t v___y_3605_; uint8_t v___x_3608_; 
v_x_3596_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3596_);
v_i_3597_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_i_3597_);
v_y_3598_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_y_3598_);
v_b_3599_ = lean_ctor_get(v_x_3533_, 3);
lean_inc(v_b_3599_);
lean_dec_ref_known(v_x_3533_, 4);
v_x_3600_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3600_);
v_i_3601_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_i_3601_);
v_y_3602_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_y_3602_);
v_b_3603_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_b_3603_);
lean_dec_ref_known(v_x_3534_, 4);
v___x_3608_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_x_3596_, v_x_3600_);
lean_dec(v_x_3600_);
lean_dec(v_x_3596_);
if (v___x_3608_ == 0)
{
lean_dec(v_i_3601_);
lean_dec(v_i_3597_);
v___y_3605_ = v___x_3608_;
goto v___jp_3604_;
}
else
{
uint8_t v___x_3609_; 
v___x_3609_ = lean_nat_dec_eq(v_i_3597_, v_i_3601_);
lean_dec(v_i_3601_);
lean_dec(v_i_3597_);
v___y_3605_ = v___x_3609_;
goto v___jp_3604_;
}
v___jp_3604_:
{
if (v___y_3605_ == 0)
{
lean_dec(v_b_3603_);
lean_dec(v_y_3602_);
lean_dec(v_b_3599_);
lean_dec(v_y_3598_);
lean_dec(v_x_3532_);
return v___y_3605_;
}
else
{
uint8_t v___x_3606_; 
v___x_3606_ = l_Lean_IR_Arg_alphaEqv(v_x_3532_, v_y_3598_, v_y_3602_);
lean_dec(v_y_3602_);
lean_dec(v_y_3598_);
if (v___x_3606_ == 0)
{
lean_dec(v_b_3603_);
lean_dec(v_b_3599_);
lean_dec(v_x_3532_);
return v___x_3606_;
}
else
{
v_x_3533_ = v_b_3599_;
v_x_3534_ = v_b_3603_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3610_; 
lean_dec_ref_known(v_x_3533_, 4);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3610_ = 0;
return v___x_3610_;
}
}
case 3:
{
if (lean_obj_tag(v_x_3534_) == 3)
{
lean_object* v_x_3611_; lean_object* v_cidx_3612_; lean_object* v_b_3613_; lean_object* v_x_3614_; lean_object* v_cidx_3615_; lean_object* v_b_3616_; uint8_t v___y_3618_; uint8_t v___x_3620_; 
v_x_3611_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3611_);
v_cidx_3612_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_cidx_3612_);
v_b_3613_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_b_3613_);
lean_dec_ref_known(v_x_3533_, 3);
v_x_3614_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3614_);
v_cidx_3615_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_cidx_3615_);
v_b_3616_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_b_3616_);
lean_dec_ref_known(v_x_3534_, 3);
v___x_3620_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_x_3611_, v_x_3614_);
lean_dec(v_x_3614_);
lean_dec(v_x_3611_);
if (v___x_3620_ == 0)
{
lean_dec(v_cidx_3615_);
lean_dec(v_cidx_3612_);
v___y_3618_ = v___x_3620_;
goto v___jp_3617_;
}
else
{
uint8_t v___x_3621_; 
v___x_3621_ = lean_nat_dec_eq(v_cidx_3612_, v_cidx_3615_);
lean_dec(v_cidx_3615_);
lean_dec(v_cidx_3612_);
v___y_3618_ = v___x_3621_;
goto v___jp_3617_;
}
v___jp_3617_:
{
if (v___y_3618_ == 0)
{
lean_dec(v_b_3616_);
lean_dec(v_b_3613_);
lean_dec(v_x_3532_);
return v___y_3618_;
}
else
{
v_x_3533_ = v_b_3613_;
v_x_3534_ = v_b_3616_;
goto _start;
}
}
}
else
{
uint8_t v___x_3622_; 
lean_dec_ref_known(v_x_3533_, 3);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3622_ = 0;
return v___x_3622_;
}
}
case 4:
{
if (lean_obj_tag(v_x_3534_) == 4)
{
lean_object* v_x_3623_; lean_object* v_i_3624_; lean_object* v_y_3625_; lean_object* v_b_3626_; lean_object* v_x_3627_; lean_object* v_i_3628_; lean_object* v_y_3629_; lean_object* v_b_3630_; uint8_t v___y_3632_; uint8_t v___x_3635_; 
v_x_3623_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3623_);
v_i_3624_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_i_3624_);
v_y_3625_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_y_3625_);
v_b_3626_ = lean_ctor_get(v_x_3533_, 3);
lean_inc(v_b_3626_);
lean_dec_ref_known(v_x_3533_, 4);
v_x_3627_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3627_);
v_i_3628_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_i_3628_);
v_y_3629_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_y_3629_);
v_b_3630_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_b_3630_);
lean_dec_ref_known(v_x_3534_, 4);
v___x_3635_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_x_3623_, v_x_3627_);
lean_dec(v_x_3627_);
lean_dec(v_x_3623_);
if (v___x_3635_ == 0)
{
lean_dec(v_i_3628_);
lean_dec(v_i_3624_);
v___y_3632_ = v___x_3635_;
goto v___jp_3631_;
}
else
{
uint8_t v___x_3636_; 
v___x_3636_ = lean_nat_dec_eq(v_i_3624_, v_i_3628_);
lean_dec(v_i_3628_);
lean_dec(v_i_3624_);
v___y_3632_ = v___x_3636_;
goto v___jp_3631_;
}
v___jp_3631_:
{
if (v___y_3632_ == 0)
{
lean_dec(v_b_3630_);
lean_dec(v_y_3629_);
lean_dec(v_b_3626_);
lean_dec(v_y_3625_);
lean_dec(v_x_3532_);
return v___y_3632_;
}
else
{
uint8_t v___x_3633_; 
v___x_3633_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_y_3625_, v_y_3629_);
lean_dec(v_y_3629_);
lean_dec(v_y_3625_);
if (v___x_3633_ == 0)
{
lean_dec(v_b_3630_);
lean_dec(v_b_3626_);
lean_dec(v_x_3532_);
return v___x_3633_;
}
else
{
v_x_3533_ = v_b_3626_;
v_x_3534_ = v_b_3630_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_3637_; 
lean_dec_ref_known(v_x_3533_, 4);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3637_ = 0;
return v___x_3637_;
}
}
case 5:
{
if (lean_obj_tag(v_x_3534_) == 5)
{
lean_object* v_x_3638_; lean_object* v_i_3639_; lean_object* v_offset_3640_; lean_object* v_y_3641_; lean_object* v_ty_3642_; lean_object* v_b_3643_; lean_object* v_x_3644_; lean_object* v_i_3645_; lean_object* v_offset_3646_; lean_object* v_y_3647_; lean_object* v_ty_3648_; lean_object* v_b_3649_; uint8_t v___y_3651_; uint8_t v___x_3656_; 
v_x_3638_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3638_);
v_i_3639_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_i_3639_);
v_offset_3640_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_offset_3640_);
v_y_3641_ = lean_ctor_get(v_x_3533_, 3);
lean_inc(v_y_3641_);
v_ty_3642_ = lean_ctor_get(v_x_3533_, 4);
lean_inc(v_ty_3642_);
v_b_3643_ = lean_ctor_get(v_x_3533_, 5);
lean_inc(v_b_3643_);
lean_dec_ref_known(v_x_3533_, 6);
v_x_3644_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3644_);
v_i_3645_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_i_3645_);
v_offset_3646_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_offset_3646_);
v_y_3647_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_y_3647_);
v_ty_3648_ = lean_ctor_get(v_x_3534_, 4);
lean_inc(v_ty_3648_);
v_b_3649_ = lean_ctor_get(v_x_3534_, 5);
lean_inc(v_b_3649_);
lean_dec_ref_known(v_x_3534_, 6);
v___x_3656_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_x_3638_, v_x_3644_);
lean_dec(v_x_3644_);
lean_dec(v_x_3638_);
if (v___x_3656_ == 0)
{
lean_dec(v_i_3645_);
lean_dec(v_i_3639_);
v___y_3651_ = v___x_3656_;
goto v___jp_3650_;
}
else
{
uint8_t v___x_3657_; 
v___x_3657_ = lean_nat_dec_eq(v_i_3639_, v_i_3645_);
lean_dec(v_i_3645_);
lean_dec(v_i_3639_);
v___y_3651_ = v___x_3657_;
goto v___jp_3650_;
}
v___jp_3650_:
{
if (v___y_3651_ == 0)
{
lean_dec(v_b_3649_);
lean_dec(v_ty_3648_);
lean_dec(v_y_3647_);
lean_dec(v_offset_3646_);
lean_dec(v_b_3643_);
lean_dec(v_ty_3642_);
lean_dec(v_y_3641_);
lean_dec(v_offset_3640_);
lean_dec(v_x_3532_);
return v___y_3651_;
}
else
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_nat_dec_eq(v_offset_3640_, v_offset_3646_);
lean_dec(v_offset_3646_);
lean_dec(v_offset_3640_);
if (v___x_3652_ == 0)
{
lean_dec(v_b_3649_);
lean_dec(v_ty_3648_);
lean_dec(v_y_3647_);
lean_dec(v_b_3643_);
lean_dec(v_ty_3642_);
lean_dec(v_y_3641_);
lean_dec(v_x_3532_);
return v___x_3652_;
}
else
{
uint8_t v___x_3653_; 
v___x_3653_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_y_3641_, v_y_3647_);
lean_dec(v_y_3647_);
lean_dec(v_y_3641_);
if (v___x_3653_ == 0)
{
lean_dec(v_b_3649_);
lean_dec(v_ty_3648_);
lean_dec(v_b_3643_);
lean_dec(v_ty_3642_);
lean_dec(v_x_3532_);
return v___x_3653_;
}
else
{
uint8_t v___x_3654_; 
v___x_3654_ = l_Lean_IR_instBEqIRType_beq(v_ty_3642_, v_ty_3648_);
lean_dec(v_ty_3648_);
lean_dec(v_ty_3642_);
if (v___x_3654_ == 0)
{
lean_dec(v_b_3649_);
lean_dec(v_b_3643_);
lean_dec(v_x_3532_);
return v___x_3654_;
}
else
{
v_x_3533_ = v_b_3643_;
v_x_3534_ = v_b_3649_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_3658_; 
lean_dec_ref_known(v_x_3533_, 6);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3658_ = 0;
return v___x_3658_;
}
}
case 6:
{
if (lean_obj_tag(v_x_3534_) == 6)
{
lean_object* v_x_3659_; lean_object* v_n_3660_; uint8_t v_c_3661_; uint8_t v_persistent_3662_; lean_object* v_b_3663_; lean_object* v_x_3664_; lean_object* v_n_3665_; uint8_t v_c_3666_; uint8_t v_persistent_3667_; lean_object* v_b_3668_; 
v_x_3659_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3659_);
v_n_3660_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_n_3660_);
v_c_3661_ = lean_ctor_get_uint8(v_x_3533_, sizeof(void*)*3);
v_persistent_3662_ = lean_ctor_get_uint8(v_x_3533_, sizeof(void*)*3 + 1);
v_b_3663_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_b_3663_);
lean_dec_ref_known(v_x_3533_, 3);
v_x_3664_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3664_);
v_n_3665_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_n_3665_);
v_c_3666_ = lean_ctor_get_uint8(v_x_3534_, sizeof(void*)*3);
v_persistent_3667_ = lean_ctor_get_uint8(v_x_3534_, sizeof(void*)*3 + 1);
v_b_3668_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_b_3668_);
lean_dec_ref_known(v_x_3534_, 3);
v_00_u03c1_3553_ = v_x_3532_;
v_x_u2081_3554_ = v_x_3659_;
v_n_u2081_3555_ = v_n_3660_;
v_c_u2081_3556_ = v_c_3661_;
v_p_u2081_3557_ = v_persistent_3662_;
v_b_u2081_3558_ = v_b_3663_;
v_x_u2082_3559_ = v_x_3664_;
v_n_u2082_3560_ = v_n_3665_;
v_c_u2082_3561_ = v_c_3666_;
v_p_u2082_3562_ = v_persistent_3667_;
v_b_u2082_3563_ = v_b_3668_;
goto v___jp_3552_;
}
else
{
uint8_t v___x_3669_; 
lean_dec_ref_known(v_x_3533_, 3);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3669_ = 0;
return v___x_3669_;
}
}
case 7:
{
if (lean_obj_tag(v_x_3534_) == 7)
{
lean_object* v_x_3670_; lean_object* v_n_3671_; uint8_t v_c_3672_; uint8_t v_persistent_3673_; lean_object* v_b_3674_; lean_object* v_x_3675_; lean_object* v_n_3676_; uint8_t v_c_3677_; uint8_t v_persistent_3678_; lean_object* v_b_3679_; 
v_x_3670_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3670_);
v_n_3671_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_n_3671_);
v_c_3672_ = lean_ctor_get_uint8(v_x_3533_, sizeof(void*)*3);
v_persistent_3673_ = lean_ctor_get_uint8(v_x_3533_, sizeof(void*)*3 + 1);
v_b_3674_ = lean_ctor_get(v_x_3533_, 2);
lean_inc(v_b_3674_);
lean_dec_ref_known(v_x_3533_, 3);
v_x_3675_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3675_);
v_n_3676_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_n_3676_);
v_c_3677_ = lean_ctor_get_uint8(v_x_3534_, sizeof(void*)*3);
v_persistent_3678_ = lean_ctor_get_uint8(v_x_3534_, sizeof(void*)*3 + 1);
v_b_3679_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_b_3679_);
lean_dec_ref_known(v_x_3534_, 3);
v_00_u03c1_3553_ = v_x_3532_;
v_x_u2081_3554_ = v_x_3670_;
v_n_u2081_3555_ = v_n_3671_;
v_c_u2081_3556_ = v_c_3672_;
v_p_u2081_3557_ = v_persistent_3673_;
v_b_u2081_3558_ = v_b_3674_;
v_x_u2082_3559_ = v_x_3675_;
v_n_u2082_3560_ = v_n_3676_;
v_c_u2082_3561_ = v_c_3677_;
v_p_u2082_3562_ = v_persistent_3678_;
v_b_u2082_3563_ = v_b_3679_;
goto v___jp_3552_;
}
else
{
uint8_t v___x_3680_; 
lean_dec_ref_known(v_x_3533_, 3);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3680_ = 0;
return v___x_3680_;
}
}
case 8:
{
if (lean_obj_tag(v_x_3534_) == 8)
{
lean_object* v_x_3681_; lean_object* v_b_3682_; lean_object* v_x_3683_; lean_object* v_b_3684_; uint8_t v___x_3685_; 
v_x_3681_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3681_);
v_b_3682_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_b_3682_);
lean_dec_ref_known(v_x_3533_, 2);
v_x_3683_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3683_);
v_b_3684_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_b_3684_);
lean_dec_ref_known(v_x_3534_, 2);
v___x_3685_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_x_3681_, v_x_3683_);
lean_dec(v_x_3683_);
lean_dec(v_x_3681_);
if (v___x_3685_ == 0)
{
lean_dec(v_b_3684_);
lean_dec(v_b_3682_);
lean_dec(v_x_3532_);
return v___x_3685_;
}
else
{
v_x_3533_ = v_b_3682_;
v_x_3534_ = v_b_3684_;
goto _start;
}
}
else
{
uint8_t v___x_3687_; 
lean_dec_ref_known(v_x_3533_, 2);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3687_ = 0;
return v___x_3687_;
}
}
case 9:
{
if (lean_obj_tag(v_x_3534_) == 9)
{
lean_object* v_tid_3688_; lean_object* v_x_3689_; lean_object* v_cs_3690_; lean_object* v_tid_3691_; lean_object* v_x_3692_; lean_object* v_cs_3693_; uint8_t v___y_3695_; uint8_t v___x_3700_; 
v_tid_3688_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_tid_3688_);
v_x_3689_ = lean_ctor_get(v_x_3533_, 1);
lean_inc(v_x_3689_);
v_cs_3690_ = lean_ctor_get(v_x_3533_, 3);
lean_inc_ref(v_cs_3690_);
lean_dec_ref_known(v_x_3533_, 4);
v_tid_3691_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_tid_3691_);
v_x_3692_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_x_3692_);
v_cs_3693_ = lean_ctor_get(v_x_3534_, 3);
lean_inc_ref(v_cs_3693_);
lean_dec_ref_known(v_x_3534_, 4);
v___x_3700_ = lean_name_eq(v_tid_3688_, v_tid_3691_);
lean_dec(v_tid_3691_);
lean_dec(v_tid_3688_);
if (v___x_3700_ == 0)
{
lean_dec(v_x_3692_);
lean_dec(v_x_3689_);
v___y_3695_ = v___x_3700_;
goto v___jp_3694_;
}
else
{
uint8_t v___x_3701_; 
v___x_3701_ = l_Lean_IR_VarId_alphaEqv(v_x_3532_, v_x_3689_, v_x_3692_);
lean_dec(v_x_3692_);
lean_dec(v_x_3689_);
v___y_3695_ = v___x_3701_;
goto v___jp_3694_;
}
v___jp_3694_:
{
if (v___y_3695_ == 0)
{
lean_dec_ref(v_cs_3693_);
lean_dec_ref(v_cs_3690_);
lean_dec(v_x_3532_);
return v___y_3695_;
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3696_ = lean_array_get_size(v_cs_3690_);
v___x_3697_ = lean_array_get_size(v_cs_3693_);
v___x_3698_ = lean_nat_dec_eq(v___x_3696_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_dec_ref(v_cs_3693_);
lean_dec_ref(v_cs_3690_);
lean_dec(v_x_3532_);
return v___x_3698_;
}
else
{
uint8_t v___x_3699_; 
v___x_3699_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3532_, v_cs_3690_, v_cs_3693_, v___x_3696_);
lean_dec_ref(v_cs_3693_);
lean_dec_ref(v_cs_3690_);
return v___x_3699_;
}
}
}
}
else
{
uint8_t v___x_3702_; 
lean_dec_ref_known(v_x_3533_, 4);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3702_ = 0;
return v___x_3702_;
}
}
case 10:
{
if (lean_obj_tag(v_x_3534_) == 10)
{
lean_object* v_x_3703_; lean_object* v_x_3704_; uint8_t v___x_3705_; 
v_x_3703_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_x_3703_);
lean_dec_ref_known(v_x_3533_, 1);
v_x_3704_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_x_3704_);
lean_dec_ref_known(v_x_3534_, 1);
v___x_3705_ = l_Lean_IR_Arg_alphaEqv(v_x_3532_, v_x_3703_, v_x_3704_);
lean_dec(v_x_3704_);
lean_dec(v_x_3703_);
lean_dec(v_x_3532_);
return v___x_3705_;
}
else
{
uint8_t v___x_3706_; 
lean_dec_ref_known(v_x_3533_, 1);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3706_ = 0;
return v___x_3706_;
}
}
case 11:
{
if (lean_obj_tag(v_x_3534_) == 11)
{
lean_object* v_j_3707_; lean_object* v_ys_3708_; lean_object* v_j_3709_; lean_object* v_ys_3710_; uint8_t v___x_3711_; 
v_j_3707_ = lean_ctor_get(v_x_3533_, 0);
lean_inc(v_j_3707_);
v_ys_3708_ = lean_ctor_get(v_x_3533_, 1);
lean_inc_ref(v_ys_3708_);
lean_dec_ref_known(v_x_3533_, 2);
v_j_3709_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_j_3709_);
v_ys_3710_ = lean_ctor_get(v_x_3534_, 1);
lean_inc_ref(v_ys_3710_);
lean_dec_ref_known(v_x_3534_, 2);
v___x_3711_ = lean_nat_dec_eq(v_j_3707_, v_j_3709_);
lean_dec(v_j_3709_);
lean_dec(v_j_3707_);
if (v___x_3711_ == 0)
{
lean_dec_ref(v_ys_3710_);
lean_dec_ref(v_ys_3708_);
lean_dec(v_x_3532_);
return v___x_3711_;
}
else
{
uint8_t v___x_3712_; 
v___x_3712_ = l_Lean_IR_args_alphaEqv(v_x_3532_, v_ys_3708_, v_ys_3710_);
lean_dec_ref(v_ys_3710_);
lean_dec_ref(v_ys_3708_);
lean_dec(v_x_3532_);
return v___x_3712_;
}
}
else
{
uint8_t v___x_3713_; 
lean_dec_ref_known(v_x_3533_, 2);
lean_dec(v_x_3534_);
lean_dec(v_x_3532_);
v___x_3713_ = 0;
return v___x_3713_;
}
}
default: 
{
lean_dec(v_x_3532_);
if (lean_obj_tag(v_x_3534_) == 12)
{
uint8_t v___x_3714_; 
v___x_3714_ = 1;
return v___x_3714_;
}
else
{
uint8_t v___x_3715_; 
lean_dec(v_x_3534_);
v___x_3715_ = 0;
return v___x_3715_;
}
}
}
v___jp_3535_:
{
if (v___y_3539_ == 0)
{
if (v___y_3538_ == 0)
{
v_x_3532_ = v___y_3537_;
v_x_3533_ = v___y_3540_;
v_x_3534_ = v___y_3536_;
goto _start;
}
else
{
lean_dec(v___y_3540_);
lean_dec(v___y_3537_);
lean_dec(v___y_3536_);
return v___y_3539_;
}
}
else
{
if (v___y_3538_ == 0)
{
lean_dec(v___y_3540_);
lean_dec(v___y_3537_);
lean_dec(v___y_3536_);
return v___y_3538_;
}
else
{
v_x_3532_ = v___y_3537_;
v_x_3533_ = v___y_3540_;
v_x_3534_ = v___y_3536_;
goto _start;
}
}
}
v___jp_3543_:
{
if (v___y_3551_ == 0)
{
lean_dec(v___y_3550_);
lean_dec(v___y_3545_);
lean_dec(v___y_3544_);
return v___y_3551_;
}
else
{
if (v___y_3547_ == 0)
{
if (v___y_3546_ == 0)
{
v___y_3536_ = v___y_3545_;
v___y_3537_ = v___y_3544_;
v___y_3538_ = v___y_3549_;
v___y_3539_ = v___y_3548_;
v___y_3540_ = v___y_3550_;
goto v___jp_3535_;
}
else
{
lean_dec(v___y_3550_);
lean_dec(v___y_3545_);
lean_dec(v___y_3544_);
return v___y_3547_;
}
}
else
{
if (v___y_3546_ == 0)
{
lean_dec(v___y_3550_);
lean_dec(v___y_3545_);
lean_dec(v___y_3544_);
return v___y_3546_;
}
else
{
v___y_3536_ = v___y_3545_;
v___y_3537_ = v___y_3544_;
v___y_3538_ = v___y_3549_;
v___y_3539_ = v___y_3548_;
v___y_3540_ = v___y_3550_;
goto v___jp_3535_;
}
}
}
}
v___jp_3552_:
{
uint8_t v___x_3564_; 
v___x_3564_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_3553_, v_x_u2081_3554_, v_x_u2082_3559_);
lean_dec(v_x_u2082_3559_);
lean_dec(v_x_u2081_3554_);
if (v___x_3564_ == 0)
{
lean_dec(v_n_u2082_3560_);
lean_dec(v_n_u2081_3555_);
v___y_3544_ = v_00_u03c1_3553_;
v___y_3545_ = v_b_u2082_3563_;
v___y_3546_ = v_c_u2081_3556_;
v___y_3547_ = v_c_u2082_3561_;
v___y_3548_ = v_p_u2082_3562_;
v___y_3549_ = v_p_u2081_3557_;
v___y_3550_ = v_b_u2081_3558_;
v___y_3551_ = v___x_3564_;
goto v___jp_3543_;
}
else
{
uint8_t v___x_3565_; 
v___x_3565_ = lean_nat_dec_eq(v_n_u2081_3555_, v_n_u2082_3560_);
lean_dec(v_n_u2082_3560_);
lean_dec(v_n_u2081_3555_);
v___y_3544_ = v_00_u03c1_3553_;
v___y_3545_ = v_b_u2082_3563_;
v___y_3546_ = v_c_u2081_3556_;
v___y_3547_ = v_c_u2082_3561_;
v___y_3548_ = v_p_u2082_3562_;
v___y_3549_ = v_p_u2081_3557_;
v___y_3550_ = v_b_u2081_3558_;
v___y_3551_ = v___x_3565_;
goto v___jp_3543_;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* v_x_3716_, lean_object* v_xs_3717_, lean_object* v_ys_3718_, lean_object* v_x_3719_){
_start:
{
lean_object* v_zero_3720_; uint8_t v_isZero_3721_; 
v_zero_3720_ = lean_unsigned_to_nat(0u);
v_isZero_3721_ = lean_nat_dec_eq(v_x_3719_, v_zero_3720_);
if (v_isZero_3721_ == 1)
{
lean_dec(v_x_3719_);
lean_dec(v_x_3716_);
return v_isZero_3721_;
}
else
{
lean_object* v_one_3722_; lean_object* v_n_3723_; uint8_t v___y_3725_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_one_3722_ = lean_unsigned_to_nat(1u);
v_n_3723_ = lean_nat_sub(v_x_3719_, v_one_3722_);
lean_dec(v_x_3719_);
v___x_3727_ = lean_array_fget_borrowed(v_xs_3717_, v_n_3723_);
v___x_3728_ = lean_array_fget_borrowed(v_ys_3718_, v_n_3723_);
if (lean_obj_tag(v___x_3727_) == 0)
{
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_info_3729_; lean_object* v_b_3730_; lean_object* v_info_3731_; lean_object* v_b_3732_; uint8_t v___x_3733_; 
v_info_3729_ = lean_ctor_get(v___x_3727_, 0);
v_b_3730_ = lean_ctor_get(v___x_3727_, 1);
v_info_3731_ = lean_ctor_get(v___x_3728_, 0);
v_b_3732_ = lean_ctor_get(v___x_3728_, 1);
v___x_3733_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_3729_, v_info_3731_);
if (v___x_3733_ == 0)
{
v___y_3725_ = v___x_3733_;
goto v___jp_3724_;
}
else
{
uint8_t v___x_3734_; 
lean_inc(v_b_3732_);
lean_inc(v_b_3730_);
lean_inc(v_x_3716_);
v___x_3734_ = l_Lean_IR_FnBody_alphaEqv(v_x_3716_, v_b_3730_, v_b_3732_);
v___y_3725_ = v___x_3734_;
goto v___jp_3724_;
}
}
else
{
lean_dec(v_n_3723_);
lean_dec(v_x_3716_);
return v_isZero_3721_;
}
}
else
{
if (lean_obj_tag(v___x_3728_) == 1)
{
lean_object* v_b_3735_; lean_object* v_b_3736_; uint8_t v___x_3737_; 
v_b_3735_ = lean_ctor_get(v___x_3727_, 0);
v_b_3736_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_b_3736_);
lean_inc(v_b_3735_);
lean_inc(v_x_3716_);
v___x_3737_ = l_Lean_IR_FnBody_alphaEqv(v_x_3716_, v_b_3735_, v_b_3736_);
v___y_3725_ = v___x_3737_;
goto v___jp_3724_;
}
else
{
lean_dec(v_n_3723_);
lean_dec(v_x_3716_);
return v_isZero_3721_;
}
}
v___jp_3724_:
{
if (v___y_3725_ == 0)
{
lean_dec(v_n_3723_);
lean_dec(v_x_3716_);
return v___y_3725_;
}
else
{
v_x_3719_ = v_n_3723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* v_x_3738_, lean_object* v_xs_3739_, lean_object* v_ys_3740_, lean_object* v_x_3741_){
_start:
{
uint8_t v_res_3742_; lean_object* v_r_3743_; 
v_res_3742_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3738_, v_xs_3739_, v_ys_3740_, v_x_3741_);
lean_dec_ref(v_ys_3740_);
lean_dec_ref(v_xs_3739_);
v_r_3743_ = lean_box(v_res_3742_);
return v_r_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* v_x_3744_, lean_object* v_x_3745_, lean_object* v_x_3746_){
_start:
{
uint8_t v_res_3747_; lean_object* v_r_3748_; 
v_res_3747_ = l_Lean_IR_FnBody_alphaEqv(v_x_3744_, v_x_3745_, v_x_3746_);
v_r_3748_ = lean_box(v_res_3747_);
return v_r_3748_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(lean_object* v_x_3749_, lean_object* v_xs_3750_, lean_object* v_ys_3751_, lean_object* v_hsz_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_){
_start:
{
uint8_t v___x_3755_; 
v___x_3755_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(v_x_3749_, v_xs_3750_, v_ys_3751_, v_x_3753_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* v_x_3756_, lean_object* v_xs_3757_, lean_object* v_ys_3758_, lean_object* v_hsz_3759_, lean_object* v_x_3760_, lean_object* v_x_3761_){
_start:
{
uint8_t v_res_3762_; lean_object* v_r_3763_; 
v_res_3762_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(v_x_3756_, v_xs_3757_, v_ys_3758_, v_hsz_3759_, v_x_3760_, v_x_3761_);
lean_dec_ref(v_ys_3758_);
lean_dec_ref(v_xs_3757_);
v_r_3763_ = lean_box(v_res_3762_);
return v_r_3763_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* v_b_u2081_3764_, lean_object* v_b_u2082_3765_){
_start:
{
lean_object* v___x_3766_; uint8_t v___x_3767_; 
v___x_3766_ = lean_box(1);
v___x_3767_ = l_Lean_IR_FnBody_alphaEqv(v___x_3766_, v_b_u2081_3764_, v_b_u2082_3765_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* v_b_u2081_3768_, lean_object* v_b_u2082_3769_){
_start:
{
uint8_t v_res_3770_; lean_object* v_r_3771_; 
v_res_3770_ = l_Lean_IR_FnBody_beq(v_b_u2081_3768_, v_b_u2082_3769_);
v_r_3771_ = lean_box(v_res_3770_);
return v_r_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* v_x_3792_, lean_object* v_t_3793_, lean_object* v_e_3794_){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3795_ = ((lean_object*)(l_Lean_IR_mkIf___closed__1));
v___x_3796_ = lean_box(1);
v___x_3797_ = ((lean_object*)(l_Lean_IR_mkIf___closed__4));
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v_e_3794_);
v___x_3799_ = ((lean_object*)(l_Lean_IR_mkIf___closed__7));
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
lean_ctor_set(v___x_3800_, 1, v_t_3793_);
v___x_3801_ = lean_unsigned_to_nat(2u);
v___x_3802_ = lean_mk_empty_array_with_capacity(v___x_3801_);
v___x_3803_ = lean_array_push(v___x_3802_, v___x_3798_);
v___x_3804_ = lean_array_push(v___x_3803_, v___x_3800_);
v___x_3805_ = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3795_);
lean_ctor_set(v___x_3805_, 1, v_x_3792_);
lean_ctor_set(v___x_3805_, 2, v___x_3796_);
lean_ctor_set(v___x_3805_, 3, v___x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* v_t_3812_){
_start:
{
switch(lean_obj_tag(v_t_3812_))
{
case 5:
{
lean_object* v___x_3813_; 
v___x_3813_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__0));
return v___x_3813_;
}
case 3:
{
lean_object* v___x_3814_; 
v___x_3814_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__1));
return v___x_3814_;
}
case 4:
{
lean_object* v___x_3815_; 
v___x_3815_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__2));
return v___x_3815_;
}
case 0:
{
lean_object* v___x_3816_; 
v___x_3816_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__3));
return v___x_3816_;
}
case 9:
{
lean_object* v___x_3817_; 
v___x_3817_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__4));
return v___x_3817_;
}
default: 
{
lean_object* v___x_3818_; 
v___x_3818_ = ((lean_object*)(l_Lean_IR_getUnboxOpName___closed__5));
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* v_t_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_IR_getUnboxOpName(v_t_3819_);
lean_dec(v_t_3819_);
return v_res_3820_;
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
