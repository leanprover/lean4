// Lean compiler output
// Module: Lean.Expr
// Imports: public import Init.Data.Hashable public import Lean.Level import Init.Omega
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_uint64_to_uint8(uint64_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint32_t lean_uint64_to_uint32(uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint64_t lean_uint32_to_uint64(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_instReprLevel_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_KVMap_size(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_decEq___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedLiteral_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedLiteral_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLiteral_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLiteral_default = (const lean_object*)&l_Lean_instInhabitedLiteral_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLiteral = (const lean_object*)&l_Lean_instInhabitedLiteral_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqLiteral_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqLiteral___closed__0 = (const lean_object*)&l_Lean_instBEqLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqLiteral = (const lean_object*)&l_Lean_instBEqLiteral___closed__0_value;
static const lean_string_object l_Lean_instReprLiteral_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Literal.natVal"};
static const lean_object* l_Lean_instReprLiteral_repr___closed__0 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__1 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__2 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__2_value;
static lean_once_cell_t l_Lean_instReprLiteral_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLiteral_repr___closed__3;
static lean_once_cell_t l_Lean_instReprLiteral_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLiteral_repr___closed__4;
static const lean_string_object l_Lean_instReprLiteral_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Literal.strVal"};
static const lean_object* l_Lean_instReprLiteral_repr___closed__5 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__5_value)}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__6 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__7 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLiteral_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLiteral___closed__0 = (const lean_object*)&l_Lean_instReprLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLiteral = (const lean_object*)&l_Lean_instReprLiteral___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Literal_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLiteral___closed__0 = (const lean_object*)&l_Lean_instHashableLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLiteral = (const lean_object*)&l_Lean_instHashableLiteral___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instLTLiteral;
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo;
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqBinderInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqBinderInfo___closed__0 = (const lean_object*)&l_Lean_instBEqBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqBinderInfo = (const lean_object*)&l_Lean_instBEqBinderInfo___closed__0_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.BinderInfo.default"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__0 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__1 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__1_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.BinderInfo.implicit"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__2 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__3 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__3_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.BinderInfo.strictImplicit"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__4 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__5 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__5_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.BinderInfo.instImplicit"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__6 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__6_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__7 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprBinderInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprBinderInfo___closed__0 = (const lean_object*)&l_Lean_instReprBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprBinderInfo = (const lean_object*)&l_Lean_instReprBinderInfo___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_BinderInfo_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableBinderInfo___closed__0 = (const lean_object*)&l_Lean_instHashableBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableBinderInfo = (const lean_object*)&l_Lean_instHashableBinderInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_empty;
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1___aux__1;
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1;
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instBEqData__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqData__1___closed__0 = (const lean_object*)&l_Lean_instBEqData__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqData__1 = (const lean_object*)&l_Lean_instBEqData__1___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
uint64_t lean_expr_mk_data(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_expr_mk_app_data(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (hasLevelMVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (hasExprMVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " (hasFVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (approxDepth := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expr.mkData "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__7_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " (looseBVarRange := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__8 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprData__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprData__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprData__1___closed__0 = (const lean_object*)&l_Lean_instReprData__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprData__1 = (const lean_object*)&l_Lean_instReprData__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqFVarId___closed__0 = (const lean_object*)&l_Lean_instBEqFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqFVarId = (const lean_object*)&l_Lean_instBEqFVarId___closed__0_value;
static lean_once_cell_t l_Lean_instHashableFVarId_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableFVarId_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableFVarId___closed__0 = (const lean_object*)&l_Lean_instHashableFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableFVarId = (const lean_object*)&l_Lean_instHashableFVarId___closed__0_value;
static const lean_closure_object l_Lean_instReprFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprFVarId___closed__0 = (const lean_object*)&l_Lean_instReprFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprFVarId = (const lean_object*)&l_Lean_instReprFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdSet;
static const lean_closure_object l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0 = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
static const lean_closure_object l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instSingletonFVarIdFVarIdSet___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instSingletonFVarIdFVarIdSet___closed__0 = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instSingletonFVarIdFVarIdSet = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0;
static lean_once_cell_t l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1;
static lean_once_cell_t l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdHashSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdHashSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId;
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqMVarId___closed__0 = (const lean_object*)&l_Lean_instBEqMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqMVarId = (const lean_object*)&l_Lean_instBEqMVarId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableMVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableMVarId___closed__0 = (const lean_object*)&l_Lean_instHashableMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableMVarId = (const lean_object*)&l_Lean_instHashableMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprMVarId = (const lean_object*)&l_Lean_instReprFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdSet;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_expr_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.bvar"};
static const lean_object* l_Lean_instReprExpr_repr___closed__0 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__1 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__2 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__2_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.fvar"};
static const lean_object* l_Lean_instReprExpr_repr___closed__3 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__3_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__3_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__4 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__5 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__5_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.mvar"};
static const lean_object* l_Lean_instReprExpr_repr___closed__6 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__6_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__7 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__7_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__8 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__8_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.sort"};
static const lean_object* l_Lean_instReprExpr_repr___closed__9 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__9_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__9_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__10 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__10_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__11 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__11_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Expr.const"};
static const lean_object* l_Lean_instReprExpr_repr___closed__12 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__12_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__12_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__13 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__13_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__14 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__14_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Expr.app"};
static const lean_object* l_Lean_instReprExpr_repr___closed__15 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__15_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__15_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__16 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__16_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__17 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__17_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Expr.lam"};
static const lean_object* l_Lean_instReprExpr_repr___closed__18 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__18_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__18_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__19 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__19_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__20 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__20_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.forallE"};
static const lean_object* l_Lean_instReprExpr_repr___closed__21 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__21_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__21_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__22 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__22_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__23 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__23_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.letE"};
static const lean_object* l_Lean_instReprExpr_repr___closed__24 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__24_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__24_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__25 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__25_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__26 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__26_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Expr.lit"};
static const lean_object* l_Lean_instReprExpr_repr___closed__27 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__27_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__27_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__28 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__28_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__28_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__29 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__29_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Expr.mdata"};
static const lean_object* l_Lean_instReprExpr_repr___closed__30 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__30_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__30_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__31 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__31_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__31_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__32 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__32_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.proj"};
static const lean_object* l_Lean_instReprExpr_repr___closed__33 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__33_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__33_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__34 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__34_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__34_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__35 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__35_value;
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprExpr___closed__0 = (const lean_object*)&l_Lean_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprExpr = (const lean_object*)&l_Lean_instReprExpr___closed__0_value;
static const lean_string_object l_Lean_instInhabitedExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedExpr___closed__0 = (const lean_object*)&l_Lean_instInhabitedExpr___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedExpr___closed__1 = (const lean_object*)&l_Lean_instInhabitedExpr___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExpr;
static const lean_string_object l_Lean_Expr_ctorName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l_Lean_Expr_ctorName___closed__0 = (const lean_object*)&l_Lean_Expr_ctorName___closed__0_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l_Lean_Expr_ctorName___closed__1 = (const lean_object*)&l_Lean_Expr_ctorName___closed__1_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mvar"};
static const lean_object* l_Lean_Expr_ctorName___closed__2 = (const lean_object*)&l_Lean_Expr_ctorName___closed__2_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_Lean_Expr_ctorName___closed__3 = (const lean_object*)&l_Lean_Expr_ctorName___closed__3_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Expr_ctorName___closed__4 = (const lean_object*)&l_Lean_Expr_ctorName___closed__4_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Expr_ctorName___closed__5 = (const lean_object*)&l_Lean_Expr_ctorName___closed__5_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l_Lean_Expr_ctorName___closed__6 = (const lean_object*)&l_Lean_Expr_ctorName___closed__6_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l_Lean_Expr_ctorName___closed__7 = (const lean_object*)&l_Lean_Expr_ctorName___closed__7_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l_Lean_Expr_ctorName___closed__8 = (const lean_object*)&l_Lean_Expr_ctorName___closed__8_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l_Lean_Expr_ctorName___closed__9 = (const lean_object*)&l_Lean_Expr_ctorName___closed__9_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l_Lean_Expr_ctorName___closed__10 = (const lean_object*)&l_Lean_Expr_ctorName___closed__10_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Expr_ctorName___closed__11 = (const lean_object*)&l_Lean_Expr_ctorName___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_instHashable___closed__0 = (const lean_object*)&l_Lean_Expr_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Expr_instHashable = (const lean_object*)&l_Lean_Expr_instHashable___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
LEAN_EXPORT uint64_t lean_expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static const lean_string_object l_Lean_Literal_type___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Literal_type___closed__0 = (const lean_object*)&l_Lean_Literal_type___closed__0_value;
static const lean_ctor_object l_Lean_Literal_type___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Literal_type___closed__1 = (const lean_object*)&l_Lean_Literal_type___closed__1_value;
static lean_once_cell_t l_Lean_Literal_type___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Literal_type___closed__2;
static const lean_string_object l_Lean_Literal_type___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Literal_type___closed__3 = (const lean_object*)&l_Lean_Literal_type___closed__3_value;
static const lean_ctor_object l_Lean_Literal_type___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Literal_type___closed__4 = (const lean_object*)&l_Lean_Literal_type___closed__4_value;
static lean_once_cell_t l_Lean_Literal_type___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Literal_type___closed__5;
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_lit_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkSimpleThunkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_mkSimpleThunkType___closed__0 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__0_value;
static const lean_ctor_object l_Lean_mkSimpleThunkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSimpleThunkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_mkSimpleThunkType___closed__1 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__1_value;
static const lean_string_object l_Lean_mkSimpleThunkType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_mkSimpleThunkType___closed__2 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__2_value;
static const lean_ctor_object l_Lean_mkSimpleThunkType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSimpleThunkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_mkSimpleThunkType___closed__3 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__3_value;
static lean_once_cell_t l_Lean_mkSimpleThunkType___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkSimpleThunkType___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object*);
static const lean_string_object l_Lean_mkInstOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_mkInstOfNatNat___closed__0 = (const lean_object*)&l_Lean_mkInstOfNatNat___closed__0_value;
static const lean_ctor_object l_Lean_mkInstOfNatNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkInstOfNatNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_mkInstOfNatNat___closed__1 = (const lean_object*)&l_Lean_mkInstOfNatNat___closed__1_value;
static lean_once_cell_t l_Lean_mkInstOfNatNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkInstOfNatNat___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object*);
static const lean_string_object l_Lean_mkNatLitCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_mkNatLitCore___closed__0 = (const lean_object*)&l_Lean_mkNatLitCore___closed__0_value;
static const lean_string_object l_Lean_mkNatLitCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_mkNatLitCore___closed__1 = (const lean_object*)&l_Lean_mkNatLitCore___closed__1_value;
static const lean_ctor_object l_Lean_mkNatLitCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatLitCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_mkNatLitCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatLitCore___closed__2_value_aux_0),((lean_object*)&l_Lean_mkNatLitCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_mkNatLitCore___closed__2 = (const lean_object*)&l_Lean_mkNatLitCore___closed__2_value;
static const lean_ctor_object l_Lean_mkNatLitCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_mkNatLitCore___closed__3 = (const lean_object*)&l_Lean_mkNatLitCore___closed__3_value;
static lean_once_cell_t l_Lean_mkNatLitCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatLitCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_instBEq___closed__0 = (const lean_object*)&l_Lean_Expr_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Expr_instBEq = (const lean_object*)&l_Lean_Expr_instBEq___closed__0_value;
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_appFn_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l_Lean_Expr_appFn_x21___closed__0 = (const lean_object*)&l_Lean_Expr_appFn_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_appFn_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Expr.appFn!"};
static const lean_object* l_Lean_Expr_appFn_x21___closed__1 = (const lean_object*)&l_Lean_Expr_appFn_x21___closed__1_value;
static const lean_string_object l_Lean_Expr_appFn_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l_Lean_Expr_appFn_x21___closed__2 = (const lean_object*)&l_Lean_Expr_appFn_x21___closed__2_value;
static lean_once_cell_t l_Lean_Expr_appFn_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appFn_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_appArg_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.appArg!"};
static const lean_object* l_Lean_Expr_appArg_x21___closed__0 = (const lean_object*)&l_Lean_Expr_appArg_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_appArg_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appArg_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_appFn_x21_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.appFn!'"};
static const lean_object* l_Lean_Expr_appFn_x21_x27___closed__0 = (const lean_object*)&l_Lean_Expr_appFn_x21_x27___closed__0_value;
static lean_once_cell_t l_Lean_Expr_appFn_x21_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appFn_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_appArg_x21_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.appArg!'"};
static const lean_object* l_Lean_Expr_appArg_x21_x27___closed__0 = (const lean_object*)&l_Lean_Expr_appArg_x21_x27___closed__0_value;
static lean_once_cell_t l_Lean_Expr_appArg_x21_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appArg_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_sortLevel_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.sortLevel!"};
static const lean_object* l_Lean_Expr_sortLevel_x21___closed__0 = (const lean_object*)&l_Lean_Expr_sortLevel_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_sortLevel_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sort expected"};
static const lean_object* l_Lean_Expr_sortLevel_x21___closed__1 = (const lean_object*)&l_Lean_Expr_sortLevel_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_sortLevel_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_sortLevel_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_litValue_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.litValue!"};
static const lean_object* l_Lean_Expr_litValue_x21___closed__0 = (const lean_object*)&l_Lean_Expr_litValue_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_litValue_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "literal expected"};
static const lean_object* l_Lean_Expr_litValue_x21___closed__1 = (const lean_object*)&l_Lean_Expr_litValue_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_litValue_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_litValue_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isCharLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Expr_isCharLit___closed__0 = (const lean_object*)&l_Lean_Expr_isCharLit___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isCharLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isCharLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Expr_isCharLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isCharLit___closed__1_value_aux_0),((lean_object*)&l_Lean_mkNatLitCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Expr_isCharLit___closed__1 = (const lean_object*)&l_Lean_Expr_isCharLit___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_constName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.constName!"};
static const lean_object* l_Lean_Expr_constName_x21___closed__0 = (const lean_object*)&l_Lean_Expr_constName_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_constName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "constant expected"};
static const lean_object* l_Lean_Expr_constName_x21___closed__1 = (const lean_object*)&l_Lean_Expr_constName_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_constName_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_constName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_constLevels_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.constLevels!"};
static const lean_object* l_Lean_Expr_constLevels_x21___closed__0 = (const lean_object*)&l_Lean_Expr_constLevels_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_constLevels_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_constLevels_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_bvarIdx_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.bvarIdx!"};
static const lean_object* l_Lean_Expr_bvarIdx_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bvarIdx_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_bvarIdx_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "bvar expected"};
static const lean_object* l_Lean_Expr_bvarIdx_x21___closed__1 = (const lean_object*)&l_Lean_Expr_bvarIdx_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_bvarIdx_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_fvarId_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.fvarId!"};
static const lean_object* l_Lean_Expr_fvarId_x21___closed__0 = (const lean_object*)&l_Lean_Expr_fvarId_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_fvarId_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fvar expected"};
static const lean_object* l_Lean_Expr_fvarId_x21___closed__1 = (const lean_object*)&l_Lean_Expr_fvarId_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_fvarId_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_fvarId_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_mvarId_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.mvarId!"};
static const lean_object* l_Lean_Expr_mvarId_x21___closed__0 = (const lean_object*)&l_Lean_Expr_mvarId_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_mvarId_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mvar expected"};
static const lean_object* l_Lean_Expr_mvarId_x21___closed__1 = (const lean_object*)&l_Lean_Expr_mvarId_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_mvarId_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_mvarId_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.bindingName!"};
static const lean_object* l_Lean_Expr_bindingName_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingName_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_bindingName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "binding expected"};
static const lean_object* l_Lean_Expr_bindingName_x21___closed__1 = (const lean_object*)&l_Lean_Expr_bindingName_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_bindingName_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingDomain_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.bindingDomain!"};
static const lean_object* l_Lean_Expr_bindingDomain_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingDomain_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_bindingDomain_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.bindingBody!"};
static const lean_object* l_Lean_Expr_bindingBody_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingBody_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_bindingBody_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingInfo_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.bindingInfo!"};
static const lean_object* l_Lean_Expr_bindingInfo_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingInfo_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_bindingInfo_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_letName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.letName!"};
static const lean_object* l_Lean_Expr_letName_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letName_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_letName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "let expression expected"};
static const lean_object* l_Lean_Expr_letName_x21___closed__1 = (const lean_object*)&l_Lean_Expr_letName_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_letName_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letType_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.letType!"};
static const lean_object* l_Lean_Expr_letType_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letType_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letType_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letType_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letValue_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.letValue!"};
static const lean_object* l_Lean_Expr_letValue_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letValue_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letValue_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letValue_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.letBody!"};
static const lean_object* l_Lean_Expr_letBody_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letBody_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letBody_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letNondep_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.letNondep!"};
static const lean_object* l_Lean_Expr_letNondep_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letNondep_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letNondep_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letNondep_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_mdataExpr_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.mdataExpr!"};
static const lean_object* l_Lean_Expr_mdataExpr_x21___closed__0 = (const lean_object*)&l_Lean_Expr_mdataExpr_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_mdataExpr_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mdata expression expected"};
static const lean_object* l_Lean_Expr_mdataExpr_x21___closed__1 = (const lean_object*)&l_Lean_Expr_mdataExpr_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_mdataExpr_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_projExpr_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.projExpr!"};
static const lean_object* l_Lean_Expr_projExpr_x21___closed__0 = (const lean_object*)&l_Lean_Expr_projExpr_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_projExpr_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "proj expression expected"};
static const lean_object* l_Lean_Expr_projExpr_x21___closed__1 = (const lean_object*)&l_Lean_Expr_projExpr_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_projExpr_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_projExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_projIdx_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.projIdx!"};
static const lean_object* l_Lean_Expr_projIdx_x21___closed__0 = (const lean_object*)&l_Lean_Expr_projIdx_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_projIdx_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_projIdx_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_getAppArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_getAppArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.getAppArgsN.loop"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "too few arguments at"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_traverseApp___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkAppN___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_traverseApp___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_traverseApp___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_getRevArg_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.getRevArg!"};
static const lean_object* l_Lean_Expr_getRevArg_x21___closed__0 = (const lean_object*)&l_Lean_Expr_getRevArg_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_getRevArg_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid index"};
static const lean_object* l_Lean_Expr_getRevArg_x21___closed__1 = (const lean_object*)&l_Lean_Expr_getRevArg_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_getRevArg_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_getRevArg_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_getRevArg_x21_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.getRevArg!'"};
static const lean_object* l_Lean_Expr_getRevArg_x21_x27___closed__0 = (const lean_object*)&l_Lean_Expr_getRevArg_x21_x27___closed__0_value;
static lean_once_cell_t l_Lean_Expr_getRevArg_x21_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_getRevArg_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object*, lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_dbgToString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_instToString___closed__0 = (const lean_object*)&l_Lean_Expr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Expr_instToString = (const lean_object*)&l_Lean_Expr_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
static const lean_string_object l_Lean_mkDecIsTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_mkDecIsTrue___closed__0 = (const lean_object*)&l_Lean_mkDecIsTrue___closed__0_value;
static const lean_string_object l_Lean_mkDecIsTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_Lean_mkDecIsTrue___closed__1 = (const lean_object*)&l_Lean_mkDecIsTrue___closed__1_value;
static const lean_ctor_object l_Lean_mkDecIsTrue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkDecIsTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_mkDecIsTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkDecIsTrue___closed__2_value_aux_0),((lean_object*)&l_Lean_mkDecIsTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_Lean_mkDecIsTrue___closed__2 = (const lean_object*)&l_Lean_mkDecIsTrue___closed__2_value;
static lean_once_cell_t l_Lean_mkDecIsTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkDecIsTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkDecIsFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_Lean_mkDecIsFalse___closed__0 = (const lean_object*)&l_Lean_mkDecIsFalse___closed__0_value;
static const lean_ctor_object l_Lean_mkDecIsFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkDecIsTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_mkDecIsFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkDecIsFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_mkDecIsFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_Lean_mkDecIsFalse___closed__1 = (const lean_object*)&l_Lean_mkDecIsFalse___closed__1_value;
static lean_once_cell_t l_Lean_mkDecIsFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkDecIsFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq;
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instCoeExprExprStructEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeExprExprStructEq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeExprExprStructEq___closed__0 = (const lean_object*)&l_Lean_instCoeExprExprStructEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeExprExprStructEq = (const lean_object*)&l_Lean_instCoeExprExprStructEq___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_ExprStructEq_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ExprStructEq_instBEq___closed__0 = (const lean_object*)&l_Lean_ExprStructEq_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ExprStructEq_instBEq = (const lean_object*)&l_Lean_ExprStructEq_instBEq___closed__0_value;
static const lean_closure_object l_Lean_ExprStructEq_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ExprStructEq_instHashable___closed__0 = (const lean_object*)&l_Lean_ExprStructEq_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ExprStructEq_instHashable = (const lean_object*)&l_Lean_ExprStructEq_instHashable___closed__0_value;
static const lean_closure_object l_Lean_ExprStructEq_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_dbgToString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ExprStructEq_instToString___closed__0 = (const lean_object*)&l_Lean_ExprStructEq_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ExprStructEq_instToString = (const lean_object*)&l_Lean_ExprStructEq_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
static const lean_string_object l_Lean_Expr_getOptParamDefault_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optParam"};
static const lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_getOptParamDefault_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_getOptParamDefault_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_getOptParamDefault_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 160, 223, 165, 16, 51, 54, 209)}};
static const lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_getOptParamDefault_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_getAutoParamTactic_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "autoParam"};
static const lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_getAutoParamTactic_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_getAutoParamTactic_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_getAutoParamTactic_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 161, 241, 39, 119, 172, 48, 112)}};
static const lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_getAutoParamTactic_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isOutParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "outParam"};
static const lean_object* l_Lean_Expr_isOutParam___closed__0 = (const lean_object*)&l_Lean_Expr_isOutParam___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isOutParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isOutParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 153, 87, 30, 57, 250, 25, 29)}};
static const lean_object* l_Lean_Expr_isOutParam___closed__1 = (const lean_object*)&l_Lean_Expr_isOutParam___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isSemiOutParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "semiOutParam"};
static const lean_object* l_Lean_Expr_isSemiOutParam___closed__0 = (const lean_object*)&l_Lean_Expr_isSemiOutParam___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isSemiOutParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSemiOutParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 187, 140, 108, 143, 232, 13, 120)}};
static const lean_object* l_Lean_Expr_isSemiOutParam___closed__1 = (const lean_object*)&l_Lean_Expr_isSemiOutParam___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_isFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Expr_isFalse___closed__0 = (const lean_object*)&l_Lean_Expr_isFalse___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Expr_isFalse___closed__1 = (const lean_object*)&l_Lean_Expr_isFalse___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Expr_isTrue___closed__0 = (const lean_object*)&l_Lean_Expr_isTrue___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Expr_isTrue___closed__1 = (const lean_object*)&l_Lean_Expr_isTrue___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isBoolFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__0 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isBoolFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isBoolFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isBoolFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_instReprData__1___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__1 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object*);
static const lean_ctor_object l_Lean_Expr_isBoolTrue___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isBoolTrue___closed__0_value_aux_0),((lean_object*)&l_Lean_instReprData__1___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Expr_isBoolTrue___closed__0 = (const lean_object*)&l_Lean_Expr_isBoolTrue___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object*);
static const lean_string_object l_Lean_Expr_int_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Expr_int_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__0_value;
static const lean_string_object l_Lean_Expr_int_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Expr_int_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Expr_int_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_int_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Expr_int_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_int_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_int_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Expr_int_x3f___closed__2 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateApp!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateFVar_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateFVar!"};
static const lean_object* l_Lean_Expr_updateFVar_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateFVar_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateFVar_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateFVar_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateConst!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateSort!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "level expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateMData!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mdata expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateForall!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateForallE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallE!"};
static const lean_object* l_Lean_Expr_updateForallE_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateForallE_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateForallE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLambdaE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateLambdaE!"};
static const lean_object* l_Lean_Expr_updateLambdaE_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateLambdaE_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateLambdaE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateLet!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLetE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateLetE!"};
static const lean_object* l_Lean_Expr_updateLetE_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateLetE_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateLetE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLetE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPExplicit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_Expr_setPPExplicit___closed__0 = (const lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value;
static const lean_string_object l_Lean_Expr_setPPExplicit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_Lean_Expr_setPPExplicit___closed__1 = (const lean_object*)&l_Lean_Expr_setPPExplicit___closed__1_value;
static const lean_ctor_object l_Lean_Expr_setPPExplicit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPExplicit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPExplicit___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 109, 223, 122, 147, 21, 229, 249)}};
static const lean_object* l_Lean_Expr_setPPExplicit___closed__2 = (const lean_object*)&l_Lean_Expr_setPPExplicit___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPUniverses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "universes"};
static const lean_object* l_Lean_Expr_setPPUniverses___closed__0 = (const lean_object*)&l_Lean_Expr_setPPUniverses___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPUniverses___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPUniverses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPUniverses___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPUniverses___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 49, 200, 238, 5, 247, 132, 121)}};
static const lean_object* l_Lean_Expr_setPPUniverses___closed__1 = (const lean_object*)&l_Lean_Expr_setPPUniverses___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPPiBinderTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "piBinderTypes"};
static const lean_object* l_Lean_Expr_setPPPiBinderTypes___closed__0 = (const lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPPiBinderTypes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPPiBinderTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 18, 16, 117, 190, 60, 138)}};
static const lean_object* l_Lean_Expr_setPPPiBinderTypes___closed__1 = (const lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPFunBinderTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "funBinderTypes"};
static const lean_object* l_Lean_Expr_setPPFunBinderTypes___closed__0 = (const lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPFunBinderTypes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPFunBinderTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 61, 49, 152, 149, 112, 61, 41)}};
static const lean_object* l_Lean_Expr_setPPFunBinderTypes___closed__1 = (const lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPNumericTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "numericTypes"};
static const lean_object* l_Lean_Expr_setPPNumericTypes___closed__0 = (const lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPNumericTypes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPNumericTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 29, 124, 132, 27, 235, 94, 122)}};
static const lean_object* l_Lean_Expr_setPPNumericTypes___closed__1 = (const lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_foldlM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_foldlM___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_foldlM___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_foldlM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object*);
static const lean_ctor_object l_Lean_mkAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_mkAnnotation___closed__0 = (const lean_object*)&l_Lean_mkAnnotation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkInaccessible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_inaccessible"};
static const lean_object* l_Lean_mkInaccessible___closed__0 = (const lean_object*)&l_Lean_mkInaccessible___closed__0_value;
static const lean_ctor_object l_Lean_mkInaccessible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkInaccessible___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 29, 104, 7, 111, 207, 123, 40)}};
static const lean_object* l_Lean_mkInaccessible___closed__1 = (const lean_object*)&l_Lean_mkInaccessible___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_patWithRef"};
static const lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 181, 220, 147, 186, 176, 190, 234)}};
static const lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey = (const lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_mkLHSGoalRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_lhsGoal"};
static const lean_object* l_Lean_mkLHSGoalRaw___closed__0 = (const lean_object*)&l_Lean_mkLHSGoalRaw___closed__0_value;
static const lean_ctor_object l_Lean_mkLHSGoalRaw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLHSGoalRaw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 54, 195, 36, 174, 14, 147, 139)}};
static const lean_object* l_Lean_mkLHSGoalRaw___closed__1 = (const lean_object*)&l_Lean_mkLHSGoalRaw___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
static const lean_string_object l_Lean_isLHSGoal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_isLHSGoal_x3f___closed__0 = (const lean_object*)&l_Lean_isLHSGoal_x3f___closed__0_value;
static const lean_ctor_object l_Lean_isLHSGoal_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLHSGoal_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_isLHSGoal_x3f___closed__1 = (const lean_object*)&l_Lean_isLHSGoal_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkNot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_mkNot___closed__0 = (const lean_object*)&l_Lean_mkNot___closed__0_value;
static const lean_ctor_object l_Lean_mkNot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_mkNot___closed__1 = (const lean_object*)&l_Lean_mkNot___closed__1_value;
static lean_once_cell_t l_Lean_mkNot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNot___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object*);
static const lean_string_object l_Lean_mkOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_mkOr___closed__0 = (const lean_object*)&l_Lean_mkOr___closed__0_value;
static const lean_ctor_object l_Lean_mkOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkOr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_mkOr___closed__1 = (const lean_object*)&l_Lean_mkOr___closed__1_value;
static lean_once_cell_t l_Lean_mkOr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkOr___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_mkAnd___closed__0 = (const lean_object*)&l_Lean_mkAnd___closed__0_value;
static const lean_ctor_object l_Lean_mkAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_mkAnd___closed__1 = (const lean_object*)&l_Lean_mkAnd___closed__1_value;
static lean_once_cell_t l_Lean_mkAnd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkAnd___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkAndN___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkAndN___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object*);
static const lean_string_object l_Lean_mkEM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_mkEM___closed__0 = (const lean_object*)&l_Lean_mkEM___closed__0_value;
static const lean_string_object l_Lean_mkEM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "em"};
static const lean_object* l_Lean_mkEM___closed__1 = (const lean_object*)&l_Lean_mkEM___closed__1_value;
static const lean_ctor_object l_Lean_mkEM___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_mkEM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkEM___closed__2_value_aux_0),((lean_object*)&l_Lean_mkEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(138, 250, 26, 166, 192, 110, 127, 170)}};
static const lean_object* l_Lean_mkEM___closed__2 = (const lean_object*)&l_Lean_mkEM___closed__2_value;
static lean_once_cell_t l_Lean_mkEM___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkEM___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object*);
static const lean_string_object l_Lean_mkIff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_mkIff___closed__0 = (const lean_object*)&l_Lean_mkIff___closed__0_value;
static const lean_ctor_object l_Lean_mkIff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_mkIff___closed__1 = (const lean_object*)&l_Lean_mkIff___closed__1_value;
static lean_once_cell_t l_Lean_mkIff___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIff___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkType;
static const lean_string_object l_Lean_Nat_mkInstAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l_Lean_Nat_mkInstAdd___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstAdd___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l_Lean_Nat_mkInstAdd___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstAdd___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstAdd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstAdd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstAdd;
static const lean_string_object l_Lean_Nat_mkInstHAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Nat_mkInstHAdd___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHAdd___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Nat_mkInstHAdd___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHAdd___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHAdd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHAdd___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHAdd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHAdd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHAdd;
static const lean_string_object l_Lean_Nat_mkInstSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instSubNat"};
static const lean_object* l_Lean_Nat_mkInstSub___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstSub___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 126, 242, 252, 139, 96, 73, 92)}};
static const lean_object* l_Lean_Nat_mkInstSub___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstSub___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstSub___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstSub___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstSub;
static const lean_string_object l_Lean_Nat_mkInstHSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Nat_mkInstHSub___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHSub___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Nat_mkInstHSub___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHSub___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHSub___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHSub___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHSub___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHSub___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHSub;
static const lean_string_object l_Lean_Nat_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instMulNat"};
static const lean_object* l_Lean_Nat_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 250, 177, 143, 4, 122, 150, 94)}};
static const lean_object* l_Lean_Nat_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstMul;
static const lean_string_object l_Lean_Nat_mkInstHMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Nat_mkInstHMul___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHMul___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Nat_mkInstHMul___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHMul___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMul___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHMul___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMul___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHMul;
static const lean_string_object l_Lean_Nat_mkInstDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l_Lean_Nat_mkInstDiv___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstDiv___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstDiv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Nat_mkInstDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Nat_mkInstDiv___closed__1_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 220, 27, 244, 214, 254, 46, 170)}};
static const lean_object* l_Lean_Nat_mkInstDiv___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstDiv___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstDiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstDiv___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstDiv;
static const lean_string_object l_Lean_Nat_mkInstHDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Nat_mkInstHDiv___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHDiv___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Nat_mkInstHDiv___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHDiv___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHDiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHDiv___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHDiv___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHDiv;
static const lean_string_object l_Lean_Nat_mkInstMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMod"};
static const lean_object* l_Lean_Nat_mkInstMod___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstMod___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstMod___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Nat_mkInstMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Nat_mkInstMod___closed__1_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 28, 178, 185, 13, 18, 77, 86)}};
static const lean_object* l_Lean_Nat_mkInstMod___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstMod___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstMod___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstMod___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstMod;
static const lean_string_object l_Lean_Nat_mkInstHMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMod"};
static const lean_object* l_Lean_Nat_mkInstHMod___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHMod___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 7, 29, 140, 31, 32, 204, 87)}};
static const lean_object* l_Lean_Nat_mkInstHMod___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHMod___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHMod___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMod___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHMod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMod___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHMod;
static const lean_string_object l_Lean_Nat_mkInstNatPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "instNatPowNat"};
static const lean_object* l_Lean_Nat_mkInstNatPow___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstNatPow___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstNatPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstNatPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 252, 138, 245, 102, 141, 87, 126)}};
static const lean_object* l_Lean_Nat_mkInstNatPow___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstNatPow___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstNatPow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstNatPow___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstNatPow;
static const lean_string_object l_Lean_Nat_mkInstPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instPowNat"};
static const lean_object* l_Lean_Nat_mkInstPow___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstPow___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 228, 103, 52, 5, 80, 7, 4)}};
static const lean_object* l_Lean_Nat_mkInstPow___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstPow___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstPow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstPow___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstPow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstPow___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstPow;
static const lean_string_object l_Lean_Nat_mkInstHPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHPow"};
static const lean_object* l_Lean_Nat_mkInstHPow___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHPow___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 197, 76, 235, 199, 0, 254, 199)}};
static const lean_object* l_Lean_Nat_mkInstHPow___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHPow___closed__1_value;
static const lean_ctor_object l_Lean_Nat_mkInstHPow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatLitCore___closed__3_value)}};
static const lean_object* l_Lean_Nat_mkInstHPow___closed__2 = (const lean_object*)&l_Lean_Nat_mkInstHPow___closed__2_value;
static lean_once_cell_t l_Lean_Nat_mkInstHPow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHPow___closed__3;
static lean_once_cell_t l_Lean_Nat_mkInstHPow___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHPow___closed__4;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHPow;
static const lean_string_object l_Lean_Nat_mkInstLT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Nat_mkInstLT___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstLT___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstLT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstLT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Nat_mkInstLT___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstLT___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstLT___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstLT___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstLT;
static const lean_string_object l_Lean_Nat_mkInstLE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Nat_mkInstLE___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstLE___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstLE___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstLE___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Nat_mkInstLE___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstLE___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstLE___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstLE___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstLE;
static const lean_string_object l___private_Lean_Expr_0__Lean_natAddFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natAddFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__4;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__5;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__6;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__7;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natAddFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_natSubFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natSubFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natSubFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_natMulFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natMulFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natMulFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_natPowFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natPowFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natPowFn;
static const lean_string_object l_Lean_mkNatSucc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_mkNatSucc___closed__0 = (const lean_object*)&l_Lean_mkNatSucc___closed__0_value;
static const lean_ctor_object l_Lean_mkNatSucc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_mkNatSucc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatSucc___closed__1_value_aux_0),((lean_object*)&l_Lean_mkNatSucc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_mkNatSucc___closed__1 = (const lean_object*)&l_Lean_mkNatSucc___closed__1_value;
static lean_once_cell_t l_Lean_mkNatSucc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatSucc___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_natLEPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natLEPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natLEPred;
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__0;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__1;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__2;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natEqPred;
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_propEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_propEq___closed__0;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_propEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_propEq___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_propEq;
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static const lean_string_object l_Lean_Int_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Int_mkType___closed__0 = (const lean_object*)&l_Lean_Int_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Int_mkType___closed__1 = (const lean_object*)&l_Lean_Int_mkType___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkType;
static const lean_string_object l_Lean_Int_mkInstNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Int_mkInstNeg___closed__0 = (const lean_object*)&l_Lean_Int_mkInstNeg___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstNeg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstNeg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstNeg___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstNeg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Int_mkInstNeg___closed__1 = (const lean_object*)&l_Lean_Int_mkInstNeg___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstNeg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstNeg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstNeg;
static const lean_string_object l_Lean_Int_mkInstAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instAdd"};
static const lean_object* l_Lean_Int_mkInstAdd___closed__0 = (const lean_object*)&l_Lean_Int_mkInstAdd___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstAdd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstAdd___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 99, 69, 75, 84, 154, 200, 179)}};
static const lean_object* l_Lean_Int_mkInstAdd___closed__1 = (const lean_object*)&l_Lean_Int_mkInstAdd___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstAdd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstAdd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstAdd;
static lean_once_cell_t l_Lean_Int_mkInstHAdd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHAdd___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHAdd;
static const lean_string_object l_Lean_Int_mkInstSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instSub"};
static const lean_object* l_Lean_Int_mkInstSub___closed__0 = (const lean_object*)&l_Lean_Int_mkInstSub___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstSub___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstSub___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 85, 79, 77, 38, 86, 116, 189)}};
static const lean_object* l_Lean_Int_mkInstSub___closed__1 = (const lean_object*)&l_Lean_Int_mkInstSub___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstSub___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstSub___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstSub;
static lean_once_cell_t l_Lean_Int_mkInstHSub___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHSub___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHSub;
static const lean_string_object l_Lean_Int_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Int_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Int_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstMul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstMul___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 121, 189, 72, 180, 169, 35, 121)}};
static const lean_object* l_Lean_Int_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Int_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstMul;
static lean_once_cell_t l_Lean_Int_mkInstHMul___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHMul___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHMul;
static const lean_ctor_object l_Lean_Int_mkInstDiv___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstDiv___closed__0_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 154, 103, 19, 118, 118, 20, 12)}};
static const lean_object* l_Lean_Int_mkInstDiv___closed__0 = (const lean_object*)&l_Lean_Int_mkInstDiv___closed__0_value;
static lean_once_cell_t l_Lean_Int_mkInstDiv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstDiv___closed__1;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstDiv;
static lean_once_cell_t l_Lean_Int_mkInstHDiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHDiv___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHDiv;
static const lean_ctor_object l_Lean_Int_mkInstMod___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstMod___closed__0_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 18, 147, 153, 76, 63, 153, 183)}};
static const lean_object* l_Lean_Int_mkInstMod___closed__0 = (const lean_object*)&l_Lean_Int_mkInstMod___closed__0_value;
static lean_once_cell_t l_Lean_Int_mkInstMod___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstMod___closed__1;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstMod;
static lean_once_cell_t l_Lean_Int_mkInstHMod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHMod___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHMod;
static const lean_string_object l_Lean_Int_mkInstPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNatPow"};
static const lean_object* l_Lean_Int_mkInstPow___closed__0 = (const lean_object*)&l_Lean_Int_mkInstPow___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstPow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstPow___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 111, 246, 9, 99, 98, 200, 100)}};
static const lean_object* l_Lean_Int_mkInstPow___closed__1 = (const lean_object*)&l_Lean_Int_mkInstPow___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstPow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstPow___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstPow;
static lean_once_cell_t l_Lean_Int_mkInstPowNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstPowNat___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstPowNat;
static lean_once_cell_t l_Lean_Int_mkInstHPow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHPow___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHPow;
static const lean_string_object l_Lean_Int_mkInstLT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Int_mkInstLT___closed__0 = (const lean_object*)&l_Lean_Int_mkInstLT___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstLT___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstLT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstLT___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstLT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Int_mkInstLT___closed__1 = (const lean_object*)&l_Lean_Int_mkInstLT___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstLT___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstLT___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstLT;
static const lean_string_object l_Lean_Int_mkInstLE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLEInt"};
static const lean_object* l_Lean_Int_mkInstLE___closed__0 = (const lean_object*)&l_Lean_Int_mkInstLE___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstLE___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstLE___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstLE___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstLE___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 143, 147, 243, 104, 145, 221, 241)}};
static const lean_object* l_Lean_Int_mkInstLE___closed__1 = (const lean_object*)&l_Lean_Int_mkInstLE___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstLE___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstLE___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstLE;
static const lean_string_object l_Lean_Int_mkInstNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l_Lean_Int_mkInstNatCast___closed__0 = (const lean_object*)&l_Lean_Int_mkInstNatCast___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstNatCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkInstNatCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l_Lean_Int_mkInstNatCast___closed__1 = (const lean_object*)&l_Lean_Int_mkInstNatCast___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstNatCast___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstNatCast___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstNatCast;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNegFn___closed__0;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNegFn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intNegFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intAddFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intAddFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intSubFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intSubFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intMulFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intMulFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_intDivFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intDivFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_intDivFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intDivFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intDivFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_intDivFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intDivFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_intDivFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_intDivFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intDivFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intDivFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_intModFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intModFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_intModFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intModFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intModFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_intModFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intModFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_intModFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_intModFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intModFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intModFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intModFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intModFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intPowNatFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn;
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intLEPred___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intLEPred;
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_intLTPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_intLTPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intLTPred;
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intEqPred___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intEqPred;
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkIntDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_mkIntDvd___closed__0 = (const lean_object*)&l_Lean_mkIntDvd___closed__0_value;
static const lean_string_object l_Lean_mkIntDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_mkIntDvd___closed__1 = (const lean_object*)&l_Lean_mkIntDvd___closed__1_value;
static const lean_ctor_object l_Lean_mkIntDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkIntDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_mkIntDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkIntDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_mkIntDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_mkIntDvd___closed__2 = (const lean_object*)&l_Lean_mkIntDvd___closed__2_value;
static lean_once_cell_t l_Lean_mkIntDvd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntDvd___closed__3;
static const lean_string_object l_Lean_mkIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Lean_mkIntDvd___closed__4 = (const lean_object*)&l_Lean_mkIntDvd___closed__4_value;
static const lean_ctor_object l_Lean_mkIntDvd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_mkIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkIntDvd___closed__5_value_aux_0),((lean_object*)&l_Lean_mkIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l_Lean_mkIntDvd___closed__5 = (const lean_object*)&l_Lean_mkIntDvd___closed__5_value;
static lean_once_cell_t l_Lean_mkIntDvd___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntDvd___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkIntLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_mkIntLit___closed__0 = (const lean_object*)&l_Lean_mkIntLit___closed__0_value;
static const lean_ctor_object l_Lean_mkIntLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkIntLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_mkIntLit___closed__1 = (const lean_object*)&l_Lean_mkIntLit___closed__1_value;
static lean_once_cell_t l_Lean_mkIntLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntLit___closed__2;
static lean_once_cell_t l_Lean_mkIntLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntLit___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object*);
static const lean_string_object l_Lean_reflBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_reflBoolTrue___closed__0 = (const lean_object*)&l_Lean_reflBoolTrue___closed__0_value;
static const lean_ctor_object l_Lean_reflBoolTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLHSGoal_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_reflBoolTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_reflBoolTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_reflBoolTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_reflBoolTrue___closed__1 = (const lean_object*)&l_Lean_reflBoolTrue___closed__1_value;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__2;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__3;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__4;
static const lean_ctor_object l_Lean_reflBoolTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_reflBoolTrue___closed__5 = (const lean_object*)&l_Lean_reflBoolTrue___closed__5_value;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__6;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__7;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__8;
LEAN_EXPORT lean_object* l_Lean_reflBoolTrue;
static lean_once_cell_t l_Lean_reflBoolFalse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolFalse___closed__0;
static lean_once_cell_t l_Lean_reflBoolFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_reflBoolFalse;
static const lean_string_object l_Lean_eagerReflBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eagerReduce"};
static const lean_object* l_Lean_eagerReflBoolTrue___closed__0 = (const lean_object*)&l_Lean_eagerReflBoolTrue___closed__0_value;
static const lean_ctor_object l_Lean_eagerReflBoolTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_eagerReflBoolTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 243, 67, 12, 220, 84, 120, 222)}};
static const lean_object* l_Lean_eagerReflBoolTrue___closed__1 = (const lean_object*)&l_Lean_eagerReflBoolTrue___closed__1_value;
static lean_once_cell_t l_Lean_eagerReflBoolTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolTrue___closed__2;
static lean_once_cell_t l_Lean_eagerReflBoolTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolTrue___closed__3;
static lean_once_cell_t l_Lean_eagerReflBoolTrue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolTrue___closed__4;
LEAN_EXPORT lean_object* l_Lean_eagerReflBoolTrue;
static lean_once_cell_t l_Lean_eagerReflBoolFalse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolFalse___closed__0;
static lean_once_cell_t l_Lean_eagerReflBoolFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_eagerReflBoolFalse;
static const lean_string_object l_Lean_Expr_replaceFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.replaceFn"};
static const lean_object* l_Lean_Expr_replaceFn___closed__0 = (const lean_object*)&l_Lean_Expr_replaceFn___closed__0_value;
static const lean_string_object l_Lean_Expr_replaceFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "function application or constant expected"};
static const lean_object* l_Lean_Expr_replaceFn___closed__1 = (const lean_object*)&l_Lean_Expr_replaceFn___closed__1_value;
static lean_once_cell_t l_Lean_Expr_replaceFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_replaceFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Literal_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_val_8_; lean_object* v___x_9_; 
v_val_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_val_8_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_11_; 
v_val_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_val_10_);
lean_dec_ref_known(v_t_6_, 1);
v___x_11_ = lean_apply_1(v_k_7_, v_val_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Literal_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Literal_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim___redArg(lean_object* v_t_24_, lean_object* v_natVal_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Literal_ctorElim___redArg(v_t_24_, v_natVal_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_natVal_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Literal_ctorElim___redArg(v_t_28_, v_natVal_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim___redArg(lean_object* v_t_32_, lean_object* v_strVal_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Literal_ctorElim___redArg(v_t_32_, v_strVal_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_strVal_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Literal_ctorElim___redArg(v_t_36_, v_strVal_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLiteral_beq(lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v_val_46_; lean_object* v_val_47_; uint8_t v___x_48_; 
v_val_46_ = lean_ctor_get(v_x_44_, 0);
v_val_47_ = lean_ctor_get(v_x_45_, 0);
v___x_48_ = lean_nat_dec_eq(v_val_46_, v_val_47_);
return v___x_48_;
}
else
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
else
{
if (lean_obj_tag(v_x_45_) == 1)
{
lean_object* v_val_50_; lean_object* v_val_51_; uint8_t v___x_52_; 
v_val_50_ = lean_ctor_get(v_x_44_, 0);
v_val_51_ = lean_ctor_get(v_x_45_, 0);
v___x_52_ = lean_string_dec_eq(v_val_50_, v_val_51_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral_beq___boxed(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_instBEqLiteral_beq(v_x_54_, v_x_55_);
lean_dec_ref(v_x_55_);
lean_dec_ref(v_x_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
static lean_object* _init_l_Lean_instReprLiteral_repr___closed__3(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(2u);
v___x_67_ = lean_nat_to_int(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_instReprLiteral_repr___closed__4(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_to_int(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr(lean_object* v_x_76_, lean_object* v_prec_77_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_val_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_98_; 
v_val_78_ = lean_ctor_get(v_x_76_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_98_ == 0)
{
v___x_80_ = v_x_76_;
v_isShared_81_ = v_isSharedCheck_98_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_val_78_);
lean_dec(v_x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_98_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___y_83_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1024u);
v___x_95_ = lean_nat_dec_le(v___x_94_, v_prec_77_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_83_ = v___x_96_;
goto v___jp_82_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_83_ = v___x_97_;
goto v___jp_82_;
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(l_Lean_instReprLiteral_repr___closed__2));
v___x_85_ = l_Nat_reprFast(v_val_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 3);
lean_ctor_set(v___x_80_, 0, v___x_85_);
v___x_87_ = v___x_80_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_93_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_84_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
lean_inc(v___y_83_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_83_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_77_);
return v___x_92_;
}
}
}
}
else
{
lean_object* v_val_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_119_; 
v_val_99_ = lean_ctor_get(v_x_76_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_119_ == 0)
{
v___x_101_ = v_x_76_;
v_isShared_102_ = v_isSharedCheck_119_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_val_99_);
lean_dec(v_x_76_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_119_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___y_104_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1024u);
v___x_116_ = lean_nat_dec_le(v___x_115_, v_prec_77_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_104_ = v___x_117_;
goto v___jp_103_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_104_ = v___x_118_;
goto v___jp_103_;
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_105_ = ((lean_object*)(l_Lean_instReprLiteral_repr___closed__7));
v___x_106_ = l_String_quote(v_val_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 3);
lean_ctor_set(v___x_101_, 0, v___x_106_);
v___x_108_ = v___x_101_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_114_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_105_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
lean_inc(v___y_104_);
v___x_110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_104_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_prec_77_);
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr___boxed(lean_object* v_x_120_, lean_object* v_prec_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_instReprLiteral_repr(v_x_120_, v_prec_121_);
lean_dec(v_prec_121_);
return v_res_122_;
}
}
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v_val_126_; uint64_t v___x_127_; 
v_val_126_ = lean_ctor_get(v_x_125_, 0);
v___x_127_ = lean_uint64_of_nat(v_val_126_);
return v___x_127_;
}
else
{
lean_object* v_val_128_; uint64_t v___x_129_; 
v_val_128_ = lean_ctor_get(v_x_125_, 0);
v___x_129_ = lean_string_hash(v_val_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* v_x_130_){
_start:
{
uint64_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_Literal_hash(v_x_130_);
lean_dec_ref(v_x_130_);
v_r_132_ = lean_box_uint64(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_val_137_; lean_object* v_val_138_; uint8_t v___x_139_; 
v_val_137_ = lean_ctor_get(v_x_135_, 0);
v_val_138_ = lean_ctor_get(v_x_136_, 0);
v___x_139_ = lean_nat_dec_lt(v_val_137_, v_val_138_);
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
}
else
{
if (lean_obj_tag(v_x_136_) == 1)
{
lean_object* v_val_141_; lean_object* v_val_142_; uint8_t v___x_143_; 
v_val_141_ = lean_ctor_get(v_x_135_, 0);
v_val_142_ = lean_ctor_get(v_x_136_, 0);
v___x_143_ = lean_string_dec_lt(v_val_141_, v_val_142_);
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Lean_Literal_lt(v_x_145_, v_x_146_);
lean_dec_ref(v_x_146_);
lean_dec_ref(v_x_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
static lean_object* _init_l_Lean_instLTLiteral(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_Literal_lt(v_a_150_, v_b_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_instDecidableLtLiteral(v_a_153_, v_b_154_);
lean_dec_ref(v_b_154_);
lean_dec_ref(v_a_153_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx(uint8_t v_x_157_){
_start:
{
switch(v_x_157_)
{
case 0:
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(0u);
return v___x_158_;
}
case 1:
{
lean_object* v___x_159_; 
v___x_159_ = lean_unsigned_to_nat(1u);
return v___x_159_;
}
case 2:
{
lean_object* v___x_160_; 
v___x_160_ = lean_unsigned_to_nat(2u);
return v___x_160_;
}
default: 
{
lean_object* v___x_161_; 
v___x_161_ = lean_unsigned_to_nat(3u);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___boxed(lean_object* v_x_162_){
_start:
{
uint8_t v_x_boxed_163_; lean_object* v_res_164_; 
v_x_boxed_163_ = lean_unbox(v_x_162_);
v_res_164_ = l_Lean_BinderInfo_ctorIdx(v_x_boxed_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object* v_k_165_){
_start:
{
lean_inc(v_k_165_);
return v_k_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object* v_k_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_BinderInfo_ctorElim___redArg(v_k_166_);
lean_dec(v_k_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object* v_motive_168_, lean_object* v_ctorIdx_169_, uint8_t v_t_170_, lean_object* v_h_171_, lean_object* v_k_172_){
_start:
{
lean_inc(v_k_172_);
return v_k_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object* v_motive_173_, lean_object* v_ctorIdx_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_k_177_){
_start:
{
uint8_t v_t_boxed_178_; lean_object* v_res_179_; 
v_t_boxed_178_ = lean_unbox(v_t_175_);
v_res_179_ = l_Lean_BinderInfo_ctorElim(v_motive_173_, v_ctorIdx_174_, v_t_boxed_178_, v_h_176_, v_k_177_);
lean_dec(v_k_177_);
lean_dec(v_ctorIdx_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object* v_default_180_){
_start:
{
lean_inc(v_default_180_);
return v_default_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object* v_default_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_BinderInfo_default_elim___redArg(v_default_181_);
lean_dec(v_default_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object* v_motive_183_, uint8_t v_t_184_, lean_object* v_h_185_, lean_object* v_default_186_){
_start:
{
lean_inc(v_default_186_);
return v_default_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object* v_motive_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_default_190_){
_start:
{
uint8_t v_t_boxed_191_; lean_object* v_res_192_; 
v_t_boxed_191_ = lean_unbox(v_t_188_);
v_res_192_ = l_Lean_BinderInfo_default_elim(v_motive_187_, v_t_boxed_191_, v_h_189_, v_default_190_);
lean_dec(v_default_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object* v_implicit_193_){
_start:
{
lean_inc(v_implicit_193_);
return v_implicit_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object* v_implicit_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_BinderInfo_implicit_elim___redArg(v_implicit_194_);
lean_dec(v_implicit_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object* v_motive_196_, uint8_t v_t_197_, lean_object* v_h_198_, lean_object* v_implicit_199_){
_start:
{
lean_inc(v_implicit_199_);
return v_implicit_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object* v_motive_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_implicit_203_){
_start:
{
uint8_t v_t_boxed_204_; lean_object* v_res_205_; 
v_t_boxed_204_ = lean_unbox(v_t_201_);
v_res_205_ = l_Lean_BinderInfo_implicit_elim(v_motive_200_, v_t_boxed_204_, v_h_202_, v_implicit_203_);
lean_dec(v_implicit_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object* v_strictImplicit_206_){
_start:
{
lean_inc(v_strictImplicit_206_);
return v_strictImplicit_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object* v_strictImplicit_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_BinderInfo_strictImplicit_elim___redArg(v_strictImplicit_207_);
lean_dec(v_strictImplicit_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object* v_motive_209_, uint8_t v_t_210_, lean_object* v_h_211_, lean_object* v_strictImplicit_212_){
_start:
{
lean_inc(v_strictImplicit_212_);
return v_strictImplicit_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_strictImplicit_216_){
_start:
{
uint8_t v_t_boxed_217_; lean_object* v_res_218_; 
v_t_boxed_217_ = lean_unbox(v_t_214_);
v_res_218_ = l_Lean_BinderInfo_strictImplicit_elim(v_motive_213_, v_t_boxed_217_, v_h_215_, v_strictImplicit_216_);
lean_dec(v_strictImplicit_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object* v_instImplicit_219_){
_start:
{
lean_inc(v_instImplicit_219_);
return v_instImplicit_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object* v_instImplicit_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_BinderInfo_instImplicit_elim___redArg(v_instImplicit_220_);
lean_dec(v_instImplicit_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object* v_motive_222_, uint8_t v_t_223_, lean_object* v_h_224_, lean_object* v_instImplicit_225_){
_start:
{
lean_inc(v_instImplicit_225_);
return v_instImplicit_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object* v_motive_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_instImplicit_229_){
_start:
{
uint8_t v_t_boxed_230_; lean_object* v_res_231_; 
v_t_boxed_230_ = lean_unbox(v_t_227_);
v_res_231_ = l_Lean_BinderInfo_instImplicit_elim(v_motive_226_, v_t_boxed_230_, v_h_228_, v_instImplicit_229_);
lean_dec(v_instImplicit_229_);
return v_res_231_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo_default(void){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = 0;
return v___x_232_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo(void){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t v_x_234_, uint8_t v_y_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_Lean_BinderInfo_ctorIdx(v_x_234_);
v___x_237_ = l_Lean_BinderInfo_ctorIdx(v_y_235_);
v___x_238_ = lean_nat_dec_eq(v___x_236_, v___x_237_);
lean_dec(v___x_237_);
lean_dec(v___x_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object* v_x_239_, lean_object* v_y_240_){
_start:
{
uint8_t v_x_17__boxed_241_; uint8_t v_y_18__boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_x_17__boxed_241_ = lean_unbox(v_x_239_);
v_y_18__boxed_242_ = lean_unbox(v_y_240_);
v_res_243_ = l_Lean_instBEqBinderInfo_beq(v_x_17__boxed_241_, v_y_18__boxed_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t v_x_259_, lean_object* v_prec_260_){
_start:
{
lean_object* v___y_262_; lean_object* v___y_269_; lean_object* v___y_276_; lean_object* v___y_283_; 
switch(v_x_259_)
{
case 0:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1024u);
v___x_290_ = lean_nat_dec_le(v___x_289_, v_prec_260_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_262_ = v___x_291_;
goto v___jp_261_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_262_ = v___x_292_;
goto v___jp_261_;
}
}
case 1:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1024u);
v___x_294_ = lean_nat_dec_le(v___x_293_, v_prec_260_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_269_ = v___x_295_;
goto v___jp_268_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_269_ = v___x_296_;
goto v___jp_268_;
}
}
case 2:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1024u);
v___x_298_ = lean_nat_dec_le(v___x_297_, v_prec_260_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_276_ = v___x_299_;
goto v___jp_275_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_276_ = v___x_300_;
goto v___jp_275_;
}
}
default: 
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1024u);
v___x_302_ = lean_nat_dec_le(v___x_301_, v_prec_260_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_283_ = v___x_303_;
goto v___jp_282_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_283_ = v___x_304_;
goto v___jp_282_;
}
}
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__1));
lean_inc(v___y_262_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_260_);
return v___x_267_;
}
v___jp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_270_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__3));
lean_inc(v___y_269_);
v___x_271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_271_, 0, v___y_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = 0;
v___x_273_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_272_);
v___x_274_ = l_Repr_addAppParen(v___x_273_, v_prec_260_);
return v___x_274_;
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_277_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__5));
lean_inc(v___y_276_);
v___x_278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_278_, 0, v___y_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = 0;
v___x_280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*1, v___x_279_);
v___x_281_ = l_Repr_addAppParen(v___x_280_, v_prec_260_);
return v___x_281_;
}
v___jp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_284_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__7));
lean_inc(v___y_283_);
v___x_285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_285_, 0, v___y_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = 0;
v___x_287_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*1, v___x_286_);
v___x_288_ = l_Repr_addAppParen(v___x_287_, v_prec_260_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object* v_x_305_, lean_object* v_prec_306_){
_start:
{
uint8_t v_x_229__boxed_307_; lean_object* v_res_308_; 
v_x_229__boxed_307_ = lean_unbox(v_x_305_);
v_res_308_ = l_Lean_instReprBinderInfo_repr(v_x_229__boxed_307_, v_prec_306_);
lean_dec(v_prec_306_);
return v_res_308_;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t v_x_311_){
_start:
{
switch(v_x_311_)
{
case 0:
{
uint64_t v___x_312_; 
v___x_312_ = 947ULL;
return v___x_312_;
}
case 1:
{
uint64_t v___x_313_; 
v___x_313_ = 1019ULL;
return v___x_313_;
}
case 2:
{
uint64_t v___x_314_; 
v___x_314_ = 1087ULL;
return v___x_314_;
}
default: 
{
uint64_t v___x_315_; 
v___x_315_ = 1153ULL;
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* v_x_316_){
_start:
{
uint8_t v_x_52__boxed_317_; uint64_t v_res_318_; lean_object* v_r_319_; 
v_x_52__boxed_317_ = lean_unbox(v_x_316_);
v_res_318_ = l_Lean_BinderInfo_hash(v_x_52__boxed_317_);
v_r_319_ = lean_box_uint64(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t v_x_320_){
_start:
{
switch(v_x_320_)
{
case 1:
{
uint8_t v___x_321_; 
v___x_321_ = 0;
return v___x_321_;
}
case 2:
{
uint8_t v___x_322_; 
v___x_322_ = 0;
return v___x_322_;
}
case 3:
{
uint8_t v___x_323_; 
v___x_323_ = 0;
return v___x_323_;
}
default: 
{
uint8_t v___x_324_; 
v___x_324_ = 1;
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* v_x_325_){
_start:
{
uint8_t v_x_31__boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_x_31__boxed_326_ = lean_unbox(v_x_325_);
v_res_327_ = l_Lean_BinderInfo_isExplicit(v_x_31__boxed_326_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t v_x_331_){
_start:
{
if (v_x_331_ == 3)
{
uint8_t v___x_332_; 
v___x_332_ = 1;
return v___x_332_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = 0;
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* v_x_334_){
_start:
{
uint8_t v_x_21__boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_x_21__boxed_335_ = lean_unbox(v_x_334_);
v_res_336_ = l_Lean_BinderInfo_isInstImplicit(v_x_21__boxed_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t v_x_338_){
_start:
{
if (v_x_338_ == 1)
{
uint8_t v___x_339_; 
v___x_339_ = 1;
return v___x_339_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* v_x_341_){
_start:
{
uint8_t v_x_21__boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_x_21__boxed_342_ = lean_unbox(v_x_341_);
v_res_343_ = l_Lean_BinderInfo_isImplicit(v_x_21__boxed_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t v_x_345_){
_start:
{
if (v_x_345_ == 2)
{
uint8_t v___x_346_; 
v___x_346_ = 1;
return v___x_346_;
}
else
{
uint8_t v___x_347_; 
v___x_347_ = 0;
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* v_x_348_){
_start:
{
uint8_t v_x_21__boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_x_21__boxed_349_ = lean_unbox(v_x_348_);
v_res_350_ = l_Lean_BinderInfo_isStrictImplicit(v_x_21__boxed_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
static lean_object* _init_l_Lean_MData_empty(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_353_; 
v___x_353_ = 0ULL;
return v___x_353_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_354_; 
v___x_354_ = 0ULL;
return v___x_354_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_355_){
_start:
{
uint32_t v___x_356_; uint64_t v___x_357_; 
v___x_356_ = lean_uint64_to_uint32(v_c_355_);
v___x_357_ = lean_uint32_to_uint64(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_358_){
_start:
{
uint64_t v_c_boxed_359_; uint64_t v_res_360_; lean_object* v_r_361_; 
v_c_boxed_359_ = lean_unbox_uint64(v_c_358_);
lean_dec_ref(v_c_358_);
v_res_360_ = l_Lean_Expr_Data_hash(v_c_boxed_359_);
v_r_361_ = lean_box_uint64(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_364_){
_start:
{
uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint8_t v___x_369_; 
v___x_365_ = 32ULL;
v___x_366_ = lean_uint64_shift_right(v_c_364_, v___x_365_);
v___x_367_ = 255ULL;
v___x_368_ = lean_uint64_land(v___x_366_, v___x_367_);
v___x_369_ = lean_uint64_to_uint8(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_370_){
_start:
{
uint64_t v_c_boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v_c_boxed_371_ = lean_unbox_uint64(v_c_370_);
lean_dec_ref(v_c_370_);
v_res_372_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_374_){
_start:
{
uint64_t v___x_375_; uint64_t v___x_376_; uint32_t v___x_377_; 
v___x_375_ = 44ULL;
v___x_376_ = lean_uint64_shift_right(v_c_374_, v___x_375_);
v___x_377_ = lean_uint64_to_uint32(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_378_){
_start:
{
uint64_t v_c_boxed_379_; uint32_t v_res_380_; lean_object* v_r_381_; 
v_c_boxed_379_ = lean_unbox_uint64(v_c_378_);
lean_dec_ref(v_c_378_);
v_res_380_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_379_);
v_r_381_ = lean_box_uint32(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_382_){
_start:
{
uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; uint8_t v___x_387_; 
v___x_383_ = 40ULL;
v___x_384_ = lean_uint64_shift_right(v_c_382_, v___x_383_);
v___x_385_ = 1ULL;
v___x_386_ = lean_uint64_land(v___x_384_, v___x_385_);
v___x_387_ = lean_uint64_dec_eq(v___x_386_, v___x_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_388_){
_start:
{
uint64_t v_c_boxed_389_; uint8_t v_res_390_; lean_object* v_r_391_; 
v_c_boxed_389_ = lean_unbox_uint64(v_c_388_);
lean_dec_ref(v_c_388_);
v_res_390_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_392_){
_start:
{
uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint8_t v___x_397_; 
v___x_393_ = 41ULL;
v___x_394_ = lean_uint64_shift_right(v_c_392_, v___x_393_);
v___x_395_ = 1ULL;
v___x_396_ = lean_uint64_land(v___x_394_, v___x_395_);
v___x_397_ = lean_uint64_dec_eq(v___x_396_, v___x_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_398_){
_start:
{
uint64_t v_c_boxed_399_; uint8_t v_res_400_; lean_object* v_r_401_; 
v_c_boxed_399_ = lean_unbox_uint64(v_c_398_);
lean_dec_ref(v_c_398_);
v_res_400_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_402_){
_start:
{
uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint8_t v___x_407_; 
v___x_403_ = 42ULL;
v___x_404_ = lean_uint64_shift_right(v_c_402_, v___x_403_);
v___x_405_ = 1ULL;
v___x_406_ = lean_uint64_land(v___x_404_, v___x_405_);
v___x_407_ = lean_uint64_dec_eq(v___x_406_, v___x_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_408_){
_start:
{
uint64_t v_c_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_c_boxed_409_ = lean_unbox_uint64(v_c_408_);
lean_dec_ref(v_c_408_);
v_res_410_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_412_){
_start:
{
uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint8_t v___x_417_; 
v___x_413_ = 43ULL;
v___x_414_ = lean_uint64_shift_right(v_c_412_, v___x_413_);
v___x_415_ = 1ULL;
v___x_416_ = lean_uint64_land(v___x_414_, v___x_415_);
v___x_417_ = lean_uint64_dec_eq(v___x_416_, v___x_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_418_){
_start:
{
uint64_t v_c_boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_c_boxed_419_ = lean_unbox_uint64(v_c_418_);
lean_dec_ref(v_c_418_);
v_res_420_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_423_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_424_; uint64_t v_res_425_; lean_object* v_r_426_; 
v_a_00___x40___internal___hyg_1__boxed_424_ = lean_unbox(v_a_00___x40___internal___hyg_423_);
v_res_425_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_424_);
v_r_426_ = lean_box_uint64(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_434_, lean_object* v_looseBVarRange_435_, lean_object* v_approxDepth_436_, lean_object* v_hasFVar_437_, lean_object* v_hasExprMVar_438_, lean_object* v_hasLevelMVar_439_, lean_object* v_hasLevelParam_440_){
_start:
{
uint64_t v_h_boxed_441_; uint32_t v_approxDepth_boxed_442_; uint8_t v_hasFVar_boxed_443_; uint8_t v_hasExprMVar_boxed_444_; uint8_t v_hasLevelMVar_boxed_445_; uint8_t v_hasLevelParam_boxed_446_; uint64_t v_res_447_; lean_object* v_r_448_; 
v_h_boxed_441_ = lean_unbox_uint64(v_h_434_);
lean_dec_ref(v_h_434_);
v_approxDepth_boxed_442_ = lean_unbox_uint32(v_approxDepth_436_);
lean_dec(v_approxDepth_436_);
v_hasFVar_boxed_443_ = lean_unbox(v_hasFVar_437_);
v_hasExprMVar_boxed_444_ = lean_unbox(v_hasExprMVar_438_);
v_hasLevelMVar_boxed_445_ = lean_unbox(v_hasLevelMVar_439_);
v_hasLevelParam_boxed_446_ = lean_unbox(v_hasLevelParam_440_);
v_res_447_ = lean_expr_mk_data(v_h_boxed_441_, v_looseBVarRange_435_, v_approxDepth_boxed_442_, v_hasFVar_boxed_443_, v_hasExprMVar_boxed_444_, v_hasLevelMVar_boxed_445_, v_hasLevelParam_boxed_446_);
v_r_448_ = lean_box_uint64(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_451_, lean_object* v_aData_452_){
_start:
{
uint64_t v_fData_boxed_453_; uint64_t v_aData_boxed_454_; uint64_t v_res_455_; lean_object* v_r_456_; 
v_fData_boxed_453_ = lean_unbox_uint64(v_fData_451_);
lean_dec_ref(v_fData_451_);
v_aData_boxed_454_ = lean_unbox_uint64(v_aData_452_);
lean_dec_ref(v_aData_452_);
v_res_455_ = lean_expr_mk_app_data(v_fData_boxed_453_, v_aData_boxed_454_);
v_r_456_ = lean_box_uint64(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_457_, lean_object* v_looseBVarRange_458_, uint32_t v_approxDepth_459_, uint8_t v_hasFVar_460_, uint8_t v_hasExprMVar_461_, uint8_t v_hasLevelMVar_462_, uint8_t v_hasLevelParam_463_){
_start:
{
uint64_t v___x_464_; 
v___x_464_ = lean_expr_mk_data(v_h_457_, v_looseBVarRange_458_, v_approxDepth_459_, v_hasFVar_460_, v_hasExprMVar_461_, v_hasLevelMVar_462_, v_hasLevelParam_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_465_, lean_object* v_looseBVarRange_466_, lean_object* v_approxDepth_467_, lean_object* v_hasFVar_468_, lean_object* v_hasExprMVar_469_, lean_object* v_hasLevelMVar_470_, lean_object* v_hasLevelParam_471_){
_start:
{
uint64_t v_h_boxed_472_; uint32_t v_approxDepth_boxed_473_; uint8_t v_hasFVar_boxed_474_; uint8_t v_hasExprMVar_boxed_475_; uint8_t v_hasLevelMVar_boxed_476_; uint8_t v_hasLevelParam_boxed_477_; uint64_t v_res_478_; lean_object* v_r_479_; 
v_h_boxed_472_ = lean_unbox_uint64(v_h_465_);
lean_dec_ref(v_h_465_);
v_approxDepth_boxed_473_ = lean_unbox_uint32(v_approxDepth_467_);
lean_dec(v_approxDepth_467_);
v_hasFVar_boxed_474_ = lean_unbox(v_hasFVar_468_);
v_hasExprMVar_boxed_475_ = lean_unbox(v_hasExprMVar_469_);
v_hasLevelMVar_boxed_476_ = lean_unbox(v_hasLevelMVar_470_);
v_hasLevelParam_boxed_477_ = lean_unbox(v_hasLevelParam_471_);
v_res_478_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_472_, v_looseBVarRange_466_, v_approxDepth_boxed_473_, v_hasFVar_boxed_474_, v_hasExprMVar_boxed_475_, v_hasLevelMVar_boxed_476_, v_hasLevelParam_boxed_477_);
v_r_479_ = lean_box_uint64(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_480_, lean_object* v_looseBVarRange_481_, uint32_t v_approxDepth_482_, uint8_t v_hasFVar_483_, uint8_t v_hasExprMVar_484_, uint8_t v_hasLevelMVar_485_, uint8_t v_hasLevelParam_486_){
_start:
{
uint64_t v___x_487_; 
v___x_487_ = lean_expr_mk_data(v_h_480_, v_looseBVarRange_481_, v_approxDepth_482_, v_hasFVar_483_, v_hasExprMVar_484_, v_hasLevelMVar_485_, v_hasLevelParam_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_488_, lean_object* v_looseBVarRange_489_, lean_object* v_approxDepth_490_, lean_object* v_hasFVar_491_, lean_object* v_hasExprMVar_492_, lean_object* v_hasLevelMVar_493_, lean_object* v_hasLevelParam_494_){
_start:
{
uint64_t v_h_boxed_495_; uint32_t v_approxDepth_boxed_496_; uint8_t v_hasFVar_boxed_497_; uint8_t v_hasExprMVar_boxed_498_; uint8_t v_hasLevelMVar_boxed_499_; uint8_t v_hasLevelParam_boxed_500_; uint64_t v_res_501_; lean_object* v_r_502_; 
v_h_boxed_495_ = lean_unbox_uint64(v_h_488_);
lean_dec_ref(v_h_488_);
v_approxDepth_boxed_496_ = lean_unbox_uint32(v_approxDepth_490_);
lean_dec(v_approxDepth_490_);
v_hasFVar_boxed_497_ = lean_unbox(v_hasFVar_491_);
v_hasExprMVar_boxed_498_ = lean_unbox(v_hasExprMVar_492_);
v_hasLevelMVar_boxed_499_ = lean_unbox(v_hasLevelMVar_493_);
v_hasLevelParam_boxed_500_ = lean_unbox(v_hasLevelParam_494_);
v_res_501_ = l_Lean_Expr_mkDataForLet(v_h_boxed_495_, v_looseBVarRange_489_, v_approxDepth_boxed_496_, v_hasFVar_boxed_497_, v_hasExprMVar_boxed_498_, v_hasLevelMVar_boxed_499_, v_hasLevelParam_boxed_500_);
v_r_502_ = lean_box_uint64(v_res_501_);
return v_r_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_512_, lean_object* v_prec_513_){
_start:
{
lean_object* v_r_515_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v_r_525_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v_r_538_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v_r_551_; lean_object* v_r_558_; lean_object* v___x_569_; uint64_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_r_573_; uint32_t v___x_574_; uint32_t v___x_575_; uint8_t v___x_576_; 
v___x_569_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_570_ = l_Lean_Expr_Data_hash(v_v_512_);
v___x_571_ = lean_uint64_to_nat(v___x_570_);
v___x_572_ = l_Nat_reprFast(v___x_571_);
v_r_573_ = lean_string_append(v___x_569_, v___x_572_);
lean_dec_ref(v___x_572_);
v___x_574_ = l_Lean_Expr_Data_looseBVarRange(v_v_512_);
v___x_575_ = 0;
v___x_576_ = lean_uint32_dec_eq(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_r_583_; 
v___x_577_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__8));
v___x_578_ = lean_string_append(v_r_573_, v___x_577_);
v___x_579_ = lean_uint32_to_nat(v___x_574_);
v___x_580_ = l_Nat_reprFast(v___x_579_);
v___x_581_ = lean_string_append(v___x_578_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_583_ = lean_string_append(v___x_581_, v___x_582_);
v_r_558_ = v_r_583_;
goto v___jp_557_;
}
else
{
v_r_558_ = v_r_573_;
goto v___jp_557_;
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_516_, 0, v_r_515_);
v___x_517_ = l_Repr_addAppParen(v___x_516_, v_prec_513_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_r_523_; 
v___x_521_ = lean_string_append(v___y_519_, v___y_520_);
v___x_522_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_523_ = lean_string_append(v___x_521_, v___x_522_);
v_r_515_ = v_r_523_;
goto v___jp_514_;
}
v___jp_524_:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Expr_Data_hasLevelMVar(v_v_512_);
if (v___x_526_ == 0)
{
v_r_515_ = v_r_525_;
goto v___jp_514_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_528_ = lean_string_append(v_r_525_, v___x_527_);
if (v___x_526_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_519_ = v___x_528_;
v___y_520_ = v___x_529_;
goto v___jp_518_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_519_ = v___x_528_;
v___y_520_ = v___x_530_;
goto v___jp_518_;
}
}
}
v___jp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_r_536_; 
v___x_534_ = lean_string_append(v___y_532_, v___y_533_);
v___x_535_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_536_ = lean_string_append(v___x_534_, v___x_535_);
v_r_525_ = v_r_536_;
goto v___jp_524_;
}
v___jp_537_:
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_Expr_Data_hasExprMVar(v_v_512_);
if (v___x_539_ == 0)
{
v_r_525_ = v_r_538_;
goto v___jp_524_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_541_ = lean_string_append(v_r_538_, v___x_540_);
if (v___x_539_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_532_ = v___x_541_;
v___y_533_ = v___x_542_;
goto v___jp_531_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_532_ = v___x_541_;
v___y_533_ = v___x_543_;
goto v___jp_531_;
}
}
}
v___jp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_r_549_; 
v___x_547_ = lean_string_append(v___y_545_, v___y_546_);
v___x_548_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_549_ = lean_string_append(v___x_547_, v___x_548_);
v_r_538_ = v_r_549_;
goto v___jp_537_;
}
v___jp_550_:
{
uint8_t v___x_552_; 
v___x_552_ = l_Lean_Expr_Data_hasFVar(v_v_512_);
if (v___x_552_ == 0)
{
v_r_538_ = v_r_551_;
goto v___jp_537_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_554_ = lean_string_append(v_r_551_, v___x_553_);
if (v___x_552_ == 0)
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v___y_545_ = v___x_554_;
v___y_546_ = v___x_555_;
goto v___jp_544_;
}
else
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___y_545_ = v___x_554_;
v___y_546_ = v___x_556_;
goto v___jp_544_;
}
}
}
v___jp_557_:
{
uint8_t v___x_559_; uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = l_Lean_Expr_Data_approxDepth(v_v_512_);
v___x_560_ = 0;
v___x_561_ = lean_uint8_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_r_568_; 
v___x_562_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_563_ = lean_string_append(v_r_558_, v___x_562_);
v___x_564_ = lean_uint8_to_nat(v___x_559_);
v___x_565_ = l_Nat_reprFast(v___x_564_);
v___x_566_ = lean_string_append(v___x_563_, v___x_565_);
lean_dec_ref(v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v_r_568_ = lean_string_append(v___x_566_, v___x_567_);
v_r_551_ = v_r_568_;
goto v___jp_550_;
}
else
{
v_r_551_ = v_r_558_;
goto v___jp_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_584_, lean_object* v_prec_585_){
_start:
{
uint64_t v_v_boxed_586_; lean_object* v_res_587_; 
v_v_boxed_586_ = lean_unbox_uint64(v_v_584_);
lean_dec_ref(v_v_584_);
v_res_587_ = l_Lean_instReprData__1___lam__0(v_v_boxed_586_, v_prec_585_);
lean_dec(v_prec_585_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
return v___x_591_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_name_eq(v_x_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Lean_instBEqFVarId_beq(v_x_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec(v_x_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
static uint64_t _init_l_Lean_instHashableFVarId_hash___closed__0(void){
_start:
{
uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; 
v___x_601_ = 1723ULL;
v___x_602_ = 0ULL;
v___x_603_ = lean_uint64_mix_hash(v___x_602_, v___x_601_);
return v___x_603_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_604_){
_start:
{
uint64_t v___x_605_; 
v___x_605_ = 0ULL;
if (lean_obj_tag(v_x_604_) == 0)
{
uint64_t v___x_606_; 
v___x_606_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
return v___x_606_;
}
else
{
uint64_t v_hash_607_; uint64_t v___x_608_; 
v_hash_607_ = lean_ctor_get_uint64(v_x_604_, sizeof(void*)*2);
v___x_608_ = lean_uint64_mix_hash(v___x_605_, v_hash_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_609_){
_start:
{
uint64_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_instHashableFVarId_hash(v_x_609_);
lean_dec(v_x_609_);
v_r_611_ = lean_box_uint64(v_res_610_);
return v_r_611_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(1);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_box(1);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_box(1);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_box(1);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_621_){
_start:
{
lean_object* v___f_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___f_622_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_623_ = lean_box(1);
lean_inc(v_e_621_);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_622_, v_e_621_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(0);
v___x_626_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_622_, v_e_621_, v___x_625_, v___x_623_);
return v___x_626_;
}
else
{
lean_dec(v_e_621_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_627_, lean_object* v_v_628_, lean_object* v_t_629_){
_start:
{
if (lean_obj_tag(v_t_629_) == 0)
{
lean_object* v_size_630_; lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v_l_633_; lean_object* v_r_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_914_; 
v_size_630_ = lean_ctor_get(v_t_629_, 0);
v_k_631_ = lean_ctor_get(v_t_629_, 1);
v_v_632_ = lean_ctor_get(v_t_629_, 2);
v_l_633_ = lean_ctor_get(v_t_629_, 3);
v_r_634_ = lean_ctor_get(v_t_629_, 4);
v_isSharedCheck_914_ = !lean_is_exclusive(v_t_629_);
if (v_isSharedCheck_914_ == 0)
{
v___x_636_ = v_t_629_;
v_isShared_637_ = v_isSharedCheck_914_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_r_634_);
lean_inc(v_l_633_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
lean_inc(v_size_630_);
lean_dec(v_t_629_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_914_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v___x_638_; 
v___x_638_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_627_, v_k_631_);
switch(v___x_638_)
{
case 0:
{
lean_object* v_impl_639_; lean_object* v___x_640_; 
lean_dec(v_size_630_);
v_impl_639_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_627_, v_v_628_, v_l_633_);
v___x_640_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_634_) == 0)
{
lean_object* v_size_641_; lean_object* v_size_642_; lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_size_641_ = lean_ctor_get(v_r_634_, 0);
v_size_642_ = lean_ctor_get(v_impl_639_, 0);
lean_inc(v_size_642_);
v_k_643_ = lean_ctor_get(v_impl_639_, 1);
lean_inc(v_k_643_);
v_v_644_ = lean_ctor_get(v_impl_639_, 2);
lean_inc(v_v_644_);
v_l_645_ = lean_ctor_get(v_impl_639_, 3);
lean_inc(v_l_645_);
v_r_646_ = lean_ctor_get(v_impl_639_, 4);
lean_inc(v_r_646_);
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = lean_nat_mul(v___x_647_, v_size_641_);
v___x_649_ = lean_nat_dec_lt(v___x_648_, v_size_642_);
lean_dec(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
lean_dec(v_r_646_);
lean_dec(v_l_645_);
lean_dec(v_v_644_);
lean_dec(v_k_643_);
v___x_650_ = lean_nat_add(v___x_640_, v_size_642_);
lean_dec(v_size_642_);
v___x_651_ = lean_nat_add(v___x_650_, v_size_641_);
lean_dec(v___x_650_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 3, v_impl_639_);
lean_ctor_set(v___x_636_, 0, v___x_651_);
v___x_653_ = v___x_636_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_impl_639_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_r_634_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_720_; 
v_isSharedCheck_720_ = !lean_is_exclusive(v_impl_639_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; 
v_unused_721_ = lean_ctor_get(v_impl_639_, 4);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_impl_639_, 3);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_impl_639_, 2);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_impl_639_, 1);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_impl_639_, 0);
lean_dec(v_unused_725_);
v___x_656_ = v_impl_639_;
v_isShared_657_ = v_isSharedCheck_720_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_impl_639_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_720_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_size_658_; lean_object* v_size_659_; lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v_l_662_; lean_object* v_r_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_size_658_ = lean_ctor_get(v_l_645_, 0);
v_size_659_ = lean_ctor_get(v_r_646_, 0);
v_k_660_ = lean_ctor_get(v_r_646_, 1);
v_v_661_ = lean_ctor_get(v_r_646_, 2);
v_l_662_ = lean_ctor_get(v_r_646_, 3);
v_r_663_ = lean_ctor_get(v_r_646_, 4);
v___x_664_ = lean_unsigned_to_nat(2u);
v___x_665_ = lean_nat_mul(v___x_664_, v_size_658_);
v___x_666_ = lean_nat_dec_lt(v_size_659_, v___x_665_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_695_; 
lean_inc(v_r_663_);
lean_inc(v_l_662_);
lean_inc(v_v_661_);
lean_inc(v_k_660_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_r_646_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_696_ = lean_ctor_get(v_r_646_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_r_646_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_r_646_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_r_646_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_r_646_, 0);
lean_dec(v_unused_700_);
v___x_668_ = v_r_646_;
v_isShared_669_ = v_isSharedCheck_695_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_r_646_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_695_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___x_683_; lean_object* v___y_685_; 
v___x_670_ = lean_nat_add(v___x_640_, v_size_642_);
lean_dec(v_size_642_);
v___x_671_ = lean_nat_add(v___x_670_, v_size_641_);
lean_dec(v___x_670_);
v___x_683_ = lean_nat_add(v___x_640_, v_size_658_);
if (lean_obj_tag(v_l_662_) == 0)
{
lean_object* v_size_693_; 
v_size_693_ = lean_ctor_get(v_l_662_, 0);
lean_inc(v_size_693_);
v___y_685_ = v_size_693_;
goto v___jp_684_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___y_685_ = v___x_694_;
goto v___jp_684_;
}
v___jp_672_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_nat_add(v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 4, v_r_634_);
lean_ctor_set(v___x_668_, 3, v_r_663_);
lean_ctor_set(v___x_668_, 2, v_v_632_);
lean_ctor_set(v___x_668_, 1, v_k_631_);
lean_ctor_set(v___x_668_, 0, v___x_676_);
v___x_678_ = v___x_668_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_r_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_r_634_);
v___x_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_678_);
lean_ctor_set(v___x_656_, 3, v___y_673_);
lean_ctor_set(v___x_656_, 2, v_v_661_);
lean_ctor_set(v___x_656_, 1, v_k_660_);
lean_ctor_set(v___x_656_, 0, v___x_671_);
v___x_680_ = v___x_656_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___y_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_nat_add(v___x_683_, v___y_685_);
lean_dec(v___y_685_);
lean_dec(v___x_683_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v_l_662_);
lean_ctor_set(v___x_636_, 3, v_l_645_);
lean_ctor_set(v___x_636_, 2, v_v_644_);
lean_ctor_set(v___x_636_, 1, v_k_643_);
lean_ctor_set(v___x_636_, 0, v___x_686_);
v___x_688_ = v___x_636_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_l_645_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_l_662_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_nat_add(v___x_640_, v_size_641_);
if (lean_obj_tag(v_r_663_) == 0)
{
lean_object* v_size_690_; 
v_size_690_ = lean_ctor_get(v_r_663_, 0);
lean_inc(v_size_690_);
v___y_673_ = v___x_688_;
v___y_674_ = v___x_689_;
v___y_675_ = v_size_690_;
goto v___jp_672_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_673_ = v___x_688_;
v___y_674_ = v___x_689_;
v___y_675_ = v___x_691_;
goto v___jp_672_;
}
}
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_del_object(v___x_636_);
v___x_701_ = lean_nat_add(v___x_640_, v_size_642_);
lean_dec(v_size_642_);
v___x_702_ = lean_nat_add(v___x_701_, v_size_641_);
lean_dec(v___x_701_);
v___x_703_ = lean_nat_add(v___x_640_, v_size_641_);
v___x_704_ = lean_nat_add(v___x_703_, v_size_659_);
lean_dec(v___x_703_);
lean_inc_ref(v_r_634_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_r_634_);
lean_ctor_set(v___x_656_, 3, v_r_646_);
lean_ctor_set(v___x_656_, 2, v_v_632_);
lean_ctor_set(v___x_656_, 1, v_k_631_);
lean_ctor_set(v___x_656_, 0, v___x_704_);
v___x_706_ = v___x_656_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_r_634_);
v___x_706_ = v_reuseFailAlloc_719_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_isSharedCheck_713_ = !lean_is_exclusive(v_r_634_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_714_ = lean_ctor_get(v_r_634_, 4);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_r_634_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_r_634_, 2);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_r_634_, 1);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_r_634_, 0);
lean_dec(v_unused_718_);
v___x_708_ = v_r_634_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_r_634_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v___x_706_);
lean_ctor_set(v___x_708_, 3, v_l_645_);
lean_ctor_set(v___x_708_, 2, v_v_644_);
lean_ctor_set(v___x_708_, 1, v_k_643_);
lean_ctor_set(v___x_708_, 0, v___x_702_);
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_l_645_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v___x_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_726_; 
v_l_726_ = lean_ctor_get(v_impl_639_, 3);
lean_inc(v_l_726_);
if (lean_obj_tag(v_l_726_) == 0)
{
lean_object* v_r_727_; lean_object* v_k_728_; lean_object* v_v_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_740_; 
v_r_727_ = lean_ctor_get(v_impl_639_, 4);
v_k_728_ = lean_ctor_get(v_impl_639_, 1);
v_v_729_ = lean_ctor_get(v_impl_639_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_impl_639_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; lean_object* v_unused_742_; 
v_unused_741_ = lean_ctor_get(v_impl_639_, 3);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_impl_639_, 0);
lean_dec(v_unused_742_);
v___x_731_ = v_impl_639_;
v_isShared_732_ = v_isSharedCheck_740_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_r_727_);
lean_inc(v_v_729_);
lean_inc(v_k_728_);
lean_dec(v_impl_639_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_740_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_727_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 3, v_r_727_);
lean_ctor_set(v___x_731_, 2, v_v_632_);
lean_ctor_set(v___x_731_, 1, v_k_631_);
lean_ctor_set(v___x_731_, 0, v___x_640_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_r_727_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_r_727_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v___x_735_);
lean_ctor_set(v___x_636_, 3, v_l_726_);
lean_ctor_set(v___x_636_, 2, v_v_729_);
lean_ctor_set(v___x_636_, 1, v_k_728_);
lean_ctor_set(v___x_636_, 0, v___x_733_);
v___x_737_ = v___x_636_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_k_728_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_v_729_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_l_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_r_743_; 
v_r_743_ = lean_ctor_get(v_impl_639_, 4);
lean_inc(v_r_743_);
if (lean_obj_tag(v_r_743_) == 0)
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_768_; 
v_k_744_ = lean_ctor_get(v_impl_639_, 1);
v_v_745_ = lean_ctor_get(v_impl_639_, 2);
v_isSharedCheck_768_ = !lean_is_exclusive(v_impl_639_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; 
v_unused_769_ = lean_ctor_get(v_impl_639_, 4);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_impl_639_, 3);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_impl_639_, 0);
lean_dec(v_unused_771_);
v___x_747_ = v_impl_639_;
v_isShared_748_ = v_isSharedCheck_768_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_v_745_);
lean_inc(v_k_744_);
lean_dec(v_impl_639_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_768_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_k_749_; lean_object* v_v_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_764_; 
v_k_749_ = lean_ctor_get(v_r_743_, 1);
v_v_750_ = lean_ctor_get(v_r_743_, 2);
v_isSharedCheck_764_ = !lean_is_exclusive(v_r_743_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_765_ = lean_ctor_get(v_r_743_, 4);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_r_743_, 3);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_r_743_, 0);
lean_dec(v_unused_767_);
v___x_752_ = v_r_743_;
v_isShared_753_ = v_isSharedCheck_764_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_v_750_);
lean_inc(v_k_749_);
lean_dec(v_r_743_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_764_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_unsigned_to_nat(3u);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 4, v_l_726_);
lean_ctor_set(v___x_752_, 3, v_l_726_);
lean_ctor_set(v___x_752_, 2, v_v_745_);
lean_ctor_set(v___x_752_, 1, v_k_744_);
lean_ctor_set(v___x_752_, 0, v___x_640_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_744_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_745_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_l_726_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_l_726_);
v___x_756_ = v_reuseFailAlloc_763_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 4, v_l_726_);
lean_ctor_set(v___x_747_, 2, v_v_632_);
lean_ctor_set(v___x_747_, 1, v_k_631_);
lean_ctor_set(v___x_747_, 0, v___x_640_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_l_726_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_l_726_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v___x_758_);
lean_ctor_set(v___x_636_, 3, v___x_756_);
lean_ctor_set(v___x_636_, 2, v_v_750_);
lean_ctor_set(v___x_636_, 1, v_k_749_);
lean_ctor_set(v___x_636_, 0, v___x_754_);
v___x_760_ = v___x_636_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_unsigned_to_nat(2u);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v_r_743_);
lean_ctor_set(v___x_636_, 3, v_impl_639_);
lean_ctor_set(v___x_636_, 0, v___x_772_);
v___x_774_ = v___x_636_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_impl_639_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_r_743_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
case 1:
{
lean_object* v___x_777_; 
lean_dec(v_v_632_);
lean_dec(v_k_631_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v_v_628_);
lean_ctor_set(v___x_636_, 1, v_k_627_);
v___x_777_ = v___x_636_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_size_630_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_l_633_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_r_634_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
default: 
{
lean_object* v_impl_779_; lean_object* v___x_780_; 
lean_dec(v_size_630_);
v_impl_779_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_627_, v_v_628_, v_r_634_);
v___x_780_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_633_) == 0)
{
lean_object* v_size_781_; lean_object* v_size_782_; lean_object* v_k_783_; lean_object* v_v_784_; lean_object* v_l_785_; lean_object* v_r_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_size_781_ = lean_ctor_get(v_l_633_, 0);
v_size_782_ = lean_ctor_get(v_impl_779_, 0);
lean_inc(v_size_782_);
v_k_783_ = lean_ctor_get(v_impl_779_, 1);
lean_inc(v_k_783_);
v_v_784_ = lean_ctor_get(v_impl_779_, 2);
lean_inc(v_v_784_);
v_l_785_ = lean_ctor_get(v_impl_779_, 3);
lean_inc(v_l_785_);
v_r_786_ = lean_ctor_get(v_impl_779_, 4);
lean_inc(v_r_786_);
v___x_787_ = lean_unsigned_to_nat(3u);
v___x_788_ = lean_nat_mul(v___x_787_, v_size_781_);
v___x_789_ = lean_nat_dec_lt(v___x_788_, v_size_782_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_dec(v_r_786_);
lean_dec(v_l_785_);
lean_dec(v_v_784_);
lean_dec(v_k_783_);
v___x_790_ = lean_nat_add(v___x_780_, v_size_781_);
v___x_791_ = lean_nat_add(v___x_790_, v_size_782_);
lean_dec(v_size_782_);
lean_dec(v___x_790_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v_impl_779_);
lean_ctor_set(v___x_636_, 0, v___x_791_);
v___x_793_ = v___x_636_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_l_633_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_impl_779_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_858_; 
v_isSharedCheck_858_ = !lean_is_exclusive(v_impl_779_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; lean_object* v_unused_860_; lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; 
v_unused_859_ = lean_ctor_get(v_impl_779_, 4);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_impl_779_, 3);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v_impl_779_, 2);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_impl_779_, 1);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_impl_779_, 0);
lean_dec(v_unused_863_);
v___x_796_ = v_impl_779_;
v_isShared_797_ = v_isSharedCheck_858_;
goto v_resetjp_795_;
}
else
{
lean_dec(v_impl_779_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_858_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_size_798_; lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v_l_801_; lean_object* v_r_802_; lean_object* v_size_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_size_798_ = lean_ctor_get(v_l_785_, 0);
v_k_799_ = lean_ctor_get(v_l_785_, 1);
v_v_800_ = lean_ctor_get(v_l_785_, 2);
v_l_801_ = lean_ctor_get(v_l_785_, 3);
v_r_802_ = lean_ctor_get(v_l_785_, 4);
v_size_803_ = lean_ctor_get(v_r_786_, 0);
v___x_804_ = lean_unsigned_to_nat(2u);
v___x_805_ = lean_nat_mul(v___x_804_, v_size_803_);
v___x_806_ = lean_nat_dec_lt(v_size_798_, v___x_805_);
lean_dec(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_834_; 
lean_inc(v_r_802_);
lean_inc(v_l_801_);
lean_inc(v_v_800_);
lean_inc(v_k_799_);
v_isSharedCheck_834_ = !lean_is_exclusive(v_l_785_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; 
v_unused_835_ = lean_ctor_get(v_l_785_, 4);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_l_785_, 3);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_l_785_, 2);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_l_785_, 1);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_785_, 0);
lean_dec(v_unused_839_);
v___x_808_ = v_l_785_;
v_isShared_809_ = v_isSharedCheck_834_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_l_785_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_834_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_824_; 
v___x_810_ = lean_nat_add(v___x_780_, v_size_781_);
v___x_811_ = lean_nat_add(v___x_810_, v_size_782_);
lean_dec(v_size_782_);
if (lean_obj_tag(v_l_801_) == 0)
{
lean_object* v_size_832_; 
v_size_832_ = lean_ctor_get(v_l_801_, 0);
lean_inc(v_size_832_);
v___y_824_ = v_size_832_;
goto v___jp_823_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___y_824_ = v___x_833_;
goto v___jp_823_;
}
v___jp_812_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_nat_add(v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec(v___y_814_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_r_786_);
lean_ctor_set(v___x_808_, 3, v_r_802_);
lean_ctor_set(v___x_808_, 2, v_v_784_);
lean_ctor_set(v___x_808_, 1, v_k_783_);
lean_ctor_set(v___x_808_, 0, v___x_816_);
v___x_818_ = v___x_808_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_r_802_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_r_786_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 4, v___x_818_);
lean_ctor_set(v___x_796_, 3, v___y_813_);
lean_ctor_set(v___x_796_, 2, v_v_800_);
lean_ctor_set(v___x_796_, 1, v_k_799_);
lean_ctor_set(v___x_796_, 0, v___x_811_);
v___x_820_ = v___x_796_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___y_813_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_nat_add(v___x_810_, v___y_824_);
lean_dec(v___y_824_);
lean_dec(v___x_810_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v_l_801_);
lean_ctor_set(v___x_636_, 0, v___x_825_);
v___x_827_ = v___x_636_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_l_633_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_l_801_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_nat_add(v___x_780_, v_size_803_);
if (lean_obj_tag(v_r_802_) == 0)
{
lean_object* v_size_829_; 
v_size_829_ = lean_ctor_get(v_r_802_, 0);
lean_inc(v_size_829_);
v___y_813_ = v___x_827_;
v___y_814_ = v___x_828_;
v___y_815_ = v_size_829_;
goto v___jp_812_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___y_813_ = v___x_827_;
v___y_814_ = v___x_828_;
v___y_815_ = v___x_830_;
goto v___jp_812_;
}
}
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
lean_del_object(v___x_636_);
v___x_840_ = lean_nat_add(v___x_780_, v_size_781_);
v___x_841_ = lean_nat_add(v___x_840_, v_size_782_);
lean_dec(v_size_782_);
v___x_842_ = lean_nat_add(v___x_840_, v_size_798_);
lean_dec(v___x_840_);
lean_inc_ref(v_l_633_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 4, v_l_785_);
lean_ctor_set(v___x_796_, 3, v_l_633_);
lean_ctor_set(v___x_796_, 2, v_v_632_);
lean_ctor_set(v___x_796_, 1, v_k_631_);
lean_ctor_set(v___x_796_, 0, v___x_842_);
v___x_844_ = v___x_796_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_l_633_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_l_785_);
v___x_844_ = v_reuseFailAlloc_857_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v_l_633_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; lean_object* v_unused_854_; lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_852_ = lean_ctor_get(v_l_633_, 4);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_l_633_, 3);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_l_633_, 2);
lean_dec(v_unused_854_);
v_unused_855_ = lean_ctor_get(v_l_633_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_l_633_, 0);
lean_dec(v_unused_856_);
v___x_846_ = v_l_633_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_l_633_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_r_786_);
lean_ctor_set(v___x_846_, 3, v___x_844_);
lean_ctor_set(v___x_846_, 2, v_v_784_);
lean_ctor_set(v___x_846_, 1, v_k_783_);
lean_ctor_set(v___x_846_, 0, v___x_841_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_r_786_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_864_; 
v_l_864_ = lean_ctor_get(v_impl_779_, 3);
lean_inc(v_l_864_);
if (lean_obj_tag(v_l_864_) == 0)
{
lean_object* v_r_865_; lean_object* v_k_866_; lean_object* v_v_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_890_; 
v_r_865_ = lean_ctor_get(v_impl_779_, 4);
v_k_866_ = lean_ctor_get(v_impl_779_, 1);
v_v_867_ = lean_ctor_get(v_impl_779_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_impl_779_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_891_ = lean_ctor_get(v_impl_779_, 3);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_impl_779_, 0);
lean_dec(v_unused_892_);
v___x_869_ = v_impl_779_;
v_isShared_870_ = v_isSharedCheck_890_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_r_865_);
lean_inc(v_v_867_);
lean_inc(v_k_866_);
lean_dec(v_impl_779_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_890_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_k_871_ = lean_ctor_get(v_l_864_, 1);
v_v_872_ = lean_ctor_get(v_l_864_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_l_864_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; lean_object* v_unused_888_; lean_object* v_unused_889_; 
v_unused_887_ = lean_ctor_get(v_l_864_, 4);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_l_864_, 3);
lean_dec(v_unused_888_);
v_unused_889_ = lean_ctor_get(v_l_864_, 0);
lean_dec(v_unused_889_);
v___x_874_ = v_l_864_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_v_872_);
lean_inc(v_k_871_);
lean_dec(v_l_864_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_865_, 2);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v_r_865_);
lean_ctor_set(v___x_874_, 3, v_r_865_);
lean_ctor_set(v___x_874_, 2, v_v_632_);
lean_ctor_set(v___x_874_, 1, v_k_631_);
lean_ctor_set(v___x_874_, 0, v___x_780_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_r_865_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_r_865_);
v___x_878_ = v_reuseFailAlloc_885_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
lean_inc(v_r_865_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 3, v_r_865_);
lean_ctor_set(v___x_869_, 0, v___x_780_);
v___x_880_ = v___x_869_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_k_866_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_v_867_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_r_865_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v_r_865_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v___x_880_);
lean_ctor_set(v___x_636_, 3, v___x_878_);
lean_ctor_set(v___x_636_, 2, v_v_872_);
lean_ctor_set(v___x_636_, 1, v_k_871_);
lean_ctor_set(v___x_636_, 0, v___x_876_);
v___x_882_ = v___x_636_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
else
{
lean_object* v_r_893_; 
v_r_893_ = lean_ctor_get(v_impl_779_, 4);
lean_inc(v_r_893_);
if (lean_obj_tag(v_r_893_) == 0)
{
lean_object* v_k_894_; lean_object* v_v_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_906_; 
v_k_894_ = lean_ctor_get(v_impl_779_, 1);
v_v_895_ = lean_ctor_get(v_impl_779_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_impl_779_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_907_ = lean_ctor_get(v_impl_779_, 4);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_impl_779_, 3);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_impl_779_, 0);
lean_dec(v_unused_909_);
v___x_897_ = v_impl_779_;
v_isShared_898_ = v_isSharedCheck_906_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_v_895_);
lean_inc(v_k_894_);
lean_dec(v_impl_779_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_906_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_unsigned_to_nat(3u);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 4, v_l_864_);
lean_ctor_set(v___x_897_, 2, v_v_632_);
lean_ctor_set(v___x_897_, 1, v_k_631_);
lean_ctor_set(v___x_897_, 0, v___x_780_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_864_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_l_864_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v_r_893_);
lean_ctor_set(v___x_636_, 3, v___x_901_);
lean_ctor_set(v___x_636_, 2, v_v_895_);
lean_ctor_set(v___x_636_, 1, v_k_894_);
lean_ctor_set(v___x_636_, 0, v___x_899_);
v___x_903_ = v___x_636_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_893_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_unsigned_to_nat(2u);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 4, v_impl_779_);
lean_ctor_set(v___x_636_, 3, v_r_893_);
lean_ctor_set(v___x_636_, 0, v___x_910_);
v___x_912_ = v___x_636_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_r_893_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_impl_779_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
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
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_k_627_);
lean_ctor_set(v___x_916_, 2, v_v_628_);
lean_ctor_set(v___x_916_, 3, v_t_629_);
lean_ctor_set(v___x_916_, 4, v_t_629_);
return v___x_916_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_917_, lean_object* v_t_918_){
_start:
{
if (lean_obj_tag(v_t_918_) == 0)
{
lean_object* v_k_919_; lean_object* v_l_920_; lean_object* v_r_921_; uint8_t v___x_922_; 
v_k_919_ = lean_ctor_get(v_t_918_, 1);
v_l_920_ = lean_ctor_get(v_t_918_, 3);
v_r_921_ = lean_ctor_get(v_t_918_, 4);
v___x_922_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_917_, v_k_919_);
switch(v___x_922_)
{
case 0:
{
v_t_918_ = v_l_920_;
goto _start;
}
case 1:
{
uint8_t v___x_924_; 
v___x_924_ = 1;
return v___x_924_;
}
default: 
{
v_t_918_ = v_r_921_;
goto _start;
}
}
}
else
{
uint8_t v___x_926_; 
v___x_926_ = 0;
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_927_, lean_object* v_t_928_){
_start:
{
uint8_t v_res_929_; lean_object* v_r_930_; 
v_res_929_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_927_, v_t_928_);
lean_dec(v_t_928_);
lean_dec(v_k_927_);
v_r_930_ = lean_box(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_931_){
_start:
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_box(1);
v___x_933_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_box(0);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_931_, v___x_934_, v___x_932_);
return v___x_935_;
}
else
{
lean_dec(v___y_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_938_, lean_object* v_k_939_, lean_object* v_t_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_939_, v_t_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_942_, lean_object* v_k_943_, lean_object* v_t_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_942_, v_k_943_, v_t_944_);
lean_dec(v_t_944_);
lean_dec(v_k_943_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_947_, lean_object* v_k_948_, lean_object* v_v_949_, lean_object* v_t_950_, lean_object* v_hl_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_948_, v_v_949_, v_t_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_953_, lean_object* v_a_954_, lean_object* v_b_955_, lean_object* v_c_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_apply_2(v_f_953_, v_a_954_, v_c_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_958_, lean_object* v_____do__lift_959_){
_start:
{
lean_object* v_a_960_; lean_object* v___x_961_; 
v_a_960_ = lean_ctor_get(v_____do__lift_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v_____do__lift_959_);
v___x_961_ = lean_apply_2(v_toPure_958_, lean_box(0), v_a_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_962_, lean_object* v_m_963_, lean_object* v_init_964_, lean_object* v_f_965_){
_start:
{
lean_object* v_toApplicative_966_; lean_object* v_toBind_967_; lean_object* v_toPure_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___x_972_; 
v_toApplicative_966_ = lean_ctor_get(v_inst_962_, 0);
v_toBind_967_ = lean_ctor_get(v_inst_962_, 1);
lean_inc(v_toBind_967_);
v_toPure_968_ = lean_ctor_get(v_toApplicative_966_, 1);
lean_inc(v_toPure_968_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_969_, 0, v_f_965_);
v___x_970_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_962_, v___f_969_, v_init_964_, v_m_963_);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_971_, 0, v_toPure_968_);
v___x_972_ = lean_apply_4(v_toBind_967_, lean_box(0), lean_box(0), v___x_970_, v___f_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_973_, lean_object* v_inst_974_, lean_object* v_00_u03b2_975_, lean_object* v_m_976_, lean_object* v_init_977_, lean_object* v_f_978_){
_start:
{
lean_object* v_toApplicative_979_; lean_object* v_toBind_980_; lean_object* v_toPure_981_; lean_object* v___f_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
v_toApplicative_979_ = lean_ctor_get(v_inst_974_, 0);
v_toBind_980_ = lean_ctor_get(v_inst_974_, 1);
lean_inc(v_toBind_980_);
v_toPure_981_ = lean_ctor_get(v_toApplicative_979_, 1);
lean_inc(v_toPure_981_);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_982_, 0, v_f_978_);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_974_, v___f_982_, v_init_977_, v_m_976_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_984_, 0, v_toPure_981_);
v___x_985_ = lean_apply_4(v_toBind_980_, lean_box(0), lean_box(0), v___x_983_, v___f_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_987_, 0, lean_box(0));
lean_closure_set(v___x_987_, 1, v_inst_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_990_, 0, lean_box(0));
lean_closure_set(v___x_990_, 1, v_inst_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_991_, lean_object* v_fvarId_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_992_, v_s_991_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_box(0);
v___x_995_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_992_, v___x_994_, v_s_991_);
return v___x_995_;
}
else
{
lean_dec(v_fvarId_992_);
return v_s_991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_996_, lean_object* v_x_997_){
_start:
{
if (lean_obj_tag(v_x_997_) == 0)
{
lean_object* v_k_998_; lean_object* v_l_999_; lean_object* v_r_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_k_998_ = lean_ctor_get(v_x_997_, 1);
lean_inc(v_k_998_);
v_l_999_ = lean_ctor_get(v_x_997_, 3);
lean_inc(v_l_999_);
v_r_1000_ = lean_ctor_get(v_x_997_, 4);
lean_inc(v_r_1000_);
lean_dec_ref_known(v_x_997_, 5);
v___x_1001_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_996_, v_l_999_);
v___x_1002_ = l_Lean_FVarIdSet_insert(v___x_1001_, v_k_998_);
v_init_996_ = v___x_1002_;
v_x_997_ = v_r_1000_;
goto _start;
}
else
{
return v_init_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_1004_, lean_object* v_vs_u2082_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_1005_, v_vs_u2081_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_1007_, lean_object* v_t_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_1007_, v_t_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_1010_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___f_1011_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1012_ = l_Std_TreeSet_ofList___redArg(v_l_1010_, v___f_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_FVarIdSet_ofList(v_l_1013_);
lean_dec(v_l_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_1015_){
_start:
{
lean_object* v___f_1016_; lean_object* v___x_1017_; 
v___f_1016_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1017_ = l_Std_TreeSet_ofArray___redArg(v_l_1015_, v___f_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_FVarIdSet_ofArray(v_l_1018_);
lean_dec_ref(v_l_1018_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v_cellCount_1020_; lean_object* v___x_1021_; 
v_cellCount_1020_ = lean_unsigned_to_nat(16u);
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v_cellCount_1022_; lean_object* v___x_1023_; 
v_cellCount_1022_ = lean_unsigned_to_nat(16u);
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
v___x_1025_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
lean_ctor_set(v___x_1027_, 2, v___x_1024_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__2);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1032_, lean_object* v_fvarId_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1033_, v_a_1034_, v_s_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1036_, lean_object* v_s_1037_, lean_object* v_fvarId_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1038_, v_a_1039_, v_s_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(1);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_box(1);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_box(1);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_box(0);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_name_eq(v_x_1049_, v_x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Lean_instBEqMVarId_beq(v_x_1052_, v_x_1053_);
lean_dec(v_x_1053_);
lean_dec(v_x_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1058_){
_start:
{
uint64_t v___x_1059_; 
v___x_1059_ = 0ULL;
if (lean_obj_tag(v_x_1058_) == 0)
{
uint64_t v___x_1060_; 
v___x_1060_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
return v___x_1060_;
}
else
{
uint64_t v_hash_1061_; uint64_t v___x_1062_; 
v_hash_1061_ = lean_ctor_get_uint64(v_x_1058_, sizeof(void*)*2);
v___x_1062_ = lean_uint64_mix_hash(v___x_1059_, v_hash_1061_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1063_){
_start:
{
uint64_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lean_instHashableMVarId_hash(v_x_1063_);
lean_dec(v_x_1063_);
v_r_1065_ = lean_box_uint64(v_res_1064_);
return v_r_1065_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_box(1);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(1);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_box(1);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_box(1);
return v___x_1072_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1073_, lean_object* v_t_1074_){
_start:
{
if (lean_obj_tag(v_t_1074_) == 0)
{
lean_object* v_k_1075_; lean_object* v_l_1076_; lean_object* v_r_1077_; uint8_t v___x_1078_; 
v_k_1075_ = lean_ctor_get(v_t_1074_, 1);
v_l_1076_ = lean_ctor_get(v_t_1074_, 3);
v_r_1077_ = lean_ctor_get(v_t_1074_, 4);
v___x_1078_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1073_, v_k_1075_);
switch(v___x_1078_)
{
case 0:
{
v_t_1074_ = v_l_1076_;
goto _start;
}
case 1:
{
uint8_t v___x_1080_; 
v___x_1080_ = 1;
return v___x_1080_;
}
default: 
{
v_t_1074_ = v_r_1077_;
goto _start;
}
}
}
else
{
uint8_t v___x_1082_; 
v___x_1082_ = 0;
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1083_, lean_object* v_t_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1083_, v_t_1084_);
lean_dec(v_t_1084_);
lean_dec(v_k_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1087_, lean_object* v_v_1088_, lean_object* v_t_1089_){
_start:
{
if (lean_obj_tag(v_t_1089_) == 0)
{
lean_object* v_size_1090_; lean_object* v_k_1091_; lean_object* v_v_1092_; lean_object* v_l_1093_; lean_object* v_r_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1374_; 
v_size_1090_ = lean_ctor_get(v_t_1089_, 0);
v_k_1091_ = lean_ctor_get(v_t_1089_, 1);
v_v_1092_ = lean_ctor_get(v_t_1089_, 2);
v_l_1093_ = lean_ctor_get(v_t_1089_, 3);
v_r_1094_ = lean_ctor_get(v_t_1089_, 4);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_t_1089_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1096_ = v_t_1089_;
v_isShared_1097_ = v_isSharedCheck_1374_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_r_1094_);
lean_inc(v_l_1093_);
lean_inc(v_v_1092_);
lean_inc(v_k_1091_);
lean_inc(v_size_1090_);
lean_dec(v_t_1089_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1374_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1087_, v_k_1091_);
switch(v___x_1098_)
{
case 0:
{
lean_object* v_impl_1099_; lean_object* v___x_1100_; 
lean_dec(v_size_1090_);
v_impl_1099_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1087_, v_v_1088_, v_l_1093_);
v___x_1100_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1094_) == 0)
{
lean_object* v_size_1101_; lean_object* v_size_1102_; lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v_l_1105_; lean_object* v_r_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_size_1101_ = lean_ctor_get(v_r_1094_, 0);
v_size_1102_ = lean_ctor_get(v_impl_1099_, 0);
lean_inc(v_size_1102_);
v_k_1103_ = lean_ctor_get(v_impl_1099_, 1);
lean_inc(v_k_1103_);
v_v_1104_ = lean_ctor_get(v_impl_1099_, 2);
lean_inc(v_v_1104_);
v_l_1105_ = lean_ctor_get(v_impl_1099_, 3);
lean_inc(v_l_1105_);
v_r_1106_ = lean_ctor_get(v_impl_1099_, 4);
lean_inc(v_r_1106_);
v___x_1107_ = lean_unsigned_to_nat(3u);
v___x_1108_ = lean_nat_mul(v___x_1107_, v_size_1101_);
v___x_1109_ = lean_nat_dec_lt(v___x_1108_, v_size_1102_);
lean_dec(v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_r_1106_);
lean_dec(v_l_1105_);
lean_dec(v_v_1104_);
lean_dec(v_k_1103_);
v___x_1110_ = lean_nat_add(v___x_1100_, v_size_1102_);
lean_dec(v_size_1102_);
v___x_1111_ = lean_nat_add(v___x_1110_, v_size_1101_);
lean_dec(v___x_1110_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 3, v_impl_1099_);
lean_ctor_set(v___x_1096_, 0, v___x_1111_);
v___x_1113_ = v___x_1096_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_r_1094_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1180_; 
v_isSharedCheck_1180_ = !lean_is_exclusive(v_impl_1099_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1181_ = lean_ctor_get(v_impl_1099_, 4);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_impl_1099_, 3);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_impl_1099_, 2);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_impl_1099_, 1);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_impl_1099_, 0);
lean_dec(v_unused_1185_);
v___x_1116_ = v_impl_1099_;
v_isShared_1117_ = v_isSharedCheck_1180_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_impl_1099_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1180_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_size_1118_; lean_object* v_size_1119_; lean_object* v_k_1120_; lean_object* v_v_1121_; lean_object* v_l_1122_; lean_object* v_r_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_size_1118_ = lean_ctor_get(v_l_1105_, 0);
v_size_1119_ = lean_ctor_get(v_r_1106_, 0);
v_k_1120_ = lean_ctor_get(v_r_1106_, 1);
v_v_1121_ = lean_ctor_get(v_r_1106_, 2);
v_l_1122_ = lean_ctor_get(v_r_1106_, 3);
v_r_1123_ = lean_ctor_get(v_r_1106_, 4);
v___x_1124_ = lean_unsigned_to_nat(2u);
v___x_1125_ = lean_nat_mul(v___x_1124_, v_size_1118_);
v___x_1126_ = lean_nat_dec_lt(v_size_1119_, v___x_1125_);
lean_dec(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1155_; 
lean_inc(v_r_1123_);
lean_inc(v_l_1122_);
lean_inc(v_v_1121_);
lean_inc(v_k_1120_);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; lean_object* v_unused_1159_; lean_object* v_unused_1160_; 
v_unused_1156_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_r_1106_, 2);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_r_1106_, 1);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1160_);
v___x_1128_ = v_r_1106_;
v_isShared_1129_ = v_isSharedCheck_1155_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v_r_1106_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1155_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___x_1143_; lean_object* v___y_1145_; 
v___x_1130_ = lean_nat_add(v___x_1100_, v_size_1102_);
lean_dec(v_size_1102_);
v___x_1131_ = lean_nat_add(v___x_1130_, v_size_1101_);
lean_dec(v___x_1130_);
v___x_1143_ = lean_nat_add(v___x_1100_, v_size_1118_);
if (lean_obj_tag(v_l_1122_) == 0)
{
lean_object* v_size_1153_; 
v_size_1153_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_size_1153_);
v___y_1145_ = v_size_1153_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___y_1145_ = v___x_1154_;
goto v___jp_1144_;
}
v___jp_1132_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_nat_add(v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec(v___y_1134_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v_r_1094_);
lean_ctor_set(v___x_1128_, 3, v_r_1123_);
lean_ctor_set(v___x_1128_, 2, v_v_1092_);
lean_ctor_set(v___x_1128_, 1, v_k_1091_);
lean_ctor_set(v___x_1128_, 0, v___x_1136_);
v___x_1138_ = v___x_1128_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_r_1123_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_r_1094_);
v___x_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v___x_1138_);
lean_ctor_set(v___x_1116_, 3, v___y_1133_);
lean_ctor_set(v___x_1116_, 2, v_v_1121_);
lean_ctor_set(v___x_1116_, 1, v_k_1120_);
lean_ctor_set(v___x_1116_, 0, v___x_1131_);
v___x_1140_ = v___x_1116_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_1120_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v___y_1133_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
v___jp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_nat_add(v___x_1143_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec(v___x_1143_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v_l_1122_);
lean_ctor_set(v___x_1096_, 3, v_l_1105_);
lean_ctor_set(v___x_1096_, 2, v_v_1104_);
lean_ctor_set(v___x_1096_, 1, v_k_1103_);
lean_ctor_set(v___x_1096_, 0, v___x_1146_);
v___x_1148_ = v___x_1096_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_l_1122_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_nat_add(v___x_1100_, v_size_1101_);
if (lean_obj_tag(v_r_1123_) == 0)
{
lean_object* v_size_1150_; 
v_size_1150_ = lean_ctor_get(v_r_1123_, 0);
lean_inc(v_size_1150_);
v___y_1133_ = v___x_1148_;
v___y_1134_ = v___x_1149_;
v___y_1135_ = v_size_1150_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v___y_1133_ = v___x_1148_;
v___y_1134_ = v___x_1149_;
v___y_1135_ = v___x_1151_;
goto v___jp_1132_;
}
}
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_del_object(v___x_1096_);
v___x_1161_ = lean_nat_add(v___x_1100_, v_size_1102_);
lean_dec(v_size_1102_);
v___x_1162_ = lean_nat_add(v___x_1161_, v_size_1101_);
lean_dec(v___x_1161_);
v___x_1163_ = lean_nat_add(v___x_1100_, v_size_1101_);
v___x_1164_ = lean_nat_add(v___x_1163_, v_size_1119_);
lean_dec(v___x_1163_);
lean_inc_ref(v_r_1094_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 4, v_r_1094_);
lean_ctor_set(v___x_1116_, 3, v_r_1106_);
lean_ctor_set(v___x_1116_, 2, v_v_1092_);
lean_ctor_set(v___x_1116_, 1, v_k_1091_);
lean_ctor_set(v___x_1116_, 0, v___x_1164_);
v___x_1166_ = v___x_1116_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_r_1106_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_r_1094_);
v___x_1166_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_isSharedCheck_1173_ = !lean_is_exclusive(v_r_1094_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1174_ = lean_ctor_get(v_r_1094_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_r_1094_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_r_1094_, 2);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_r_1094_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_1094_, 0);
lean_dec(v_unused_1178_);
v___x_1168_ = v_r_1094_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v_r_1094_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 4, v___x_1166_);
lean_ctor_set(v___x_1168_, 3, v_l_1105_);
lean_ctor_set(v___x_1168_, 2, v_v_1104_);
lean_ctor_set(v___x_1168_, 1, v_k_1103_);
lean_ctor_set(v___x_1168_, 0, v___x_1162_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v___x_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1186_; 
v_l_1186_ = lean_ctor_get(v_impl_1099_, 3);
lean_inc(v_l_1186_);
if (lean_obj_tag(v_l_1186_) == 0)
{
lean_object* v_r_1187_; lean_object* v_k_1188_; lean_object* v_v_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1200_; 
v_r_1187_ = lean_ctor_get(v_impl_1099_, 4);
v_k_1188_ = lean_ctor_get(v_impl_1099_, 1);
v_v_1189_ = lean_ctor_get(v_impl_1099_, 2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_impl_1099_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; lean_object* v_unused_1202_; 
v_unused_1201_ = lean_ctor_get(v_impl_1099_, 3);
lean_dec(v_unused_1201_);
v_unused_1202_ = lean_ctor_get(v_impl_1099_, 0);
lean_dec(v_unused_1202_);
v___x_1191_ = v_impl_1099_;
v_isShared_1192_ = v_isSharedCheck_1200_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_r_1187_);
lean_inc(v_v_1189_);
lean_inc(v_k_1188_);
lean_dec(v_impl_1099_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1200_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1187_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 3, v_r_1187_);
lean_ctor_set(v___x_1191_, 2, v_v_1092_);
lean_ctor_set(v___x_1191_, 1, v_k_1091_);
lean_ctor_set(v___x_1191_, 0, v___x_1100_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_r_1187_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v_r_1187_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v___x_1195_);
lean_ctor_set(v___x_1096_, 3, v_l_1186_);
lean_ctor_set(v___x_1096_, 2, v_v_1189_);
lean_ctor_set(v___x_1096_, 1, v_k_1188_);
lean_ctor_set(v___x_1096_, 0, v___x_1193_);
v___x_1197_ = v___x_1096_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_k_1188_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_v_1189_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_l_1186_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_r_1203_; 
v_r_1203_ = lean_ctor_get(v_impl_1099_, 4);
lean_inc(v_r_1203_);
if (lean_obj_tag(v_r_1203_) == 0)
{
lean_object* v_k_1204_; lean_object* v_v_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1228_; 
v_k_1204_ = lean_ctor_get(v_impl_1099_, 1);
v_v_1205_ = lean_ctor_get(v_impl_1099_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_impl_1099_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; lean_object* v_unused_1230_; lean_object* v_unused_1231_; 
v_unused_1229_ = lean_ctor_get(v_impl_1099_, 4);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_impl_1099_, 3);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_impl_1099_, 0);
lean_dec(v_unused_1231_);
v___x_1207_ = v_impl_1099_;
v_isShared_1208_ = v_isSharedCheck_1228_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_v_1205_);
lean_inc(v_k_1204_);
lean_dec(v_impl_1099_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1228_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_k_1209_; lean_object* v_v_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1224_; 
v_k_1209_ = lean_ctor_get(v_r_1203_, 1);
v_v_1210_ = lean_ctor_get(v_r_1203_, 2);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_r_1203_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1225_ = lean_ctor_get(v_r_1203_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_r_1203_, 3);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_r_1203_, 0);
lean_dec(v_unused_1227_);
v___x_1212_ = v_r_1203_;
v_isShared_1213_ = v_isSharedCheck_1224_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_v_1210_);
lean_inc(v_k_1209_);
lean_dec(v_r_1203_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1224_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_unsigned_to_nat(3u);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 4, v_l_1186_);
lean_ctor_set(v___x_1212_, 3, v_l_1186_);
lean_ctor_set(v___x_1212_, 2, v_v_1205_);
lean_ctor_set(v___x_1212_, 1, v_k_1204_);
lean_ctor_set(v___x_1212_, 0, v___x_1100_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1204_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1205_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_l_1186_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_l_1186_);
v___x_1216_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_l_1186_);
lean_ctor_set(v___x_1207_, 2, v_v_1092_);
lean_ctor_set(v___x_1207_, 1, v_k_1091_);
lean_ctor_set(v___x_1207_, 0, v___x_1100_);
v___x_1218_ = v___x_1207_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_l_1186_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_l_1186_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v___x_1218_);
lean_ctor_set(v___x_1096_, 3, v___x_1216_);
lean_ctor_set(v___x_1096_, 2, v_v_1210_);
lean_ctor_set(v___x_1096_, 1, v_k_1209_);
lean_ctor_set(v___x_1096_, 0, v___x_1214_);
v___x_1220_ = v___x_1096_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1209_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_unsigned_to_nat(2u);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v_r_1203_);
lean_ctor_set(v___x_1096_, 3, v_impl_1099_);
lean_ctor_set(v___x_1096_, 0, v___x_1232_);
v___x_1234_ = v___x_1096_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_impl_1099_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_r_1203_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1237_; 
lean_dec(v_v_1092_);
lean_dec(v_k_1091_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 2, v_v_1088_);
lean_ctor_set(v___x_1096_, 1, v_k_1087_);
v___x_1237_ = v___x_1096_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_size_1090_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_l_1093_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v_r_1094_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
default: 
{
lean_object* v_impl_1239_; lean_object* v___x_1240_; 
lean_dec(v_size_1090_);
v_impl_1239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1087_, v_v_1088_, v_r_1094_);
v___x_1240_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1093_) == 0)
{
lean_object* v_size_1241_; lean_object* v_size_1242_; lean_object* v_k_1243_; lean_object* v_v_1244_; lean_object* v_l_1245_; lean_object* v_r_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_size_1241_ = lean_ctor_get(v_l_1093_, 0);
v_size_1242_ = lean_ctor_get(v_impl_1239_, 0);
lean_inc(v_size_1242_);
v_k_1243_ = lean_ctor_get(v_impl_1239_, 1);
lean_inc(v_k_1243_);
v_v_1244_ = lean_ctor_get(v_impl_1239_, 2);
lean_inc(v_v_1244_);
v_l_1245_ = lean_ctor_get(v_impl_1239_, 3);
lean_inc(v_l_1245_);
v_r_1246_ = lean_ctor_get(v_impl_1239_, 4);
lean_inc(v_r_1246_);
v___x_1247_ = lean_unsigned_to_nat(3u);
v___x_1248_ = lean_nat_mul(v___x_1247_, v_size_1241_);
v___x_1249_ = lean_nat_dec_lt(v___x_1248_, v_size_1242_);
lean_dec(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_dec(v_r_1246_);
lean_dec(v_l_1245_);
lean_dec(v_v_1244_);
lean_dec(v_k_1243_);
v___x_1250_ = lean_nat_add(v___x_1240_, v_size_1241_);
v___x_1251_ = lean_nat_add(v___x_1250_, v_size_1242_);
lean_dec(v_size_1242_);
lean_dec(v___x_1250_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v_impl_1239_);
lean_ctor_set(v___x_1096_, 0, v___x_1251_);
v___x_1253_ = v___x_1096_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_l_1093_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_impl_1239_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v_impl_1239_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; lean_object* v_unused_1322_; lean_object* v_unused_1323_; 
v_unused_1319_ = lean_ctor_get(v_impl_1239_, 4);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_impl_1239_, 3);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_impl_1239_, 2);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v_impl_1239_, 1);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_impl_1239_, 0);
lean_dec(v_unused_1323_);
v___x_1256_ = v_impl_1239_;
v_isShared_1257_ = v_isSharedCheck_1318_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v_impl_1239_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1318_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_size_1258_; lean_object* v_k_1259_; lean_object* v_v_1260_; lean_object* v_l_1261_; lean_object* v_r_1262_; lean_object* v_size_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_size_1258_ = lean_ctor_get(v_l_1245_, 0);
v_k_1259_ = lean_ctor_get(v_l_1245_, 1);
v_v_1260_ = lean_ctor_get(v_l_1245_, 2);
v_l_1261_ = lean_ctor_get(v_l_1245_, 3);
v_r_1262_ = lean_ctor_get(v_l_1245_, 4);
v_size_1263_ = lean_ctor_get(v_r_1246_, 0);
v___x_1264_ = lean_unsigned_to_nat(2u);
v___x_1265_ = lean_nat_mul(v___x_1264_, v_size_1263_);
v___x_1266_ = lean_nat_dec_lt(v_size_1258_, v___x_1265_);
lean_dec(v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1294_; 
lean_inc(v_r_1262_);
lean_inc(v_l_1261_);
lean_inc(v_v_1260_);
lean_inc(v_k_1259_);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_l_1245_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; lean_object* v_unused_1296_; lean_object* v_unused_1297_; lean_object* v_unused_1298_; lean_object* v_unused_1299_; 
v_unused_1295_ = lean_ctor_get(v_l_1245_, 4);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_l_1245_, 3);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_l_1245_, 2);
lean_dec(v_unused_1297_);
v_unused_1298_ = lean_ctor_get(v_l_1245_, 1);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_l_1245_, 0);
lean_dec(v_unused_1299_);
v___x_1268_ = v_l_1245_;
v_isShared_1269_ = v_isSharedCheck_1294_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v_l_1245_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1294_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1284_; 
v___x_1270_ = lean_nat_add(v___x_1240_, v_size_1241_);
v___x_1271_ = lean_nat_add(v___x_1270_, v_size_1242_);
lean_dec(v_size_1242_);
if (lean_obj_tag(v_l_1261_) == 0)
{
lean_object* v_size_1292_; 
v_size_1292_ = lean_ctor_get(v_l_1261_, 0);
lean_inc(v_size_1292_);
v___y_1284_ = v_size_1292_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___y_1284_ = v___x_1293_;
goto v___jp_1283_;
}
v___jp_1272_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_nat_add(v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_r_1246_);
lean_ctor_set(v___x_1268_, 3, v_r_1262_);
lean_ctor_set(v___x_1268_, 2, v_v_1244_);
lean_ctor_set(v___x_1268_, 1, v_k_1243_);
lean_ctor_set(v___x_1268_, 0, v___x_1276_);
v___x_1278_ = v___x_1268_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_r_1262_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_r_1246_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1278_);
lean_ctor_set(v___x_1256_, 3, v___y_1273_);
lean_ctor_set(v___x_1256_, 2, v_v_1260_);
lean_ctor_set(v___x_1256_, 1, v_k_1259_);
lean_ctor_set(v___x_1256_, 0, v___x_1271_);
v___x_1280_ = v___x_1256_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_k_1259_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_v_1260_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v___y_1273_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_nat_add(v___x_1270_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec(v___x_1270_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v_l_1261_);
lean_ctor_set(v___x_1096_, 0, v___x_1285_);
v___x_1287_ = v___x_1096_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_l_1093_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_l_1261_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_nat_add(v___x_1240_, v_size_1263_);
if (lean_obj_tag(v_r_1262_) == 0)
{
lean_object* v_size_1289_; 
v_size_1289_ = lean_ctor_get(v_r_1262_, 0);
lean_inc(v_size_1289_);
v___y_1273_ = v___x_1287_;
v___y_1274_ = v___x_1288_;
v___y_1275_ = v_size_1289_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___y_1273_ = v___x_1287_;
v___y_1274_ = v___x_1288_;
v___y_1275_ = v___x_1290_;
goto v___jp_1272_;
}
}
}
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_del_object(v___x_1096_);
v___x_1300_ = lean_nat_add(v___x_1240_, v_size_1241_);
v___x_1301_ = lean_nat_add(v___x_1300_, v_size_1242_);
lean_dec(v_size_1242_);
v___x_1302_ = lean_nat_add(v___x_1300_, v_size_1258_);
lean_dec(v___x_1300_);
lean_inc_ref(v_l_1093_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v_l_1245_);
lean_ctor_set(v___x_1256_, 3, v_l_1093_);
lean_ctor_set(v___x_1256_, 2, v_v_1092_);
lean_ctor_set(v___x_1256_, 1, v_k_1091_);
lean_ctor_set(v___x_1256_, 0, v___x_1302_);
v___x_1304_ = v___x_1256_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_l_1093_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_l_1245_);
v___x_1304_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_isSharedCheck_1311_ = !lean_is_exclusive(v_l_1093_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; lean_object* v_unused_1316_; 
v_unused_1312_ = lean_ctor_get(v_l_1093_, 4);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_l_1093_, 3);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_l_1093_, 2);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_l_1093_, 1);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_l_1093_, 0);
lean_dec(v_unused_1316_);
v___x_1306_ = v_l_1093_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v_l_1093_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 4, v_r_1246_);
lean_ctor_set(v___x_1306_, 3, v___x_1304_);
lean_ctor_set(v___x_1306_, 2, v_v_1244_);
lean_ctor_set(v___x_1306_, 1, v_k_1243_);
lean_ctor_set(v___x_1306_, 0, v___x_1301_);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_r_1246_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1324_; 
v_l_1324_ = lean_ctor_get(v_impl_1239_, 3);
lean_inc(v_l_1324_);
if (lean_obj_tag(v_l_1324_) == 0)
{
lean_object* v_r_1325_; lean_object* v_k_1326_; lean_object* v_v_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1350_; 
v_r_1325_ = lean_ctor_get(v_impl_1239_, 4);
v_k_1326_ = lean_ctor_get(v_impl_1239_, 1);
v_v_1327_ = lean_ctor_get(v_impl_1239_, 2);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_impl_1239_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v_impl_1239_, 3);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_impl_1239_, 0);
lean_dec(v_unused_1352_);
v___x_1329_ = v_impl_1239_;
v_isShared_1330_ = v_isSharedCheck_1350_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_r_1325_);
lean_inc(v_v_1327_);
lean_inc(v_k_1326_);
lean_dec(v_impl_1239_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1350_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_k_1331_; lean_object* v_v_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1346_; 
v_k_1331_ = lean_ctor_get(v_l_1324_, 1);
v_v_1332_ = lean_ctor_get(v_l_1324_, 2);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_l_1324_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; 
v_unused_1347_ = lean_ctor_get(v_l_1324_, 4);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_l_1324_, 3);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_l_1324_, 0);
lean_dec(v_unused_1349_);
v___x_1334_ = v_l_1324_;
v_isShared_1335_ = v_isSharedCheck_1346_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_v_1332_);
lean_inc(v_k_1331_);
lean_dec(v_l_1324_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1346_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1325_, 2);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 4, v_r_1325_);
lean_ctor_set(v___x_1334_, 3, v_r_1325_);
lean_ctor_set(v___x_1334_, 2, v_v_1092_);
lean_ctor_set(v___x_1334_, 1, v_k_1091_);
lean_ctor_set(v___x_1334_, 0, v___x_1240_);
v___x_1338_ = v___x_1334_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_r_1325_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_r_1325_);
v___x_1338_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
lean_inc(v_r_1325_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 3, v_r_1325_);
lean_ctor_set(v___x_1329_, 0, v___x_1240_);
v___x_1340_ = v___x_1329_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_k_1326_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_v_1327_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_r_1325_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_r_1325_);
v___x_1340_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v___x_1340_);
lean_ctor_set(v___x_1096_, 3, v___x_1338_);
lean_ctor_set(v___x_1096_, 2, v_v_1332_);
lean_ctor_set(v___x_1096_, 1, v_k_1331_);
lean_ctor_set(v___x_1096_, 0, v___x_1336_);
v___x_1342_ = v___x_1096_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1331_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1332_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
else
{
lean_object* v_r_1353_; 
v_r_1353_ = lean_ctor_get(v_impl_1239_, 4);
lean_inc(v_r_1353_);
if (lean_obj_tag(v_r_1353_) == 0)
{
lean_object* v_k_1354_; lean_object* v_v_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1366_; 
v_k_1354_ = lean_ctor_get(v_impl_1239_, 1);
v_v_1355_ = lean_ctor_get(v_impl_1239_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_impl_1239_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1367_ = lean_ctor_get(v_impl_1239_, 4);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_impl_1239_, 3);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_impl_1239_, 0);
lean_dec(v_unused_1369_);
v___x_1357_ = v_impl_1239_;
v_isShared_1358_ = v_isSharedCheck_1366_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_v_1355_);
lean_inc(v_k_1354_);
lean_dec(v_impl_1239_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1366_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(3u);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_l_1324_);
lean_ctor_set(v___x_1357_, 2, v_v_1092_);
lean_ctor_set(v___x_1357_, 1, v_k_1091_);
lean_ctor_set(v___x_1357_, 0, v___x_1240_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_l_1324_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_l_1324_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v_r_1353_);
lean_ctor_set(v___x_1096_, 3, v___x_1361_);
lean_ctor_set(v___x_1096_, 2, v_v_1355_);
lean_ctor_set(v___x_1096_, 1, v_k_1354_);
lean_ctor_set(v___x_1096_, 0, v___x_1359_);
v___x_1363_ = v___x_1096_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_k_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_v_1355_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_r_1353_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_unsigned_to_nat(2u);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 4, v_impl_1239_);
lean_ctor_set(v___x_1096_, 3, v_r_1353_);
lean_ctor_set(v___x_1096_, 0, v___x_1370_);
v___x_1372_ = v___x_1096_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_r_1353_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_impl_1239_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
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
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v_k_1087_);
lean_ctor_set(v___x_1376_, 2, v_v_1088_);
lean_ctor_set(v___x_1376_, 3, v_t_1089_);
lean_ctor_set(v___x_1376_, 4, v_t_1089_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1377_, lean_object* v_mvarId_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1378_, v_s_1377_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1378_, v___x_1380_, v_s_1377_);
return v___x_1381_;
}
else
{
lean_dec(v_mvarId_1378_);
return v_s_1377_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1382_, lean_object* v_k_1383_, lean_object* v_t_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1383_, v_t_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1386_, lean_object* v_k_1387_, lean_object* v_t_1388_){
_start:
{
uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_res_1389_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1386_, v_k_1387_, v_t_1388_);
lean_dec(v_t_1388_);
lean_dec(v_k_1387_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1391_, lean_object* v_k_1392_, lean_object* v_v_1393_, lean_object* v_t_1394_, lean_object* v_hl_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1392_, v_v_1393_, v_t_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1397_){
_start:
{
lean_object* v___f_1398_; lean_object* v___x_1399_; 
v___f_1398_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1399_ = l_Std_TreeSet_ofList___redArg(v_l_1397_, v___f_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_MVarIdSet_ofList(v_l_1400_);
lean_dec(v_l_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1402_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; 
v___f_1403_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1404_ = l_Std_TreeSet_ofArray___redArg(v_l_1402_, v___f_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_MVarIdSet_ofArray(v_l_1405_);
lean_dec_ref(v_l_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1407_, lean_object* v_m_1408_, lean_object* v_init_1409_, lean_object* v_f_1410_){
_start:
{
lean_object* v_toApplicative_1411_; lean_object* v_toBind_1412_; lean_object* v_toPure_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; 
v_toApplicative_1411_ = lean_ctor_get(v_inst_1407_, 0);
v_toBind_1412_ = lean_ctor_get(v_inst_1407_, 1);
lean_inc(v_toBind_1412_);
v_toPure_1413_ = lean_ctor_get(v_toApplicative_1411_, 1);
lean_inc(v_toPure_1413_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1414_, 0, v_f_1410_);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1407_, v___f_1414_, v_init_1409_, v_m_1408_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1416_, 0, v_toPure_1413_);
v___x_1417_ = lean_apply_4(v_toBind_1412_, lean_box(0), lean_box(0), v___x_1415_, v___f_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1418_, lean_object* v_inst_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_m_1421_, lean_object* v_init_1422_, lean_object* v_f_1423_){
_start:
{
lean_object* v_toApplicative_1424_; lean_object* v_toBind_1425_; lean_object* v_toPure_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; 
v_toApplicative_1424_ = lean_ctor_get(v_inst_1419_, 0);
v_toBind_1425_ = lean_ctor_get(v_inst_1419_, 1);
lean_inc(v_toBind_1425_);
v_toPure_1426_ = lean_ctor_get(v_toApplicative_1424_, 1);
lean_inc(v_toPure_1426_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1427_, 0, v_f_1423_);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1419_, v___f_1427_, v_init_1422_, v_m_1421_);
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1429_, 0, v_toPure_1426_);
v___x_1430_ = lean_apply_4(v_toBind_1425_, lean_box(0), lean_box(0), v___x_1428_, v___f_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1432_, 0, lean_box(0));
lean_closure_set(v___x_1432_, 1, v_inst_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1433_, lean_object* v_inst_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1435_, 0, lean_box(0));
lean_closure_set(v___x_1435_, 1, v_inst_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1436_, lean_object* v_mvarId_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1437_, v_a_1438_, v_s_1436_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1440_, lean_object* v_s_1441_, lean_object* v_mvarId_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1442_, v_a_1443_, v_s_1441_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_box(1);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_box(1);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1449_, lean_object* v_a_1450_, lean_object* v_b_1451_, lean_object* v_c_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1450_);
lean_ctor_set(v___x_1453_, 1, v_b_1451_);
v___x_1454_ = lean_apply_2(v_f_1449_, v___x_1453_, v_c_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1455_, lean_object* v_m_1456_, lean_object* v_init_1457_, lean_object* v_f_1458_){
_start:
{
lean_object* v_toApplicative_1459_; lean_object* v_toBind_1460_; lean_object* v_toPure_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; 
v_toApplicative_1459_ = lean_ctor_get(v_inst_1455_, 0);
v_toBind_1460_ = lean_ctor_get(v_inst_1455_, 1);
lean_inc(v_toBind_1460_);
v_toPure_1461_ = lean_ctor_get(v_toApplicative_1459_, 1);
lean_inc(v_toPure_1461_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1462_, 0, v_f_1458_);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1455_, v___f_1462_, v_init_1457_, v_m_1456_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1464_, 0, v_toPure_1461_);
v___x_1465_ = lean_apply_4(v_toBind_1460_, lean_box(0), lean_box(0), v___x_1463_, v___f_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1466_, lean_object* v_00_u03b1_1467_, lean_object* v_inst_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_m_1470_, lean_object* v_init_1471_, lean_object* v_f_1472_){
_start:
{
lean_object* v_toApplicative_1473_; lean_object* v_toBind_1474_; lean_object* v_toPure_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; 
v_toApplicative_1473_ = lean_ctor_get(v_inst_1468_, 0);
v_toBind_1474_ = lean_ctor_get(v_inst_1468_, 1);
lean_inc(v_toBind_1474_);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1473_, 1);
lean_inc(v_toPure_1475_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1476_, 0, v_f_1472_);
v___x_1477_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1468_, v___f_1476_, v_init_1471_, v_m_1470_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1478_, 0, v_toPure_1475_);
v___x_1479_ = lean_apply_4(v_toBind_1474_, lean_box(0), lean_box(0), v___x_1477_, v___f_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1481_, 0, lean_box(0));
lean_closure_set(v___x_1481_, 1, lean_box(0));
lean_closure_set(v___x_1481_, 2, v_inst_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1482_, lean_object* v_00_u03b1_1483_, lean_object* v_inst_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1485_, 0, lean_box(0));
lean_closure_set(v___x_1485_, 1, lean_box(0));
lean_closure_set(v___x_1485_, 2, v_inst_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_box(1);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1488_){
_start:
{
switch(lean_obj_tag(v_x_1488_))
{
case 0:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
return v___x_1489_;
}
case 1:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
return v___x_1490_;
}
case 2:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(2u);
return v___x_1491_;
}
case 3:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_unsigned_to_nat(3u);
return v___x_1492_;
}
case 4:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(4u);
return v___x_1493_;
}
case 5:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(5u);
return v___x_1494_;
}
case 6:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_unsigned_to_nat(6u);
return v___x_1495_;
}
case 7:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(7u);
return v___x_1496_;
}
case 8:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(8u);
return v___x_1497_;
}
case 9:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(9u);
return v___x_1498_;
}
case 10:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(10u);
return v___x_1499_;
}
default: 
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(11u);
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Expr_ctorIdx(v_x_1501_);
lean_dec_ref(v_x_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1503_, lean_object* v_k_1504_){
_start:
{
switch(lean_obj_tag(v_t_1503_))
{
case 4:
{
lean_object* v_declName_1505_; lean_object* v_us_1506_; lean_object* v___x_1507_; 
v_declName_1505_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_declName_1505_);
v_us_1506_ = lean_ctor_get(v_t_1503_, 1);
lean_inc(v_us_1506_);
lean_dec_ref_known(v_t_1503_, 2);
v___x_1507_ = lean_apply_2(v_k_1504_, v_declName_1505_, v_us_1506_);
return v___x_1507_;
}
case 5:
{
lean_object* v_fn_1508_; lean_object* v_arg_1509_; lean_object* v___x_1510_; 
v_fn_1508_ = lean_ctor_get(v_t_1503_, 0);
lean_inc_ref(v_fn_1508_);
v_arg_1509_ = lean_ctor_get(v_t_1503_, 1);
lean_inc_ref(v_arg_1509_);
lean_dec_ref_known(v_t_1503_, 2);
v___x_1510_ = lean_apply_2(v_k_1504_, v_fn_1508_, v_arg_1509_);
return v___x_1510_;
}
case 6:
{
lean_object* v_binderName_1511_; lean_object* v_binderType_1512_; lean_object* v_body_1513_; uint8_t v_binderInfo_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_binderName_1511_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_binderName_1511_);
v_binderType_1512_ = lean_ctor_get(v_t_1503_, 1);
lean_inc_ref(v_binderType_1512_);
v_body_1513_ = lean_ctor_get(v_t_1503_, 2);
lean_inc_ref(v_body_1513_);
v_binderInfo_1514_ = lean_ctor_get_uint8(v_t_1503_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1503_, 3);
v___x_1515_ = lean_box(v_binderInfo_1514_);
v___x_1516_ = lean_apply_4(v_k_1504_, v_binderName_1511_, v_binderType_1512_, v_body_1513_, v___x_1515_);
return v___x_1516_;
}
case 7:
{
lean_object* v_binderName_1517_; lean_object* v_binderType_1518_; lean_object* v_body_1519_; uint8_t v_binderInfo_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_binderName_1517_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_binderName_1517_);
v_binderType_1518_ = lean_ctor_get(v_t_1503_, 1);
lean_inc_ref(v_binderType_1518_);
v_body_1519_ = lean_ctor_get(v_t_1503_, 2);
lean_inc_ref(v_body_1519_);
v_binderInfo_1520_ = lean_ctor_get_uint8(v_t_1503_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1503_, 3);
v___x_1521_ = lean_box(v_binderInfo_1520_);
v___x_1522_ = lean_apply_4(v_k_1504_, v_binderName_1517_, v_binderType_1518_, v_body_1519_, v___x_1521_);
return v___x_1522_;
}
case 8:
{
lean_object* v_declName_1523_; lean_object* v_type_1524_; lean_object* v_value_1525_; lean_object* v_body_1526_; uint8_t v_nondep_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_declName_1523_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_declName_1523_);
v_type_1524_ = lean_ctor_get(v_t_1503_, 1);
lean_inc_ref(v_type_1524_);
v_value_1525_ = lean_ctor_get(v_t_1503_, 2);
lean_inc_ref(v_value_1525_);
v_body_1526_ = lean_ctor_get(v_t_1503_, 3);
lean_inc_ref(v_body_1526_);
v_nondep_1527_ = lean_ctor_get_uint8(v_t_1503_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1503_, 4);
v___x_1528_ = lean_box(v_nondep_1527_);
v___x_1529_ = lean_apply_5(v_k_1504_, v_declName_1523_, v_type_1524_, v_value_1525_, v_body_1526_, v___x_1528_);
return v___x_1529_;
}
case 9:
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v_t_1503_, 0);
lean_inc_ref(v_a_1530_);
lean_dec_ref_known(v_t_1503_, 1);
v___x_1531_ = lean_apply_1(v_k_1504_, v_a_1530_);
return v___x_1531_;
}
case 10:
{
lean_object* v_data_1532_; lean_object* v_expr_1533_; lean_object* v___x_1534_; 
v_data_1532_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_data_1532_);
v_expr_1533_ = lean_ctor_get(v_t_1503_, 1);
lean_inc_ref(v_expr_1533_);
lean_dec_ref_known(v_t_1503_, 2);
v___x_1534_ = lean_apply_2(v_k_1504_, v_data_1532_, v_expr_1533_);
return v___x_1534_;
}
case 11:
{
lean_object* v_typeName_1535_; lean_object* v_idx_1536_; lean_object* v_struct_1537_; lean_object* v___x_1538_; 
v_typeName_1535_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_typeName_1535_);
v_idx_1536_ = lean_ctor_get(v_t_1503_, 1);
lean_inc(v_idx_1536_);
v_struct_1537_ = lean_ctor_get(v_t_1503_, 2);
lean_inc_ref(v_struct_1537_);
lean_dec_ref_known(v_t_1503_, 3);
v___x_1538_ = lean_apply_3(v_k_1504_, v_typeName_1535_, v_idx_1536_, v_struct_1537_);
return v___x_1538_;
}
default: 
{
lean_object* v_deBruijnIndex_1539_; lean_object* v___x_1540_; 
v_deBruijnIndex_1539_ = lean_ctor_get(v_t_1503_, 0);
lean_inc(v_deBruijnIndex_1539_);
lean_dec_ref(v_t_1503_);
v___x_1540_ = lean_apply_1(v_k_1504_, v_deBruijnIndex_1539_);
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1541_, lean_object* v_ctorIdx_1542_, lean_object* v_t_1543_, lean_object* v_h_1544_, lean_object* v_k_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Expr_ctorElim___redArg(v_t_1543_, v_k_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1547_, lean_object* v_ctorIdx_1548_, lean_object* v_t_1549_, lean_object* v_h_1550_, lean_object* v_k_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Expr_ctorElim(v_motive_1547_, v_ctorIdx_1548_, v_t_1549_, v_h_1550_, v_k_1551_);
lean_dec(v_ctorIdx_1548_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1553_, lean_object* v_bvar_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Expr_ctorElim___redArg(v_t_1553_, v_bvar_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1556_, lean_object* v_t_1557_, lean_object* v_h_1558_, lean_object* v_bvar_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Expr_ctorElim___redArg(v_t_1557_, v_bvar_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1561_, lean_object* v_fvar_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Expr_ctorElim___redArg(v_t_1561_, v_fvar_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1564_, lean_object* v_t_1565_, lean_object* v_h_1566_, lean_object* v_fvar_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Expr_ctorElim___redArg(v_t_1565_, v_fvar_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1569_, lean_object* v_mvar_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Expr_ctorElim___redArg(v_t_1569_, v_mvar_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1572_, lean_object* v_t_1573_, lean_object* v_h_1574_, lean_object* v_mvar_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Expr_ctorElim___redArg(v_t_1573_, v_mvar_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1577_, lean_object* v_sort_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Expr_ctorElim___redArg(v_t_1577_, v_sort_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1580_, lean_object* v_t_1581_, lean_object* v_h_1582_, lean_object* v_sort_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Expr_ctorElim___redArg(v_t_1581_, v_sort_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1585_, lean_object* v_const_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Expr_ctorElim___redArg(v_t_1585_, v_const_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1588_, lean_object* v_t_1589_, lean_object* v_h_1590_, lean_object* v_const_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Expr_ctorElim___redArg(v_t_1589_, v_const_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1593_, lean_object* v_app_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Expr_ctorElim___redArg(v_t_1593_, v_app_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1596_, lean_object* v_t_1597_, lean_object* v_h_1598_, lean_object* v_app_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Expr_ctorElim___redArg(v_t_1597_, v_app_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1601_, lean_object* v_lam_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Expr_ctorElim___redArg(v_t_1601_, v_lam_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1604_, lean_object* v_t_1605_, lean_object* v_h_1606_, lean_object* v_lam_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Expr_ctorElim___redArg(v_t_1605_, v_lam_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1609_, lean_object* v_forallE_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Expr_ctorElim___redArg(v_t_1609_, v_forallE_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1612_, lean_object* v_t_1613_, lean_object* v_h_1614_, lean_object* v_forallE_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Expr_ctorElim___redArg(v_t_1613_, v_forallE_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1617_, lean_object* v_letE_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Expr_ctorElim___redArg(v_t_1617_, v_letE_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1620_, lean_object* v_t_1621_, lean_object* v_h_1622_, lean_object* v_letE_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Expr_ctorElim___redArg(v_t_1621_, v_letE_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1625_, lean_object* v_lit_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Expr_ctorElim___redArg(v_t_1625_, v_lit_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1628_, lean_object* v_t_1629_, lean_object* v_h_1630_, lean_object* v_lit_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Expr_ctorElim___redArg(v_t_1629_, v_lit_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1633_, lean_object* v_mdata_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Expr_ctorElim___redArg(v_t_1633_, v_mdata_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1636_, lean_object* v_t_1637_, lean_object* v_h_1638_, lean_object* v_mdata_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Expr_ctorElim___redArg(v_t_1637_, v_mdata_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1641_, lean_object* v_proj_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Expr_ctorElim___redArg(v_t_1641_, v_proj_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1644_, lean_object* v_t_1645_, lean_object* v_h_1646_, lean_object* v_proj_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Expr_ctorElim___redArg(v_t_1645_, v_proj_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1650_){
_start:
{
uint64_t v_res_1651_; lean_object* v_r_1652_; 
v_res_1651_ = lean_expr_data(v_a_00___x40___internal___hyg_1650_);
lean_dec_ref(v_a_00___x40___internal___hyg_1650_);
v_r_1652_ = lean_box_uint64(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1653_, lean_object* v_bvar_1654_, lean_object* v_fvar_1655_, lean_object* v_mvar_1656_, lean_object* v_sort_1657_, lean_object* v_const_1658_, lean_object* v_app_1659_, lean_object* v_lam_1660_, lean_object* v_forallE_1661_, lean_object* v_letE_1662_, lean_object* v_lit_1663_, lean_object* v_mdata_1664_, lean_object* v_proj_1665_){
_start:
{
switch(lean_obj_tag(v_t_1653_))
{
case 0:
{
lean_object* v_deBruijnIndex_1666_; lean_object* v___x_1667_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
v_deBruijnIndex_1666_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_deBruijnIndex_1666_);
lean_dec_ref_known(v_t_1653_, 1);
v___x_1667_ = lean_apply_1(v_bvar_1654_, v_deBruijnIndex_1666_);
return v___x_1667_;
}
case 1:
{
lean_object* v_fvarId_1668_; lean_object* v___x_1669_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_bvar_1654_);
v_fvarId_1668_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_fvarId_1668_);
lean_dec_ref_known(v_t_1653_, 1);
v___x_1669_ = lean_apply_1(v_fvar_1655_, v_fvarId_1668_);
return v___x_1669_;
}
case 2:
{
lean_object* v_mvarId_1670_; lean_object* v___x_1671_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_mvarId_1670_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_mvarId_1670_);
lean_dec_ref_known(v_t_1653_, 1);
v___x_1671_ = lean_apply_1(v_mvar_1656_, v_mvarId_1670_);
return v___x_1671_;
}
case 3:
{
lean_object* v_u_1672_; lean_object* v___x_1673_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_u_1672_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_u_1672_);
lean_dec_ref_known(v_t_1653_, 1);
v___x_1673_ = lean_apply_1(v_sort_1657_, v_u_1672_);
return v___x_1673_;
}
case 4:
{
lean_object* v_declName_1674_; lean_object* v_us_1675_; lean_object* v___x_1676_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_declName_1674_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_declName_1674_);
v_us_1675_ = lean_ctor_get(v_t_1653_, 1);
lean_inc(v_us_1675_);
lean_dec_ref_known(v_t_1653_, 2);
v___x_1676_ = lean_apply_2(v_const_1658_, v_declName_1674_, v_us_1675_);
return v___x_1676_;
}
case 5:
{
lean_object* v_fn_1677_; lean_object* v_arg_1678_; lean_object* v___x_1679_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_fn_1677_ = lean_ctor_get(v_t_1653_, 0);
lean_inc_ref(v_fn_1677_);
v_arg_1678_ = lean_ctor_get(v_t_1653_, 1);
lean_inc_ref(v_arg_1678_);
lean_dec_ref_known(v_t_1653_, 2);
v___x_1679_ = lean_apply_2(v_app_1659_, v_fn_1677_, v_arg_1678_);
return v___x_1679_;
}
case 6:
{
lean_object* v_binderName_1680_; lean_object* v_binderType_1681_; lean_object* v_body_1682_; uint8_t v_binderInfo_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_binderName_1680_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_binderName_1680_);
v_binderType_1681_ = lean_ctor_get(v_t_1653_, 1);
lean_inc_ref(v_binderType_1681_);
v_body_1682_ = lean_ctor_get(v_t_1653_, 2);
lean_inc_ref(v_body_1682_);
v_binderInfo_1683_ = lean_ctor_get_uint8(v_t_1653_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1653_, 3);
v___x_1684_ = lean_box(v_binderInfo_1683_);
v___x_1685_ = lean_apply_4(v_lam_1660_, v_binderName_1680_, v_binderType_1681_, v_body_1682_, v___x_1684_);
return v___x_1685_;
}
case 7:
{
lean_object* v_binderName_1686_; lean_object* v_binderType_1687_; lean_object* v_body_1688_; uint8_t v_binderInfo_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_binderName_1686_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_binderName_1686_);
v_binderType_1687_ = lean_ctor_get(v_t_1653_, 1);
lean_inc_ref(v_binderType_1687_);
v_body_1688_ = lean_ctor_get(v_t_1653_, 2);
lean_inc_ref(v_body_1688_);
v_binderInfo_1689_ = lean_ctor_get_uint8(v_t_1653_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1653_, 3);
v___x_1690_ = lean_box(v_binderInfo_1689_);
v___x_1691_ = lean_apply_4(v_forallE_1661_, v_binderName_1686_, v_binderType_1687_, v_body_1688_, v___x_1690_);
return v___x_1691_;
}
case 8:
{
lean_object* v_declName_1692_; lean_object* v_type_1693_; lean_object* v_value_1694_; lean_object* v_body_1695_; uint8_t v_nondep_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_declName_1692_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_declName_1692_);
v_type_1693_ = lean_ctor_get(v_t_1653_, 1);
lean_inc_ref(v_type_1693_);
v_value_1694_ = lean_ctor_get(v_t_1653_, 2);
lean_inc_ref(v_value_1694_);
v_body_1695_ = lean_ctor_get(v_t_1653_, 3);
lean_inc_ref(v_body_1695_);
v_nondep_1696_ = lean_ctor_get_uint8(v_t_1653_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1653_, 4);
v___x_1697_ = lean_box(v_nondep_1696_);
v___x_1698_ = lean_apply_5(v_letE_1662_, v_declName_1692_, v_type_1693_, v_value_1694_, v_body_1695_, v___x_1697_);
return v___x_1698_;
}
case 9:
{
lean_object* v_a_1699_; lean_object* v___x_1700_; 
lean_dec(v_proj_1665_);
lean_dec(v_mdata_1664_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_a_1699_ = lean_ctor_get(v_t_1653_, 0);
lean_inc_ref(v_a_1699_);
lean_dec_ref_known(v_t_1653_, 1);
v___x_1700_ = lean_apply_1(v_lit_1663_, v_a_1699_);
return v___x_1700_;
}
case 10:
{
lean_object* v_data_1701_; lean_object* v_expr_1702_; lean_object* v___x_1703_; 
lean_dec(v_proj_1665_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_data_1701_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_data_1701_);
v_expr_1702_ = lean_ctor_get(v_t_1653_, 1);
lean_inc_ref(v_expr_1702_);
lean_dec_ref_known(v_t_1653_, 2);
v___x_1703_ = lean_apply_2(v_mdata_1664_, v_data_1701_, v_expr_1702_);
return v___x_1703_;
}
default: 
{
lean_object* v_typeName_1704_; lean_object* v_idx_1705_; lean_object* v_struct_1706_; lean_object* v___x_1707_; 
lean_dec(v_mdata_1664_);
lean_dec(v_lit_1663_);
lean_dec(v_letE_1662_);
lean_dec(v_forallE_1661_);
lean_dec(v_lam_1660_);
lean_dec(v_app_1659_);
lean_dec(v_const_1658_);
lean_dec(v_sort_1657_);
lean_dec(v_mvar_1656_);
lean_dec(v_fvar_1655_);
lean_dec(v_bvar_1654_);
v_typeName_1704_ = lean_ctor_get(v_t_1653_, 0);
lean_inc(v_typeName_1704_);
v_idx_1705_ = lean_ctor_get(v_t_1653_, 1);
lean_inc(v_idx_1705_);
v_struct_1706_ = lean_ctor_get(v_t_1653_, 2);
lean_inc_ref(v_struct_1706_);
lean_dec_ref_known(v_t_1653_, 3);
v___x_1707_ = lean_apply_3(v_proj_1665_, v_typeName_1704_, v_idx_1705_, v_struct_1706_);
return v___x_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1708_, lean_object* v_t_1709_, lean_object* v_bvar_1710_, lean_object* v_fvar_1711_, lean_object* v_mvar_1712_, lean_object* v_sort_1713_, lean_object* v_const_1714_, lean_object* v_app_1715_, lean_object* v_lam_1716_, lean_object* v_forallE_1717_, lean_object* v_letE_1718_, lean_object* v_lit_1719_, lean_object* v_mdata_1720_, lean_object* v_proj_1721_){
_start:
{
switch(lean_obj_tag(v_t_1709_))
{
case 0:
{
lean_object* v_deBruijnIndex_1722_; lean_object* v___x_1723_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
v_deBruijnIndex_1722_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_deBruijnIndex_1722_);
lean_dec_ref_known(v_t_1709_, 1);
v___x_1723_ = lean_apply_1(v_bvar_1710_, v_deBruijnIndex_1722_);
return v___x_1723_;
}
case 1:
{
lean_object* v_fvarId_1724_; lean_object* v___x_1725_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_bvar_1710_);
v_fvarId_1724_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_fvarId_1724_);
lean_dec_ref_known(v_t_1709_, 1);
v___x_1725_ = lean_apply_1(v_fvar_1711_, v_fvarId_1724_);
return v___x_1725_;
}
case 2:
{
lean_object* v_mvarId_1726_; lean_object* v___x_1727_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_mvarId_1726_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_mvarId_1726_);
lean_dec_ref_known(v_t_1709_, 1);
v___x_1727_ = lean_apply_1(v_mvar_1712_, v_mvarId_1726_);
return v___x_1727_;
}
case 3:
{
lean_object* v_u_1728_; lean_object* v___x_1729_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_u_1728_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_u_1728_);
lean_dec_ref_known(v_t_1709_, 1);
v___x_1729_ = lean_apply_1(v_sort_1713_, v_u_1728_);
return v___x_1729_;
}
case 4:
{
lean_object* v_declName_1730_; lean_object* v_us_1731_; lean_object* v___x_1732_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_declName_1730_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_declName_1730_);
v_us_1731_ = lean_ctor_get(v_t_1709_, 1);
lean_inc(v_us_1731_);
lean_dec_ref_known(v_t_1709_, 2);
v___x_1732_ = lean_apply_2(v_const_1714_, v_declName_1730_, v_us_1731_);
return v___x_1732_;
}
case 5:
{
lean_object* v_fn_1733_; lean_object* v_arg_1734_; lean_object* v___x_1735_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_fn_1733_ = lean_ctor_get(v_t_1709_, 0);
lean_inc_ref(v_fn_1733_);
v_arg_1734_ = lean_ctor_get(v_t_1709_, 1);
lean_inc_ref(v_arg_1734_);
lean_dec_ref_known(v_t_1709_, 2);
v___x_1735_ = lean_apply_2(v_app_1715_, v_fn_1733_, v_arg_1734_);
return v___x_1735_;
}
case 6:
{
lean_object* v_binderName_1736_; lean_object* v_binderType_1737_; lean_object* v_body_1738_; uint8_t v_binderInfo_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_binderName_1736_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_binderName_1736_);
v_binderType_1737_ = lean_ctor_get(v_t_1709_, 1);
lean_inc_ref(v_binderType_1737_);
v_body_1738_ = lean_ctor_get(v_t_1709_, 2);
lean_inc_ref(v_body_1738_);
v_binderInfo_1739_ = lean_ctor_get_uint8(v_t_1709_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1709_, 3);
v___x_1740_ = lean_box(v_binderInfo_1739_);
v___x_1741_ = lean_apply_4(v_lam_1716_, v_binderName_1736_, v_binderType_1737_, v_body_1738_, v___x_1740_);
return v___x_1741_;
}
case 7:
{
lean_object* v_binderName_1742_; lean_object* v_binderType_1743_; lean_object* v_body_1744_; uint8_t v_binderInfo_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_binderName_1742_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_binderName_1742_);
v_binderType_1743_ = lean_ctor_get(v_t_1709_, 1);
lean_inc_ref(v_binderType_1743_);
v_body_1744_ = lean_ctor_get(v_t_1709_, 2);
lean_inc_ref(v_body_1744_);
v_binderInfo_1745_ = lean_ctor_get_uint8(v_t_1709_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1709_, 3);
v___x_1746_ = lean_box(v_binderInfo_1745_);
v___x_1747_ = lean_apply_4(v_forallE_1717_, v_binderName_1742_, v_binderType_1743_, v_body_1744_, v___x_1746_);
return v___x_1747_;
}
case 8:
{
lean_object* v_declName_1748_; lean_object* v_type_1749_; lean_object* v_value_1750_; lean_object* v_body_1751_; uint8_t v_nondep_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_declName_1748_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_declName_1748_);
v_type_1749_ = lean_ctor_get(v_t_1709_, 1);
lean_inc_ref(v_type_1749_);
v_value_1750_ = lean_ctor_get(v_t_1709_, 2);
lean_inc_ref(v_value_1750_);
v_body_1751_ = lean_ctor_get(v_t_1709_, 3);
lean_inc_ref(v_body_1751_);
v_nondep_1752_ = lean_ctor_get_uint8(v_t_1709_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1709_, 4);
v___x_1753_ = lean_box(v_nondep_1752_);
v___x_1754_ = lean_apply_5(v_letE_1718_, v_declName_1748_, v_type_1749_, v_value_1750_, v_body_1751_, v___x_1753_);
return v___x_1754_;
}
case 9:
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
lean_dec(v_proj_1721_);
lean_dec(v_mdata_1720_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_a_1755_ = lean_ctor_get(v_t_1709_, 0);
lean_inc_ref(v_a_1755_);
lean_dec_ref_known(v_t_1709_, 1);
v___x_1756_ = lean_apply_1(v_lit_1719_, v_a_1755_);
return v___x_1756_;
}
case 10:
{
lean_object* v_data_1757_; lean_object* v_expr_1758_; lean_object* v___x_1759_; 
lean_dec(v_proj_1721_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_data_1757_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_data_1757_);
v_expr_1758_ = lean_ctor_get(v_t_1709_, 1);
lean_inc_ref(v_expr_1758_);
lean_dec_ref_known(v_t_1709_, 2);
v___x_1759_ = lean_apply_2(v_mdata_1720_, v_data_1757_, v_expr_1758_);
return v___x_1759_;
}
default: 
{
lean_object* v_typeName_1760_; lean_object* v_idx_1761_; lean_object* v_struct_1762_; lean_object* v___x_1763_; 
lean_dec(v_mdata_1720_);
lean_dec(v_lit_1719_);
lean_dec(v_letE_1718_);
lean_dec(v_forallE_1717_);
lean_dec(v_lam_1716_);
lean_dec(v_app_1715_);
lean_dec(v_const_1714_);
lean_dec(v_sort_1713_);
lean_dec(v_mvar_1712_);
lean_dec(v_fvar_1711_);
lean_dec(v_bvar_1710_);
v_typeName_1760_ = lean_ctor_get(v_t_1709_, 0);
lean_inc(v_typeName_1760_);
v_idx_1761_ = lean_ctor_get(v_t_1709_, 1);
lean_inc(v_idx_1761_);
v_struct_1762_ = lean_ctor_get(v_t_1709_, 2);
lean_inc_ref(v_struct_1762_);
lean_dec_ref_known(v_t_1709_, 3);
v___x_1763_ = lean_apply_3(v_proj_1721_, v_typeName_1760_, v_idx_1761_, v_struct_1762_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1764_){
_start:
{
uint64_t v___x_1765_; uint64_t v___x_1766_; uint64_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint32_t v___x_1770_; uint8_t v___x_1771_; uint64_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1765_ = 7ULL;
v___x_1766_ = lean_uint64_of_nat(v_deBruijnIndex_1764_);
v___x_1767_ = lean_uint64_mix_hash(v___x_1765_, v___x_1766_);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_deBruijnIndex_1764_, v___x_1768_);
v___x_1770_ = 0;
v___x_1771_ = 0;
v___x_1772_ = lean_expr_mk_data(v___x_1767_, v___x_1769_, v___x_1770_, v___x_1771_, v___x_1771_, v___x_1771_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1773_, 0, v_deBruijnIndex_1764_);
lean_ctor_set_uint64(v___x_1773_, sizeof(void*)*1, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1774_){
_start:
{
uint64_t v___x_1775_; uint64_t v___x_1776_; uint64_t v___x_1777_; lean_object* v___x_1778_; uint32_t v___x_1779_; uint8_t v___x_1780_; uint8_t v___x_1781_; uint64_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1775_ = 13ULL;
v___x_1776_ = l_Lean_instHashableFVarId_hash(v_fvarId_1774_);
v___x_1777_ = lean_uint64_mix_hash(v___x_1775_, v___x_1776_);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = 0;
v___x_1780_ = 1;
v___x_1781_ = 0;
v___x_1782_ = lean_expr_mk_data(v___x_1777_, v___x_1778_, v___x_1779_, v___x_1780_, v___x_1781_, v___x_1781_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1783_, 0, v_fvarId_1774_);
lean_ctor_set_uint64(v___x_1783_, sizeof(void*)*1, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1784_){
_start:
{
uint64_t v___x_1785_; uint64_t v___x_1786_; uint64_t v___x_1787_; lean_object* v___x_1788_; uint32_t v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; uint64_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1785_ = 17ULL;
v___x_1786_ = l_Lean_instHashableMVarId_hash(v_mvarId_1784_);
v___x_1787_ = lean_uint64_mix_hash(v___x_1785_, v___x_1786_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = 0;
v___x_1790_ = 0;
v___x_1791_ = 1;
v___x_1792_ = lean_expr_mk_data(v___x_1787_, v___x_1788_, v___x_1789_, v___x_1790_, v___x_1791_, v___x_1790_, v___x_1790_);
v___x_1793_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1793_, 0, v_mvarId_1784_);
lean_ctor_set_uint64(v___x_1793_, sizeof(void*)*1, v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1794_){
_start:
{
uint64_t v___x_1795_; uint64_t v___x_1796_; uint64_t v___x_1797_; lean_object* v___x_1798_; uint32_t v___x_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; uint64_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1795_ = 11ULL;
v___x_1796_ = l_Lean_Level_hash(v_u_1794_);
v___x_1797_ = lean_uint64_mix_hash(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = 0;
v___x_1800_ = 0;
v___x_1801_ = l_Lean_Level_hasMVar(v_u_1794_);
v___x_1802_ = l_Lean_Level_hasParam(v_u_1794_);
v___x_1803_ = lean_expr_mk_data(v___x_1797_, v___x_1798_, v___x_1799_, v___x_1800_, v___x_1800_, v___x_1801_, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1804_, 0, v_u_1794_);
lean_ctor_set_uint64(v___x_1804_, sizeof(void*)*1, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1805_, lean_object* v_arg_1806_){
_start:
{
uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_expr_data(v_fn_1805_);
v___x_1808_ = lean_expr_data(v_arg_1806_);
v___x_1809_ = lean_expr_mk_app_data(v___x_1807_, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1810_, 0, v_fn_1805_);
lean_ctor_set(v___x_1810_, 1, v_arg_1806_);
lean_ctor_set_uint64(v___x_1810_, sizeof(void*)*2, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1811_, lean_object* v_binderType_1812_, lean_object* v_body_1813_, uint8_t v_binderInfo_1814_){
_start:
{
lean_object* v___y_1816_; uint32_t v___y_1817_; uint8_t v___y_1818_; uint64_t v___y_1819_; uint8_t v___y_1820_; uint8_t v___y_1821_; uint8_t v___y_1822_; uint64_t v___x_1825_; uint8_t v___x_1826_; uint32_t v___x_1827_; uint64_t v___x_1828_; lean_object* v___y_1830_; uint32_t v___y_1831_; uint64_t v___y_1832_; uint8_t v___y_1833_; uint8_t v___y_1834_; uint8_t v___y_1835_; lean_object* v___y_1839_; uint32_t v___y_1840_; uint64_t v___y_1841_; uint8_t v___y_1842_; uint8_t v___y_1843_; lean_object* v___y_1847_; uint32_t v___y_1848_; uint64_t v___y_1849_; uint8_t v___y_1850_; uint32_t v___y_1854_; uint64_t v___y_1855_; lean_object* v___y_1856_; uint32_t v___y_1860_; uint8_t v___x_1875_; uint32_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1825_ = lean_expr_data(v_binderType_1812_);
v___x_1826_ = l_Lean_Expr_Data_approxDepth(v___x_1825_);
v___x_1827_ = lean_uint8_to_uint32(v___x_1826_);
v___x_1828_ = lean_expr_data(v_body_1813_);
v___x_1875_ = l_Lean_Expr_Data_approxDepth(v___x_1828_);
v___x_1876_ = lean_uint8_to_uint32(v___x_1875_);
v___x_1877_ = lean_uint32_dec_le(v___x_1827_, v___x_1876_);
if (v___x_1877_ == 0)
{
v___y_1860_ = v___x_1827_;
goto v___jp_1859_;
}
else
{
v___y_1860_ = v___x_1876_;
goto v___jp_1859_;
}
v___jp_1815_:
{
uint64_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_expr_mk_data(v___y_1819_, v___y_1816_, v___y_1817_, v___y_1821_, v___y_1820_, v___y_1818_, v___y_1822_);
v___x_1824_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1824_, 0, v_binderName_1811_);
lean_ctor_set(v___x_1824_, 1, v_binderType_1812_);
lean_ctor_set(v___x_1824_, 2, v_body_1813_);
lean_ctor_set_uint64(v___x_1824_, sizeof(void*)*3, v___x_1823_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*3 + 8, v_binderInfo_1814_);
return v___x_1824_;
}
v___jp_1829_:
{
uint8_t v___x_1836_; 
v___x_1836_ = l_Lean_Expr_Data_hasLevelParam(v___x_1825_);
if (v___x_1836_ == 0)
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Lean_Expr_Data_hasLevelParam(v___x_1828_);
v___y_1816_ = v___y_1830_;
v___y_1817_ = v___y_1831_;
v___y_1818_ = v___y_1835_;
v___y_1819_ = v___y_1832_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1834_;
v___y_1822_ = v___x_1837_;
goto v___jp_1815_;
}
else
{
v___y_1816_ = v___y_1830_;
v___y_1817_ = v___y_1831_;
v___y_1818_ = v___y_1835_;
v___y_1819_ = v___y_1832_;
v___y_1820_ = v___y_1833_;
v___y_1821_ = v___y_1834_;
v___y_1822_ = v___x_1836_;
goto v___jp_1815_;
}
}
v___jp_1838_:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1825_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1828_);
v___y_1830_ = v___y_1839_;
v___y_1831_ = v___y_1840_;
v___y_1832_ = v___y_1841_;
v___y_1833_ = v___y_1843_;
v___y_1834_ = v___y_1842_;
v___y_1835_ = v___x_1845_;
goto v___jp_1829_;
}
else
{
v___y_1830_ = v___y_1839_;
v___y_1831_ = v___y_1840_;
v___y_1832_ = v___y_1841_;
v___y_1833_ = v___y_1843_;
v___y_1834_ = v___y_1842_;
v___y_1835_ = v___x_1844_;
goto v___jp_1829_;
}
}
v___jp_1846_:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_Lean_Expr_Data_hasExprMVar(v___x_1825_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_Expr_Data_hasExprMVar(v___x_1828_);
v___y_1839_ = v___y_1847_;
v___y_1840_ = v___y_1848_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___x_1852_;
goto v___jp_1838_;
}
else
{
v___y_1839_ = v___y_1847_;
v___y_1840_ = v___y_1848_;
v___y_1841_ = v___y_1849_;
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___x_1851_;
goto v___jp_1838_;
}
}
v___jp_1853_:
{
uint8_t v___x_1857_; 
v___x_1857_ = l_Lean_Expr_Data_hasFVar(v___x_1825_);
if (v___x_1857_ == 0)
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Lean_Expr_Data_hasFVar(v___x_1828_);
v___y_1847_ = v___y_1856_;
v___y_1848_ = v___y_1854_;
v___y_1849_ = v___y_1855_;
v___y_1850_ = v___x_1858_;
goto v___jp_1846_;
}
else
{
v___y_1847_ = v___y_1856_;
v___y_1848_ = v___y_1854_;
v___y_1849_ = v___y_1855_;
v___y_1850_ = v___x_1857_;
goto v___jp_1846_;
}
}
v___jp_1859_:
{
lean_object* v___x_1861_; uint32_t v___x_1862_; uint32_t v___x_1863_; uint64_t v___x_1864_; uint64_t v___x_1865_; uint64_t v___x_1866_; uint64_t v___x_1867_; uint64_t v___x_1868_; uint32_t v___x_1869_; lean_object* v___x_1870_; uint32_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = 1;
v___x_1863_ = lean_uint32_add(v___y_1860_, v___x_1862_);
v___x_1864_ = lean_uint32_to_uint64(v___x_1863_);
v___x_1865_ = l_Lean_Expr_Data_hash(v___x_1825_);
v___x_1866_ = l_Lean_Expr_Data_hash(v___x_1828_);
v___x_1867_ = lean_uint64_mix_hash(v___x_1865_, v___x_1866_);
v___x_1868_ = lean_uint64_mix_hash(v___x_1864_, v___x_1867_);
v___x_1869_ = l_Lean_Expr_Data_looseBVarRange(v___x_1825_);
v___x_1870_ = lean_uint32_to_nat(v___x_1869_);
v___x_1871_ = l_Lean_Expr_Data_looseBVarRange(v___x_1828_);
v___x_1872_ = lean_uint32_to_nat(v___x_1871_);
v___x_1873_ = lean_nat_sub(v___x_1872_, v___x_1861_);
lean_dec(v___x_1872_);
v___x_1874_ = lean_nat_dec_le(v___x_1870_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_dec(v___x_1873_);
v___y_1854_ = v___x_1863_;
v___y_1855_ = v___x_1868_;
v___y_1856_ = v___x_1870_;
goto v___jp_1853_;
}
else
{
lean_dec(v___x_1870_);
v___y_1854_ = v___x_1863_;
v___y_1855_ = v___x_1868_;
v___y_1856_ = v___x_1873_;
goto v___jp_1853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1878_, lean_object* v_binderType_1879_, lean_object* v_body_1880_, lean_object* v_binderInfo_1881_){
_start:
{
uint8_t v_binderInfo_boxed_1882_; lean_object* v_res_1883_; 
v_binderInfo_boxed_1882_ = lean_unbox(v_binderInfo_1881_);
v_res_1883_ = l_Lean_Expr_lam___override(v_binderName_1878_, v_binderType_1879_, v_body_1880_, v_binderInfo_boxed_1882_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1884_, lean_object* v_binderType_1885_, lean_object* v_body_1886_, uint8_t v_binderInfo_1887_){
_start:
{
uint8_t v___y_1889_; uint64_t v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1892_; uint32_t v___y_1893_; uint8_t v___y_1894_; uint8_t v___y_1895_; uint64_t v___x_1898_; uint8_t v___x_1899_; uint32_t v___x_1900_; uint64_t v___x_1901_; uint8_t v___y_1903_; uint64_t v___y_1904_; uint8_t v___y_1905_; lean_object* v___y_1906_; uint32_t v___y_1907_; uint8_t v___y_1908_; uint8_t v___y_1912_; uint64_t v___y_1913_; lean_object* v___y_1914_; uint32_t v___y_1915_; uint8_t v___y_1916_; uint64_t v___y_1920_; lean_object* v___y_1921_; uint32_t v___y_1922_; uint8_t v___y_1923_; uint64_t v___y_1927_; uint32_t v___y_1928_; lean_object* v___y_1929_; uint32_t v___y_1933_; uint8_t v___x_1948_; uint32_t v___x_1949_; uint8_t v___x_1950_; 
v___x_1898_ = lean_expr_data(v_binderType_1885_);
v___x_1899_ = l_Lean_Expr_Data_approxDepth(v___x_1898_);
v___x_1900_ = lean_uint8_to_uint32(v___x_1899_);
v___x_1901_ = lean_expr_data(v_body_1886_);
v___x_1948_ = l_Lean_Expr_Data_approxDepth(v___x_1901_);
v___x_1949_ = lean_uint8_to_uint32(v___x_1948_);
v___x_1950_ = lean_uint32_dec_le(v___x_1900_, v___x_1949_);
if (v___x_1950_ == 0)
{
v___y_1933_ = v___x_1900_;
goto v___jp_1932_;
}
else
{
v___y_1933_ = v___x_1949_;
goto v___jp_1932_;
}
v___jp_1888_:
{
uint64_t v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_expr_mk_data(v___y_1890_, v___y_1892_, v___y_1893_, v___y_1889_, v___y_1891_, v___y_1894_, v___y_1895_);
v___x_1897_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1897_, 0, v_binderName_1884_);
lean_ctor_set(v___x_1897_, 1, v_binderType_1885_);
lean_ctor_set(v___x_1897_, 2, v_body_1886_);
lean_ctor_set_uint64(v___x_1897_, sizeof(void*)*3, v___x_1896_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*3 + 8, v_binderInfo_1887_);
return v___x_1897_;
}
v___jp_1902_:
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Expr_Data_hasLevelParam(v___x_1898_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Lean_Expr_Data_hasLevelParam(v___x_1901_);
v___y_1889_ = v___y_1903_;
v___y_1890_ = v___y_1904_;
v___y_1891_ = v___y_1905_;
v___y_1892_ = v___y_1906_;
v___y_1893_ = v___y_1907_;
v___y_1894_ = v___y_1908_;
v___y_1895_ = v___x_1910_;
goto v___jp_1888_;
}
else
{
v___y_1889_ = v___y_1903_;
v___y_1890_ = v___y_1904_;
v___y_1891_ = v___y_1905_;
v___y_1892_ = v___y_1906_;
v___y_1893_ = v___y_1907_;
v___y_1894_ = v___y_1908_;
v___y_1895_ = v___x_1909_;
goto v___jp_1888_;
}
}
v___jp_1911_:
{
uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1898_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1901_);
v___y_1903_ = v___y_1912_;
v___y_1904_ = v___y_1913_;
v___y_1905_ = v___y_1916_;
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___x_1918_;
goto v___jp_1902_;
}
else
{
v___y_1903_ = v___y_1912_;
v___y_1904_ = v___y_1913_;
v___y_1905_ = v___y_1916_;
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___x_1917_;
goto v___jp_1902_;
}
}
v___jp_1919_:
{
uint8_t v___x_1924_; 
v___x_1924_ = l_Lean_Expr_Data_hasExprMVar(v___x_1898_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = l_Lean_Expr_Data_hasExprMVar(v___x_1901_);
v___y_1912_ = v___y_1923_;
v___y_1913_ = v___y_1920_;
v___y_1914_ = v___y_1921_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___x_1925_;
goto v___jp_1911_;
}
else
{
v___y_1912_ = v___y_1923_;
v___y_1913_ = v___y_1920_;
v___y_1914_ = v___y_1921_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___x_1924_;
goto v___jp_1911_;
}
}
v___jp_1926_:
{
uint8_t v___x_1930_; 
v___x_1930_ = l_Lean_Expr_Data_hasFVar(v___x_1898_);
if (v___x_1930_ == 0)
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_Expr_Data_hasFVar(v___x_1901_);
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1929_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___x_1931_;
goto v___jp_1919_;
}
else
{
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1929_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___x_1930_;
goto v___jp_1919_;
}
}
v___jp_1932_:
{
lean_object* v___x_1934_; uint32_t v___x_1935_; uint32_t v___x_1936_; uint64_t v___x_1937_; uint64_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint32_t v___x_1942_; lean_object* v___x_1943_; uint32_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = 1;
v___x_1936_ = lean_uint32_add(v___y_1933_, v___x_1935_);
v___x_1937_ = lean_uint32_to_uint64(v___x_1936_);
v___x_1938_ = l_Lean_Expr_Data_hash(v___x_1898_);
v___x_1939_ = l_Lean_Expr_Data_hash(v___x_1901_);
v___x_1940_ = lean_uint64_mix_hash(v___x_1938_, v___x_1939_);
v___x_1941_ = lean_uint64_mix_hash(v___x_1937_, v___x_1940_);
v___x_1942_ = l_Lean_Expr_Data_looseBVarRange(v___x_1898_);
v___x_1943_ = lean_uint32_to_nat(v___x_1942_);
v___x_1944_ = l_Lean_Expr_Data_looseBVarRange(v___x_1901_);
v___x_1945_ = lean_uint32_to_nat(v___x_1944_);
v___x_1946_ = lean_nat_sub(v___x_1945_, v___x_1934_);
lean_dec(v___x_1945_);
v___x_1947_ = lean_nat_dec_le(v___x_1943_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_dec(v___x_1946_);
v___y_1927_ = v___x_1941_;
v___y_1928_ = v___x_1936_;
v___y_1929_ = v___x_1943_;
goto v___jp_1926_;
}
else
{
lean_dec(v___x_1943_);
v___y_1927_ = v___x_1941_;
v___y_1928_ = v___x_1936_;
v___y_1929_ = v___x_1946_;
goto v___jp_1926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1951_, lean_object* v_binderType_1952_, lean_object* v_body_1953_, lean_object* v_binderInfo_1954_){
_start:
{
uint8_t v_binderInfo_boxed_1955_; lean_object* v_res_1956_; 
v_binderInfo_boxed_1955_ = lean_unbox(v_binderInfo_1954_);
v_res_1956_ = l_Lean_Expr_forallE___override(v_binderName_1951_, v_binderType_1952_, v_body_1953_, v_binderInfo_boxed_1955_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1957_, lean_object* v_type_1958_, lean_object* v_value_1959_, lean_object* v_body_1960_, uint8_t v_nondep_1961_){
_start:
{
uint32_t v___y_1963_; uint64_t v___y_1964_; uint8_t v___y_1965_; uint8_t v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_1968_; uint8_t v___y_1969_; uint32_t v___y_1973_; uint64_t v___y_1974_; uint8_t v___y_1975_; uint8_t v___y_1976_; uint64_t v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1979_; uint8_t v___y_1980_; uint64_t v___x_1982_; uint8_t v___x_1983_; uint32_t v___x_1984_; uint64_t v___x_1985_; uint32_t v___y_1987_; uint64_t v___y_1988_; uint8_t v___y_1989_; uint8_t v___y_1990_; lean_object* v___y_1991_; uint64_t v___y_1992_; uint8_t v___y_1993_; uint32_t v___y_1997_; uint64_t v___y_1998_; uint8_t v___y_1999_; uint64_t v___y_2000_; uint8_t v___y_2001_; lean_object* v___y_2002_; uint8_t v___y_2003_; uint32_t v___y_2006_; uint64_t v___y_2007_; uint8_t v___y_2008_; uint64_t v___y_2009_; lean_object* v___y_2010_; uint8_t v___y_2011_; uint32_t v___y_2015_; uint64_t v___y_2016_; uint8_t v___y_2017_; uint64_t v___y_2018_; lean_object* v___y_2019_; uint8_t v___y_2020_; uint32_t v___y_2023_; uint64_t v___y_2024_; uint64_t v___y_2025_; lean_object* v___y_2026_; uint8_t v___y_2027_; uint32_t v___y_2031_; uint64_t v___y_2032_; uint64_t v___y_2033_; lean_object* v___y_2034_; uint8_t v___y_2035_; uint32_t v___y_2038_; uint64_t v___y_2039_; uint64_t v___y_2040_; lean_object* v___y_2041_; uint32_t v___y_2045_; uint64_t v___y_2046_; uint64_t v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint64_t v___y_2055_; uint32_t v___y_2056_; uint32_t v___y_2073_; uint8_t v___x_2078_; uint32_t v___x_2079_; uint8_t v___x_2080_; 
v___x_1982_ = lean_expr_data(v_type_1958_);
v___x_1983_ = l_Lean_Expr_Data_approxDepth(v___x_1982_);
v___x_1984_ = lean_uint8_to_uint32(v___x_1983_);
v___x_1985_ = lean_expr_data(v_value_1959_);
v___x_2078_ = l_Lean_Expr_Data_approxDepth(v___x_1985_);
v___x_2079_ = lean_uint8_to_uint32(v___x_2078_);
v___x_2080_ = lean_uint32_dec_le(v___x_1984_, v___x_2079_);
if (v___x_2080_ == 0)
{
v___y_2073_ = v___x_1984_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v___x_2079_;
goto v___jp_2072_;
}
v___jp_1962_:
{
uint64_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_expr_mk_data(v___y_1964_, v___y_1968_, v___y_1963_, v___y_1966_, v___y_1967_, v___y_1965_, v___y_1969_);
v___x_1971_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1971_, 0, v_declName_1957_);
lean_ctor_set(v___x_1971_, 1, v_type_1958_);
lean_ctor_set(v___x_1971_, 2, v_value_1959_);
lean_ctor_set(v___x_1971_, 3, v_body_1960_);
lean_ctor_set_uint64(v___x_1971_, sizeof(void*)*4, v___x_1970_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*4 + 8, v_nondep_1961_);
return v___x_1971_;
}
v___jp_1972_:
{
if (v___y_1980_ == 0)
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Expr_Data_hasLevelParam(v___y_1977_);
v___y_1963_ = v___y_1973_;
v___y_1964_ = v___y_1974_;
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1978_;
v___y_1968_ = v___y_1979_;
v___y_1969_ = v___x_1981_;
goto v___jp_1962_;
}
else
{
v___y_1963_ = v___y_1973_;
v___y_1964_ = v___y_1974_;
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1978_;
v___y_1968_ = v___y_1979_;
v___y_1969_ = v___y_1980_;
goto v___jp_1962_;
}
}
v___jp_1986_:
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_Expr_Data_hasLevelParam(v___x_1982_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_Expr_Data_hasLevelParam(v___x_1985_);
v___y_1973_ = v___y_1987_;
v___y_1974_ = v___y_1988_;
v___y_1975_ = v___y_1993_;
v___y_1976_ = v___y_1989_;
v___y_1977_ = v___y_1992_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1991_;
v___y_1980_ = v___x_1995_;
goto v___jp_1972_;
}
else
{
v___y_1973_ = v___y_1987_;
v___y_1974_ = v___y_1988_;
v___y_1975_ = v___y_1993_;
v___y_1976_ = v___y_1989_;
v___y_1977_ = v___y_1992_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1991_;
v___y_1980_ = v___x_1994_;
goto v___jp_1972_;
}
}
v___jp_1996_:
{
if (v___y_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2000_);
v___y_1987_ = v___y_1997_;
v___y_1988_ = v___y_1998_;
v___y_1989_ = v___y_1999_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___y_2002_;
v___y_1992_ = v___y_2000_;
v___y_1993_ = v___x_2004_;
goto v___jp_1986_;
}
else
{
v___y_1987_ = v___y_1997_;
v___y_1988_ = v___y_1998_;
v___y_1989_ = v___y_1999_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___y_2002_;
v___y_1992_ = v___y_2000_;
v___y_1993_ = v___y_2003_;
goto v___jp_1986_;
}
}
v___jp_2005_:
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1982_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1985_);
v___y_1997_ = v___y_2006_;
v___y_1998_ = v___y_2007_;
v___y_1999_ = v___y_2008_;
v___y_2000_ = v___y_2009_;
v___y_2001_ = v___y_2011_;
v___y_2002_ = v___y_2010_;
v___y_2003_ = v___x_2013_;
goto v___jp_1996_;
}
else
{
v___y_1997_ = v___y_2006_;
v___y_1998_ = v___y_2007_;
v___y_1999_ = v___y_2008_;
v___y_2000_ = v___y_2009_;
v___y_2001_ = v___y_2011_;
v___y_2002_ = v___y_2010_;
v___y_2003_ = v___x_2012_;
goto v___jp_1996_;
}
}
v___jp_2014_:
{
if (v___y_2020_ == 0)
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Expr_Data_hasExprMVar(v___y_2018_);
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2018_;
v___y_2010_ = v___y_2019_;
v___y_2011_ = v___x_2021_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2015_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2018_;
v___y_2010_ = v___y_2019_;
v___y_2011_ = v___y_2020_;
goto v___jp_2005_;
}
}
v___jp_2022_:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_Data_hasExprMVar(v___x_1982_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; 
v___x_2029_ = l_Lean_Expr_Data_hasExprMVar(v___x_1985_);
v___y_2015_ = v___y_2023_;
v___y_2016_ = v___y_2024_;
v___y_2017_ = v___y_2027_;
v___y_2018_ = v___y_2025_;
v___y_2019_ = v___y_2026_;
v___y_2020_ = v___x_2029_;
goto v___jp_2014_;
}
else
{
v___y_2015_ = v___y_2023_;
v___y_2016_ = v___y_2024_;
v___y_2017_ = v___y_2027_;
v___y_2018_ = v___y_2025_;
v___y_2019_ = v___y_2026_;
v___y_2020_ = v___x_2028_;
goto v___jp_2014_;
}
}
v___jp_2030_:
{
if (v___y_2035_ == 0)
{
uint8_t v___x_2036_; 
v___x_2036_ = l_Lean_Expr_Data_hasFVar(v___y_2033_);
v___y_2023_ = v___y_2031_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2034_;
v___y_2027_ = v___x_2036_;
goto v___jp_2022_;
}
else
{
v___y_2023_ = v___y_2031_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2034_;
v___y_2027_ = v___y_2035_;
goto v___jp_2022_;
}
}
v___jp_2037_:
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Expr_Data_hasFVar(v___x_1982_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_Expr_Data_hasFVar(v___x_1985_);
v___y_2031_ = v___y_2038_;
v___y_2032_ = v___y_2039_;
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v___y_2035_ = v___x_2043_;
goto v___jp_2030_;
}
else
{
v___y_2031_ = v___y_2038_;
v___y_2032_ = v___y_2039_;
v___y_2033_ = v___y_2040_;
v___y_2034_ = v___y_2041_;
v___y_2035_ = v___x_2042_;
goto v___jp_2030_;
}
}
v___jp_2044_:
{
uint32_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2050_ = l_Lean_Expr_Data_looseBVarRange(v___y_2047_);
v___x_2051_ = lean_uint32_to_nat(v___x_2050_);
v___x_2052_ = lean_nat_sub(v___x_2051_, v___y_2048_);
lean_dec(v___x_2051_);
v___x_2053_ = lean_nat_dec_le(v___y_2049_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec(v___x_2052_);
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2049_;
goto v___jp_2037_;
}
else
{
lean_dec(v___y_2049_);
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___y_2046_;
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___x_2052_;
goto v___jp_2037_;
}
}
v___jp_2054_:
{
lean_object* v___x_2057_; uint32_t v___x_2058_; uint32_t v___x_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v___x_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint32_t v___x_2067_; lean_object* v___x_2068_; uint32_t v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = 1;
v___x_2059_ = lean_uint32_add(v___y_2056_, v___x_2058_);
v___x_2060_ = lean_uint32_to_uint64(v___x_2059_);
v___x_2061_ = l_Lean_Expr_Data_hash(v___x_1982_);
v___x_2062_ = l_Lean_Expr_Data_hash(v___x_1985_);
v___x_2063_ = l_Lean_Expr_Data_hash(v___y_2055_);
v___x_2064_ = lean_uint64_mix_hash(v___x_2062_, v___x_2063_);
v___x_2065_ = lean_uint64_mix_hash(v___x_2061_, v___x_2064_);
v___x_2066_ = lean_uint64_mix_hash(v___x_2060_, v___x_2065_);
v___x_2067_ = l_Lean_Expr_Data_looseBVarRange(v___x_1982_);
v___x_2068_ = lean_uint32_to_nat(v___x_2067_);
v___x_2069_ = l_Lean_Expr_Data_looseBVarRange(v___x_1985_);
v___x_2070_ = lean_uint32_to_nat(v___x_2069_);
v___x_2071_ = lean_nat_dec_le(v___x_2068_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v___x_2070_);
v___y_2045_ = v___x_2059_;
v___y_2046_ = v___x_2066_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___x_2057_;
v___y_2049_ = v___x_2068_;
goto v___jp_2044_;
}
else
{
lean_dec(v___x_2068_);
v___y_2045_ = v___x_2059_;
v___y_2046_ = v___x_2066_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___x_2057_;
v___y_2049_ = v___x_2070_;
goto v___jp_2044_;
}
}
v___jp_2072_:
{
uint64_t v___x_2074_; uint8_t v___x_2075_; uint32_t v___x_2076_; uint8_t v___x_2077_; 
v___x_2074_ = lean_expr_data(v_body_1960_);
v___x_2075_ = l_Lean_Expr_Data_approxDepth(v___x_2074_);
v___x_2076_ = lean_uint8_to_uint32(v___x_2075_);
v___x_2077_ = lean_uint32_dec_le(v___y_2073_, v___x_2076_);
if (v___x_2077_ == 0)
{
v___y_2055_ = v___x_2074_;
v___y_2056_ = v___y_2073_;
goto v___jp_2054_;
}
else
{
v___y_2055_ = v___x_2074_;
v___y_2056_ = v___x_2076_;
goto v___jp_2054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2081_, lean_object* v_type_2082_, lean_object* v_value_2083_, lean_object* v_body_2084_, lean_object* v_nondep_2085_){
_start:
{
uint8_t v_nondep_boxed_2086_; lean_object* v_res_2087_; 
v_nondep_boxed_2086_ = lean_unbox(v_nondep_2085_);
v_res_2087_ = l_Lean_Expr_letE___override(v_declName_2081_, v_type_2082_, v_value_2083_, v_body_2084_, v_nondep_boxed_2086_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2088_){
_start:
{
uint64_t v___x_2089_; uint64_t v___x_2090_; uint64_t v___x_2091_; lean_object* v___x_2092_; uint32_t v___x_2093_; uint8_t v___x_2094_; uint64_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2089_ = 3ULL;
v___x_2090_ = l_Lean_Literal_hash(v_a_2088_);
v___x_2091_ = lean_uint64_mix_hash(v___x_2089_, v___x_2090_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = 0;
v___x_2094_ = 0;
v___x_2095_ = lean_expr_mk_data(v___x_2091_, v___x_2092_, v___x_2093_, v___x_2094_, v___x_2094_, v___x_2094_, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2096_, 0, v_a_2088_);
lean_ctor_set_uint64(v___x_2096_, sizeof(void*)*1, v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2097_, lean_object* v_expr_2098_){
_start:
{
uint64_t v___x_2099_; uint8_t v___x_2100_; uint32_t v___x_2101_; uint32_t v___x_2102_; uint32_t v___x_2103_; uint64_t v___x_2104_; uint64_t v___x_2105_; uint64_t v___x_2106_; uint32_t v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; uint64_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2099_ = lean_expr_data(v_expr_2098_);
v___x_2100_ = l_Lean_Expr_Data_approxDepth(v___x_2099_);
v___x_2101_ = lean_uint8_to_uint32(v___x_2100_);
v___x_2102_ = 1;
v___x_2103_ = lean_uint32_add(v___x_2101_, v___x_2102_);
v___x_2104_ = lean_uint32_to_uint64(v___x_2103_);
v___x_2105_ = l_Lean_Expr_Data_hash(v___x_2099_);
v___x_2106_ = lean_uint64_mix_hash(v___x_2104_, v___x_2105_);
v___x_2107_ = l_Lean_Expr_Data_looseBVarRange(v___x_2099_);
v___x_2108_ = lean_uint32_to_nat(v___x_2107_);
v___x_2109_ = l_Lean_Expr_Data_hasFVar(v___x_2099_);
v___x_2110_ = l_Lean_Expr_Data_hasExprMVar(v___x_2099_);
v___x_2111_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2099_);
v___x_2112_ = l_Lean_Expr_Data_hasLevelParam(v___x_2099_);
v___x_2113_ = lean_expr_mk_data(v___x_2106_, v___x_2108_, v___x_2103_, v___x_2109_, v___x_2110_, v___x_2111_, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2114_, 0, v_data_2097_);
lean_ctor_set(v___x_2114_, 1, v_expr_2098_);
lean_ctor_set_uint64(v___x_2114_, sizeof(void*)*2, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2115_, lean_object* v_idx_2116_, lean_object* v_struct_2117_){
_start:
{
uint64_t v___x_2118_; uint8_t v___x_2119_; uint32_t v___x_2120_; uint32_t v___x_2121_; uint32_t v___x_2122_; uint64_t v___x_2123_; uint64_t v___y_2125_; 
v___x_2118_ = lean_expr_data(v_struct_2117_);
v___x_2119_ = l_Lean_Expr_Data_approxDepth(v___x_2118_);
v___x_2120_ = lean_uint8_to_uint32(v___x_2119_);
v___x_2121_ = 1;
v___x_2122_ = lean_uint32_add(v___x_2120_, v___x_2121_);
v___x_2123_ = lean_uint32_to_uint64(v___x_2122_);
if (lean_obj_tag(v_typeName_2115_) == 0)
{
uint64_t v___x_2139_; 
v___x_2139_ = 1723ULL;
v___y_2125_ = v___x_2139_;
goto v___jp_2124_;
}
else
{
uint64_t v_hash_2140_; 
v_hash_2140_ = lean_ctor_get_uint64(v_typeName_2115_, sizeof(void*)*2);
v___y_2125_ = v_hash_2140_;
goto v___jp_2124_;
}
v___jp_2124_:
{
uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; uint32_t v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; uint8_t v___x_2136_; uint64_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2126_ = lean_uint64_of_nat(v_idx_2116_);
v___x_2127_ = l_Lean_Expr_Data_hash(v___x_2118_);
v___x_2128_ = lean_uint64_mix_hash(v___x_2126_, v___x_2127_);
v___x_2129_ = lean_uint64_mix_hash(v___y_2125_, v___x_2128_);
v___x_2130_ = lean_uint64_mix_hash(v___x_2123_, v___x_2129_);
v___x_2131_ = l_Lean_Expr_Data_looseBVarRange(v___x_2118_);
v___x_2132_ = lean_uint32_to_nat(v___x_2131_);
v___x_2133_ = l_Lean_Expr_Data_hasFVar(v___x_2118_);
v___x_2134_ = l_Lean_Expr_Data_hasExprMVar(v___x_2118_);
v___x_2135_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2118_);
v___x_2136_ = l_Lean_Expr_Data_hasLevelParam(v___x_2118_);
v___x_2137_ = lean_expr_mk_data(v___x_2130_, v___x_2132_, v___x_2122_, v___x_2133_, v___x_2134_, v___x_2135_, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2138_, 0, v_typeName_2115_);
lean_ctor_set(v___x_2138_, 1, v_idx_2116_);
lean_ctor_set(v___x_2138_, 2, v_struct_2117_);
lean_ctor_set_uint64(v___x_2138_, sizeof(void*)*3, v___x_2137_);
return v___x_2138_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
uint8_t v___x_2142_; 
v___x_2142_ = 0;
return v___x_2142_;
}
else
{
lean_object* v_head_2143_; lean_object* v_tail_2144_; uint8_t v___x_2145_; 
v_head_2143_ = lean_ctor_get(v_x_2141_, 0);
v_tail_2144_ = lean_ctor_get(v_x_2141_, 1);
v___x_2145_ = l_Lean_Level_hasMVar(v_head_2143_);
if (v___x_2145_ == 0)
{
v_x_2141_ = v_tail_2144_;
goto _start;
}
else
{
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2147_){
_start:
{
uint8_t v_res_2148_; lean_object* v_r_2149_; 
v_res_2148_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2147_);
lean_dec(v_x_2147_);
v_r_2149_ = lean_box(v_res_2148_);
return v_r_2149_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2150_, lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
return v_x_2150_;
}
else
{
lean_object* v_head_2152_; lean_object* v_tail_2153_; uint64_t v___x_2154_; uint64_t v___x_2155_; 
v_head_2152_ = lean_ctor_get(v_x_2151_, 0);
v_tail_2153_ = lean_ctor_get(v_x_2151_, 1);
v___x_2154_ = l_Lean_Level_hash(v_head_2152_);
v___x_2155_ = lean_uint64_mix_hash(v_x_2150_, v___x_2154_);
v_x_2150_ = v___x_2155_;
v_x_2151_ = v_tail_2153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
uint64_t v_x_1716__boxed_2159_; uint64_t v_res_2160_; lean_object* v_r_2161_; 
v_x_1716__boxed_2159_ = lean_unbox_uint64(v_x_2157_);
lean_dec_ref(v_x_2157_);
v_res_2160_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1716__boxed_2159_, v_x_2158_);
lean_dec(v_x_2158_);
v_r_2161_ = lean_box_uint64(v_res_2160_);
return v_r_2161_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2162_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
uint8_t v___x_2163_; 
v___x_2163_ = 0;
return v___x_2163_;
}
else
{
lean_object* v_head_2164_; lean_object* v_tail_2165_; uint8_t v___x_2166_; 
v_head_2164_ = lean_ctor_get(v_x_2162_, 0);
v_tail_2165_ = lean_ctor_get(v_x_2162_, 1);
v___x_2166_ = l_Lean_Level_hasParam(v_head_2164_);
if (v___x_2166_ == 0)
{
v_x_2162_ = v_tail_2165_;
goto _start;
}
else
{
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2168_);
lean_dec(v_x_2168_);
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2171_, lean_object* v_us_2172_){
_start:
{
uint64_t v___x_2173_; uint64_t v___y_2175_; 
v___x_2173_ = 5ULL;
if (lean_obj_tag(v_declName_2171_) == 0)
{
uint64_t v___x_2187_; 
v___x_2187_ = 1723ULL;
v___y_2175_ = v___x_2187_;
goto v___jp_2174_;
}
else
{
uint64_t v_hash_2188_; 
v_hash_2188_ = lean_ctor_get_uint64(v_declName_2171_, sizeof(void*)*2);
v___y_2175_ = v_hash_2188_;
goto v___jp_2174_;
}
v___jp_2174_:
{
uint64_t v___x_2176_; uint64_t v___x_2177_; uint64_t v___x_2178_; uint64_t v___x_2179_; lean_object* v___x_2180_; uint32_t v___x_2181_; uint8_t v___x_2182_; uint8_t v___x_2183_; uint8_t v___x_2184_; uint64_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2176_ = 7ULL;
v___x_2177_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2176_, v_us_2172_);
v___x_2178_ = lean_uint64_mix_hash(v___y_2175_, v___x_2177_);
v___x_2179_ = lean_uint64_mix_hash(v___x_2173_, v___x_2178_);
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = 0;
v___x_2182_ = 0;
v___x_2183_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2172_);
v___x_2184_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2172_);
v___x_2185_ = lean_expr_mk_data(v___x_2179_, v___x_2180_, v___x_2181_, v___x_2182_, v___x_2182_, v___x_2183_, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2186_, 0, v_declName_2171_);
lean_ctor_set(v___x_2186_, 1, v_us_2172_);
lean_ctor_set_uint64(v___x_2186_, sizeof(void*)*2, v___x_2185_);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = l_Lean_instReprLevel_repr(v___y_2189_, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_dec(v_x_2192_);
return v_x_2193_;
}
else
{
lean_object* v_head_2195_; lean_object* v_tail_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2207_; 
v_head_2195_ = lean_ctor_get(v_x_2194_, 0);
v_tail_2196_ = lean_ctor_get(v_x_2194_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2198_ = v_x_2194_;
v_isShared_2199_ = v_isSharedCheck_2207_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_tail_2196_);
lean_inc(v_head_2195_);
lean_dec(v_x_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2207_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
lean_inc(v_x_2192_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 5);
lean_ctor_set(v___x_2198_, 1, v_x_2192_);
lean_ctor_set(v___x_2198_, 0, v_x_2193_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_x_2193_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_x_2192_);
v___x_2201_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = l_Lean_instReprLevel_repr(v_head_2195_, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2201_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v_x_2193_ = v___x_2204_;
v_x_2194_ = v_tail_2196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
if (lean_obj_tag(v_x_2210_) == 0)
{
lean_dec(v_x_2208_);
return v_x_2209_;
}
else
{
lean_object* v_head_2211_; lean_object* v_tail_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2223_; 
v_head_2211_ = lean_ctor_get(v_x_2210_, 0);
v_tail_2212_ = lean_ctor_get(v_x_2210_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_x_2210_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2214_ = v_x_2210_;
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_tail_2212_);
lean_inc(v_head_2211_);
lean_dec(v_x_2210_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
lean_inc(v_x_2208_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 5);
lean_ctor_set(v___x_2214_, 1, v_x_2208_);
lean_ctor_set(v___x_2214_, 0, v_x_2209_);
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_x_2209_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_x_2208_);
v___x_2217_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = l_Lean_instReprLevel_repr(v_head_2211_, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2217_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2208_, v___x_2220_, v_tail_2212_);
return v___x_2221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v___x_2226_; 
lean_dec(v_x_2225_);
v___x_2226_ = lean_box(0);
return v___x_2226_;
}
else
{
lean_object* v_tail_2227_; 
v_tail_2227_ = lean_ctor_get(v_x_2224_, 1);
if (lean_obj_tag(v_tail_2227_) == 0)
{
lean_object* v_head_2228_; lean_object* v___x_2229_; 
lean_dec(v_x_2225_);
v_head_2228_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_head_2228_);
lean_dec_ref_known(v_x_2224_, 2);
v___x_2229_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2228_);
return v___x_2229_;
}
else
{
lean_object* v_head_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_inc(v_tail_2227_);
v_head_2230_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_head_2230_);
lean_dec_ref_known(v_x_2224_, 2);
v___x_2231_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2230_);
v___x_2232_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2225_, v___x_2231_, v_tail_2227_);
return v___x_2232_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2245_ = lean_string_length(v___x_2244_);
return v___x_2245_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2247_ = lean_nat_to_int(v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2252_){
_start:
{
if (lean_obj_tag(v_a_2252_) == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; 
v___x_2254_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2255_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2252_, v___x_2254_);
v___x_2256_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2257_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2255_);
v___x_2259_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2256_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = 0;
v___x_2263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*1, v___x_2262_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2336_, lean_object* v_prec_2337_){
_start:
{
switch(lean_obj_tag(v_x_2336_))
{
case 0:
{
lean_object* v_deBruijnIndex_2338_; lean_object* v___y_2340_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v_deBruijnIndex_2338_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_deBruijnIndex_2338_);
lean_dec_ref_known(v_x_2336_, 1);
v___x_2349_ = lean_unsigned_to_nat(1024u);
v___x_2350_ = lean_nat_dec_le(v___x_2349_, v_prec_2337_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2340_ = v___x_2351_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2340_ = v___x_2352_;
goto v___jp_2339_;
}
v___jp_2339_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2341_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2342_ = l_Nat_reprFast(v_deBruijnIndex_2338_);
v___x_2343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
v___x_2344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2341_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
lean_inc(v___y_2340_);
v___x_2345_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___y_2340_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = 0;
v___x_2347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*1, v___x_2346_);
v___x_2348_ = l_Repr_addAppParen(v___x_2347_, v_prec_2337_);
return v___x_2348_;
}
}
case 1:
{
lean_object* v_fvarId_2353_; lean_object* v___y_2355_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_fvarId_2353_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_fvarId_2353_);
lean_dec_ref_known(v_x_2336_, 1);
v___x_2364_ = lean_unsigned_to_nat(1024u);
v___x_2365_ = lean_nat_dec_le(v___x_2364_, v_prec_2337_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2355_ = v___x_2366_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2355_ = v___x_2367_;
goto v___jp_2354_;
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2356_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2357_ = lean_unsigned_to_nat(1024u);
v___x_2358_ = l_Lean_Name_reprPrec(v_fvarId_2353_, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2356_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
lean_inc(v___y_2355_);
v___x_2360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___y_2355_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = 0;
v___x_2362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*1, v___x_2361_);
v___x_2363_ = l_Repr_addAppParen(v___x_2362_, v_prec_2337_);
return v___x_2363_;
}
}
case 2:
{
lean_object* v_mvarId_2368_; lean_object* v___y_2370_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_mvarId_2368_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_mvarId_2368_);
lean_dec_ref_known(v_x_2336_, 1);
v___x_2379_ = lean_unsigned_to_nat(1024u);
v___x_2380_ = lean_nat_dec_le(v___x_2379_, v_prec_2337_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2370_ = v___x_2381_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2370_ = v___x_2382_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2371_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2372_ = lean_unsigned_to_nat(1024u);
v___x_2373_ = l_Lean_Name_reprPrec(v_mvarId_2368_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
lean_inc(v___y_2370_);
v___x_2375_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___y_2370_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = 0;
v___x_2377_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set_uint8(v___x_2377_, sizeof(void*)*1, v___x_2376_);
v___x_2378_ = l_Repr_addAppParen(v___x_2377_, v_prec_2337_);
return v___x_2378_;
}
}
case 3:
{
lean_object* v_u_2383_; lean_object* v___y_2385_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_u_2383_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_u_2383_);
lean_dec_ref_known(v_x_2336_, 1);
v___x_2394_ = lean_unsigned_to_nat(1024u);
v___x_2395_ = lean_nat_dec_le(v___x_2394_, v_prec_2337_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2385_ = v___x_2396_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2385_ = v___x_2397_;
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2386_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2387_ = lean_unsigned_to_nat(1024u);
v___x_2388_ = l_Lean_instReprLevel_repr(v_u_2383_, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v___y_2385_);
v___x_2390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___y_2385_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = 0;
v___x_2392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*1, v___x_2391_);
v___x_2393_ = l_Repr_addAppParen(v___x_2392_, v_prec_2337_);
return v___x_2393_;
}
}
case 4:
{
lean_object* v_declName_2398_; lean_object* v_us_2399_; lean_object* v___y_2401_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_declName_2398_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_declName_2398_);
v_us_2399_ = lean_ctor_get(v_x_2336_, 1);
lean_inc(v_us_2399_);
lean_dec_ref_known(v_x_2336_, 2);
v___x_2414_ = lean_unsigned_to_nat(1024u);
v___x_2415_ = lean_nat_dec_le(v___x_2414_, v_prec_2337_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2401_ = v___x_2416_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2401_ = v___x_2417_;
goto v___jp_2400_;
}
v___jp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2402_ = lean_box(1);
v___x_2403_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2404_ = lean_unsigned_to_nat(1024u);
v___x_2405_ = l_Lean_Name_reprPrec(v_declName_2398_, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2403_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2402_);
v___x_2408_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2399_);
v___x_2409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
lean_inc(v___y_2401_);
v___x_2410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___y_2401_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = 0;
v___x_2412_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*1, v___x_2411_);
v___x_2413_ = l_Repr_addAppParen(v___x_2412_, v_prec_2337_);
return v___x_2413_;
}
}
case 5:
{
lean_object* v_fn_2418_; lean_object* v_arg_2419_; lean_object* v___x_2420_; lean_object* v___y_2422_; uint8_t v___x_2434_; 
v_fn_2418_ = lean_ctor_get(v_x_2336_, 0);
lean_inc_ref(v_fn_2418_);
v_arg_2419_ = lean_ctor_get(v_x_2336_, 1);
lean_inc_ref(v_arg_2419_);
lean_dec_ref_known(v_x_2336_, 2);
v___x_2420_ = lean_unsigned_to_nat(1024u);
v___x_2434_ = lean_nat_dec_le(v___x_2420_, v_prec_2337_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2422_ = v___x_2435_;
goto v___jp_2421_;
}
else
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2422_ = v___x_2436_;
goto v___jp_2421_;
}
v___jp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2423_ = lean_box(1);
v___x_2424_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2425_ = l_Lean_instReprExpr_repr(v_fn_2418_, v___x_2420_);
v___x_2426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_2423_);
v___x_2428_ = l_Lean_instReprExpr_repr(v_arg_2419_, v___x_2420_);
v___x_2429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
lean_inc(v___y_2422_);
v___x_2430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___y_2422_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = 0;
v___x_2432_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set_uint8(v___x_2432_, sizeof(void*)*1, v___x_2431_);
v___x_2433_ = l_Repr_addAppParen(v___x_2432_, v_prec_2337_);
return v___x_2433_;
}
}
case 6:
{
lean_object* v_binderName_2437_; lean_object* v_binderType_2438_; lean_object* v_body_2439_; uint8_t v_binderInfo_2440_; lean_object* v___x_2441_; lean_object* v___y_2443_; uint8_t v___x_2461_; 
v_binderName_2437_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_binderName_2437_);
v_binderType_2438_ = lean_ctor_get(v_x_2336_, 1);
lean_inc_ref(v_binderType_2438_);
v_body_2439_ = lean_ctor_get(v_x_2336_, 2);
lean_inc_ref(v_body_2439_);
v_binderInfo_2440_ = lean_ctor_get_uint8(v_x_2336_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2336_, 3);
v___x_2441_ = lean_unsigned_to_nat(1024u);
v___x_2461_ = lean_nat_dec_le(v___x_2441_, v_prec_2337_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2443_ = v___x_2462_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2443_ = v___x_2463_;
goto v___jp_2442_;
}
v___jp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2444_ = lean_box(1);
v___x_2445_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2446_ = l_Lean_Name_reprPrec(v_binderName_2437_, v___x_2441_);
v___x_2447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2444_);
v___x_2449_ = l_Lean_instReprExpr_repr(v_binderType_2438_, v___x_2441_);
v___x_2450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
lean_ctor_set(v___x_2451_, 1, v___x_2444_);
v___x_2452_ = l_Lean_instReprExpr_repr(v_body_2439_, v___x_2441_);
v___x_2453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
lean_ctor_set(v___x_2454_, 1, v___x_2444_);
v___x_2455_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2440_, v___x_2441_);
v___x_2456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_inc(v___y_2443_);
v___x_2457_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___y_2443_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = 0;
v___x_2459_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*1, v___x_2458_);
v___x_2460_ = l_Repr_addAppParen(v___x_2459_, v_prec_2337_);
return v___x_2460_;
}
}
case 7:
{
lean_object* v_binderName_2464_; lean_object* v_binderType_2465_; lean_object* v_body_2466_; uint8_t v_binderInfo_2467_; lean_object* v___x_2468_; lean_object* v___y_2470_; uint8_t v___x_2488_; 
v_binderName_2464_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_binderName_2464_);
v_binderType_2465_ = lean_ctor_get(v_x_2336_, 1);
lean_inc_ref(v_binderType_2465_);
v_body_2466_ = lean_ctor_get(v_x_2336_, 2);
lean_inc_ref(v_body_2466_);
v_binderInfo_2467_ = lean_ctor_get_uint8(v_x_2336_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2336_, 3);
v___x_2468_ = lean_unsigned_to_nat(1024u);
v___x_2488_ = lean_nat_dec_le(v___x_2468_, v_prec_2337_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2470_ = v___x_2489_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2470_ = v___x_2490_;
goto v___jp_2469_;
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2471_ = lean_box(1);
v___x_2472_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2473_ = l_Lean_Name_reprPrec(v_binderName_2464_, v___x_2468_);
v___x_2474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
lean_ctor_set(v___x_2475_, 1, v___x_2471_);
v___x_2476_ = l_Lean_instReprExpr_repr(v_binderType_2465_, v___x_2468_);
v___x_2477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___x_2471_);
v___x_2479_ = l_Lean_instReprExpr_repr(v_body_2466_, v___x_2468_);
v___x_2480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___x_2471_);
v___x_2482_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2467_, v___x_2468_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
lean_inc(v___y_2470_);
v___x_2484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___y_2470_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = 0;
v___x_2486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*1, v___x_2485_);
v___x_2487_ = l_Repr_addAppParen(v___x_2486_, v_prec_2337_);
return v___x_2487_;
}
}
case 8:
{
lean_object* v_declName_2491_; lean_object* v_type_2492_; lean_object* v_value_2493_; lean_object* v_body_2494_; uint8_t v_nondep_2495_; lean_object* v___x_2496_; lean_object* v___y_2498_; uint8_t v___x_2519_; 
v_declName_2491_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_declName_2491_);
v_type_2492_ = lean_ctor_get(v_x_2336_, 1);
lean_inc_ref(v_type_2492_);
v_value_2493_ = lean_ctor_get(v_x_2336_, 2);
lean_inc_ref(v_value_2493_);
v_body_2494_ = lean_ctor_get(v_x_2336_, 3);
lean_inc_ref(v_body_2494_);
v_nondep_2495_ = lean_ctor_get_uint8(v_x_2336_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2336_, 4);
v___x_2496_ = lean_unsigned_to_nat(1024u);
v___x_2519_ = lean_nat_dec_le(v___x_2496_, v_prec_2337_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2498_ = v___x_2520_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2498_ = v___x_2521_;
goto v___jp_2497_;
}
v___jp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2499_ = lean_box(1);
v___x_2500_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2501_ = l_Lean_Name_reprPrec(v_declName_2491_, v___x_2496_);
v___x_2502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___x_2499_);
v___x_2504_ = l_Lean_instReprExpr_repr(v_type_2492_, v___x_2496_);
v___x_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2499_);
v___x_2507_ = l_Lean_instReprExpr_repr(v_value_2493_, v___x_2496_);
v___x_2508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2499_);
v___x_2510_ = l_Lean_instReprExpr_repr(v_body_2494_, v___x_2496_);
v___x_2511_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___x_2499_);
v___x_2513_ = l_Bool_repr___redArg(v_nondep_2495_);
v___x_2514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
lean_inc(v___y_2498_);
v___x_2515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___y_2498_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = 0;
v___x_2517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set_uint8(v___x_2517_, sizeof(void*)*1, v___x_2516_);
v___x_2518_ = l_Repr_addAppParen(v___x_2517_, v_prec_2337_);
return v___x_2518_;
}
}
case 9:
{
lean_object* v_a_2522_; lean_object* v___y_2524_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_a_2522_ = lean_ctor_get(v_x_2336_, 0);
lean_inc_ref(v_a_2522_);
lean_dec_ref_known(v_x_2336_, 1);
v___x_2533_ = lean_unsigned_to_nat(1024u);
v___x_2534_ = lean_nat_dec_le(v___x_2533_, v_prec_2337_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2524_ = v___x_2535_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2524_ = v___x_2536_;
goto v___jp_2523_;
}
v___jp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2525_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2526_ = lean_unsigned_to_nat(1024u);
v___x_2527_ = l_Lean_instReprLiteral_repr(v_a_2522_, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2525_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_inc(v___y_2524_);
v___x_2529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___y_2524_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = 0;
v___x_2531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set_uint8(v___x_2531_, sizeof(void*)*1, v___x_2530_);
v___x_2532_ = l_Repr_addAppParen(v___x_2531_, v_prec_2337_);
return v___x_2532_;
}
}
case 10:
{
lean_object* v_data_2537_; lean_object* v_expr_2538_; lean_object* v___x_2539_; lean_object* v___y_2541_; uint8_t v___x_2553_; 
v_data_2537_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_data_2537_);
v_expr_2538_ = lean_ctor_get(v_x_2336_, 1);
lean_inc_ref(v_expr_2538_);
lean_dec_ref_known(v_x_2336_, 2);
v___x_2539_ = lean_unsigned_to_nat(1024u);
v___x_2553_ = lean_nat_dec_le(v___x_2539_, v_prec_2337_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2541_ = v___x_2554_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2541_ = v___x_2555_;
goto v___jp_2540_;
}
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2542_ = lean_box(1);
v___x_2543_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2544_ = l_Lean_instReprKVMap_repr___redArg(v_data_2537_);
v___x_2545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2542_);
v___x_2547_ = l_Lean_instReprExpr_repr(v_expr_2538_, v___x_2539_);
v___x_2548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
lean_inc(v___y_2541_);
v___x_2549_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___y_2541_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = 0;
v___x_2551_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set_uint8(v___x_2551_, sizeof(void*)*1, v___x_2550_);
v___x_2552_ = l_Repr_addAppParen(v___x_2551_, v_prec_2337_);
return v___x_2552_;
}
}
default: 
{
lean_object* v_typeName_2556_; lean_object* v_idx_2557_; lean_object* v_struct_2558_; lean_object* v___x_2559_; lean_object* v___y_2561_; uint8_t v___x_2577_; 
v_typeName_2556_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_typeName_2556_);
v_idx_2557_ = lean_ctor_get(v_x_2336_, 1);
lean_inc(v_idx_2557_);
v_struct_2558_ = lean_ctor_get(v_x_2336_, 2);
lean_inc_ref(v_struct_2558_);
lean_dec_ref_known(v_x_2336_, 3);
v___x_2559_ = lean_unsigned_to_nat(1024u);
v___x_2577_ = lean_nat_dec_le(v___x_2559_, v_prec_2337_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2561_ = v___x_2578_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2561_ = v___x_2579_;
goto v___jp_2560_;
}
v___jp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2562_ = lean_box(1);
v___x_2563_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2564_ = l_Lean_Name_reprPrec(v_typeName_2556_, v___x_2559_);
v___x_2565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v___x_2562_);
v___x_2567_ = l_Nat_reprFast(v_idx_2557_);
v___x_2568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
v___x_2569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2566_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v___x_2562_);
v___x_2571_ = l_Lean_instReprExpr_repr(v_struct_2558_, v___x_2559_);
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_inc(v___y_2561_);
v___x_2573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2561_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = 0;
v___x_2575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*1, v___x_2574_);
v___x_2576_ = l_Repr_addAppParen(v___x_2575_, v_prec_2337_);
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2580_, lean_object* v_prec_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_instReprExpr_repr(v_x_2580_, v_prec_2581_);
lean_dec(v_prec_2581_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_nat_to_int(v_a_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2585_, lean_object* v_n_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2588_, lean_object* v_n_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2588_, v_n_2589_);
lean_dec(v_n_2589_);
return v_res_2590_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_box(0);
v___x_2597_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2598_ = l_Lean_Expr_const___override(v___x_2597_, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2612_){
_start:
{
switch(lean_obj_tag(v_x_2612_))
{
case 0:
{
lean_object* v___x_2613_; 
v___x_2613_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2613_;
}
case 1:
{
lean_object* v___x_2614_; 
v___x_2614_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2614_;
}
case 2:
{
lean_object* v___x_2615_; 
v___x_2615_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2615_;
}
case 3:
{
lean_object* v___x_2616_; 
v___x_2616_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2616_;
}
case 4:
{
lean_object* v___x_2617_; 
v___x_2617_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2617_;
}
case 5:
{
lean_object* v___x_2618_; 
v___x_2618_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2618_;
}
case 6:
{
lean_object* v___x_2619_; 
v___x_2619_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2619_;
}
case 7:
{
lean_object* v___x_2620_; 
v___x_2620_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2620_;
}
case 8:
{
lean_object* v___x_2621_; 
v___x_2621_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2621_;
}
case 9:
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2622_;
}
case 10:
{
lean_object* v___x_2623_; 
v___x_2623_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2623_;
}
default: 
{
lean_object* v___x_2624_; 
v___x_2624_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Expr_ctorName(v_x_2625_);
lean_dec_ref(v_x_2625_);
return v_res_2626_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2627_){
_start:
{
uint64_t v___x_2628_; uint64_t v___x_2629_; 
v___x_2628_ = lean_expr_data(v_e_2627_);
v___x_2629_ = l_Lean_Expr_Data_hash(v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2630_){
_start:
{
uint64_t v_res_2631_; lean_object* v_r_2632_; 
v_res_2631_ = l_Lean_Expr_hash(v_e_2630_);
lean_dec_ref(v_e_2630_);
v_r_2632_ = lean_box_uint64(v_res_2631_);
return v_r_2632_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2635_){
_start:
{
uint64_t v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = lean_expr_data(v_e_2635_);
v___x_2637_ = l_Lean_Expr_Data_hasFVar(v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2638_){
_start:
{
uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_res_2639_ = l_Lean_Expr_hasFVar(v_e_2638_);
lean_dec_ref(v_e_2638_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2641_){
_start:
{
uint64_t v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = lean_expr_data(v_e_2641_);
v___x_2643_ = l_Lean_Expr_Data_hasExprMVar(v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Lean_Expr_hasExprMVar(v_e_2644_);
lean_dec_ref(v_e_2644_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2647_){
_start:
{
uint64_t v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = lean_expr_data(v_e_2647_);
v___x_2649_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Lean_Expr_hasLevelMVar(v_e_2650_);
lean_dec_ref(v_e_2650_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2653_){
_start:
{
uint64_t v_d_2654_; uint8_t v___x_2655_; 
v_d_2654_ = lean_expr_data(v_e_2653_);
v___x_2655_ = l_Lean_Expr_Data_hasExprMVar(v_d_2654_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; 
v___x_2656_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2654_);
return v___x_2656_;
}
else
{
return v___x_2655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = l_Lean_Expr_hasMVar(v_e_2657_);
lean_dec_ref(v_e_2657_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2660_){
_start:
{
uint64_t v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_expr_data(v_e_2660_);
v___x_2662_ = l_Lean_Expr_Data_hasLevelParam(v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Lean_Expr_hasLevelParam(v_e_2663_);
lean_dec_ref(v_e_2663_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2666_){
_start:
{
uint64_t v___x_2667_; uint8_t v___x_2668_; uint32_t v___x_2669_; 
v___x_2667_ = lean_expr_data(v_e_2666_);
v___x_2668_ = l_Lean_Expr_Data_approxDepth(v___x_2667_);
v___x_2669_ = lean_uint8_to_uint32(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2670_){
_start:
{
uint32_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_Lean_Expr_approxDepth(v_e_2670_);
lean_dec_ref(v_e_2670_);
v_r_2672_ = lean_box_uint32(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2673_){
_start:
{
uint64_t v___x_2674_; uint32_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_expr_data(v_e_2673_);
v___x_2675_ = l_Lean_Expr_Data_looseBVarRange(v___x_2674_);
v___x_2676_ = lean_uint32_to_nat(v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Expr_looseBVarRange(v_e_2677_);
lean_dec_ref(v_e_2677_);
return v_res_2678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2679_){
_start:
{
switch(lean_obj_tag(v_e_2679_))
{
case 7:
{
uint8_t v_binderInfo_2680_; 
v_binderInfo_2680_ = lean_ctor_get_uint8(v_e_2679_, sizeof(void*)*3 + 8);
return v_binderInfo_2680_;
}
case 6:
{
uint8_t v_binderInfo_2681_; 
v_binderInfo_2681_ = lean_ctor_get_uint8(v_e_2679_, sizeof(void*)*3 + 8);
return v_binderInfo_2681_;
}
default: 
{
uint8_t v___x_2682_; 
v___x_2682_ = 0;
return v___x_2682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2683_){
_start:
{
uint8_t v_res_2684_; lean_object* v_r_2685_; 
v_res_2684_ = l_Lean_Expr_binderInfo(v_e_2683_);
lean_dec_ref(v_e_2683_);
v_r_2685_ = lean_box(v_res_2684_);
return v_r_2685_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2686_){
_start:
{
uint64_t v___x_2687_; 
v___x_2687_ = l_Lean_Expr_hash(v_a_2686_);
lean_dec_ref(v_a_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2688_){
_start:
{
uint64_t v_res_2689_; lean_object* v_r_2690_; 
v_res_2689_ = lean_expr_hash(v_a_2688_);
v_r_2690_ = lean_box_uint64(v_res_2689_);
return v_r_2690_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2691_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = l_Lean_Expr_hasFVar(v_e_2691_);
lean_dec_ref(v_e_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = lean_expr_has_fvar(v_e_2693_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2696_){
_start:
{
uint8_t v___x_2697_; 
v___x_2697_ = l_Lean_Expr_hasExprMVar(v_e_2696_);
lean_dec_ref(v_e_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = lean_expr_has_expr_mvar(v_e_2698_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2701_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = l_Lean_Expr_hasLevelMVar(v_e_2701_);
lean_dec_ref(v_e_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2703_){
_start:
{
uint8_t v_res_2704_; lean_object* v_r_2705_; 
v_res_2704_ = lean_expr_has_level_mvar(v_e_2703_);
v_r_2705_ = lean_box(v_res_2704_);
return v_r_2705_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2706_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = l_Lean_Expr_hasLevelParam(v_e_2706_);
lean_dec_ref(v_e_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2708_){
_start:
{
uint8_t v_res_2709_; lean_object* v_r_2710_; 
v_res_2709_ = lean_expr_has_level_param(v_e_2708_);
v_r_2710_ = lean_box(v_res_2709_);
return v_r_2710_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2711_){
_start:
{
uint64_t v___x_2712_; uint32_t v___x_2713_; 
v___x_2712_ = lean_expr_data(v_e_2711_);
lean_dec_ref(v_e_2711_);
v___x_2713_ = l_Lean_Expr_Data_looseBVarRange(v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2714_){
_start:
{
uint32_t v_res_2715_; lean_object* v_r_2716_; 
v_res_2715_ = lean_expr_loose_bvar_range(v_e_2714_);
v_r_2716_ = lean_box_uint32(v_res_2715_);
return v_r_2716_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2717_){
_start:
{
uint8_t v___x_2718_; 
v___x_2718_ = l_Lean_Expr_binderInfo(v_e_2717_);
lean_dec_ref(v_e_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = lean_expr_binder_info(v_e_2719_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2722_, lean_object* v_us_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Expr_const___override(v_declName_2722_, v_us_2723_);
return v___x_2724_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = lean_box(0);
v___x_2729_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2730_ = l_Lean_Expr_const___override(v___x_2729_, v___x_2728_);
return v___x_2730_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_box(0);
v___x_2735_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2736_ = l_Lean_Expr_const___override(v___x_2735_, v___x_2734_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2737_){
_start:
{
if (lean_obj_tag(v_x_2737_) == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Literal_type(v_x_2740_);
lean_dec_ref(v_x_2740_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Literal_type(v_a_2742_);
lean_dec_ref(v_a_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Expr_bvar___override(v_idx_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Expr_sort___override(v_u_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Expr_fvar___override(v_fvarId_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Expr_mvar___override(v_mvarId_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2752_, lean_object* v_e_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_Expr_mdata___override(v_m_2752_, v_e_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2755_, lean_object* v_idx_2756_, lean_object* v_struct_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Expr_proj___override(v_structName_2755_, v_idx_2756_, v_struct_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Expr_app___override(v_f_2759_, v_a_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2762_, uint8_t v_bi_2763_, lean_object* v_t_2764_, lean_object* v_b_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Expr_lam___override(v_x_2762_, v_t_2764_, v_b_2765_, v_bi_2763_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2767_, lean_object* v_bi_2768_, lean_object* v_t_2769_, lean_object* v_b_2770_){
_start:
{
uint8_t v_bi_boxed_2771_; lean_object* v_res_2772_; 
v_bi_boxed_2771_ = lean_unbox(v_bi_2768_);
v_res_2772_ = l_Lean_mkLambda(v_x_2767_, v_bi_boxed_2771_, v_t_2769_, v_b_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2773_, uint8_t v_bi_2774_, lean_object* v_t_2775_, lean_object* v_b_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Expr_forallE___override(v_x_2773_, v_t_2775_, v_b_2776_, v_bi_2774_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2778_, lean_object* v_bi_2779_, lean_object* v_t_2780_, lean_object* v_b_2781_){
_start:
{
uint8_t v_bi_boxed_2782_; lean_object* v_res_2783_; 
v_bi_boxed_2782_ = lean_unbox(v_bi_2779_);
v_res_2783_ = l_Lean_mkForall(v_x_2778_, v_bi_boxed_2782_, v_t_2780_, v_b_2781_);
return v_res_2783_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = lean_box(0);
v___x_2791_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2792_ = l_Lean_Expr_const___override(v___x_2791_, v___x_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2793_){
_start:
{
lean_object* v___x_2794_; uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2794_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2795_ = 0;
v___x_2796_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2797_ = l_Lean_Expr_forallE___override(v___x_2794_, v___x_2796_, v_type_2793_, v___x_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2798_){
_start:
{
lean_object* v___x_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2799_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2800_ = 0;
v___x_2801_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2802_ = l_Lean_Expr_lam___override(v___x_2799_, v___x_2801_, v_type_2798_, v___x_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2803_, lean_object* v_t_2804_, lean_object* v_v_2805_, lean_object* v_b_2806_, uint8_t v_nondep_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Expr_letE___override(v_x_2803_, v_t_2804_, v_v_2805_, v_b_2806_, v_nondep_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2809_, lean_object* v_t_2810_, lean_object* v_v_2811_, lean_object* v_b_2812_, lean_object* v_nondep_2813_){
_start:
{
uint8_t v_nondep_boxed_2814_; lean_object* v_res_2815_; 
v_nondep_boxed_2814_ = lean_unbox(v_nondep_2813_);
v_res_2815_ = l_Lean_mkLet(v_x_2809_, v_t_2810_, v_v_2811_, v_b_2812_, v_nondep_boxed_2814_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2816_, lean_object* v_t_2817_, lean_object* v_v_2818_, lean_object* v_b_2819_){
_start:
{
uint8_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = 1;
v___x_2821_ = l_Lean_Expr_letE___override(v_x_2816_, v_t_2817_, v_v_2818_, v_b_2819_, v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2822_, lean_object* v_a_2823_, lean_object* v_b_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = l_Lean_Expr_app___override(v_f_2822_, v_a_2823_);
v___x_2826_ = l_Lean_Expr_app___override(v___x_2825_, v_b_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2827_, lean_object* v_a_2828_, lean_object* v_b_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_mkAppB(v_f_2827_, v_a_2828_, v_b_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_, lean_object* v_c_2834_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = l_Lean_mkAppB(v_f_2831_, v_a_2832_, v_b_2833_);
v___x_2836_ = l_Lean_Expr_app___override(v___x_2835_, v_c_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_, lean_object* v_c_2840_, lean_object* v_d_2841_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = l_Lean_mkAppB(v_f_2837_, v_a_2838_, v_b_2839_);
v___x_2843_ = l_Lean_mkAppB(v___x_2842_, v_c_2840_, v_d_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2844_, lean_object* v_a_2845_, lean_object* v_b_2846_, lean_object* v_c_2847_, lean_object* v_d_2848_, lean_object* v_e_2849_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = l_Lean_mkApp4(v_f_2844_, v_a_2845_, v_b_2846_, v_c_2847_, v_d_2848_);
v___x_2851_ = l_Lean_Expr_app___override(v___x_2850_, v_e_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2852_, lean_object* v_a_2853_, lean_object* v_b_2854_, lean_object* v_c_2855_, lean_object* v_d_2856_, lean_object* v_e_u2081_2857_, lean_object* v_e_u2082_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = l_Lean_mkApp4(v_f_2852_, v_a_2853_, v_b_2854_, v_c_2855_, v_d_2856_);
v___x_2860_ = l_Lean_mkAppB(v___x_2859_, v_e_u2081_2857_, v_e_u2082_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2861_, lean_object* v_a_2862_, lean_object* v_b_2863_, lean_object* v_c_2864_, lean_object* v_d_2865_, lean_object* v_e_u2081_2866_, lean_object* v_e_u2082_2867_, lean_object* v_e_u2083_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = l_Lean_mkApp4(v_f_2861_, v_a_2862_, v_b_2863_, v_c_2864_, v_d_2865_);
v___x_2870_ = l_Lean_mkApp3(v___x_2869_, v_e_u2081_2866_, v_e_u2082_2867_, v_e_u2083_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2871_, lean_object* v_a_2872_, lean_object* v_b_2873_, lean_object* v_c_2874_, lean_object* v_d_2875_, lean_object* v_e_u2081_2876_, lean_object* v_e_u2082_2877_, lean_object* v_e_u2083_2878_, lean_object* v_e_u2084_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = l_Lean_mkApp4(v_f_2871_, v_a_2872_, v_b_2873_, v_c_2874_, v_d_2875_);
v___x_2881_ = l_Lean_mkApp4(v___x_2880_, v_e_u2081_2876_, v_e_u2082_2877_, v_e_u2083_2878_, v_e_u2084_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2882_, lean_object* v_a_2883_, lean_object* v_b_2884_, lean_object* v_c_2885_, lean_object* v_d_2886_, lean_object* v_e_u2081_2887_, lean_object* v_e_u2082_2888_, lean_object* v_e_u2083_2889_, lean_object* v_e_u2084_2890_, lean_object* v_e_u2085_2891_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = l_Lean_mkApp4(v_f_2882_, v_a_2883_, v_b_2884_, v_c_2885_, v_d_2886_);
v___x_2893_ = l_Lean_mkApp5(v___x_2892_, v_e_u2081_2887_, v_e_u2082_2888_, v_e_u2083_2889_, v_e_u2084_2890_, v_e_u2085_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2894_, lean_object* v_a_2895_, lean_object* v_b_2896_, lean_object* v_c_2897_, lean_object* v_d_2898_, lean_object* v_e_u2081_2899_, lean_object* v_e_u2082_2900_, lean_object* v_e_u2083_2901_, lean_object* v_e_u2084_2902_, lean_object* v_e_u2085_2903_, lean_object* v_e_u2086_2904_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = l_Lean_mkApp4(v_f_2894_, v_a_2895_, v_b_2896_, v_c_2897_, v_d_2898_);
v___x_2906_ = l_Lean_mkApp6(v___x_2905_, v_e_u2081_2899_, v_e_u2082_2900_, v_e_u2083_2901_, v_e_u2084_2902_, v_e_u2085_2903_, v_e_u2086_2904_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Expr_lit___override(v_l_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2909_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_n_2909_);
v___x_2911_ = l_Lean_Expr_lit___override(v___x_2910_);
return v___x_2911_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_box(0);
v___x_2916_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2917_ = l_Lean_Expr_const___override(v___x_2916_, v___x_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2918_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2920_ = l_Lean_Expr_app___override(v___x_2919_, v_n_2918_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2930_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2931_ = l_Lean_Expr_const___override(v___x_2930_, v___x_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2932_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2934_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2932_);
v___x_2935_ = l_Lean_mkInstOfNatNat(v_n_2932_);
v___x_2936_ = l_Lean_mkApp3(v___x_2933_, v___x_2934_, v_n_2932_, v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = l_Lean_mkRawNatLit(v_n_2937_);
v___x_2939_ = l_Lean_mkNatLitCore(v___x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_s_2940_);
v___x_2942_ = l_Lean_Expr_lit___override(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Expr_bvar___override(v_idx_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Expr_fvar___override(v_fvarId_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Expr_mvar___override(v_mvarId_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Expr_sort___override(v_u_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2951_, lean_object* v_lvls_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Expr_const___override(v_c_2951_, v_lvls_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Expr_app___override(v_f_2954_, v_a_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2957_, lean_object* v_d_2958_, lean_object* v_b_2959_, uint8_t v_bi_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Expr_lam___override(v_n_2957_, v_d_2958_, v_b_2959_, v_bi_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2962_, lean_object* v_d_2963_, lean_object* v_b_2964_, lean_object* v_bi_2965_){
_start:
{
uint8_t v_bi_boxed_2966_; lean_object* v_res_2967_; 
v_bi_boxed_2966_ = lean_unbox(v_bi_2965_);
v_res_2967_ = lean_expr_mk_lambda(v_n_2962_, v_d_2963_, v_b_2964_, v_bi_boxed_2966_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2968_, lean_object* v_d_2969_, lean_object* v_b_2970_, uint8_t v_bi_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Expr_forallE___override(v_n_2968_, v_d_2969_, v_b_2970_, v_bi_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2973_, lean_object* v_d_2974_, lean_object* v_b_2975_, lean_object* v_bi_2976_){
_start:
{
uint8_t v_bi_boxed_2977_; lean_object* v_res_2978_; 
v_bi_boxed_2977_ = lean_unbox(v_bi_2976_);
v_res_2978_ = lean_expr_mk_forall(v_n_2973_, v_d_2974_, v_b_2975_, v_bi_boxed_2977_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2979_, lean_object* v_t_2980_, lean_object* v_v_2981_, lean_object* v_b_2982_, uint8_t v_nondep_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Expr_letE___override(v_n_2979_, v_t_2980_, v_v_2981_, v_b_2982_, v_nondep_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2985_, lean_object* v_t_2986_, lean_object* v_v_2987_, lean_object* v_b_2988_, lean_object* v_nondep_2989_){
_start:
{
uint8_t v_nondep_boxed_2990_; lean_object* v_res_2991_; 
v_nondep_boxed_2990_ = lean_unbox(v_nondep_2989_);
v_res_2991_ = lean_expr_mk_let(v_n_2985_, v_t_2986_, v_v_2987_, v_b_2988_, v_nondep_boxed_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_Expr_lit___override(v_l_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2994_, lean_object* v_e_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Expr_mdata___override(v_m_2994_, v_e_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2997_, lean_object* v_idx_2998_, lean_object* v_struct_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Expr_proj___override(v_structName_2997_, v_idx_2998_, v_struct_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_3001_, size_t v_i_3002_, size_t v_stop_3003_, lean_object* v_b_3004_){
_start:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_usize_dec_eq(v_i_3002_, v_stop_3003_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; size_t v___x_3008_; size_t v___x_3009_; 
v___x_3006_ = lean_array_uget_borrowed(v_as_3001_, v_i_3002_);
lean_inc(v___x_3006_);
v___x_3007_ = l_Lean_Expr_app___override(v_b_3004_, v___x_3006_);
v___x_3008_ = ((size_t)1ULL);
v___x_3009_ = lean_usize_add(v_i_3002_, v___x_3008_);
v_i_3002_ = v___x_3009_;
v_b_3004_ = v___x_3007_;
goto _start;
}
else
{
return v_b_3004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3011_, lean_object* v_i_3012_, lean_object* v_stop_3013_, lean_object* v_b_3014_){
_start:
{
size_t v_i_boxed_3015_; size_t v_stop_boxed_3016_; lean_object* v_res_3017_; 
v_i_boxed_3015_ = lean_unbox_usize(v_i_3012_);
lean_dec(v_i_3012_);
v_stop_boxed_3016_ = lean_unbox_usize(v_stop_3013_);
lean_dec(v_stop_3013_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3011_, v_i_boxed_3015_, v_stop_boxed_3016_, v_b_3014_);
lean_dec_ref(v_as_3011_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3018_, lean_object* v_args_3019_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_array_get_size(v_args_3019_);
v___x_3022_ = lean_nat_dec_lt(v___x_3020_, v___x_3021_);
if (v___x_3022_ == 0)
{
return v_f_3018_;
}
else
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_nat_dec_le(v___x_3021_, v___x_3021_);
if (v___x_3023_ == 0)
{
if (v___x_3022_ == 0)
{
return v_f_3018_;
}
else
{
size_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = lean_usize_of_nat(v___x_3021_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3019_, v___x_3024_, v___x_3025_, v_f_3018_);
return v___x_3026_;
}
}
else
{
size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = ((size_t)0ULL);
v___x_3028_ = lean_usize_of_nat(v___x_3021_);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3019_, v___x_3027_, v___x_3028_, v_f_3018_);
return v___x_3029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3030_, lean_object* v_args_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_mkAppN(v_f_3030_, v_args_3031_);
lean_dec_ref(v_args_3031_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3033_, lean_object* v_args_3034_, lean_object* v_i_3035_, lean_object* v_e_3036_){
_start:
{
uint8_t v___x_3037_; 
v___x_3037_ = lean_nat_dec_lt(v_i_3035_, v_n_3033_);
if (v___x_3037_ == 0)
{
lean_dec(v_i_3035_);
return v_e_3036_;
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3038_ = lean_unsigned_to_nat(1u);
v___x_3039_ = lean_nat_add(v_i_3035_, v___x_3038_);
v___x_3040_ = l_Lean_instInhabitedExpr;
v___x_3041_ = lean_array_get_borrowed(v___x_3040_, v_args_3034_, v_i_3035_);
lean_dec(v_i_3035_);
lean_inc(v___x_3041_);
v___x_3042_ = l_Lean_Expr_app___override(v_e_3036_, v___x_3041_);
v_i_3035_ = v___x_3039_;
v_e_3036_ = v___x_3042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3044_, lean_object* v_args_3045_, lean_object* v_i_3046_, lean_object* v_e_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3044_, v_args_3045_, v_i_3046_, v_e_3047_);
lean_dec_ref(v_args_3045_);
lean_dec(v_n_3044_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3049_, lean_object* v_i_3050_, lean_object* v_j_3051_, lean_object* v_args_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3051_, v_args_3052_, v_i_3050_, v_f_3049_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3054_, lean_object* v_i_3055_, lean_object* v_j_3056_, lean_object* v_args_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_mkAppRange(v_f_3054_, v_i_3055_, v_j_3056_, v_args_3057_);
lean_dec_ref(v_args_3057_);
lean_dec(v_j_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3059_, size_t v_i_3060_, size_t v_stop_3061_, lean_object* v_b_3062_){
_start:
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_usize_dec_eq(v_i_3060_, v_stop_3061_);
if (v___x_3063_ == 0)
{
size_t v___x_3064_; size_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3064_ = ((size_t)1ULL);
v___x_3065_ = lean_usize_sub(v_i_3060_, v___x_3064_);
v___x_3066_ = lean_array_uget_borrowed(v_as_3059_, v___x_3065_);
lean_inc(v___x_3066_);
v___x_3067_ = l_Lean_Expr_app___override(v_b_3062_, v___x_3066_);
v_i_3060_ = v___x_3065_;
v_b_3062_ = v___x_3067_;
goto _start;
}
else
{
return v_b_3062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3069_, lean_object* v_i_3070_, lean_object* v_stop_3071_, lean_object* v_b_3072_){
_start:
{
size_t v_i_boxed_3073_; size_t v_stop_boxed_3074_; lean_object* v_res_3075_; 
v_i_boxed_3073_ = lean_unbox_usize(v_i_3070_);
lean_dec(v_i_3070_);
v_stop_boxed_3074_ = lean_unbox_usize(v_stop_3071_);
lean_dec(v_stop_3071_);
v_res_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3069_, v_i_boxed_3073_, v_stop_boxed_3074_, v_b_3072_);
lean_dec_ref(v_as_3069_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3076_, lean_object* v_revArgs_3077_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3078_ = lean_array_get_size(v_revArgs_3077_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = lean_nat_dec_lt(v___x_3079_, v___x_3078_);
if (v___x_3080_ == 0)
{
return v_fn_3076_;
}
else
{
size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_usize_of_nat(v___x_3078_);
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3077_, v___x_3081_, v___x_3082_, v_fn_3076_);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3084_, lean_object* v_revArgs_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_mkAppRev(v_fn_3084_, v_revArgs_3085_);
lean_dec_ref(v_revArgs_3085_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = lean_expr_dbg_to_string(v_e_3088_);
lean_dec_ref(v_e_3088_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3092_, lean_object* v_b_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = lean_expr_quick_lt(v_a_3092_, v_b_3093_);
lean_dec_ref(v_b_3093_);
lean_dec_ref(v_a_3092_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3098_, lean_object* v_b_3099_){
_start:
{
uint8_t v_res_3100_; lean_object* v_r_3101_; 
v_res_3100_ = lean_expr_lt(v_a_3098_, v_b_3099_);
lean_dec_ref(v_b_3099_);
lean_dec_ref(v_a_3098_);
v_r_3101_ = lean_box(v_res_3100_);
return v_r_3101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3102_, lean_object* v_b_3103_){
_start:
{
uint8_t v___x_3104_; 
v___x_3104_ = lean_expr_quick_lt(v_a_3102_, v_b_3103_);
if (v___x_3104_ == 0)
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_expr_quick_lt(v_b_3103_, v_a_3102_);
if (v___x_3105_ == 0)
{
uint8_t v___x_3106_; 
v___x_3106_ = 1;
return v___x_3106_;
}
else
{
uint8_t v___x_3107_; 
v___x_3107_ = 2;
return v___x_3107_;
}
}
else
{
uint8_t v___x_3108_; 
v___x_3108_ = 0;
return v___x_3108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3109_, lean_object* v_b_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = l_Lean_Expr_quickComp(v_a_3109_, v_b_3110_);
lean_dec_ref(v_b_3110_);
lean_dec_ref(v_a_3109_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3115_, lean_object* v_b_3116_){
_start:
{
uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_res_3117_ = lean_expr_eqv(v_a_3115_, v_b_3116_);
lean_dec_ref(v_b_3116_);
lean_dec_ref(v_a_3115_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3123_, lean_object* v_b_3124_){
_start:
{
uint8_t v_res_3125_; lean_object* v_r_3126_; 
v_res_3125_ = lean_expr_equal(v_a_3123_, v_b_3124_);
lean_dec_ref(v_b_3124_);
lean_dec_ref(v_a_3123_);
v_r_3126_ = lean_box(v_res_3125_);
return v_r_3126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3127_){
_start:
{
if (lean_obj_tag(v_x_3127_) == 3)
{
uint8_t v___x_3128_; 
v___x_3128_ = 1;
return v___x_3128_;
}
else
{
uint8_t v___x_3129_; 
v___x_3129_ = 0;
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3130_){
_start:
{
uint8_t v_res_3131_; lean_object* v_r_3132_; 
v_res_3131_ = l_Lean_Expr_isSort(v_x_3130_);
lean_dec_ref(v_x_3130_);
v_r_3132_ = lean_box(v_res_3131_);
return v_r_3132_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3133_){
_start:
{
if (lean_obj_tag(v_x_3133_) == 3)
{
lean_object* v_u_3134_; 
v_u_3134_ = lean_ctor_get(v_x_3133_, 0);
if (lean_obj_tag(v_u_3134_) == 1)
{
uint8_t v___x_3135_; 
v___x_3135_ = 1;
return v___x_3135_;
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = 0;
return v___x_3136_;
}
}
else
{
uint8_t v___x_3137_; 
v___x_3137_ = 0;
return v___x_3137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3138_){
_start:
{
uint8_t v_res_3139_; lean_object* v_r_3140_; 
v_res_3139_ = l_Lean_Expr_isType(v_x_3138_);
lean_dec_ref(v_x_3138_);
v_r_3140_ = lean_box(v_res_3139_);
return v_r_3140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3141_){
_start:
{
if (lean_obj_tag(v_x_3141_) == 3)
{
lean_object* v_u_3142_; 
v_u_3142_ = lean_ctor_get(v_x_3141_, 0);
if (lean_obj_tag(v_u_3142_) == 1)
{
lean_object* v_a_3143_; 
v_a_3143_ = lean_ctor_get(v_u_3142_, 0);
if (lean_obj_tag(v_a_3143_) == 0)
{
uint8_t v___x_3144_; 
v___x_3144_ = 1;
return v___x_3144_;
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = 0;
return v___x_3145_;
}
}
else
{
uint8_t v___x_3146_; 
v___x_3146_ = 0;
return v___x_3146_;
}
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3148_){
_start:
{
uint8_t v_res_3149_; lean_object* v_r_3150_; 
v_res_3149_ = l_Lean_Expr_isType0(v_x_3148_);
lean_dec_ref(v_x_3148_);
v_r_3150_ = lean_box(v_res_3149_);
return v_r_3150_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3151_){
_start:
{
if (lean_obj_tag(v_x_3151_) == 3)
{
lean_object* v_u_3152_; 
v_u_3152_ = lean_ctor_get(v_x_3151_, 0);
if (lean_obj_tag(v_u_3152_) == 0)
{
uint8_t v___x_3153_; 
v___x_3153_ = 1;
return v___x_3153_;
}
else
{
uint8_t v___x_3154_; 
v___x_3154_ = 0;
return v___x_3154_;
}
}
else
{
uint8_t v___x_3155_; 
v___x_3155_ = 0;
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3156_){
_start:
{
uint8_t v_res_3157_; lean_object* v_r_3158_; 
v_res_3157_ = l_Lean_Expr_isProp(v_x_3156_);
lean_dec_ref(v_x_3156_);
v_r_3158_ = lean_box(v_res_3157_);
return v_r_3158_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3159_) == 0)
{
uint8_t v___x_3160_; 
v___x_3160_ = 1;
return v___x_3160_;
}
else
{
uint8_t v___x_3161_; 
v___x_3161_ = 0;
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3162_){
_start:
{
uint8_t v_res_3163_; lean_object* v_r_3164_; 
v_res_3163_ = l_Lean_Expr_isBVar(v_x_3162_);
lean_dec_ref(v_x_3162_);
v_r_3164_ = lean_box(v_res_3163_);
return v_r_3164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3165_){
_start:
{
if (lean_obj_tag(v_x_3165_) == 2)
{
uint8_t v___x_3166_; 
v___x_3166_ = 1;
return v___x_3166_;
}
else
{
uint8_t v___x_3167_; 
v___x_3167_ = 0;
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3168_){
_start:
{
uint8_t v_res_3169_; lean_object* v_r_3170_; 
v_res_3169_ = l_Lean_Expr_isMVar(v_x_3168_);
lean_dec_ref(v_x_3168_);
v_r_3170_ = lean_box(v_res_3169_);
return v_r_3170_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 1)
{
uint8_t v___x_3172_; 
v___x_3172_ = 1;
return v___x_3172_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = 0;
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3174_){
_start:
{
uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_res_3175_ = l_Lean_Expr_isFVar(v_x_3174_);
lean_dec_ref(v_x_3174_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3177_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 5)
{
uint8_t v___x_3178_; 
v___x_3178_ = 1;
return v___x_3178_;
}
else
{
uint8_t v___x_3179_; 
v___x_3179_ = 0;
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3180_){
_start:
{
uint8_t v_res_3181_; lean_object* v_r_3182_; 
v_res_3181_ = l_Lean_Expr_isApp(v_x_3180_);
lean_dec_ref(v_x_3180_);
v_r_3182_ = lean_box(v_res_3181_);
return v_r_3182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3183_){
_start:
{
if (lean_obj_tag(v_x_3183_) == 11)
{
uint8_t v___x_3184_; 
v___x_3184_ = 1;
return v___x_3184_;
}
else
{
uint8_t v___x_3185_; 
v___x_3185_ = 0;
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_Lean_Expr_isProj(v_x_3186_);
lean_dec_ref(v_x_3186_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3189_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 4)
{
uint8_t v___x_3190_; 
v___x_3190_ = 1;
return v___x_3190_;
}
else
{
uint8_t v___x_3191_; 
v___x_3191_ = 0;
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3192_){
_start:
{
uint8_t v_res_3193_; lean_object* v_r_3194_; 
v_res_3193_ = l_Lean_Expr_isConst(v_x_3192_);
lean_dec_ref(v_x_3192_);
v_r_3194_ = lean_box(v_res_3193_);
return v_r_3194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3195_) == 4)
{
lean_object* v_declName_3197_; uint8_t v___x_3198_; 
v_declName_3197_ = lean_ctor_get(v_x_3195_, 0);
v___x_3198_ = lean_name_eq(v_declName_3197_, v_x_3196_);
return v___x_3198_;
}
else
{
uint8_t v___x_3199_; 
v___x_3199_ = 0;
return v___x_3199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3200_, lean_object* v_x_3201_){
_start:
{
uint8_t v_res_3202_; lean_object* v_r_3203_; 
v_res_3202_ = l_Lean_Expr_isConstOf(v_x_3200_, v_x_3201_);
lean_dec(v_x_3201_);
lean_dec_ref(v_x_3200_);
v_r_3203_ = lean_box(v_res_3202_);
return v_r_3203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
if (lean_obj_tag(v_x_3204_) == 1)
{
lean_object* v_fvarId_3206_; uint8_t v___x_3207_; 
v_fvarId_3206_ = lean_ctor_get(v_x_3204_, 0);
v___x_3207_ = lean_name_eq(v_fvarId_3206_, v_x_3205_);
return v___x_3207_;
}
else
{
uint8_t v___x_3208_; 
v___x_3208_ = 0;
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
uint8_t v_res_3211_; lean_object* v_r_3212_; 
v_res_3211_ = l_Lean_Expr_isFVarOf(v_x_3209_, v_x_3210_);
lean_dec(v_x_3210_);
lean_dec_ref(v_x_3209_);
v_r_3212_ = lean_box(v_res_3211_);
return v_r_3212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3213_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 7)
{
uint8_t v___x_3214_; 
v___x_3214_ = 1;
return v___x_3214_;
}
else
{
uint8_t v___x_3215_; 
v___x_3215_ = 0;
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3216_){
_start:
{
uint8_t v_res_3217_; lean_object* v_r_3218_; 
v_res_3217_ = l_Lean_Expr_isForall(v_x_3216_);
lean_dec_ref(v_x_3216_);
v_r_3218_ = lean_box(v_res_3217_);
return v_r_3218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3219_){
_start:
{
if (lean_obj_tag(v_x_3219_) == 6)
{
uint8_t v___x_3220_; 
v___x_3220_ = 1;
return v___x_3220_;
}
else
{
uint8_t v___x_3221_; 
v___x_3221_ = 0;
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3222_){
_start:
{
uint8_t v_res_3223_; lean_object* v_r_3224_; 
v_res_3223_ = l_Lean_Expr_isLambda(v_x_3222_);
lean_dec_ref(v_x_3222_);
v_r_3224_ = lean_box(v_res_3223_);
return v_r_3224_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3225_){
_start:
{
switch(lean_obj_tag(v_x_3225_))
{
case 6:
{
uint8_t v___x_3226_; 
v___x_3226_ = 1;
return v___x_3226_;
}
case 7:
{
uint8_t v___x_3227_; 
v___x_3227_ = 1;
return v___x_3227_;
}
default: 
{
uint8_t v___x_3228_; 
v___x_3228_ = 0;
return v___x_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3229_){
_start:
{
uint8_t v_res_3230_; lean_object* v_r_3231_; 
v_res_3230_ = l_Lean_Expr_isBinding(v_x_3229_);
lean_dec_ref(v_x_3229_);
v_r_3231_ = lean_box(v_res_3230_);
return v_r_3231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 8)
{
uint8_t v___x_3233_; 
v___x_3233_ = 1;
return v___x_3233_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = 0;
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3235_){
_start:
{
uint8_t v_res_3236_; lean_object* v_r_3237_; 
v_res_3236_ = l_Lean_Expr_isLet(v_x_3235_);
lean_dec_ref(v_x_3235_);
v_r_3237_ = lean_box(v_res_3236_);
return v_r_3237_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3238_){
_start:
{
if (lean_obj_tag(v_x_3238_) == 8)
{
uint8_t v_nondep_3239_; 
v_nondep_3239_ = lean_ctor_get_uint8(v_x_3238_, sizeof(void*)*4 + 8);
return v_nondep_3239_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = 0;
return v___x_3240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3241_){
_start:
{
uint8_t v_res_3242_; lean_object* v_r_3243_; 
v_res_3242_ = l_Lean_Expr_isHave(v_x_3241_);
lean_dec_ref(v_x_3241_);
v_r_3243_ = lean_box(v_res_3242_);
return v_r_3243_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Lean_Expr_isHave(v_a_3244_);
lean_dec_ref(v_a_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = lean_expr_is_have(v_a_3246_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 10)
{
uint8_t v___x_3250_; 
v___x_3250_ = 1;
return v___x_3250_;
}
else
{
uint8_t v___x_3251_; 
v___x_3251_ = 0;
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_Expr_isMData(v_x_3252_);
lean_dec_ref(v_x_3252_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_x_3255_) == 9)
{
uint8_t v___x_3256_; 
v___x_3256_ = 1;
return v___x_3256_;
}
else
{
uint8_t v___x_3257_; 
v___x_3257_ = 0;
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3258_){
_start:
{
uint8_t v_res_3259_; lean_object* v_r_3260_; 
v_res_3259_ = l_Lean_Expr_isLit(v_x_3258_);
lean_dec_ref(v_x_3258_);
v_r_3260_ = lean_box(v_res_3259_);
return v_r_3260_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3261_){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = l_Lean_instInhabitedExpr;
v___x_3263_ = lean_panic_fn_borrowed(v___x_3262_, v_msg_3261_);
return v___x_3263_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3267_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3268_ = lean_unsigned_to_nat(15u);
v___x_3269_ = lean_unsigned_to_nat(932u);
v___x_3270_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3271_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3272_ = l_mkPanicMessageWithDecl(v___x_3271_, v___x_3270_, v___x_3269_, v___x_3268_, v___x_3267_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3273_){
_start:
{
if (lean_obj_tag(v_x_3273_) == 5)
{
lean_object* v_fn_3274_; 
v_fn_3274_ = lean_ctor_get(v_x_3273_, 0);
lean_inc_ref(v_fn_3274_);
return v_fn_3274_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3276_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3275_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Expr_appFn_x21(v_x_3277_);
lean_dec_ref(v_x_3277_);
return v_res_3278_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3280_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3281_ = lean_unsigned_to_nat(15u);
v___x_3282_ = lean_unsigned_to_nat(936u);
v___x_3283_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3284_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3285_ = l_mkPanicMessageWithDecl(v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_, v___x_3280_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3286_){
_start:
{
if (lean_obj_tag(v_x_3286_) == 5)
{
lean_object* v_arg_3287_; 
v_arg_3287_ = lean_ctor_get(v_x_3286_, 1);
lean_inc_ref(v_arg_3287_);
return v_arg_3287_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3289_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3288_);
return v___x_3289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_Expr_appArg_x21(v_x_3290_);
lean_dec_ref(v_x_3290_);
return v_res_3291_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3293_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3294_ = lean_unsigned_to_nat(17u);
v___x_3295_ = lean_unsigned_to_nat(941u);
v___x_3296_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3297_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3298_ = l_mkPanicMessageWithDecl(v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_, v___x_3293_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3299_){
_start:
{
switch(lean_obj_tag(v_x_3299_))
{
case 10:
{
lean_object* v_expr_3300_; 
v_expr_3300_ = lean_ctor_get(v_x_3299_, 1);
v_x_3299_ = v_expr_3300_;
goto _start;
}
case 5:
{
lean_object* v_fn_3302_; 
v_fn_3302_ = lean_ctor_get(v_x_3299_, 0);
lean_inc_ref(v_fn_3302_);
return v_fn_3302_;
}
default: 
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3304_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3303_);
return v___x_3304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Expr_appFn_x21_x27(v_x_3305_);
lean_dec_ref(v_x_3305_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3308_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3309_ = lean_unsigned_to_nat(17u);
v___x_3310_ = lean_unsigned_to_nat(946u);
v___x_3311_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3312_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3313_ = l_mkPanicMessageWithDecl(v___x_3312_, v___x_3311_, v___x_3310_, v___x_3309_, v___x_3308_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3314_){
_start:
{
switch(lean_obj_tag(v_x_3314_))
{
case 10:
{
lean_object* v_expr_3315_; 
v_expr_3315_ = lean_ctor_get(v_x_3314_, 1);
v_x_3314_ = v_expr_3315_;
goto _start;
}
case 5:
{
lean_object* v_arg_3317_; 
v_arg_3317_ = lean_ctor_get(v_x_3314_, 1);
lean_inc_ref(v_arg_3317_);
return v_arg_3317_;
}
default: 
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3319_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3318_);
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_Expr_appArg_x21_x27(v_x_3320_);
lean_dec_ref(v_x_3320_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3322_){
_start:
{
lean_object* v_arg_3323_; 
v_arg_3323_ = lean_ctor_get(v_e_3322_, 1);
lean_inc_ref(v_arg_3323_);
return v_arg_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Expr_appArg___redArg(v_e_3324_);
lean_dec_ref(v_e_3324_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3326_, lean_object* v_h_3327_){
_start:
{
lean_object* v_arg_3328_; 
v_arg_3328_ = lean_ctor_get(v_e_3326_, 1);
lean_inc_ref(v_arg_3328_);
return v_arg_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3329_, lean_object* v_h_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Expr_appArg(v_e_3329_, v_h_3330_);
lean_dec_ref(v_e_3329_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3332_){
_start:
{
lean_object* v_fn_3333_; 
v_fn_3333_ = lean_ctor_get(v_e_3332_, 0);
lean_inc_ref(v_fn_3333_);
return v_fn_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Expr_appFn___redArg(v_e_3334_);
lean_dec_ref(v_e_3334_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3336_, lean_object* v_h_3337_){
_start:
{
lean_object* v_fn_3338_; 
v_fn_3338_ = lean_ctor_get(v_e_3336_, 0);
lean_inc_ref(v_fn_3338_);
return v_fn_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3339_, lean_object* v_h_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Expr_appFn(v_e_3339_, v_h_3340_);
lean_dec_ref(v_e_3339_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3342_){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_panic_fn_borrowed(v___x_3343_, v_msg_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3347_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3348_ = lean_unsigned_to_nat(14u);
v___x_3349_ = lean_unsigned_to_nat(958u);
v___x_3350_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3351_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3352_ = l_mkPanicMessageWithDecl(v___x_3351_, v___x_3350_, v___x_3349_, v___x_3348_, v___x_3347_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3353_){
_start:
{
if (lean_obj_tag(v_x_3353_) == 3)
{
lean_object* v_u_3354_; 
v_u_3354_ = lean_ctor_get(v_x_3353_, 0);
lean_inc(v_u_3354_);
return v_u_3354_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3356_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3355_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Expr_sortLevel_x21(v_x_3357_);
lean_dec_ref(v_x_3357_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3359_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3361_ = lean_panic_fn_borrowed(v___x_3360_, v_msg_3359_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3364_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3365_ = lean_unsigned_to_nat(13u);
v___x_3366_ = lean_unsigned_to_nat(962u);
v___x_3367_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3368_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3369_ = l_mkPanicMessageWithDecl(v___x_3368_, v___x_3367_, v___x_3366_, v___x_3365_, v___x_3364_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 9)
{
lean_object* v_a_3371_; 
v_a_3371_ = lean_ctor_get(v_x_3370_, 0);
lean_inc_ref(v_a_3371_);
return v_a_3371_;
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3373_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3372_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_Expr_litValue_x21(v_x_3374_);
lean_dec_ref(v_x_3374_);
return v_res_3375_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 9)
{
lean_object* v_a_3377_; 
v_a_3377_ = lean_ctor_get(v_x_3376_, 0);
if (lean_obj_tag(v_a_3377_) == 0)
{
uint8_t v___x_3378_; 
v___x_3378_ = 1;
return v___x_3378_;
}
else
{
uint8_t v___x_3379_; 
v___x_3379_ = 0;
return v___x_3379_;
}
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = 0;
return v___x_3380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3381_){
_start:
{
uint8_t v_res_3382_; lean_object* v_r_3383_; 
v_res_3382_ = l_Lean_Expr_isRawNatLit(v_x_3381_);
lean_dec_ref(v_x_3381_);
v_r_3383_ = lean_box(v_res_3382_);
return v_r_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3384_){
_start:
{
if (lean_obj_tag(v_x_3384_) == 9)
{
lean_object* v_a_3385_; 
v_a_3385_ = lean_ctor_get(v_x_3384_, 0);
lean_inc_ref(v_a_3385_);
lean_dec_ref_known(v_x_3384_, 1);
if (lean_obj_tag(v_a_3385_) == 0)
{
lean_object* v_val_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v_val_3386_ = lean_ctor_get(v_a_3385_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_a_3385_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v_a_3385_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_val_3386_);
lean_dec(v_a_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 1);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_val_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
else
{
lean_object* v___x_3394_; 
lean_dec_ref(v_a_3385_);
v___x_3394_ = lean_box(0);
return v___x_3394_;
}
}
else
{
lean_object* v___x_3395_; 
lean_dec_ref(v_x_3384_);
v___x_3395_ = lean_box(0);
return v___x_3395_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3396_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 9)
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v_x_3396_, 0);
if (lean_obj_tag(v_a_3397_) == 1)
{
uint8_t v___x_3398_; 
v___x_3398_ = 1;
return v___x_3398_;
}
else
{
uint8_t v___x_3399_; 
v___x_3399_ = 0;
return v___x_3399_;
}
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = 0;
return v___x_3400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_Lean_Expr_isStringLit(v_x_3401_);
lean_dec_ref(v_x_3401_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3408_){
_start:
{
if (lean_obj_tag(v_x_3408_) == 5)
{
lean_object* v_fn_3409_; 
v_fn_3409_ = lean_ctor_get(v_x_3408_, 0);
if (lean_obj_tag(v_fn_3409_) == 4)
{
lean_object* v_arg_3410_; lean_object* v_declName_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_arg_3410_ = lean_ctor_get(v_x_3408_, 1);
v_declName_3411_ = lean_ctor_get(v_fn_3409_, 0);
v___x_3412_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3413_ = lean_name_eq(v_declName_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
return v___x_3413_;
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = l_Lean_Expr_isRawNatLit(v_arg_3410_);
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
else
{
uint8_t v___x_3416_; 
v___x_3416_ = 0;
return v___x_3416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3417_){
_start:
{
uint8_t v_res_3418_; lean_object* v_r_3419_; 
v_res_3418_ = l_Lean_Expr_isCharLit(v_x_3417_);
lean_dec_ref(v_x_3417_);
v_r_3419_ = lean_box(v_res_3418_);
return v_r_3419_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3420_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_box(0);
v___x_3422_ = lean_panic_fn_borrowed(v___x_3421_, v_msg_3420_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3425_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3426_ = lean_unsigned_to_nat(17u);
v___x_3427_ = lean_unsigned_to_nat(986u);
v___x_3428_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3429_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3430_ = l_mkPanicMessageWithDecl(v___x_3429_, v___x_3428_, v___x_3427_, v___x_3426_, v___x_3425_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3431_){
_start:
{
if (lean_obj_tag(v_x_3431_) == 4)
{
lean_object* v_declName_3432_; 
v_declName_3432_ = lean_ctor_get(v_x_3431_, 0);
lean_inc(v_declName_3432_);
return v_declName_3432_;
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3434_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3433_);
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Expr_constName_x21(v_x_3435_);
lean_dec_ref(v_x_3435_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3437_){
_start:
{
if (lean_obj_tag(v_x_3437_) == 4)
{
lean_object* v_declName_3438_; lean_object* v___x_3439_; 
v_declName_3438_ = lean_ctor_get(v_x_3437_, 0);
lean_inc(v_declName_3438_);
v___x_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_declName_3438_);
return v___x_3439_;
}
else
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_box(0);
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Expr_constName_x3f(v_x_3441_);
lean_dec_ref(v_x_3441_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Expr_constName_x3f(v_e_3443_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_box(0);
return v___x_3445_;
}
else
{
lean_object* v_val_3446_; 
v_val_3446_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_val_3446_);
lean_dec_ref_known(v___x_3444_, 1);
return v_val_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Expr_constName(v_e_3447_);
lean_dec_ref(v_e_3447_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3449_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_panic_fn_borrowed(v___x_3450_, v_msg_3449_);
return v___x_3451_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3453_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3454_ = lean_unsigned_to_nat(18u);
v___x_3455_ = lean_unsigned_to_nat(1006u);
v___x_3456_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3457_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3458_ = l_mkPanicMessageWithDecl(v___x_3457_, v___x_3456_, v___x_3455_, v___x_3454_, v___x_3453_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3459_){
_start:
{
if (lean_obj_tag(v_x_3459_) == 4)
{
lean_object* v_us_3460_; 
v_us_3460_ = lean_ctor_get(v_x_3459_, 1);
lean_inc(v_us_3460_);
return v_us_3460_;
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3462_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3461_);
return v___x_3462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Expr_constLevels_x21(v_x_3463_);
lean_dec_ref(v_x_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3465_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_panic_fn_borrowed(v___x_3466_, v_msg_3465_);
return v___x_3467_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3470_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3471_ = lean_unsigned_to_nat(16u);
v___x_3472_ = lean_unsigned_to_nat(1010u);
v___x_3473_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3474_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3475_ = l_mkPanicMessageWithDecl(v___x_3474_, v___x_3473_, v___x_3472_, v___x_3471_, v___x_3470_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3476_){
_start:
{
if (lean_obj_tag(v_x_3476_) == 0)
{
lean_object* v_deBruijnIndex_3477_; 
v_deBruijnIndex_3477_ = lean_ctor_get(v_x_3476_, 0);
lean_inc(v_deBruijnIndex_3477_);
return v_deBruijnIndex_3477_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3479_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3478_);
return v___x_3479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Expr_bvarIdx_x21(v_x_3480_);
lean_dec_ref(v_x_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_panic_fn_borrowed(v___x_3483_, v_msg_3482_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3487_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3488_ = lean_unsigned_to_nat(14u);
v___x_3489_ = lean_unsigned_to_nat(1014u);
v___x_3490_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3491_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3492_ = l_mkPanicMessageWithDecl(v___x_3491_, v___x_3490_, v___x_3489_, v___x_3488_, v___x_3487_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 1)
{
lean_object* v_fvarId_3494_; 
v_fvarId_3494_ = lean_ctor_get(v_x_3493_, 0);
lean_inc(v_fvarId_3494_);
return v_fvarId_3494_;
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3496_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3495_);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Expr_fvarId_x21(v_x_3497_);
lean_dec_ref(v_x_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3499_){
_start:
{
if (lean_obj_tag(v_x_3499_) == 1)
{
lean_object* v_fvarId_3500_; lean_object* v___x_3501_; 
v_fvarId_3500_ = lean_ctor_get(v_x_3499_, 0);
lean_inc(v_fvarId_3500_);
v___x_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_fvarId_3500_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_box(0);
return v___x_3502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Expr_fvarId_x3f(v_x_3503_);
lean_dec_ref(v_x_3503_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3505_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_panic_fn_borrowed(v___x_3506_, v_msg_3505_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3510_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3511_ = lean_unsigned_to_nat(14u);
v___x_3512_ = lean_unsigned_to_nat(1022u);
v___x_3513_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3514_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3515_ = l_mkPanicMessageWithDecl(v___x_3514_, v___x_3513_, v___x_3512_, v___x_3511_, v___x_3510_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3516_){
_start:
{
if (lean_obj_tag(v_x_3516_) == 2)
{
lean_object* v_mvarId_3517_; 
v_mvarId_3517_ = lean_ctor_get(v_x_3516_, 0);
lean_inc(v_mvarId_3517_);
return v_mvarId_3517_;
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3519_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3518_);
return v___x_3519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Expr_mvarId_x21(v_x_3520_);
lean_dec_ref(v_x_3520_);
return v_res_3521_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3524_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3525_ = lean_unsigned_to_nat(23u);
v___x_3526_ = lean_unsigned_to_nat(1027u);
v___x_3527_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3528_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3529_ = l_mkPanicMessageWithDecl(v___x_3528_, v___x_3527_, v___x_3526_, v___x_3525_, v___x_3524_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3530_){
_start:
{
switch(lean_obj_tag(v_x_3530_))
{
case 7:
{
lean_object* v_binderName_3531_; 
v_binderName_3531_ = lean_ctor_get(v_x_3530_, 0);
lean_inc(v_binderName_3531_);
return v_binderName_3531_;
}
case 6:
{
lean_object* v_binderName_3532_; 
v_binderName_3532_ = lean_ctor_get(v_x_3530_, 0);
lean_inc(v_binderName_3532_);
return v_binderName_3532_;
}
default: 
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3534_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3533_);
return v___x_3534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Expr_bindingName_x21(v_x_3535_);
lean_dec_ref(v_x_3535_);
return v_res_3536_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3538_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3539_ = lean_unsigned_to_nat(23u);
v___x_3540_ = lean_unsigned_to_nat(1032u);
v___x_3541_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3542_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3543_ = l_mkPanicMessageWithDecl(v___x_3542_, v___x_3541_, v___x_3540_, v___x_3539_, v___x_3538_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3544_){
_start:
{
switch(lean_obj_tag(v_x_3544_))
{
case 7:
{
lean_object* v_binderType_3545_; 
v_binderType_3545_ = lean_ctor_get(v_x_3544_, 1);
lean_inc_ref(v_binderType_3545_);
return v_binderType_3545_;
}
case 6:
{
lean_object* v_binderType_3546_; 
v_binderType_3546_ = lean_ctor_get(v_x_3544_, 1);
lean_inc_ref(v_binderType_3546_);
return v_binderType_3546_;
}
default: 
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3548_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3547_);
return v___x_3548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Expr_bindingDomain_x21(v_x_3549_);
lean_dec_ref(v_x_3549_);
return v_res_3550_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3552_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3553_ = lean_unsigned_to_nat(23u);
v___x_3554_ = lean_unsigned_to_nat(1037u);
v___x_3555_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3556_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3557_ = l_mkPanicMessageWithDecl(v___x_3556_, v___x_3555_, v___x_3554_, v___x_3553_, v___x_3552_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3558_){
_start:
{
switch(lean_obj_tag(v_x_3558_))
{
case 7:
{
lean_object* v_body_3559_; 
v_body_3559_ = lean_ctor_get(v_x_3558_, 2);
lean_inc_ref(v_body_3559_);
return v_body_3559_;
}
case 6:
{
lean_object* v_body_3560_; 
v_body_3560_ = lean_ctor_get(v_x_3558_, 2);
lean_inc_ref(v_body_3560_);
return v_body_3560_;
}
default: 
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3562_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3561_);
return v___x_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Expr_bindingBody_x21(v_x_3563_);
lean_dec_ref(v_x_3563_);
return v_res_3564_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3565_){
_start:
{
uint8_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3566_ = 0;
v___x_3567_ = lean_box(v___x_3566_);
v___x_3568_ = lean_panic_fn_borrowed(v___x_3567_, v_msg_3565_);
lean_dec(v___x_3567_);
v___x_3569_ = lean_unbox(v___x_3568_);
lean_dec(v___x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3570_){
_start:
{
uint8_t v_res_3571_; lean_object* v_r_3572_; 
v_res_3571_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3570_);
v_r_3572_ = lean_box(v_res_3571_);
return v_r_3572_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3574_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3575_ = lean_unsigned_to_nat(24u);
v___x_3576_ = lean_unsigned_to_nat(1042u);
v___x_3577_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3578_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3579_ = l_mkPanicMessageWithDecl(v___x_3578_, v___x_3577_, v___x_3576_, v___x_3575_, v___x_3574_);
return v___x_3579_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3580_){
_start:
{
switch(lean_obj_tag(v_x_3580_))
{
case 7:
{
uint8_t v_binderInfo_3581_; 
v_binderInfo_3581_ = lean_ctor_get_uint8(v_x_3580_, sizeof(void*)*3 + 8);
return v_binderInfo_3581_;
}
case 6:
{
uint8_t v_binderInfo_3582_; 
v_binderInfo_3582_ = lean_ctor_get_uint8(v_x_3580_, sizeof(void*)*3 + 8);
return v_binderInfo_3582_;
}
default: 
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3584_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_Lean_Expr_bindingInfo_x21(v_x_3585_);
lean_dec_ref(v_x_3585_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3588_){
_start:
{
lean_object* v_binderName_3589_; 
v_binderName_3589_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_binderName_3589_);
return v_binderName_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_Expr_forallName___redArg(v_x_3590_);
lean_dec_ref(v_x_3590_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_binderName_3594_; 
v_binderName_3594_ = lean_ctor_get(v_x_3592_, 0);
lean_inc(v_binderName_3594_);
return v_binderName_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Expr_forallName(v_x_3595_, v_x_3596_);
lean_dec_ref(v_x_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3598_){
_start:
{
lean_object* v_binderType_3599_; 
v_binderType_3599_ = lean_ctor_get(v_x_3598_, 1);
lean_inc_ref(v_binderType_3599_);
return v_binderType_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Expr_forallDomain___redArg(v_x_3600_);
lean_dec_ref(v_x_3600_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_binderType_3604_; 
v_binderType_3604_ = lean_ctor_get(v_x_3602_, 1);
lean_inc_ref(v_binderType_3604_);
return v_binderType_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3605_, lean_object* v_x_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_Expr_forallDomain(v_x_3605_, v_x_3606_);
lean_dec_ref(v_x_3605_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3608_){
_start:
{
lean_object* v_body_3609_; 
v_body_3609_ = lean_ctor_get(v_x_3608_, 2);
lean_inc_ref(v_body_3609_);
return v_body_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Expr_forallBody___redArg(v_x_3610_);
lean_dec_ref(v_x_3610_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v_body_3614_; 
v_body_3614_ = lean_ctor_get(v_x_3612_, 2);
lean_inc_ref(v_body_3614_);
return v_body_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3615_, lean_object* v_x_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_Expr_forallBody(v_x_3615_, v_x_3616_);
lean_dec_ref(v_x_3615_);
return v_res_3617_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3618_){
_start:
{
uint8_t v_binderInfo_3619_; 
v_binderInfo_3619_ = lean_ctor_get_uint8(v_x_3618_, sizeof(void*)*3 + 8);
return v_binderInfo_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3620_){
_start:
{
uint8_t v_res_3621_; lean_object* v_r_3622_; 
v_res_3621_ = l_Lean_Expr_forallInfo___redArg(v_x_3620_);
lean_dec_ref(v_x_3620_);
v_r_3622_ = lean_box(v_res_3621_);
return v_r_3622_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
uint8_t v_binderInfo_3625_; 
v_binderInfo_3625_ = lean_ctor_get_uint8(v_x_3623_, sizeof(void*)*3 + 8);
return v_binderInfo_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
uint8_t v_res_3628_; lean_object* v_r_3629_; 
v_res_3628_ = l_Lean_Expr_forallInfo(v_x_3626_, v_x_3627_);
lean_dec_ref(v_x_3626_);
v_r_3629_ = lean_box(v_res_3628_);
return v_r_3629_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3632_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3633_ = lean_unsigned_to_nat(17u);
v___x_3634_ = lean_unsigned_to_nat(1058u);
v___x_3635_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3636_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3637_ = l_mkPanicMessageWithDecl(v___x_3636_, v___x_3635_, v___x_3634_, v___x_3633_, v___x_3632_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3638_){
_start:
{
if (lean_obj_tag(v_x_3638_) == 8)
{
lean_object* v_declName_3639_; 
v_declName_3639_ = lean_ctor_get(v_x_3638_, 0);
lean_inc(v_declName_3639_);
return v_declName_3639_;
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3641_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3640_);
return v___x_3641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_Expr_letName_x21(v_x_3642_);
lean_dec_ref(v_x_3642_);
return v_res_3643_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3645_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3646_ = lean_unsigned_to_nat(19u);
v___x_3647_ = lean_unsigned_to_nat(1062u);
v___x_3648_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3649_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3650_ = l_mkPanicMessageWithDecl(v___x_3649_, v___x_3648_, v___x_3647_, v___x_3646_, v___x_3645_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3651_){
_start:
{
if (lean_obj_tag(v_x_3651_) == 8)
{
lean_object* v_type_3652_; 
v_type_3652_ = lean_ctor_get(v_x_3651_, 1);
lean_inc_ref(v_type_3652_);
return v_type_3652_;
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3654_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3653_);
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_Expr_letType_x21(v_x_3655_);
lean_dec_ref(v_x_3655_);
return v_res_3656_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3658_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3659_ = lean_unsigned_to_nat(21u);
v___x_3660_ = lean_unsigned_to_nat(1066u);
v___x_3661_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3662_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3663_ = l_mkPanicMessageWithDecl(v___x_3662_, v___x_3661_, v___x_3660_, v___x_3659_, v___x_3658_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3664_){
_start:
{
if (lean_obj_tag(v_x_3664_) == 8)
{
lean_object* v_value_3665_; 
v_value_3665_ = lean_ctor_get(v_x_3664_, 2);
lean_inc_ref(v_value_3665_);
return v_value_3665_;
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3667_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3666_);
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_Expr_letValue_x21(v_x_3668_);
lean_dec_ref(v_x_3668_);
return v_res_3669_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3671_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3672_ = lean_unsigned_to_nat(23u);
v___x_3673_ = lean_unsigned_to_nat(1070u);
v___x_3674_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3675_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3676_ = l_mkPanicMessageWithDecl(v___x_3675_, v___x_3674_, v___x_3673_, v___x_3672_, v___x_3671_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3677_){
_start:
{
if (lean_obj_tag(v_x_3677_) == 8)
{
lean_object* v_body_3678_; 
v_body_3678_ = lean_ctor_get(v_x_3677_, 3);
lean_inc_ref(v_body_3678_);
return v_body_3678_;
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3680_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3679_);
return v___x_3680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_Expr_letBody_x21(v_x_3681_);
lean_dec_ref(v_x_3681_);
return v_res_3682_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3683_){
_start:
{
uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3684_ = 0;
v___x_3685_ = lean_box(v___x_3684_);
v___x_3686_ = lean_panic_fn_borrowed(v___x_3685_, v_msg_3683_);
lean_dec(v___x_3685_);
v___x_3687_ = lean_unbox(v___x_3686_);
lean_dec(v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3688_){
_start:
{
uint8_t v_res_3689_; lean_object* v_r_3690_; 
v_res_3689_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3688_);
v_r_3690_ = lean_box(v_res_3689_);
return v_r_3690_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3692_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3693_ = lean_unsigned_to_nat(27u);
v___x_3694_ = lean_unsigned_to_nat(1074u);
v___x_3695_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3696_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3697_ = l_mkPanicMessageWithDecl(v___x_3696_, v___x_3695_, v___x_3694_, v___x_3693_, v___x_3692_);
return v___x_3697_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3698_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 8)
{
uint8_t v_nondep_3699_; 
v_nondep_3699_ = lean_ctor_get_uint8(v_x_3698_, sizeof(void*)*4 + 8);
return v_nondep_3699_;
}
else
{
lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3701_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3700_);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3702_){
_start:
{
uint8_t v_res_3703_; lean_object* v_r_3704_; 
v_res_3703_ = l_Lean_Expr_letNondep_x21(v_x_3702_);
lean_dec_ref(v_x_3702_);
v_r_3704_ = lean_box(v_res_3703_);
return v_r_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 10)
{
lean_object* v_expr_3706_; 
v_expr_3706_ = lean_ctor_get(v_x_3705_, 1);
v_x_3705_ = v_expr_3706_;
goto _start;
}
else
{
lean_inc_ref(v_x_3705_);
return v_x_3705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_Expr_consumeMData(v_x_3708_);
lean_dec_ref(v_x_3708_);
return v_res_3709_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3712_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3713_ = lean_unsigned_to_nat(17u);
v___x_3714_ = lean_unsigned_to_nat(1082u);
v___x_3715_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3716_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3717_ = l_mkPanicMessageWithDecl(v___x_3716_, v___x_3715_, v___x_3714_, v___x_3713_, v___x_3712_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 10)
{
lean_object* v_expr_3719_; 
v_expr_3719_ = lean_ctor_get(v_x_3718_, 1);
lean_inc_ref(v_expr_3719_);
return v_expr_3719_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3721_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3720_);
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_Expr_mdataExpr_x21(v_x_3722_);
lean_dec_ref(v_x_3722_);
return v_res_3723_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3726_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3727_ = lean_unsigned_to_nat(18u);
v___x_3728_ = lean_unsigned_to_nat(1086u);
v___x_3729_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3730_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3731_ = l_mkPanicMessageWithDecl(v___x_3730_, v___x_3729_, v___x_3728_, v___x_3727_, v___x_3726_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 11)
{
lean_object* v_struct_3733_; 
v_struct_3733_ = lean_ctor_get(v_x_3732_, 2);
lean_inc_ref(v_struct_3733_);
return v_struct_3733_;
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3735_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3734_);
return v___x_3735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_Expr_projExpr_x21(v_x_3736_);
lean_dec_ref(v_x_3736_);
return v_res_3737_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3739_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3740_ = lean_unsigned_to_nat(18u);
v___x_3741_ = lean_unsigned_to_nat(1090u);
v___x_3742_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3743_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3744_ = l_mkPanicMessageWithDecl(v___x_3743_, v___x_3742_, v___x_3741_, v___x_3740_, v___x_3739_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3745_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 11)
{
lean_object* v_idx_3746_; 
v_idx_3746_ = lean_ctor_get(v_x_3745_, 1);
lean_inc(v_idx_3746_);
return v_idx_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3748_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3747_);
return v___x_3748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lean_Expr_projIdx_x21(v_x_3749_);
lean_dec_ref(v_x_3749_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3751_){
_start:
{
if (lean_obj_tag(v_x_3751_) == 7)
{
lean_object* v_body_3752_; 
v_body_3752_ = lean_ctor_get(v_x_3751_, 2);
v_x_3751_ = v_body_3752_;
goto _start;
}
else
{
lean_inc_ref(v_x_3751_);
return v_x_3751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Expr_getForallBody(v_x_3754_);
lean_dec_ref(v_x_3754_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3756_, lean_object* v_x_3757_){
_start:
{
lean_object* v_zero_3758_; uint8_t v_isZero_3759_; 
v_zero_3758_ = lean_unsigned_to_nat(0u);
v_isZero_3759_ = lean_nat_dec_eq(v_x_3756_, v_zero_3758_);
if (v_isZero_3759_ == 1)
{
lean_dec(v_x_3756_);
lean_inc_ref(v_x_3757_);
return v_x_3757_;
}
else
{
if (lean_obj_tag(v_x_3757_) == 7)
{
lean_object* v_body_3760_; lean_object* v_one_3761_; lean_object* v_n_3762_; 
v_body_3760_ = lean_ctor_get(v_x_3757_, 2);
v_one_3761_ = lean_unsigned_to_nat(1u);
v_n_3762_ = lean_nat_sub(v_x_3756_, v_one_3761_);
lean_dec(v_x_3756_);
v_x_3756_ = v_n_3762_;
v_x_3757_ = v_body_3760_;
goto _start;
}
else
{
lean_dec(v_x_3756_);
lean_inc_ref(v_x_3757_);
return v_x_3757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3764_, lean_object* v_x_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3764_, v_x_3765_);
lean_dec_ref(v_x_3765_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 7)
{
lean_object* v_binderName_3768_; lean_object* v_body_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_binderName_3768_ = lean_ctor_get(v_x_3767_, 0);
v_body_3769_ = lean_ctor_get(v_x_3767_, 2);
v___x_3770_ = l_Lean_Expr_getForallBinderNames(v_body_3769_);
lean_inc(v_binderName_3768_);
v___x_3771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3771_, 0, v_binderName_3768_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
return v___x_3771_;
}
else
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_box(0);
return v___x_3772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_Expr_getForallBinderNames(v_x_3773_);
lean_dec_ref(v_x_3773_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3775_){
_start:
{
switch(lean_obj_tag(v_x_3775_))
{
case 10:
{
lean_object* v_expr_3776_; 
v_expr_3776_ = lean_ctor_get(v_x_3775_, 1);
v_x_3775_ = v_expr_3776_;
goto _start;
}
case 7:
{
lean_object* v_body_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_body_3778_ = lean_ctor_get(v_x_3775_, 2);
v___x_3779_ = l_Lean_Expr_getNumHeadForalls(v_body_3778_);
v___x_3780_ = lean_unsigned_to_nat(1u);
v___x_3781_ = lean_nat_add(v___x_3779_, v___x_3780_);
lean_dec(v___x_3779_);
return v___x_3781_;
}
default: 
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_unsigned_to_nat(0u);
return v___x_3782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Expr_getNumHeadForalls(v_x_3783_);
lean_dec_ref(v_x_3783_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3785_){
_start:
{
if (lean_obj_tag(v_x_3785_) == 5)
{
lean_object* v_fn_3786_; 
v_fn_3786_ = lean_ctor_get(v_x_3785_, 0);
v_x_3785_ = v_fn_3786_;
goto _start;
}
else
{
lean_inc_ref(v_x_3785_);
return v_x_3785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_Expr_getAppFn(v_x_3788_);
lean_dec_ref(v_x_3788_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3790_){
_start:
{
switch(lean_obj_tag(v_x_3790_))
{
case 5:
{
lean_object* v_fn_3791_; 
v_fn_3791_ = lean_ctor_get(v_x_3790_, 0);
v_x_3790_ = v_fn_3791_;
goto _start;
}
case 10:
{
lean_object* v_expr_3793_; 
v_expr_3793_ = lean_ctor_get(v_x_3790_, 1);
v_x_3790_ = v_expr_3793_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3790_);
return v_x_3790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Expr_getAppFn_x27(v_x_3795_);
lean_dec_ref(v_x_3795_);
return v_res_3796_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3797_, lean_object* v_n_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Expr_getAppFn(v_e_3797_);
if (lean_obj_tag(v___x_3799_) == 4)
{
lean_object* v_declName_3800_; uint8_t v___x_3801_; 
v_declName_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_declName_3800_);
lean_dec_ref_known(v___x_3799_, 2);
v___x_3801_ = lean_name_eq(v_declName_3800_, v_n_3798_);
lean_dec(v_declName_3800_);
return v___x_3801_;
}
else
{
uint8_t v___x_3802_; 
lean_dec_ref(v___x_3799_);
v___x_3802_ = 0;
return v___x_3802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3803_, lean_object* v_n_3804_){
_start:
{
uint8_t v_res_3805_; lean_object* v_r_3806_; 
v_res_3805_ = l_Lean_Expr_isAppOf(v_e_3803_, v_n_3804_);
lean_dec(v_n_3804_);
lean_dec_ref(v_e_3803_);
v_r_3806_ = lean_box(v_res_3805_);
return v_r_3806_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3807_, lean_object* v_x_3808_, lean_object* v_x_3809_){
_start:
{
switch(lean_obj_tag(v_x_3807_))
{
case 4:
{
lean_object* v_declName_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
v_declName_3810_ = lean_ctor_get(v_x_3807_, 0);
v___x_3811_ = lean_unsigned_to_nat(0u);
v___x_3812_ = lean_nat_dec_eq(v_x_3809_, v___x_3811_);
lean_dec(v_x_3809_);
if (v___x_3812_ == 0)
{
return v___x_3812_;
}
else
{
uint8_t v___x_3813_; 
v___x_3813_ = lean_name_eq(v_declName_3810_, v_x_3808_);
return v___x_3813_;
}
}
case 5:
{
lean_object* v_fn_3814_; lean_object* v_zero_3815_; uint8_t v_isZero_3816_; 
v_fn_3814_ = lean_ctor_get(v_x_3807_, 0);
v_zero_3815_ = lean_unsigned_to_nat(0u);
v_isZero_3816_ = lean_nat_dec_eq(v_x_3809_, v_zero_3815_);
if (v_isZero_3816_ == 0)
{
lean_object* v_one_3817_; lean_object* v_n_3818_; 
v_one_3817_ = lean_unsigned_to_nat(1u);
v_n_3818_ = lean_nat_sub(v_x_3809_, v_one_3817_);
lean_dec(v_x_3809_);
v_x_3807_ = v_fn_3814_;
v_x_3809_ = v_n_3818_;
goto _start;
}
else
{
uint8_t v___x_3820_; 
lean_dec(v_x_3809_);
v___x_3820_ = 0;
return v___x_3820_;
}
}
default: 
{
uint8_t v___x_3821_; 
lean_dec(v_x_3809_);
v___x_3821_ = 0;
return v___x_3821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3822_, lean_object* v_x_3823_, lean_object* v_x_3824_){
_start:
{
uint8_t v_res_3825_; lean_object* v_r_3826_; 
v_res_3825_ = l_Lean_Expr_isAppOfArity(v_x_3822_, v_x_3823_, v_x_3824_);
lean_dec(v_x_3823_);
lean_dec_ref(v_x_3822_);
v_r_3826_ = lean_box(v_res_3825_);
return v_r_3826_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3827_, lean_object* v_x_3828_, lean_object* v_x_3829_){
_start:
{
switch(lean_obj_tag(v_x_3827_))
{
case 10:
{
lean_object* v_expr_3830_; 
v_expr_3830_ = lean_ctor_get(v_x_3827_, 1);
v_x_3827_ = v_expr_3830_;
goto _start;
}
case 4:
{
lean_object* v_declName_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v_declName_3832_ = lean_ctor_get(v_x_3827_, 0);
v___x_3833_ = lean_unsigned_to_nat(0u);
v___x_3834_ = lean_nat_dec_eq(v_x_3829_, v___x_3833_);
lean_dec(v_x_3829_);
if (v___x_3834_ == 0)
{
return v___x_3834_;
}
else
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_name_eq(v_declName_3832_, v_x_3828_);
return v___x_3835_;
}
}
case 5:
{
lean_object* v_fn_3836_; lean_object* v_zero_3837_; uint8_t v_isZero_3838_; 
v_fn_3836_ = lean_ctor_get(v_x_3827_, 0);
v_zero_3837_ = lean_unsigned_to_nat(0u);
v_isZero_3838_ = lean_nat_dec_eq(v_x_3829_, v_zero_3837_);
if (v_isZero_3838_ == 0)
{
lean_object* v_one_3839_; lean_object* v_n_3840_; 
v_one_3839_ = lean_unsigned_to_nat(1u);
v_n_3840_ = lean_nat_sub(v_x_3829_, v_one_3839_);
lean_dec(v_x_3829_);
v_x_3827_ = v_fn_3836_;
v_x_3829_ = v_n_3840_;
goto _start;
}
else
{
uint8_t v___x_3842_; 
lean_dec(v_x_3829_);
v___x_3842_ = 0;
return v___x_3842_;
}
}
default: 
{
uint8_t v___x_3843_; 
lean_dec(v_x_3829_);
v___x_3843_ = 0;
return v___x_3843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3844_, lean_object* v_x_3845_, lean_object* v_x_3846_){
_start:
{
uint8_t v_res_3847_; lean_object* v_r_3848_; 
v_res_3847_ = l_Lean_Expr_isAppOfArity_x27(v_x_3844_, v_x_3845_, v_x_3846_);
lean_dec(v_x_3845_);
lean_dec_ref(v_x_3844_);
v_r_3848_ = lean_box(v_res_3847_);
return v_r_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3849_, lean_object* v_x_3850_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 5)
{
lean_object* v_fn_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_fn_3851_ = lean_ctor_get(v_x_3849_, 0);
v___x_3852_ = lean_unsigned_to_nat(1u);
v___x_3853_ = lean_nat_add(v_x_3850_, v___x_3852_);
lean_dec(v_x_3850_);
v_x_3849_ = v_fn_3851_;
v_x_3850_ = v___x_3853_;
goto _start;
}
else
{
return v_x_3850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3855_, lean_object* v_x_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3855_, v_x_3856_);
lean_dec_ref(v_x_3855_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3858_){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_unsigned_to_nat(0u);
v___x_3860_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3858_, v___x_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Expr_getAppNumArgs(v_e_3861_);
lean_dec_ref(v_e_3861_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
switch(lean_obj_tag(v_a_3863_))
{
case 10:
{
lean_object* v_expr_3865_; 
v_expr_3865_ = lean_ctor_get(v_a_3863_, 1);
v_a_3863_ = v_expr_3865_;
goto _start;
}
case 5:
{
lean_object* v_fn_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_fn_3867_ = lean_ctor_get(v_a_3863_, 0);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = lean_nat_add(v_a_3864_, v___x_3868_);
lean_dec(v_a_3864_);
v_a_3863_ = v_fn_3867_;
v_a_3864_ = v___x_3869_;
goto _start;
}
default: 
{
return v_a_3864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3871_, v_a_3872_);
lean_dec_ref(v_a_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_unsigned_to_nat(0u);
v___x_3876_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3874_, v___x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3877_);
lean_dec_ref(v_e_3877_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3879_, lean_object* v_x_3880_){
_start:
{
lean_object* v_zero_3881_; uint8_t v_isZero_3882_; 
v_zero_3881_ = lean_unsigned_to_nat(0u);
v_isZero_3882_ = lean_nat_dec_eq(v_x_3879_, v_zero_3881_);
if (v_isZero_3882_ == 0)
{
if (lean_obj_tag(v_x_3880_) == 5)
{
lean_object* v_fn_3883_; lean_object* v_one_3884_; lean_object* v_n_3885_; 
v_fn_3883_ = lean_ctor_get(v_x_3880_, 0);
v_one_3884_ = lean_unsigned_to_nat(1u);
v_n_3885_ = lean_nat_sub(v_x_3879_, v_one_3884_);
lean_dec(v_x_3879_);
v_x_3879_ = v_n_3885_;
v_x_3880_ = v_fn_3883_;
goto _start;
}
else
{
lean_dec(v_x_3879_);
lean_inc_ref(v_x_3880_);
return v_x_3880_;
}
}
else
{
lean_dec(v_x_3879_);
lean_inc_ref(v_x_3880_);
return v_x_3880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_Expr_getBoundedAppFn(v_x_3887_, v_x_3888_);
lean_dec_ref(v_x_3888_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3890_, lean_object* v_x_3891_, lean_object* v_x_3892_){
_start:
{
if (lean_obj_tag(v_x_3890_) == 5)
{
lean_object* v_fn_3893_; lean_object* v_arg_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_fn_3893_ = lean_ctor_get(v_x_3890_, 0);
lean_inc_ref(v_fn_3893_);
v_arg_3894_ = lean_ctor_get(v_x_3890_, 1);
lean_inc_ref(v_arg_3894_);
lean_dec_ref_known(v_x_3890_, 2);
v___x_3895_ = lean_array_set(v_x_3891_, v_x_3892_, v_arg_3894_);
v___x_3896_ = lean_unsigned_to_nat(1u);
v___x_3897_ = lean_nat_sub(v_x_3892_, v___x_3896_);
lean_dec(v_x_3892_);
v_x_3890_ = v_fn_3893_;
v_x_3891_ = v___x_3895_;
v_x_3892_ = v___x_3897_;
goto _start;
}
else
{
lean_dec(v_x_3892_);
lean_dec_ref(v_x_3890_);
return v_x_3891_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3899_; lean_object* v_dummy_3900_; 
v___x_3899_ = lean_box(0);
v_dummy_3900_ = l_Lean_Expr_sort___override(v___x_3899_);
return v_dummy_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3901_){
_start:
{
lean_object* v_dummy_3902_; lean_object* v_nargs_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_dummy_3902_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3903_ = l_Lean_Expr_getAppNumArgs(v_e_3901_);
lean_inc(v_nargs_3903_);
v___x_3904_ = lean_mk_array(v_nargs_3903_, v_dummy_3902_);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_nat_sub(v_nargs_3903_, v___x_3905_);
lean_dec(v_nargs_3903_);
v___x_3907_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3901_, v___x_3904_, v___x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3908_, lean_object* v_x_3909_, lean_object* v_x_3910_){
_start:
{
if (lean_obj_tag(v_x_3908_) == 5)
{
lean_object* v_fn_3911_; lean_object* v_arg_3912_; lean_object* v_zero_3913_; uint8_t v_isZero_3914_; 
v_fn_3911_ = lean_ctor_get(v_x_3908_, 0);
lean_inc_ref(v_fn_3911_);
v_arg_3912_ = lean_ctor_get(v_x_3908_, 1);
lean_inc_ref(v_arg_3912_);
lean_dec_ref_known(v_x_3908_, 2);
v_zero_3913_ = lean_unsigned_to_nat(0u);
v_isZero_3914_ = lean_nat_dec_eq(v_x_3910_, v_zero_3913_);
if (v_isZero_3914_ == 0)
{
lean_object* v_one_3915_; lean_object* v_n_3916_; lean_object* v___x_3917_; 
v_one_3915_ = lean_unsigned_to_nat(1u);
v_n_3916_ = lean_nat_sub(v_x_3910_, v_one_3915_);
lean_dec(v_x_3910_);
v___x_3917_ = lean_array_set(v_x_3909_, v_n_3916_, v_arg_3912_);
v_x_3908_ = v_fn_3911_;
v_x_3909_ = v___x_3917_;
v_x_3910_ = v_n_3916_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3912_);
lean_dec_ref(v_fn_3911_);
lean_dec(v_x_3910_);
return v_x_3909_;
}
}
else
{
lean_dec(v_x_3910_);
lean_dec_ref(v_x_3908_);
return v_x_3909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3919_, lean_object* v_e_3920_){
_start:
{
lean_object* v_dummy_3921_; lean_object* v___y_3923_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v_dummy_3921_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3926_ = l_Lean_Expr_getAppNumArgs(v_e_3920_);
v___x_3927_ = lean_nat_dec_le(v_maxArgs_3919_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_dec(v_maxArgs_3919_);
v___y_3923_ = v___x_3926_;
goto v___jp_3922_;
}
else
{
lean_dec(v___x_3926_);
v___y_3923_ = v_maxArgs_3919_;
goto v___jp_3922_;
}
v___jp_3922_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_inc(v___y_3923_);
v___x_3924_ = lean_mk_array(v___y_3923_, v_dummy_3921_);
v___x_3925_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3920_, v___x_3924_, v___y_3923_);
return v___x_3925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3928_, lean_object* v_x_3929_){
_start:
{
if (lean_obj_tag(v_x_3928_) == 5)
{
lean_object* v_fn_3930_; lean_object* v_arg_3931_; lean_object* v___x_3932_; 
v_fn_3930_ = lean_ctor_get(v_x_3928_, 0);
lean_inc_ref(v_fn_3930_);
v_arg_3931_ = lean_ctor_get(v_x_3928_, 1);
lean_inc_ref(v_arg_3931_);
lean_dec_ref_known(v_x_3928_, 2);
v___x_3932_ = lean_array_push(v_x_3929_, v_arg_3931_);
v_x_3928_ = v_fn_3930_;
v_x_3929_ = v___x_3932_;
goto _start;
}
else
{
lean_dec_ref(v_x_3928_);
return v_x_3929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3934_){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = l_Lean_Expr_getAppNumArgs(v_e_3934_);
v___x_3936_ = lean_mk_empty_array_with_capacity(v___x_3935_);
lean_dec(v___x_3935_);
v___x_3937_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3934_, v___x_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3938_, lean_object* v_x_3939_, lean_object* v_x_3940_, lean_object* v_x_3941_){
_start:
{
if (lean_obj_tag(v_x_3939_) == 5)
{
lean_object* v_fn_3942_; lean_object* v_arg_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_fn_3942_ = lean_ctor_get(v_x_3939_, 0);
lean_inc_ref(v_fn_3942_);
v_arg_3943_ = lean_ctor_get(v_x_3939_, 1);
lean_inc_ref(v_arg_3943_);
lean_dec_ref_known(v_x_3939_, 2);
v___x_3944_ = lean_array_set(v_x_3940_, v_x_3941_, v_arg_3943_);
v___x_3945_ = lean_unsigned_to_nat(1u);
v___x_3946_ = lean_nat_sub(v_x_3941_, v___x_3945_);
lean_dec(v_x_3941_);
v_x_3939_ = v_fn_3942_;
v_x_3940_ = v___x_3944_;
v_x_3941_ = v___x_3946_;
goto _start;
}
else
{
lean_object* v___x_3948_; 
lean_dec(v_x_3941_);
v___x_3948_ = lean_apply_2(v_k_3938_, v_x_3939_, v_x_3940_);
return v___x_3948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3949_, lean_object* v_k_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_, lean_object* v_x_3953_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Expr_withAppAux___redArg(v_k_3950_, v_x_3951_, v_x_3952_, v_x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3955_, lean_object* v_k_3956_){
_start:
{
lean_object* v_dummy_3957_; lean_object* v_nargs_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_dummy_3957_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3958_ = l_Lean_Expr_getAppNumArgs(v_e_3955_);
lean_inc(v_nargs_3958_);
v___x_3959_ = lean_mk_array(v_nargs_3958_, v_dummy_3957_);
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_3961_ = lean_nat_sub(v_nargs_3958_, v___x_3960_);
lean_dec(v_nargs_3958_);
v___x_3962_ = l_Lean_Expr_withAppAux___redArg(v_k_3956_, v_e_3955_, v___x_3959_, v___x_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3963_, lean_object* v_e_3964_, lean_object* v_k_3965_){
_start:
{
lean_object* v_dummy_3966_; lean_object* v_nargs_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_dummy_3966_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3967_ = l_Lean_Expr_getAppNumArgs(v_e_3964_);
lean_inc(v_nargs_3967_);
v___x_3968_ = lean_mk_array(v_nargs_3967_, v_dummy_3966_);
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_nat_sub(v_nargs_3967_, v___x_3969_);
lean_dec(v_nargs_3967_);
v___x_3971_ = l_Lean_Expr_withAppAux___redArg(v_k_3965_, v_e_3964_, v___x_3968_, v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3972_, lean_object* v_x_3973_, lean_object* v_x_3974_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 5)
{
lean_object* v_fn_3975_; lean_object* v_arg_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_fn_3975_ = lean_ctor_get(v_x_3972_, 0);
lean_inc_ref(v_fn_3975_);
v_arg_3976_ = lean_ctor_get(v_x_3972_, 1);
lean_inc_ref(v_arg_3976_);
lean_dec_ref_known(v_x_3972_, 2);
v___x_3977_ = lean_array_set(v_x_3973_, v_x_3974_, v_arg_3976_);
v___x_3978_ = lean_unsigned_to_nat(1u);
v___x_3979_ = lean_nat_sub(v_x_3974_, v___x_3978_);
lean_dec(v_x_3974_);
v_x_3972_ = v_fn_3975_;
v_x_3973_ = v___x_3977_;
v_x_3974_ = v___x_3979_;
goto _start;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec(v_x_3974_);
v___x_3981_ = l_Lean_Expr_constName(v_x_3972_);
lean_dec_ref(v_x_3972_);
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
lean_ctor_set(v___x_3982_, 1, v_x_3973_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3983_){
_start:
{
lean_object* v_dummy_3984_; lean_object* v_nargs_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_dummy_3984_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3985_ = l_Lean_Expr_getAppNumArgs(v_e_3983_);
lean_inc(v_nargs_3985_);
v___x_3986_ = lean_mk_array(v_nargs_3985_, v_dummy_3984_);
v___x_3987_ = lean_unsigned_to_nat(1u);
v___x_3988_ = lean_nat_sub(v_nargs_3985_, v___x_3987_);
lean_dec(v_nargs_3985_);
v___x_3989_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3983_, v___x_3986_, v___x_3988_);
return v___x_3989_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Array_instInhabited(lean_box(0));
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3991_){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3993_ = lean_panic_fn_borrowed(v___x_3992_, v_msg_3991_);
return v___x_3993_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3996_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3997_ = lean_unsigned_to_nat(27u);
v___x_3998_ = lean_unsigned_to_nat(1247u);
v___x_3999_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_4000_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4001_ = l_mkPanicMessageWithDecl(v___x_4000_, v___x_3999_, v___x_3998_, v___x_3997_, v___x_3996_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_zero_4005_; uint8_t v_isZero_4006_; 
v_zero_4005_ = lean_unsigned_to_nat(0u);
v_isZero_4006_ = lean_nat_dec_eq(v_a_4002_, v_zero_4005_);
if (v_isZero_4006_ == 1)
{
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
return v_a_4004_;
}
else
{
if (lean_obj_tag(v_a_4003_) == 5)
{
lean_object* v_fn_4007_; lean_object* v_arg_4008_; lean_object* v_one_4009_; lean_object* v_n_4010_; lean_object* v___x_4011_; 
v_fn_4007_ = lean_ctor_get(v_a_4003_, 0);
lean_inc_ref(v_fn_4007_);
v_arg_4008_ = lean_ctor_get(v_a_4003_, 1);
lean_inc_ref(v_arg_4008_);
lean_dec_ref_known(v_a_4003_, 2);
v_one_4009_ = lean_unsigned_to_nat(1u);
v_n_4010_ = lean_nat_sub(v_a_4002_, v_one_4009_);
lean_dec(v_a_4002_);
v___x_4011_ = lean_array_set(v_a_4004_, v_n_4010_, v_arg_4008_);
v_a_4002_ = v_n_4010_;
v_a_4003_ = v_fn_4007_;
v_a_4004_ = v___x_4011_;
goto _start;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_dec_ref(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
v___x_4013_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4014_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4013_);
return v___x_4014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4015_, lean_object* v_n_4016_){
_start:
{
lean_object* v_dummy_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_dummy_4017_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4016_);
v___x_4018_ = lean_mk_array(v_n_4016_, v_dummy_4017_);
v___x_4019_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4016_, v_e_4015_, v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4020_, lean_object* v_n_4021_){
_start:
{
lean_object* v_zero_4022_; uint8_t v_isZero_4023_; 
v_zero_4022_ = lean_unsigned_to_nat(0u);
v_isZero_4023_ = lean_nat_dec_eq(v_n_4021_, v_zero_4022_);
if (v_isZero_4023_ == 1)
{
lean_dec(v_n_4021_);
lean_inc_ref(v_e_4020_);
return v_e_4020_;
}
else
{
if (lean_obj_tag(v_e_4020_) == 5)
{
lean_object* v_fn_4024_; lean_object* v_one_4025_; lean_object* v_n_4026_; 
v_fn_4024_ = lean_ctor_get(v_e_4020_, 0);
v_one_4025_ = lean_unsigned_to_nat(1u);
v_n_4026_ = lean_nat_sub(v_n_4021_, v_one_4025_);
lean_dec(v_n_4021_);
v_e_4020_ = v_fn_4024_;
v_n_4021_ = v_n_4026_;
goto _start;
}
else
{
lean_dec(v_n_4021_);
lean_inc_ref(v_e_4020_);
return v_e_4020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4028_, lean_object* v_n_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_Expr_stripArgsN(v_e_4028_, v_n_4029_);
lean_dec_ref(v_e_4028_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4031_, lean_object* v_n_4032_){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = l_Lean_Expr_getAppNumArgs(v_e_4031_);
v___x_4034_ = lean_nat_sub(v___x_4033_, v_n_4032_);
lean_dec(v___x_4033_);
v___x_4035_ = l_Lean_Expr_stripArgsN(v_e_4031_, v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4036_, lean_object* v_n_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Expr_getAppPrefix(v_e_4036_, v_n_4037_);
lean_dec(v_n_4037_);
lean_dec_ref(v_e_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4039_, lean_object* v_inst_4040_, lean_object* v_f_4041_, lean_object* v_x_4042_){
_start:
{
size_t v_sz_4043_; size_t v___x_4044_; lean_object* v___x_4045_; 
v_sz_4043_ = lean_array_size(v_args_4039_);
v___x_4044_ = ((size_t)0ULL);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4040_, v_f_4041_, v_sz_4043_, v___x_4044_, v_args_4039_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4047_, lean_object* v_inst_4048_, lean_object* v_f_4049_, lean_object* v_toSeq_4050_, lean_object* v_fn_4051_, lean_object* v_args_4052_){
_start:
{
lean_object* v_map_4053_; lean_object* v___f_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v_map_4053_ = lean_ctor_get(v_toFunctor_4047_, 0);
lean_inc(v_map_4053_);
lean_dec_ref(v_toFunctor_4047_);
lean_inc(v_f_4049_);
v___f_4054_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4054_, 0, v_args_4052_);
lean_closure_set(v___f_4054_, 1, v_inst_4048_);
lean_closure_set(v___f_4054_, 2, v_f_4049_);
v___x_4055_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4056_ = lean_apply_1(v_f_4049_, v_fn_4051_);
v___x_4057_ = lean_apply_4(v_map_4053_, lean_box(0), lean_box(0), v___x_4055_, v___x_4056_);
v___x_4058_ = lean_apply_4(v_toSeq_4050_, lean_box(0), lean_box(0), v___x_4057_, v___f_4054_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4059_, lean_object* v_f_4060_, lean_object* v_e_4061_){
_start:
{
lean_object* v_toApplicative_4062_; lean_object* v_toFunctor_4063_; lean_object* v_toSeq_4064_; lean_object* v___f_4065_; lean_object* v_dummy_4066_; lean_object* v_nargs_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_toApplicative_4062_ = lean_ctor_get(v_inst_4059_, 0);
v_toFunctor_4063_ = lean_ctor_get(v_toApplicative_4062_, 0);
lean_inc_ref(v_toFunctor_4063_);
v_toSeq_4064_ = lean_ctor_get(v_toApplicative_4062_, 2);
lean_inc(v_toSeq_4064_);
v___f_4065_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4065_, 0, v_toFunctor_4063_);
lean_closure_set(v___f_4065_, 1, v_inst_4059_);
lean_closure_set(v___f_4065_, 2, v_f_4060_);
lean_closure_set(v___f_4065_, 3, v_toSeq_4064_);
v_dummy_4066_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4067_ = l_Lean_Expr_getAppNumArgs(v_e_4061_);
lean_inc(v_nargs_4067_);
v___x_4068_ = lean_mk_array(v_nargs_4067_, v_dummy_4066_);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_nat_sub(v_nargs_4067_, v___x_4069_);
lean_dec(v_nargs_4067_);
v___x_4071_ = l_Lean_Expr_withAppAux___redArg(v___f_4065_, v_e_4061_, v___x_4068_, v___x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4072_, lean_object* v_inst_4073_, lean_object* v_f_4074_, lean_object* v_e_4075_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_Expr_traverseApp___redArg(v_inst_4073_, v_f_4074_, v_e_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4077_, lean_object* v_x_4078_, lean_object* v_x_4079_){
_start:
{
if (lean_obj_tag(v_x_4078_) == 5)
{
lean_object* v_fn_4080_; lean_object* v_arg_4081_; lean_object* v___x_4082_; 
v_fn_4080_ = lean_ctor_get(v_x_4078_, 0);
lean_inc_ref(v_fn_4080_);
v_arg_4081_ = lean_ctor_get(v_x_4078_, 1);
lean_inc_ref(v_arg_4081_);
lean_dec_ref_known(v_x_4078_, 2);
v___x_4082_ = lean_array_push(v_x_4079_, v_arg_4081_);
v_x_4078_ = v_fn_4080_;
v_x_4079_ = v___x_4082_;
goto _start;
}
else
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_apply_2(v_k_4077_, v_x_4078_, v_x_4079_);
return v___x_4084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4085_, lean_object* v_k_4086_, lean_object* v_x_4087_, lean_object* v_x_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4086_, v_x_4087_, v_x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4090_, lean_object* v_k_4091_){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = l_Lean_Expr_getAppNumArgs(v_e_4090_);
v___x_4093_ = lean_mk_empty_array_with_capacity(v___x_4092_);
lean_dec(v___x_4092_);
v___x_4094_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4091_, v_e_4090_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4095_, lean_object* v_e_4096_, lean_object* v_k_4097_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = l_Lean_Expr_getAppNumArgs(v_e_4096_);
v___x_4099_ = lean_mk_empty_array_with_capacity(v___x_4098_);
lean_dec(v___x_4098_);
v___x_4100_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4097_, v_e_4096_, v___x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4101_, lean_object* v_x_4102_, lean_object* v_x_4103_){
_start:
{
if (lean_obj_tag(v_x_4101_) == 5)
{
lean_object* v_fn_4104_; lean_object* v_arg_4105_; lean_object* v_zero_4106_; uint8_t v_isZero_4107_; 
v_fn_4104_ = lean_ctor_get(v_x_4101_, 0);
v_arg_4105_ = lean_ctor_get(v_x_4101_, 1);
v_zero_4106_ = lean_unsigned_to_nat(0u);
v_isZero_4107_ = lean_nat_dec_eq(v_x_4102_, v_zero_4106_);
if (v_isZero_4107_ == 1)
{
lean_dec(v_x_4102_);
lean_inc_ref(v_arg_4105_);
return v_arg_4105_;
}
else
{
lean_object* v_one_4108_; lean_object* v_n_4109_; 
v_one_4108_ = lean_unsigned_to_nat(1u);
v_n_4109_ = lean_nat_sub(v_x_4102_, v_one_4108_);
lean_dec(v_x_4102_);
v_x_4101_ = v_fn_4104_;
v_x_4102_ = v_n_4109_;
goto _start;
}
}
else
{
lean_dec(v_x_4102_);
lean_inc_ref(v_x_4103_);
return v_x_4103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4111_, lean_object* v_x_4112_, lean_object* v_x_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_Expr_getRevArgD(v_x_4111_, v_x_4112_, v_x_4113_);
lean_dec_ref(v_x_4113_);
lean_dec_ref(v_x_4111_);
return v_res_4114_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4117_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4118_ = lean_unsigned_to_nat(20u);
v___x_4119_ = lean_unsigned_to_nat(1288u);
v___x_4120_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4121_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4122_ = l_mkPanicMessageWithDecl(v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_, v___x_4117_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4123_, lean_object* v_x_4124_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 5)
{
lean_object* v_fn_4125_; lean_object* v_arg_4126_; lean_object* v_zero_4127_; uint8_t v_isZero_4128_; 
v_fn_4125_ = lean_ctor_get(v_x_4123_, 0);
v_arg_4126_ = lean_ctor_get(v_x_4123_, 1);
v_zero_4127_ = lean_unsigned_to_nat(0u);
v_isZero_4128_ = lean_nat_dec_eq(v_x_4124_, v_zero_4127_);
if (v_isZero_4128_ == 1)
{
lean_dec(v_x_4124_);
lean_inc_ref(v_arg_4126_);
return v_arg_4126_;
}
else
{
lean_object* v_one_4129_; lean_object* v_n_4130_; 
v_one_4129_ = lean_unsigned_to_nat(1u);
v_n_4130_ = lean_nat_sub(v_x_4124_, v_one_4129_);
lean_dec(v_x_4124_);
v_x_4123_ = v_fn_4125_;
v_x_4124_ = v_n_4130_;
goto _start;
}
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_dec(v_x_4124_);
v___x_4132_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4133_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4132_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4134_, lean_object* v_x_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Expr_getRevArg_x21(v_x_4134_, v_x_4135_);
lean_dec_ref(v_x_4134_);
return v_res_4136_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4138_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4139_ = lean_unsigned_to_nat(20u);
v___x_4140_ = lean_unsigned_to_nat(1295u);
v___x_4141_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4142_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4143_ = l_mkPanicMessageWithDecl(v___x_4142_, v___x_4141_, v___x_4140_, v___x_4139_, v___x_4138_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4144_, lean_object* v_x_4145_){
_start:
{
switch(lean_obj_tag(v_x_4144_))
{
case 10:
{
lean_object* v_expr_4146_; 
v_expr_4146_ = lean_ctor_get(v_x_4144_, 1);
v_x_4144_ = v_expr_4146_;
goto _start;
}
case 5:
{
lean_object* v_fn_4148_; lean_object* v_arg_4149_; lean_object* v_zero_4150_; uint8_t v_isZero_4151_; 
v_fn_4148_ = lean_ctor_get(v_x_4144_, 0);
v_arg_4149_ = lean_ctor_get(v_x_4144_, 1);
v_zero_4150_ = lean_unsigned_to_nat(0u);
v_isZero_4151_ = lean_nat_dec_eq(v_x_4145_, v_zero_4150_);
if (v_isZero_4151_ == 1)
{
lean_dec(v_x_4145_);
lean_inc_ref(v_arg_4149_);
return v_arg_4149_;
}
else
{
lean_object* v_one_4152_; lean_object* v_n_4153_; 
v_one_4152_ = lean_unsigned_to_nat(1u);
v_n_4153_ = lean_nat_sub(v_x_4145_, v_one_4152_);
lean_dec(v_x_4145_);
v_x_4144_ = v_fn_4148_;
v_x_4145_ = v_n_4153_;
goto _start;
}
}
default: 
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec(v_x_4145_);
v___x_4155_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4156_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4155_);
return v___x_4156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4157_, lean_object* v_x_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4157_, v_x_4158_);
lean_dec_ref(v_x_4157_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4160_, lean_object* v_i_4161_, lean_object* v_n_4162_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4163_ = lean_nat_sub(v_n_4162_, v_i_4161_);
v___x_4164_ = lean_unsigned_to_nat(1u);
v___x_4165_ = lean_nat_sub(v___x_4163_, v___x_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = l_Lean_Expr_getRevArg_x21(v_e_4160_, v___x_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4167_, lean_object* v_i_4168_, lean_object* v_n_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Expr_getArg_x21(v_e_4167_, v_i_4168_, v_n_4169_);
lean_dec(v_n_4169_);
lean_dec(v_i_4168_);
lean_dec_ref(v_e_4167_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4171_, lean_object* v_i_4172_, lean_object* v_n_4173_){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4174_ = lean_nat_sub(v_n_4173_, v_i_4172_);
v___x_4175_ = lean_unsigned_to_nat(1u);
v___x_4176_ = lean_nat_sub(v___x_4174_, v___x_4175_);
lean_dec(v___x_4174_);
v___x_4177_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4171_, v___x_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4178_, lean_object* v_i_4179_, lean_object* v_n_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Expr_getArg_x21_x27(v_e_4178_, v_i_4179_, v_n_4180_);
lean_dec(v_n_4180_);
lean_dec(v_i_4179_);
lean_dec_ref(v_e_4178_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4182_, lean_object* v_i_4183_, lean_object* v_v_u2080_4184_, lean_object* v_n_4185_){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4186_ = lean_nat_sub(v_n_4185_, v_i_4183_);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = lean_nat_sub(v___x_4186_, v___x_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = l_Lean_Expr_getRevArgD(v_e_4182_, v___x_4188_, v_v_u2080_4184_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4190_, lean_object* v_i_4191_, lean_object* v_v_u2080_4192_, lean_object* v_n_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Expr_getArgD(v_e_4190_, v_i_4191_, v_v_u2080_4192_, v_n_4193_);
lean_dec(v_n_4193_);
lean_dec_ref(v_v_u2080_4192_);
lean_dec(v_i_4191_);
lean_dec_ref(v_e_4190_);
return v_res_4194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4195_){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = l_Lean_Expr_looseBVarRange(v_e_4195_);
v___x_4198_ = lean_nat_dec_lt(v___x_4196_, v___x_4197_);
lean_dec(v___x_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4199_){
_start:
{
uint8_t v_res_4200_; lean_object* v_r_4201_; 
v_res_4200_ = l_Lean_Expr_hasLooseBVars(v_e_4199_);
lean_dec_ref(v_e_4199_);
v_r_4201_ = lean_box(v_res_4200_);
return v_r_4201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4202_){
_start:
{
if (lean_obj_tag(v_e_4202_) == 7)
{
lean_object* v_body_4203_; uint8_t v___x_4204_; 
v_body_4203_ = lean_ctor_get(v_e_4202_, 2);
v___x_4204_ = l_Lean_Expr_hasLooseBVars(v_body_4203_);
if (v___x_4204_ == 0)
{
uint8_t v___x_4205_; 
v___x_4205_ = 1;
return v___x_4205_;
}
else
{
uint8_t v___x_4206_; 
v___x_4206_ = 0;
return v___x_4206_;
}
}
else
{
uint8_t v___x_4207_; 
v___x_4207_ = 0;
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4208_){
_start:
{
uint8_t v_res_4209_; lean_object* v_r_4210_; 
v_res_4209_ = l_Lean_Expr_isArrow(v_e_4208_);
lean_dec_ref(v_e_4208_);
v_r_4210_ = lean_box(v_res_4209_);
return v_r_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4213_, lean_object* v_bvarIdx_4214_){
_start:
{
uint8_t v_res_4215_; lean_object* v_r_4216_; 
v_res_4215_ = lean_expr_has_loose_bvar(v_e_4213_, v_bvarIdx_4214_);
lean_dec(v_bvarIdx_4214_);
lean_dec_ref(v_e_4213_);
v_r_4216_ = lean_box(v_res_4215_);
return v_r_4216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4217_, lean_object* v_bvarIdx_4218_, uint8_t v_considerRange_4219_){
_start:
{
if (lean_obj_tag(v_e_4217_) == 7)
{
lean_object* v_binderType_4220_; lean_object* v_body_4221_; uint8_t v_binderInfo_4222_; uint8_t v___y_4224_; uint8_t v___x_4228_; 
v_binderType_4220_ = lean_ctor_get(v_e_4217_, 1);
v_body_4221_ = lean_ctor_get(v_e_4217_, 2);
v_binderInfo_4222_ = lean_ctor_get_uint8(v_e_4217_, sizeof(void*)*3 + 8);
v___x_4228_ = lean_expr_has_loose_bvar(v_binderType_4220_, v_bvarIdx_4218_);
if (v___x_4228_ == 0)
{
v___y_4224_ = v___x_4228_;
goto v___jp_4223_;
}
else
{
uint8_t v___x_4229_; 
v___x_4229_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4222_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4221_, v___x_4230_, v_considerRange_4219_);
v___y_4224_ = v___x_4231_;
goto v___jp_4223_;
}
else
{
v___y_4224_ = v___x_4229_;
goto v___jp_4223_;
}
}
v___jp_4223_:
{
if (v___y_4224_ == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_nat_add(v_bvarIdx_4218_, v___x_4225_);
lean_dec(v_bvarIdx_4218_);
v_e_4217_ = v_body_4221_;
v_bvarIdx_4218_ = v___x_4226_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4218_);
return v___y_4224_;
}
}
}
else
{
if (v_considerRange_4219_ == 0)
{
lean_dec(v_bvarIdx_4218_);
return v_considerRange_4219_;
}
else
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_expr_has_loose_bvar(v_e_4217_, v_bvarIdx_4218_);
lean_dec(v_bvarIdx_4218_);
return v___x_4232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4233_, lean_object* v_bvarIdx_4234_, lean_object* v_considerRange_4235_){
_start:
{
uint8_t v_considerRange_boxed_4236_; uint8_t v_res_4237_; lean_object* v_r_4238_; 
v_considerRange_boxed_4236_ = lean_unbox(v_considerRange_4235_);
v_res_4237_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4233_, v_bvarIdx_4234_, v_considerRange_boxed_4236_);
lean_dec_ref(v_e_4233_);
v_r_4238_ = lean_box(v_res_4237_);
return v_r_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4242_, lean_object* v_s_4243_, lean_object* v_d_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = lean_expr_lower_loose_bvars(v_e_4242_, v_s_4243_, v_d_4244_);
lean_dec(v_d_4244_);
lean_dec(v_s_4243_);
lean_dec_ref(v_e_4242_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4249_, lean_object* v_s_4250_, lean_object* v_d_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = lean_expr_lift_loose_bvars(v_e_4249_, v_s_4250_, v_d_4251_);
lean_dec(v_d_4251_);
lean_dec(v_s_4250_);
lean_dec_ref(v_e_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4253_, lean_object* v_numParams_4254_, uint8_t v_considerRange_4255_){
_start:
{
if (lean_obj_tag(v_e_4253_) == 7)
{
lean_object* v_binderName_4256_; lean_object* v_binderType_4257_; lean_object* v_body_4258_; uint8_t v_binderInfo_4259_; lean_object* v_zero_4260_; uint8_t v_isZero_4261_; 
v_binderName_4256_ = lean_ctor_get(v_e_4253_, 0);
v_binderType_4257_ = lean_ctor_get(v_e_4253_, 1);
v_body_4258_ = lean_ctor_get(v_e_4253_, 2);
v_binderInfo_4259_ = lean_ctor_get_uint8(v_e_4253_, sizeof(void*)*3 + 8);
v_zero_4260_ = lean_unsigned_to_nat(0u);
v_isZero_4261_ = lean_nat_dec_eq(v_numParams_4254_, v_zero_4260_);
if (v_isZero_4261_ == 0)
{
lean_object* v_one_4262_; lean_object* v_n_4263_; lean_object* v_b_4264_; uint8_t v___y_4266_; uint8_t v___x_4270_; 
lean_inc_ref(v_body_4258_);
lean_inc_ref(v_binderType_4257_);
lean_inc(v_binderName_4256_);
lean_dec_ref_known(v_e_4253_, 3);
v_one_4262_ = lean_unsigned_to_nat(1u);
v_n_4263_ = lean_nat_sub(v_numParams_4254_, v_one_4262_);
v_b_4264_ = l_Lean_Expr_inferImplicit(v_body_4258_, v_n_4263_, v_considerRange_4255_);
lean_dec(v_n_4263_);
v___x_4270_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4259_);
if (v___x_4270_ == 0)
{
v___y_4266_ = v___x_4270_;
goto v___jp_4265_;
}
else
{
uint8_t v___x_4271_; 
v___x_4271_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4264_, v_zero_4260_, v_considerRange_4255_);
v___y_4266_ = v___x_4271_;
goto v___jp_4265_;
}
v___jp_4265_:
{
if (v___y_4266_ == 0)
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Expr_forallE___override(v_binderName_4256_, v_binderType_4257_, v_b_4264_, v_binderInfo_4259_);
return v___x_4267_;
}
else
{
uint8_t v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = 1;
v___x_4269_ = l_Lean_Expr_forallE___override(v_binderName_4256_, v_binderType_4257_, v_b_4264_, v___x_4268_);
return v___x_4269_;
}
}
}
else
{
return v_e_4253_;
}
}
else
{
return v_e_4253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4272_, lean_object* v_numParams_4273_, lean_object* v_considerRange_4274_){
_start:
{
uint8_t v_considerRange_boxed_4275_; lean_object* v_res_4276_; 
v_considerRange_boxed_4275_ = lean_unbox(v_considerRange_4274_);
v_res_4276_ = l_Lean_Expr_inferImplicit(v_e_4272_, v_numParams_4273_, v_considerRange_boxed_4275_);
lean_dec(v_numParams_4273_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4277_, lean_object* v_binderInfos_x3f_4278_){
_start:
{
if (lean_obj_tag(v_e_4277_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4278_) == 1)
{
lean_object* v_binderName_4279_; lean_object* v_binderType_4280_; lean_object* v_body_4281_; uint8_t v_binderInfo_4282_; lean_object* v_head_4283_; lean_object* v_tail_4284_; lean_object* v_b_4285_; 
v_binderName_4279_ = lean_ctor_get(v_e_4277_, 0);
lean_inc(v_binderName_4279_);
v_binderType_4280_ = lean_ctor_get(v_e_4277_, 1);
lean_inc_ref(v_binderType_4280_);
v_body_4281_ = lean_ctor_get(v_e_4277_, 2);
lean_inc_ref(v_body_4281_);
v_binderInfo_4282_ = lean_ctor_get_uint8(v_e_4277_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4277_, 3);
v_head_4283_ = lean_ctor_get(v_binderInfos_x3f_4278_, 0);
v_tail_4284_ = lean_ctor_get(v_binderInfos_x3f_4278_, 1);
v_b_4285_ = l_Lean_Expr_updateForallBinderInfos(v_body_4281_, v_tail_4284_);
if (lean_obj_tag(v_head_4283_) == 0)
{
lean_object* v___x_4286_; 
v___x_4286_ = l_Lean_Expr_forallE___override(v_binderName_4279_, v_binderType_4280_, v_b_4285_, v_binderInfo_4282_);
return v___x_4286_;
}
else
{
lean_object* v_val_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; 
v_val_4287_ = lean_ctor_get(v_head_4283_, 0);
v___x_4288_ = lean_unbox(v_val_4287_);
v___x_4289_ = l_Lean_Expr_forallE___override(v_binderName_4279_, v_binderType_4280_, v_b_4285_, v___x_4288_);
return v___x_4289_;
}
}
else
{
return v_e_4277_;
}
}
else
{
return v_e_4277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4290_, lean_object* v_binderInfos_x3f_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Expr_updateForallBinderInfos(v_e_4290_, v_binderInfos_x3f_4291_);
lean_dec(v_binderInfos_x3f_4291_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4293_, lean_object* v_binderNames_x3f_4294_){
_start:
{
switch(lean_obj_tag(v_e_4293_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4294_) == 1)
{
lean_object* v_binderName_4295_; lean_object* v_binderType_4296_; lean_object* v_body_4297_; uint8_t v_binderInfo_4298_; lean_object* v_head_4299_; lean_object* v_tail_4300_; lean_object* v_b_4301_; 
v_binderName_4295_ = lean_ctor_get(v_e_4293_, 0);
lean_inc(v_binderName_4295_);
v_binderType_4296_ = lean_ctor_get(v_e_4293_, 1);
lean_inc_ref(v_binderType_4296_);
v_body_4297_ = lean_ctor_get(v_e_4293_, 2);
lean_inc_ref(v_body_4297_);
v_binderInfo_4298_ = lean_ctor_get_uint8(v_e_4293_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4293_, 3);
v_head_4299_ = lean_ctor_get(v_binderNames_x3f_4294_, 0);
lean_inc(v_head_4299_);
v_tail_4300_ = lean_ctor_get(v_binderNames_x3f_4294_, 1);
lean_inc(v_tail_4300_);
lean_dec_ref_known(v_binderNames_x3f_4294_, 2);
v_b_4301_ = l_Lean_Expr_updateBinderNames(v_body_4297_, v_tail_4300_);
if (lean_obj_tag(v_head_4299_) == 0)
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Expr_forallE___override(v_binderName_4295_, v_binderType_4296_, v_b_4301_, v_binderInfo_4298_);
return v___x_4302_;
}
else
{
lean_object* v_val_4303_; lean_object* v___x_4304_; 
lean_dec(v_binderName_4295_);
v_val_4303_ = lean_ctor_get(v_head_4299_, 0);
lean_inc(v_val_4303_);
lean_dec_ref_known(v_head_4299_, 1);
v___x_4304_ = l_Lean_Expr_forallE___override(v_val_4303_, v_binderType_4296_, v_b_4301_, v_binderInfo_4298_);
return v___x_4304_;
}
}
else
{
lean_dec(v_binderNames_x3f_4294_);
return v_e_4293_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4294_) == 1)
{
lean_object* v_binderName_4305_; lean_object* v_binderType_4306_; lean_object* v_body_4307_; uint8_t v_binderInfo_4308_; lean_object* v_head_4309_; lean_object* v_tail_4310_; lean_object* v_b_4311_; 
v_binderName_4305_ = lean_ctor_get(v_e_4293_, 0);
lean_inc(v_binderName_4305_);
v_binderType_4306_ = lean_ctor_get(v_e_4293_, 1);
lean_inc_ref(v_binderType_4306_);
v_body_4307_ = lean_ctor_get(v_e_4293_, 2);
lean_inc_ref(v_body_4307_);
v_binderInfo_4308_ = lean_ctor_get_uint8(v_e_4293_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4293_, 3);
v_head_4309_ = lean_ctor_get(v_binderNames_x3f_4294_, 0);
lean_inc(v_head_4309_);
v_tail_4310_ = lean_ctor_get(v_binderNames_x3f_4294_, 1);
lean_inc(v_tail_4310_);
lean_dec_ref_known(v_binderNames_x3f_4294_, 2);
v_b_4311_ = l_Lean_Expr_updateBinderNames(v_body_4307_, v_tail_4310_);
if (lean_obj_tag(v_head_4309_) == 0)
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_Expr_lam___override(v_binderName_4305_, v_binderType_4306_, v_b_4311_, v_binderInfo_4308_);
return v___x_4312_;
}
else
{
lean_object* v_val_4313_; lean_object* v___x_4314_; 
lean_dec(v_binderName_4305_);
v_val_4313_ = lean_ctor_get(v_head_4309_, 0);
lean_inc(v_val_4313_);
lean_dec_ref_known(v_head_4309_, 1);
v___x_4314_ = l_Lean_Expr_lam___override(v_val_4313_, v_binderType_4306_, v_b_4311_, v_binderInfo_4308_);
return v___x_4314_;
}
}
else
{
lean_dec(v_binderNames_x3f_4294_);
return v_e_4293_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4294_);
return v_e_4293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4317_, lean_object* v_subst_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = lean_expr_instantiate(v_e_4317_, v_subst_4318_);
lean_dec_ref(v_subst_4318_);
lean_dec_ref(v_e_4317_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4322_, lean_object* v_subst_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = lean_expr_instantiate1(v_e_4322_, v_subst_4323_);
lean_dec_ref(v_subst_4323_);
lean_dec_ref(v_e_4322_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4327_, lean_object* v_subst_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = lean_expr_instantiate_rev(v_e_4327_, v_subst_4328_);
lean_dec_ref(v_subst_4328_);
lean_dec_ref(v_e_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4334_, lean_object* v_beginIdx_4335_, lean_object* v_endIdx_4336_, lean_object* v_subst_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = lean_expr_instantiate_range(v_e_4334_, v_beginIdx_4335_, v_endIdx_4336_, v_subst_4337_);
lean_dec_ref(v_subst_4337_);
lean_dec(v_endIdx_4336_);
lean_dec(v_beginIdx_4335_);
lean_dec_ref(v_e_4334_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4343_, lean_object* v_beginIdx_4344_, lean_object* v_endIdx_4345_, lean_object* v_subst_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = lean_expr_instantiate_rev_range(v_e_4343_, v_beginIdx_4344_, v_endIdx_4345_, v_subst_4346_);
lean_dec_ref(v_subst_4346_);
lean_dec(v_endIdx_4345_);
lean_dec(v_beginIdx_4344_);
lean_dec_ref(v_e_4343_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4350_, lean_object* v_xs_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = lean_expr_abstract(v_e_4350_, v_xs_4351_);
lean_dec_ref(v_xs_4351_);
lean_dec_ref(v_e_4350_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4356_, lean_object* v_n_4357_, lean_object* v_xs_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = lean_expr_abstract_range(v_e_4356_, v_n_4357_, v_xs_4358_);
lean_dec_ref(v_xs_4358_);
lean_dec(v_n_4357_);
lean_dec_ref(v_e_4356_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4360_, lean_object* v_fvar_4361_, lean_object* v_v_4362_){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4363_ = lean_unsigned_to_nat(1u);
v___x_4364_ = lean_mk_empty_array_with_capacity(v___x_4363_);
v___x_4365_ = lean_array_push(v___x_4364_, v_fvar_4361_);
v___x_4366_ = lean_expr_abstract(v_e_4360_, v___x_4365_);
lean_dec_ref(v___x_4365_);
v___x_4367_ = lean_expr_instantiate1(v___x_4366_, v_v_4362_);
lean_dec_ref(v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4368_, lean_object* v_fvar_4369_, lean_object* v_v_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Expr_replaceFVar(v_e_4368_, v_fvar_4369_, v_v_4370_);
lean_dec_ref(v_v_4370_);
lean_dec_ref(v_e_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4372_, lean_object* v_fvarId_4373_, lean_object* v_v_4374_){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = l_Lean_Expr_fvar___override(v_fvarId_4373_);
v___x_4376_ = l_Lean_Expr_replaceFVar(v_e_4372_, v___x_4375_, v_v_4374_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4377_, lean_object* v_fvarId_4378_, lean_object* v_v_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l_Lean_Expr_replaceFVarId(v_e_4377_, v_fvarId_4378_, v_v_4379_);
lean_dec_ref(v_v_4379_);
lean_dec_ref(v_e_4377_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4381_, lean_object* v_fvars_4382_, lean_object* v_vs_4383_){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = lean_expr_abstract(v_e_4381_, v_fvars_4382_);
v___x_4385_ = lean_expr_instantiate_rev(v___x_4384_, v_vs_4383_);
lean_dec_ref(v___x_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4386_, lean_object* v_fvars_4387_, lean_object* v_vs_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_Expr_replaceFVars(v_e_4386_, v_fvars_4387_, v_vs_4388_);
lean_dec_ref(v_vs_4388_);
lean_dec_ref(v_fvars_4387_);
lean_dec_ref(v_e_4386_);
return v_res_4389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4392_){
_start:
{
switch(lean_obj_tag(v_x_4392_))
{
case 4:
{
uint8_t v___x_4393_; 
v___x_4393_ = 1;
return v___x_4393_;
}
case 3:
{
uint8_t v___x_4394_; 
v___x_4394_ = 1;
return v___x_4394_;
}
case 0:
{
uint8_t v___x_4395_; 
v___x_4395_ = 1;
return v___x_4395_;
}
case 9:
{
uint8_t v___x_4396_; 
v___x_4396_ = 1;
return v___x_4396_;
}
case 2:
{
uint8_t v___x_4397_; 
v___x_4397_ = 1;
return v___x_4397_;
}
case 1:
{
uint8_t v___x_4398_; 
v___x_4398_ = 1;
return v___x_4398_;
}
default: 
{
uint8_t v___x_4399_; 
v___x_4399_ = 0;
return v___x_4399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4400_){
_start:
{
uint8_t v_res_4401_; lean_object* v_r_4402_; 
v_res_4401_ = l_Lean_Expr_isAtomic(v_x_4400_);
lean_dec_ref(v_x_4400_);
v_r_4402_ = lean_box(v_res_4401_);
return v_r_4402_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4408_ = lean_box(0);
v___x_4409_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4410_ = l_Lean_Expr_const___override(v___x_4409_, v___x_4408_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4411_, lean_object* v_proof_4412_){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4414_ = l_Lean_mkAppB(v___x_4413_, v_pred_4411_, v_proof_4412_);
return v___x_4414_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4419_ = lean_box(0);
v___x_4420_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4421_ = l_Lean_Expr_const___override(v___x_4420_, v___x_4419_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4422_, lean_object* v_proof_4423_){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4425_ = l_Lean_mkAppB(v___x_4424_, v_pred_4422_, v_proof_4423_);
return v___x_4425_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4426_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4428_){
_start:
{
lean_inc_ref(v_val_4428_);
return v_val_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4429_);
lean_dec_ref(v_val_4429_);
return v_res_4430_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4433_, lean_object* v_x_4434_){
_start:
{
uint8_t v___x_4435_; 
v___x_4435_ = lean_expr_equal(v_x_4433_, v_x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4436_, lean_object* v_x_4437_){
_start:
{
uint8_t v_res_4438_; lean_object* v_r_4439_; 
v_res_4438_ = l_Lean_ExprStructEq_beq(v_x_4436_, v_x_4437_);
lean_dec_ref(v_x_4437_);
lean_dec_ref(v_x_4436_);
v_r_4439_ = lean_box(v_res_4438_);
return v_r_4439_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4440_){
_start:
{
uint64_t v___x_4441_; 
v___x_4441_ = l_Lean_Expr_hash(v_x_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4442_){
_start:
{
uint64_t v_res_4443_; lean_object* v_r_4444_; 
v_res_4443_ = l_Lean_ExprStructEq_hash(v_x_4442_);
lean_dec_ref(v_x_4442_);
v_r_4444_ = lean_box_uint64(v_res_4443_);
return v_r_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4451_, lean_object* v_start_4452_, lean_object* v_b_4453_, lean_object* v_i_4454_){
_start:
{
uint8_t v___x_4455_; 
v___x_4455_ = lean_nat_dec_le(v_i_4454_, v_start_4452_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v_i_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4456_ = lean_unsigned_to_nat(1u);
v_i_4457_ = lean_nat_sub(v_i_4454_, v___x_4456_);
lean_dec(v_i_4454_);
v___x_4458_ = l_Lean_instInhabitedExpr;
v___x_4459_ = lean_array_get_borrowed(v___x_4458_, v_revArgs_4451_, v_i_4457_);
lean_inc(v___x_4459_);
v___x_4460_ = l_Lean_Expr_app___override(v_b_4453_, v___x_4459_);
v_b_4453_ = v___x_4460_;
v_i_4454_ = v_i_4457_;
goto _start;
}
else
{
lean_dec(v_i_4454_);
return v_b_4453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4462_, lean_object* v_start_4463_, lean_object* v_b_4464_, lean_object* v_i_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4462_, v_start_4463_, v_b_4464_, v_i_4465_);
lean_dec(v_start_4463_);
lean_dec_ref(v_revArgs_4462_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4467_, lean_object* v_beginIdx_4468_, lean_object* v_endIdx_4469_, lean_object* v_revArgs_4470_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4470_, v_beginIdx_4468_, v_f_4467_, v_endIdx_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4472_, lean_object* v_beginIdx_4473_, lean_object* v_endIdx_4474_, lean_object* v_revArgs_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_Expr_mkAppRevRange(v_f_4472_, v_beginIdx_4473_, v_endIdx_4474_, v_revArgs_4475_);
lean_dec_ref(v_revArgs_4475_);
lean_dec(v_beginIdx_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4477_, uint8_t v_useZeta_4478_, uint8_t v_preserveMData_4479_, lean_object* v_sz_4480_, lean_object* v_e_4481_, lean_object* v_i_4482_){
_start:
{
switch(lean_obj_tag(v_e_4481_))
{
case 6:
{
lean_object* v_body_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; uint8_t v___x_4491_; 
v_body_4488_ = lean_ctor_get(v_e_4481_, 2);
lean_inc_ref(v_body_4488_);
lean_dec_ref_known(v_e_4481_, 3);
v___x_4489_ = lean_unsigned_to_nat(1u);
v___x_4490_ = lean_nat_add(v_i_4482_, v___x_4489_);
lean_dec(v_i_4482_);
v___x_4491_ = lean_nat_dec_lt(v___x_4490_, v_sz_4480_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; 
lean_dec(v___x_4490_);
v___x_4492_ = lean_expr_instantiate(v_body_4488_, v_revArgs_4477_);
lean_dec_ref(v_body_4488_);
return v___x_4492_;
}
else
{
v_e_4481_ = v_body_4488_;
v_i_4482_ = v___x_4490_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4478_ == 0)
{
goto v___jp_4483_;
}
else
{
lean_object* v_value_4494_; lean_object* v_body_4495_; uint8_t v___x_4496_; 
v_value_4494_ = lean_ctor_get(v_e_4481_, 2);
v_body_4495_ = lean_ctor_get(v_e_4481_, 3);
v___x_4496_ = lean_nat_dec_lt(v_i_4482_, v_sz_4480_);
if (v___x_4496_ == 0)
{
goto v___jp_4483_;
}
else
{
lean_object* v___x_4497_; 
lean_inc_ref(v_body_4495_);
lean_inc_ref(v_value_4494_);
lean_dec_ref_known(v_e_4481_, 4);
v___x_4497_ = lean_expr_instantiate1(v_body_4495_, v_value_4494_);
lean_dec_ref(v_value_4494_);
lean_dec_ref(v_body_4495_);
v_e_4481_ = v___x_4497_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4479_ == 0)
{
lean_object* v_expr_4499_; 
v_expr_4499_ = lean_ctor_get(v_e_4481_, 1);
lean_inc_ref(v_expr_4499_);
lean_dec_ref_known(v_e_4481_, 2);
v_e_4481_ = v_expr_4499_;
goto _start;
}
else
{
goto v___jp_4483_;
}
}
default: 
{
goto v___jp_4483_;
}
}
v___jp_4483_:
{
lean_object* v_n_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v_n_4484_ = lean_nat_sub(v_sz_4480_, v_i_4482_);
lean_dec(v_i_4482_);
v___x_4485_ = lean_expr_instantiate_range(v_e_4481_, v_n_4484_, v_sz_4480_, v_revArgs_4477_);
lean_dec_ref(v_e_4481_);
v___x_4486_ = lean_unsigned_to_nat(0u);
v___x_4487_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4477_, v___x_4486_, v___x_4485_, v_n_4484_);
return v___x_4487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4501_, lean_object* v_useZeta_4502_, lean_object* v_preserveMData_4503_, lean_object* v_sz_4504_, lean_object* v_e_4505_, lean_object* v_i_4506_){
_start:
{
uint8_t v_useZeta_boxed_4507_; uint8_t v_preserveMData_boxed_4508_; lean_object* v_res_4509_; 
v_useZeta_boxed_4507_ = lean_unbox(v_useZeta_4502_);
v_preserveMData_boxed_4508_ = lean_unbox(v_preserveMData_4503_);
v_res_4509_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4501_, v_useZeta_boxed_4507_, v_preserveMData_boxed_4508_, v_sz_4504_, v_e_4505_, v_i_4506_);
lean_dec(v_sz_4504_);
lean_dec_ref(v_revArgs_4501_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4510_, lean_object* v_revArgs_4511_, uint8_t v_useZeta_4512_, uint8_t v_preserveMData_4513_){
_start:
{
lean_object* v_sz_4514_; lean_object* v___x_4515_; uint8_t v___x_4516_; 
v_sz_4514_ = lean_array_get_size(v_revArgs_4511_);
v___x_4515_ = lean_unsigned_to_nat(0u);
v___x_4516_ = lean_nat_dec_eq(v_sz_4514_, v___x_4515_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; 
v___x_4517_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4511_, v_useZeta_4512_, v_preserveMData_4513_, v_sz_4514_, v_f_4510_, v___x_4515_);
return v___x_4517_;
}
else
{
return v_f_4510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4518_, lean_object* v_revArgs_4519_, lean_object* v_useZeta_4520_, lean_object* v_preserveMData_4521_){
_start:
{
uint8_t v_useZeta_boxed_4522_; uint8_t v_preserveMData_boxed_4523_; lean_object* v_res_4524_; 
v_useZeta_boxed_4522_ = lean_unbox(v_useZeta_4520_);
v_preserveMData_boxed_4523_ = lean_unbox(v_preserveMData_4521_);
v_res_4524_ = l_Lean_Expr_betaRev(v_f_4518_, v_revArgs_4519_, v_useZeta_boxed_4522_, v_preserveMData_boxed_4523_);
lean_dec_ref(v_revArgs_4519_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4525_, lean_object* v_args_4526_){
_start:
{
lean_object* v___x_4527_; uint8_t v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = l_Array_reverse___redArg(v_args_4526_);
v___x_4528_ = 0;
v___x_4529_ = l_Lean_Expr_betaRev(v_f_4525_, v___x_4527_, v___x_4528_, v___x_4528_);
lean_dec_ref(v___x_4527_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4530_){
_start:
{
switch(lean_obj_tag(v_x_4530_))
{
case 6:
{
lean_object* v_body_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v_body_4531_ = lean_ctor_get(v_x_4530_, 2);
v___x_4532_ = l_Lean_Expr_getNumHeadLambdas(v_body_4531_);
v___x_4533_ = lean_unsigned_to_nat(1u);
v___x_4534_ = lean_nat_add(v___x_4532_, v___x_4533_);
lean_dec(v___x_4532_);
return v___x_4534_;
}
case 10:
{
lean_object* v_expr_4535_; 
v_expr_4535_ = lean_ctor_get(v_x_4530_, 1);
v_x_4530_ = v_expr_4535_;
goto _start;
}
default: 
{
lean_object* v___x_4537_; 
v___x_4537_ = lean_unsigned_to_nat(0u);
return v___x_4537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_Expr_getNumHeadLambdas(v_x_4538_);
lean_dec_ref(v_x_4538_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4540_){
_start:
{
switch(lean_obj_tag(v_x_4540_))
{
case 6:
{
lean_object* v_body_4541_; 
v_body_4541_ = lean_ctor_get(v_x_4540_, 2);
v_x_4540_ = v_body_4541_;
goto _start;
}
case 10:
{
lean_object* v_expr_4543_; 
v_expr_4543_ = lean_ctor_get(v_x_4540_, 1);
v_x_4540_ = v_expr_4543_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4540_);
return v_x_4540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Expr_getLambdaBody(v_x_4545_);
lean_dec_ref(v_x_4545_);
return v_res_4546_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4547_, lean_object* v_x_4548_){
_start:
{
switch(lean_obj_tag(v_x_4548_))
{
case 6:
{
uint8_t v___x_4549_; 
v___x_4549_ = 1;
return v___x_4549_;
}
case 8:
{
if (v_useZeta_4547_ == 0)
{
return v_useZeta_4547_;
}
else
{
lean_object* v_body_4550_; 
v_body_4550_ = lean_ctor_get(v_x_4548_, 3);
v_x_4548_ = v_body_4550_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4552_; 
v_expr_4552_ = lean_ctor_get(v_x_4548_, 1);
v_x_4548_ = v_expr_4552_;
goto _start;
}
default: 
{
uint8_t v___x_4554_; 
v___x_4554_ = 0;
return v___x_4554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4555_, lean_object* v_x_4556_){
_start:
{
uint8_t v_useZeta_boxed_4557_; uint8_t v_res_4558_; lean_object* v_r_4559_; 
v_useZeta_boxed_4557_ = lean_unbox(v_useZeta_4555_);
v_res_4558_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4557_, v_x_4556_);
lean_dec_ref(v_x_4556_);
v_r_4559_ = lean_box(v_res_4558_);
return v_r_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4560_){
_start:
{
lean_object* v_f_4561_; uint8_t v___x_4562_; uint8_t v___x_4563_; 
v_f_4561_ = l_Lean_Expr_getAppFn(v_e_4560_);
v___x_4562_ = 0;
v___x_4563_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4562_, v_f_4561_);
if (v___x_4563_ == 0)
{
lean_dec_ref(v_f_4561_);
return v_e_4560_;
}
else
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4564_ = l_Lean_Expr_getAppNumArgs(v_e_4560_);
v___x_4565_ = lean_mk_empty_array_with_capacity(v___x_4564_);
lean_dec(v___x_4564_);
v___x_4566_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4560_, v___x_4565_);
v___x_4567_ = l_Lean_Expr_betaRev(v_f_4561_, v___x_4566_, v___x_4562_, v___x_4562_);
lean_dec_ref(v___x_4566_);
return v___x_4567_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4568_, uint8_t v_useZeta_4569_){
_start:
{
uint8_t v___x_4570_; 
v___x_4570_ = l_Lean_Expr_isApp(v_e_4568_);
if (v___x_4570_ == 0)
{
return v___x_4570_;
}
else
{
lean_object* v___x_4571_; uint8_t v___x_4572_; 
v___x_4571_ = l_Lean_Expr_getAppFn(v_e_4568_);
v___x_4572_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4569_, v___x_4571_);
lean_dec_ref(v___x_4571_);
return v___x_4572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4573_, lean_object* v_useZeta_4574_){
_start:
{
uint8_t v_useZeta_boxed_4575_; uint8_t v_res_4576_; lean_object* v_r_4577_; 
v_useZeta_boxed_4575_ = lean_unbox(v_useZeta_4574_);
v_res_4576_ = l_Lean_Expr_isHeadBetaTarget(v_e_4573_, v_useZeta_boxed_4575_);
lean_dec_ref(v_e_4573_);
v_r_4577_ = lean_box(v_res_4576_);
return v_r_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4578_, lean_object* v_x_4579_, lean_object* v_x_4580_){
_start:
{
lean_object* v_f_4582_; 
if (lean_obj_tag(v_x_4578_) == 5)
{
lean_object* v_arg_4586_; 
v_arg_4586_ = lean_ctor_get(v_x_4578_, 1);
if (lean_obj_tag(v_arg_4586_) == 0)
{
lean_object* v_fn_4587_; lean_object* v_deBruijnIndex_4588_; lean_object* v_zero_4589_; uint8_t v_isZero_4590_; 
v_fn_4587_ = lean_ctor_get(v_x_4578_, 0);
v_deBruijnIndex_4588_ = lean_ctor_get(v_arg_4586_, 0);
v_zero_4589_ = lean_unsigned_to_nat(0u);
v_isZero_4590_ = lean_nat_dec_eq(v_x_4579_, v_zero_4589_);
if (v_isZero_4590_ == 1)
{
lean_dec(v_x_4580_);
lean_dec(v_x_4579_);
v_f_4582_ = v_x_4578_;
goto v___jp_4581_;
}
else
{
uint8_t v___x_4591_; 
lean_inc(v_deBruijnIndex_4588_);
lean_inc_ref(v_fn_4587_);
lean_dec_ref_known(v_x_4578_, 2);
v___x_4591_ = lean_nat_dec_eq(v_deBruijnIndex_4588_, v_x_4580_);
lean_dec(v_deBruijnIndex_4588_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_dec_ref(v_fn_4587_);
lean_dec(v_x_4580_);
lean_dec(v_x_4579_);
v___x_4592_ = lean_box(0);
return v___x_4592_;
}
else
{
lean_object* v_one_4593_; lean_object* v_n_4594_; lean_object* v___x_4595_; 
v_one_4593_ = lean_unsigned_to_nat(1u);
v_n_4594_ = lean_nat_sub(v_x_4579_, v_one_4593_);
lean_dec(v_x_4579_);
v___x_4595_ = lean_nat_add(v_x_4580_, v_one_4593_);
lean_dec(v_x_4580_);
v_x_4578_ = v_fn_4587_;
v_x_4579_ = v_n_4594_;
v_x_4580_ = v___x_4595_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4597_; uint8_t v_isZero_4598_; 
lean_dec(v_x_4580_);
v_zero_4597_ = lean_unsigned_to_nat(0u);
v_isZero_4598_ = lean_nat_dec_eq(v_x_4579_, v_zero_4597_);
lean_dec(v_x_4579_);
if (v_isZero_4598_ == 1)
{
v_f_4582_ = v_x_4578_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4599_; 
lean_dec_ref_known(v_x_4578_, 2);
v___x_4599_ = lean_box(0);
return v___x_4599_;
}
}
}
else
{
lean_object* v_zero_4600_; uint8_t v_isZero_4601_; 
lean_dec(v_x_4580_);
v_zero_4600_ = lean_unsigned_to_nat(0u);
v_isZero_4601_ = lean_nat_dec_eq(v_x_4579_, v_zero_4600_);
lean_dec(v_x_4579_);
if (v_isZero_4601_ == 1)
{
v_f_4582_ = v_x_4578_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4602_; 
lean_dec_ref(v_x_4578_);
v___x_4602_ = lean_box(0);
return v___x_4602_;
}
}
v___jp_4581_:
{
uint8_t v___x_4583_; 
v___x_4583_ = l_Lean_Expr_hasLooseBVars(v_f_4582_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4584_, 0, v_f_4582_);
return v___x_4584_;
}
else
{
lean_object* v___x_4585_; 
lean_dec_ref(v_f_4582_);
v___x_4585_ = lean_box(0);
return v___x_4585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4603_, lean_object* v_x_4604_){
_start:
{
if (lean_obj_tag(v_x_4603_) == 6)
{
lean_object* v_body_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v_body_4605_ = lean_ctor_get(v_x_4603_, 2);
lean_inc_ref(v_body_4605_);
lean_dec_ref_known(v_x_4603_, 3);
v___x_4606_ = lean_unsigned_to_nat(1u);
v___x_4607_ = lean_nat_add(v_x_4604_, v___x_4606_);
lean_dec(v_x_4604_);
v_x_4603_ = v_body_4605_;
v_x_4604_ = v___x_4607_;
goto _start;
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = lean_unsigned_to_nat(0u);
v___x_4610_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4603_, v_x_4604_, v___x_4609_);
return v___x_4610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4611_){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4612_ = lean_unsigned_to_nat(0u);
v___x_4613_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4611_, v___x_4612_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4614_){
_start:
{
if (lean_obj_tag(v_x_4614_) == 6)
{
lean_object* v_body_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v_body_4615_ = lean_ctor_get(v_x_4614_, 2);
lean_inc_ref(v_body_4615_);
lean_dec_ref_known(v_x_4614_, 3);
v___x_4616_ = lean_unsigned_to_nat(1u);
v___x_4617_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4615_, v___x_4616_);
return v___x_4617_;
}
else
{
lean_object* v___x_4618_; 
lean_dec_ref(v_x_4614_);
v___x_4618_ = lean_box(0);
return v___x_4618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4622_){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4623_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4624_ = lean_unsigned_to_nat(2u);
v___x_4625_ = l_Lean_Expr_isAppOfArity(v_e_4622_, v___x_4623_, v___x_4624_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
v___x_4626_ = lean_box(0);
return v___x_4626_;
}
else
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = l_Lean_Expr_appArg_x21(v_e_4622_);
v___x_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
return v___x_4628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4629_);
lean_dec_ref(v_e_4629_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4634_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4635_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4636_ = lean_unsigned_to_nat(2u);
v___x_4637_ = l_Lean_Expr_isAppOfArity(v_e_4634_, v___x_4635_, v___x_4636_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_box(0);
return v___x_4638_;
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = l_Lean_Expr_appArg_x21(v_e_4634_);
v___x_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4641_);
lean_dec_ref(v_e_4641_);
return v_res_4642_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4646_){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v___x_4647_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4648_ = lean_unsigned_to_nat(1u);
v___x_4649_ = l_Lean_Expr_isAppOfArity(v_e_4646_, v___x_4647_, v___x_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4650_){
_start:
{
uint8_t v_res_4651_; lean_object* v_r_4652_; 
v_res_4651_ = l_Lean_Expr_isOutParam(v_e_4650_);
lean_dec_ref(v_e_4650_);
v_r_4652_ = lean_box(v_res_4651_);
return v_r_4652_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4656_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4657_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4658_ = lean_unsigned_to_nat(1u);
v___x_4659_ = l_Lean_Expr_isAppOfArity(v_e_4656_, v___x_4657_, v___x_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4660_){
_start:
{
uint8_t v_res_4661_; lean_object* v_r_4662_; 
v_res_4661_ = l_Lean_Expr_isSemiOutParam(v_e_4660_);
lean_dec_ref(v_e_4660_);
v_r_4662_ = lean_box(v_res_4661_);
return v_r_4662_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4663_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4664_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4665_ = lean_unsigned_to_nat(2u);
v___x_4666_ = l_Lean_Expr_isAppOfArity(v_e_4663_, v___x_4664_, v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4667_){
_start:
{
uint8_t v_res_4668_; lean_object* v_r_4669_; 
v_res_4668_ = l_Lean_Expr_isOptParam(v_e_4667_);
lean_dec_ref(v_e_4667_);
v_r_4669_ = lean_box(v_res_4668_);
return v_r_4669_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4670_){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4671_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4672_ = lean_unsigned_to_nat(2u);
v___x_4673_ = l_Lean_Expr_isAppOfArity(v_e_4670_, v___x_4671_, v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4674_){
_start:
{
uint8_t v_res_4675_; lean_object* v_r_4676_; 
v_res_4675_ = l_Lean_Expr_isAutoParam(v_e_4674_);
lean_dec_ref(v_e_4674_);
v_r_4676_ = lean_box(v_res_4675_);
return v_r_4676_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4677_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Lean_Expr_getAppFn(v_e_4677_);
if (lean_obj_tag(v___x_4678_) == 4)
{
lean_object* v_declName_4679_; uint8_t v___y_4681_; lean_object* v___x_4686_; uint8_t v___x_4687_; 
v_declName_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_declName_4679_);
lean_dec_ref_known(v___x_4678_, 2);
v___x_4686_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4687_ = lean_name_eq(v_declName_4679_, v___x_4686_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; uint8_t v___x_4689_; 
v___x_4688_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4689_ = lean_name_eq(v_declName_4679_, v___x_4688_);
v___y_4681_ = v___x_4689_;
goto v___jp_4680_;
}
else
{
v___y_4681_ = v___x_4687_;
goto v___jp_4680_;
}
v___jp_4680_:
{
if (v___y_4681_ == 0)
{
lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4682_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4683_ = lean_name_eq(v_declName_4679_, v___x_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4684_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4685_ = lean_name_eq(v_declName_4679_, v___x_4684_);
lean_dec(v_declName_4679_);
return v___x_4685_;
}
else
{
lean_dec(v_declName_4679_);
return v___x_4683_;
}
}
else
{
lean_dec(v_declName_4679_);
return v___y_4681_;
}
}
}
else
{
uint8_t v___x_4690_; 
lean_dec_ref(v___x_4678_);
v___x_4690_ = 0;
return v___x_4690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4691_){
_start:
{
uint8_t v_res_4692_; lean_object* v_r_4693_; 
v_res_4692_ = l_Lean_Expr_isTypeAnnotation(v_e_4691_);
lean_dec_ref(v_e_4691_);
v_r_4693_ = lean_box(v_res_4692_);
return v_r_4693_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4694_){
_start:
{
uint8_t v___y_4696_; uint8_t v___y_4700_; uint8_t v___x_4706_; 
v___x_4706_ = l_Lean_Expr_isOptParam(v_e_4694_);
if (v___x_4706_ == 0)
{
uint8_t v___x_4707_; 
v___x_4707_ = l_Lean_Expr_isAutoParam(v_e_4694_);
v___y_4700_ = v___x_4707_;
goto v___jp_4699_;
}
else
{
v___y_4700_ = v___x_4706_;
goto v___jp_4699_;
}
v___jp_4695_:
{
if (v___y_4696_ == 0)
{
return v_e_4694_;
}
else
{
lean_object* v___x_4697_; 
v___x_4697_ = l_Lean_Expr_appArg_x21(v_e_4694_);
lean_dec_ref(v_e_4694_);
v_e_4694_ = v___x_4697_;
goto _start;
}
}
v___jp_4699_:
{
if (v___y_4700_ == 0)
{
uint8_t v___x_4701_; 
v___x_4701_ = l_Lean_Expr_isOutParam(v_e_4694_);
if (v___x_4701_ == 0)
{
uint8_t v___x_4702_; 
v___x_4702_ = l_Lean_Expr_isSemiOutParam(v_e_4694_);
v___y_4696_ = v___x_4702_;
goto v___jp_4695_;
}
else
{
v___y_4696_ = v___x_4701_;
goto v___jp_4695_;
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = l_Lean_Expr_appFn_x21(v_e_4694_);
lean_dec_ref(v_e_4694_);
v___x_4704_ = l_Lean_Expr_appArg_x21(v___x_4703_);
lean_dec_ref(v___x_4703_);
v_e_4694_ = v___x_4704_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4708_){
_start:
{
lean_object* v___x_4709_; lean_object* v_e_x27_4710_; uint8_t v___x_4711_; 
v___x_4709_ = l_Lean_Expr_consumeMData(v_e_4708_);
v_e_x27_4710_ = lean_expr_consume_type_annotations(v___x_4709_);
v___x_4711_ = lean_expr_eqv(v_e_x27_4710_, v_e_4708_);
if (v___x_4711_ == 0)
{
lean_dec_ref(v_e_4708_);
v_e_4708_ = v_e_x27_4710_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4710_);
return v_e_4708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4713_){
_start:
{
lean_object* v_fn_4714_; lean_object* v___x_4715_; 
v_fn_4714_ = lean_ctor_get(v_e_4713_, 0);
lean_inc_ref(v_fn_4714_);
lean_dec_ref(v_e_4713_);
v___x_4715_ = l_Lean_Expr_cleanupAnnotations(v_fn_4714_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4716_, lean_object* v_h_4717_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4716_);
return v___x_4718_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4722_){
_start:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; 
v___x_4723_ = l_Lean_Expr_cleanupAnnotations(v_e_4722_);
v___x_4724_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4725_ = l_Lean_Expr_isConstOf(v___x_4723_, v___x_4724_);
lean_dec_ref(v___x_4723_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4726_){
_start:
{
uint8_t v_res_4727_; lean_object* v_r_4728_; 
v_res_4727_ = l_Lean_Expr_isFalse(v_e_4726_);
v_r_4728_ = lean_box(v_res_4727_);
return v_r_4728_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4732_){
_start:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4733_ = l_Lean_Expr_cleanupAnnotations(v_e_4732_);
v___x_4734_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4735_ = l_Lean_Expr_isConstOf(v___x_4733_, v___x_4734_);
lean_dec_ref(v___x_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4736_){
_start:
{
uint8_t v_res_4737_; lean_object* v_r_4738_; 
v_res_4737_ = l_Lean_Expr_isTrue(v_e_4736_);
v_r_4738_ = lean_box(v_res_4737_);
return v_r_4738_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4743_){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v___x_4744_ = l_Lean_Expr_cleanupAnnotations(v_e_4743_);
v___x_4745_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4746_ = l_Lean_Expr_isConstOf(v___x_4744_, v___x_4745_);
lean_dec_ref(v___x_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4747_){
_start:
{
uint8_t v_res_4748_; lean_object* v_r_4749_; 
v_res_4748_ = l_Lean_Expr_isBoolFalse(v_e_4747_);
v_r_4749_ = lean_box(v_res_4748_);
return v_r_4749_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4753_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4754_ = l_Lean_Expr_cleanupAnnotations(v_e_4753_);
v___x_4755_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4756_ = l_Lean_Expr_isConstOf(v___x_4754_, v___x_4755_);
lean_dec_ref(v___x_4754_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4757_){
_start:
{
uint8_t v_res_4758_; lean_object* v_r_4759_; 
v_res_4758_ = l_Lean_Expr_isBoolTrue(v_e_4757_);
v_r_4759_ = lean_box(v_res_4758_);
return v_r_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4760_){
_start:
{
switch(lean_obj_tag(v_x_4760_))
{
case 10:
{
lean_object* v_expr_4761_; 
v_expr_4761_ = lean_ctor_get(v_x_4760_, 1);
lean_inc_ref(v_expr_4761_);
lean_dec_ref_known(v_x_4760_, 2);
v_x_4760_ = v_expr_4761_;
goto _start;
}
case 7:
{
lean_object* v_body_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v_body_4763_ = lean_ctor_get(v_x_4760_, 2);
lean_inc_ref(v_body_4763_);
lean_dec_ref_known(v_x_4760_, 3);
v___x_4764_ = l_Lean_Expr_getForallArity(v_body_4763_);
v___x_4765_ = lean_unsigned_to_nat(1u);
v___x_4766_ = lean_nat_add(v___x_4764_, v___x_4765_);
lean_dec(v___x_4764_);
return v___x_4766_;
}
default: 
{
uint8_t v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = 0;
v___x_4768_ = l_Lean_Expr_isHeadBetaTarget(v_x_4760_, v___x_4767_);
if (v___x_4768_ == 0)
{
lean_object* v_e_x27_4769_; uint8_t v___x_4770_; 
lean_inc_ref(v_x_4760_);
v_e_x27_4769_ = l_Lean_Expr_cleanupAnnotations(v_x_4760_);
v___x_4770_ = lean_expr_eqv(v_x_4760_, v_e_x27_4769_);
lean_dec_ref(v_x_4760_);
if (v___x_4770_ == 0)
{
v_x_4760_ = v_e_x27_4769_;
goto _start;
}
else
{
lean_object* v___x_4772_; 
lean_dec_ref(v_e_x27_4769_);
v___x_4772_ = lean_unsigned_to_nat(0u);
return v___x_4772_;
}
}
else
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Expr_headBeta(v_x_4760_);
v_x_4760_ = v___x_4773_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4775_){
_start:
{
lean_object* v___x_4776_; uint8_t v___x_4777_; 
v___x_4776_ = l_Lean_Expr_cleanupAnnotations(v_e_4775_);
v___x_4777_ = l_Lean_Expr_isApp(v___x_4776_);
if (v___x_4777_ == 0)
{
lean_object* v___x_4778_; 
lean_dec_ref(v___x_4776_);
v___x_4778_ = lean_box(0);
return v___x_4778_;
}
else
{
lean_object* v___x_4779_; uint8_t v___x_4780_; 
v___x_4779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4776_);
v___x_4780_ = l_Lean_Expr_isApp(v___x_4779_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; 
lean_dec_ref(v___x_4779_);
v___x_4781_ = lean_box(0);
return v___x_4781_;
}
else
{
lean_object* v_arg_4782_; lean_object* v___x_4783_; uint8_t v___x_4784_; 
v_arg_4782_ = lean_ctor_get(v___x_4779_, 1);
lean_inc_ref(v_arg_4782_);
v___x_4783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4779_);
v___x_4784_ = l_Lean_Expr_isApp(v___x_4783_);
if (v___x_4784_ == 0)
{
lean_object* v___x_4785_; 
lean_dec_ref(v___x_4783_);
lean_dec_ref(v_arg_4782_);
v___x_4785_ = lean_box(0);
return v___x_4785_;
}
else
{
lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4783_);
v___x_4787_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4788_ = l_Lean_Expr_isConstOf(v___x_4786_, v___x_4787_);
lean_dec_ref(v___x_4786_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; 
lean_dec_ref(v_arg_4782_);
v___x_4789_ = lean_box(0);
return v___x_4789_;
}
else
{
if (lean_obj_tag(v_arg_4782_) == 9)
{
lean_object* v_a_4790_; 
v_a_4790_ = lean_ctor_get(v_arg_4782_, 0);
lean_inc_ref(v_a_4790_);
lean_dec_ref_known(v_arg_4782_, 1);
if (lean_obj_tag(v_a_4790_) == 0)
{
lean_object* v_val_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
v_val_4791_ = lean_ctor_get(v_a_4790_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_a_4790_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v_a_4790_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_val_4791_);
lean_dec(v_a_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
lean_ctor_set_tag(v___x_4793_, 1);
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_val_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
else
{
lean_object* v___x_4799_; 
lean_dec_ref(v_a_4790_);
v___x_4799_ = lean_box(0);
return v___x_4799_;
}
}
else
{
lean_object* v___x_4800_; 
lean_dec_ref(v_arg_4782_);
v___x_4800_ = lean_box(0);
return v___x_4800_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4806_){
_start:
{
lean_object* v___x_4819_; uint8_t v___x_4820_; 
lean_inc_ref(v_e_4806_);
v___x_4819_ = l_Lean_Expr_cleanupAnnotations(v_e_4806_);
v___x_4820_ = l_Lean_Expr_isApp(v___x_4819_);
if (v___x_4820_ == 0)
{
lean_dec_ref(v___x_4819_);
goto v___jp_4807_;
}
else
{
lean_object* v_arg_4821_; lean_object* v___x_4822_; uint8_t v___x_4823_; 
v_arg_4821_ = lean_ctor_get(v___x_4819_, 1);
lean_inc_ref(v_arg_4821_);
v___x_4822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4819_);
v___x_4823_ = l_Lean_Expr_isApp(v___x_4822_);
if (v___x_4823_ == 0)
{
lean_dec_ref(v___x_4822_);
lean_dec_ref(v_arg_4821_);
goto v___jp_4807_;
}
else
{
lean_object* v___x_4824_; uint8_t v___x_4825_; 
v___x_4824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4822_);
v___x_4825_ = l_Lean_Expr_isApp(v___x_4824_);
if (v___x_4825_ == 0)
{
lean_dec_ref(v___x_4824_);
lean_dec_ref(v_arg_4821_);
goto v___jp_4807_;
}
else
{
lean_object* v___x_4826_; lean_object* v___x_4827_; uint8_t v___x_4828_; 
v___x_4826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4824_);
v___x_4827_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4828_ = l_Lean_Expr_isConstOf(v___x_4826_, v___x_4827_);
lean_dec_ref(v___x_4826_);
if (v___x_4828_ == 0)
{
lean_dec_ref(v_arg_4821_);
goto v___jp_4807_;
}
else
{
lean_object* v___x_4829_; 
lean_dec_ref(v_e_4806_);
v___x_4829_ = l_Lean_Expr_nat_x3f(v_arg_4821_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_box(0);
return v___x_4830_;
}
else
{
lean_object* v_val_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4843_; 
v_val_4831_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4833_ = v___x_4829_;
v_isShared_4834_ = v_isSharedCheck_4843_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_val_4831_);
lean_dec(v___x_4829_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4843_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4835_ = lean_unsigned_to_nat(0u);
v___x_4836_ = lean_nat_dec_eq(v_val_4831_, v___x_4835_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4837_ = lean_nat_to_int(v_val_4831_);
v___x_4838_ = lean_int_neg(v___x_4837_);
lean_dec(v___x_4837_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4838_);
v___x_4840_ = v___x_4833_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
else
{
lean_object* v___x_4842_; 
lean_del_object(v___x_4833_);
lean_dec(v_val_4831_);
v___x_4842_ = lean_box(0);
return v___x_4842_;
}
}
}
}
}
}
}
v___jp_4807_:
{
lean_object* v___x_4808_; 
v___x_4808_ = l_Lean_Expr_nat_x3f(v_e_4806_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_box(0);
return v___x_4809_;
}
else
{
lean_object* v_val_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4818_; 
v_val_4810_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4812_ = v___x_4808_;
v_isShared_4813_ = v_isSharedCheck_4818_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_val_4810_);
lean_dec(v___x_4808_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4818_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4814_; lean_object* v___x_4816_; 
v___x_4814_ = lean_nat_to_int(v_val_4810_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4814_);
v___x_4816_ = v___x_4812_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4844_, lean_object* v_e_4845_){
_start:
{
uint8_t v___x_4846_; lean_object* v_d_4848_; lean_object* v_b_4849_; 
v___x_4846_ = l_Lean_Expr_hasFVar(v_e_4845_);
if (v___x_4846_ == 0)
{
lean_dec_ref(v_e_4845_);
lean_dec_ref(v_p_4844_);
return v___x_4846_;
}
else
{
switch(lean_obj_tag(v_e_4845_))
{
case 7:
{
lean_object* v_binderType_4852_; lean_object* v_body_4853_; 
v_binderType_4852_ = lean_ctor_get(v_e_4845_, 1);
lean_inc_ref(v_binderType_4852_);
v_body_4853_ = lean_ctor_get(v_e_4845_, 2);
lean_inc_ref(v_body_4853_);
lean_dec_ref_known(v_e_4845_, 3);
v_d_4848_ = v_binderType_4852_;
v_b_4849_ = v_body_4853_;
goto v___jp_4847_;
}
case 6:
{
lean_object* v_binderType_4854_; lean_object* v_body_4855_; 
v_binderType_4854_ = lean_ctor_get(v_e_4845_, 1);
lean_inc_ref(v_binderType_4854_);
v_body_4855_ = lean_ctor_get(v_e_4845_, 2);
lean_inc_ref(v_body_4855_);
lean_dec_ref_known(v_e_4845_, 3);
v_d_4848_ = v_binderType_4854_;
v_b_4849_ = v_body_4855_;
goto v___jp_4847_;
}
case 10:
{
lean_object* v_expr_4856_; 
v_expr_4856_ = lean_ctor_get(v_e_4845_, 1);
lean_inc_ref(v_expr_4856_);
lean_dec_ref_known(v_e_4845_, 2);
v_e_4845_ = v_expr_4856_;
goto _start;
}
case 8:
{
lean_object* v_type_4858_; lean_object* v_value_4859_; lean_object* v_body_4860_; uint8_t v___x_4861_; 
v_type_4858_ = lean_ctor_get(v_e_4845_, 1);
lean_inc_ref(v_type_4858_);
v_value_4859_ = lean_ctor_get(v_e_4845_, 2);
lean_inc_ref(v_value_4859_);
v_body_4860_ = lean_ctor_get(v_e_4845_, 3);
lean_inc_ref(v_body_4860_);
lean_dec_ref_known(v_e_4845_, 4);
lean_inc_ref(v_p_4844_);
v___x_4861_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4844_, v_type_4858_);
if (v___x_4861_ == 0)
{
uint8_t v___x_4862_; 
lean_inc_ref(v_p_4844_);
v___x_4862_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4844_, v_value_4859_);
if (v___x_4862_ == 0)
{
v_e_4845_ = v_body_4860_;
goto _start;
}
else
{
lean_dec_ref(v_body_4860_);
lean_dec_ref(v_p_4844_);
return v___x_4846_;
}
}
else
{
lean_dec_ref(v_body_4860_);
lean_dec_ref(v_value_4859_);
lean_dec_ref(v_p_4844_);
return v___x_4846_;
}
}
case 5:
{
lean_object* v_fn_4864_; lean_object* v_arg_4865_; uint8_t v___x_4866_; 
v_fn_4864_ = lean_ctor_get(v_e_4845_, 0);
lean_inc_ref(v_fn_4864_);
v_arg_4865_ = lean_ctor_get(v_e_4845_, 1);
lean_inc_ref(v_arg_4865_);
lean_dec_ref_known(v_e_4845_, 2);
lean_inc_ref(v_p_4844_);
v___x_4866_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4844_, v_fn_4864_);
if (v___x_4866_ == 0)
{
v_e_4845_ = v_arg_4865_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4865_);
lean_dec_ref(v_p_4844_);
return v___x_4846_;
}
}
case 11:
{
lean_object* v_struct_4868_; 
v_struct_4868_ = lean_ctor_get(v_e_4845_, 2);
lean_inc_ref(v_struct_4868_);
lean_dec_ref_known(v_e_4845_, 3);
v_e_4845_ = v_struct_4868_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; 
v_fvarId_4870_ = lean_ctor_get(v_e_4845_, 0);
lean_inc(v_fvarId_4870_);
lean_dec_ref_known(v_e_4845_, 1);
v___x_4871_ = lean_apply_1(v_p_4844_, v_fvarId_4870_);
v___x_4872_ = lean_unbox(v___x_4871_);
return v___x_4872_;
}
default: 
{
uint8_t v___x_4873_; 
lean_dec_ref(v_e_4845_);
lean_dec_ref(v_p_4844_);
v___x_4873_ = 0;
return v___x_4873_;
}
}
}
v___jp_4847_:
{
uint8_t v___x_4850_; 
lean_inc_ref(v_p_4844_);
v___x_4850_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4844_, v_d_4848_);
if (v___x_4850_ == 0)
{
v_e_4845_ = v_b_4849_;
goto _start;
}
else
{
lean_dec_ref(v_b_4849_);
lean_dec_ref(v_p_4844_);
return v___x_4846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4874_, lean_object* v_e_4875_){
_start:
{
uint8_t v_res_4876_; lean_object* v_r_4877_; 
v_res_4876_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4874_, v_e_4875_);
v_r_4877_ = lean_box(v_res_4876_);
return v_r_4877_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4878_, lean_object* v_p_4879_){
_start:
{
uint8_t v___x_4880_; 
v___x_4880_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4879_, v_e_4878_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4881_, lean_object* v_p_4882_){
_start:
{
uint8_t v_res_4883_; lean_object* v_r_4884_; 
v_res_4883_ = l_Lean_Expr_hasAnyFVar(v_e_4881_, v_p_4882_);
v_r_4884_ = lean_box(v_res_4883_);
return v_r_4884_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4885_, lean_object* v_e_4886_){
_start:
{
uint8_t v___x_4887_; lean_object* v_d_4889_; lean_object* v_b_4890_; 
v___x_4887_ = l_Lean_Expr_hasFVar(v_e_4886_);
if (v___x_4887_ == 0)
{
return v___x_4887_;
}
else
{
switch(lean_obj_tag(v_e_4886_))
{
case 7:
{
lean_object* v_binderType_4893_; lean_object* v_body_4894_; 
v_binderType_4893_ = lean_ctor_get(v_e_4886_, 1);
v_body_4894_ = lean_ctor_get(v_e_4886_, 2);
v_d_4889_ = v_binderType_4893_;
v_b_4890_ = v_body_4894_;
goto v___jp_4888_;
}
case 6:
{
lean_object* v_binderType_4895_; lean_object* v_body_4896_; 
v_binderType_4895_ = lean_ctor_get(v_e_4886_, 1);
v_body_4896_ = lean_ctor_get(v_e_4886_, 2);
v_d_4889_ = v_binderType_4895_;
v_b_4890_ = v_body_4896_;
goto v___jp_4888_;
}
case 10:
{
lean_object* v_expr_4897_; 
v_expr_4897_ = lean_ctor_get(v_e_4886_, 1);
v_e_4886_ = v_expr_4897_;
goto _start;
}
case 8:
{
lean_object* v_type_4899_; lean_object* v_value_4900_; lean_object* v_body_4901_; uint8_t v___x_4902_; 
v_type_4899_ = lean_ctor_get(v_e_4886_, 1);
v_value_4900_ = lean_ctor_get(v_e_4886_, 2);
v_body_4901_ = lean_ctor_get(v_e_4886_, 3);
v___x_4902_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4885_, v_type_4899_);
if (v___x_4902_ == 0)
{
uint8_t v___x_4903_; 
v___x_4903_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4885_, v_value_4900_);
if (v___x_4903_ == 0)
{
v_e_4886_ = v_body_4901_;
goto _start;
}
else
{
return v___x_4887_;
}
}
else
{
return v___x_4887_;
}
}
case 5:
{
lean_object* v_fn_4905_; lean_object* v_arg_4906_; uint8_t v___x_4907_; 
v_fn_4905_ = lean_ctor_get(v_e_4886_, 0);
v_arg_4906_ = lean_ctor_get(v_e_4886_, 1);
v___x_4907_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4885_, v_fn_4905_);
if (v___x_4907_ == 0)
{
v_e_4886_ = v_arg_4906_;
goto _start;
}
else
{
return v___x_4887_;
}
}
case 11:
{
lean_object* v_struct_4909_; 
v_struct_4909_ = lean_ctor_get(v_e_4886_, 2);
v_e_4886_ = v_struct_4909_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4911_; uint8_t v___x_4912_; 
v_fvarId_4911_ = lean_ctor_get(v_e_4886_, 0);
v___x_4912_ = lean_name_eq(v_fvarId_4911_, v_fvarId_4885_);
return v___x_4912_;
}
default: 
{
uint8_t v___x_4913_; 
v___x_4913_ = 0;
return v___x_4913_;
}
}
}
v___jp_4888_:
{
uint8_t v___x_4891_; 
v___x_4891_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4885_, v_d_4889_);
if (v___x_4891_ == 0)
{
v_e_4886_ = v_b_4890_;
goto _start;
}
else
{
return v___x_4887_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4914_, lean_object* v_e_4915_){
_start:
{
uint8_t v_res_4916_; lean_object* v_r_4917_; 
v_res_4916_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4914_, v_e_4915_);
lean_dec_ref(v_e_4915_);
lean_dec(v_fvarId_4914_);
v_r_4917_ = lean_box(v_res_4916_);
return v_r_4917_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4918_, lean_object* v_fvarId_4919_){
_start:
{
uint8_t v___x_4920_; 
v___x_4920_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4919_, v_e_4918_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4921_, lean_object* v_fvarId_4922_){
_start:
{
uint8_t v_res_4923_; lean_object* v_r_4924_; 
v_res_4923_ = l_Lean_Expr_containsFVar(v_e_4921_, v_fvarId_4922_);
lean_dec(v_fvarId_4922_);
lean_dec_ref(v_e_4921_);
v_r_4924_ = lean_box(v_res_4923_);
return v_r_4924_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4926_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4927_ = lean_unsigned_to_nat(18u);
v___x_4928_ = lean_unsigned_to_nat(1847u);
v___x_4929_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4930_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4931_ = l_mkPanicMessageWithDecl(v___x_4930_, v___x_4929_, v___x_4928_, v___x_4927_, v___x_4926_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4932_, lean_object* v_newFn_4933_, lean_object* v_newArg_4934_){
_start:
{
uint8_t v___y_4936_; 
if (lean_obj_tag(v_e_4932_) == 5)
{
lean_object* v_fn_4938_; lean_object* v_arg_4939_; size_t v___x_4940_; size_t v___x_4941_; uint8_t v___x_4942_; 
v_fn_4938_ = lean_ctor_get(v_e_4932_, 0);
v_arg_4939_ = lean_ctor_get(v_e_4932_, 1);
v___x_4940_ = lean_ptr_addr(v_fn_4938_);
v___x_4941_ = lean_ptr_addr(v_newFn_4933_);
v___x_4942_ = lean_usize_dec_eq(v___x_4940_, v___x_4941_);
if (v___x_4942_ == 0)
{
v___y_4936_ = v___x_4942_;
goto v___jp_4935_;
}
else
{
size_t v___x_4943_; size_t v___x_4944_; uint8_t v___x_4945_; 
v___x_4943_ = lean_ptr_addr(v_arg_4939_);
v___x_4944_ = lean_ptr_addr(v_newArg_4934_);
v___x_4945_ = lean_usize_dec_eq(v___x_4943_, v___x_4944_);
v___y_4936_ = v___x_4945_;
goto v___jp_4935_;
}
}
else
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
lean_dec_ref(v_newArg_4934_);
lean_dec_ref(v_newFn_4933_);
v___x_4946_ = l_Lean_instInhabitedExpr;
v___x_4947_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4948_ = l_panic___redArg(v___x_4946_, v___x_4947_);
return v___x_4948_;
}
v___jp_4935_:
{
if (v___y_4936_ == 0)
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Lean_Expr_app___override(v_newFn_4933_, v_newArg_4934_);
return v___x_4937_;
}
else
{
lean_dec_ref(v_newArg_4934_);
lean_dec_ref(v_newFn_4933_);
lean_inc_ref(v_e_4932_);
return v_e_4932_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4949_, lean_object* v_newFn_4950_, lean_object* v_newArg_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4949_, v_newFn_4950_, v_newArg_4951_);
lean_dec_ref(v_e_4949_);
return v_res_4952_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4954_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4955_ = lean_unsigned_to_nat(20u);
v___x_4956_ = lean_unsigned_to_nat(1858u);
v___x_4957_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4958_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4959_ = l_mkPanicMessageWithDecl(v___x_4958_, v___x_4957_, v___x_4956_, v___x_4955_, v___x_4954_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4960_, lean_object* v_fvarIdNew_4961_){
_start:
{
if (lean_obj_tag(v_e_4960_) == 1)
{
lean_object* v_fvarId_4962_; uint8_t v___x_4963_; 
v_fvarId_4962_ = lean_ctor_get(v_e_4960_, 0);
v___x_4963_ = lean_name_eq(v_fvarId_4962_, v_fvarIdNew_4961_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4961_);
return v___x_4964_;
}
else
{
lean_dec(v_fvarIdNew_4961_);
lean_inc_ref(v_e_4960_);
return v_e_4960_;
}
}
else
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
lean_dec(v_fvarIdNew_4961_);
v___x_4965_ = l_Lean_instInhabitedExpr;
v___x_4966_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4967_ = l_panic___redArg(v___x_4965_, v___x_4966_);
return v___x_4967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4968_, lean_object* v_fvarIdNew_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Lean_Expr_updateFVar_x21(v_e_4968_, v_fvarIdNew_4969_);
lean_dec_ref(v_e_4968_);
return v_res_4970_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4972_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4973_ = lean_unsigned_to_nat(18u);
v___x_4974_ = lean_unsigned_to_nat(1863u);
v___x_4975_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4976_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4977_ = l_mkPanicMessageWithDecl(v___x_4976_, v___x_4975_, v___x_4974_, v___x_4973_, v___x_4972_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4978_, lean_object* v_newLevels_4979_){
_start:
{
if (lean_obj_tag(v_e_4978_) == 4)
{
lean_object* v_declName_4980_; lean_object* v_us_4981_; uint8_t v___x_4982_; 
v_declName_4980_ = lean_ctor_get(v_e_4978_, 0);
v_us_4981_ = lean_ctor_get(v_e_4978_, 1);
v___x_4982_ = l_ptrEqList___redArg(v_us_4981_, v_newLevels_4979_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
lean_inc(v_declName_4980_);
lean_dec_ref_known(v_e_4978_, 2);
v___x_4983_ = l_Lean_Expr_const___override(v_declName_4980_, v_newLevels_4979_);
return v___x_4983_;
}
else
{
lean_dec(v_newLevels_4979_);
return v_e_4978_;
}
}
else
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
lean_dec(v_newLevels_4979_);
lean_dec_ref(v_e_4978_);
v___x_4984_ = l_Lean_instInhabitedExpr;
v___x_4985_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4986_ = l_panic___redArg(v___x_4984_, v___x_4985_);
return v___x_4986_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4989_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_4990_ = lean_unsigned_to_nat(14u);
v___x_4991_ = lean_unsigned_to_nat(1874u);
v___x_4992_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_4993_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4994_ = l_mkPanicMessageWithDecl(v___x_4993_, v___x_4992_, v___x_4991_, v___x_4990_, v___x_4989_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_4995_, lean_object* v_u_x27_4996_){
_start:
{
if (lean_obj_tag(v_e_4995_) == 3)
{
lean_object* v_u_4997_; size_t v___x_4998_; size_t v___x_4999_; uint8_t v___x_5000_; 
v_u_4997_ = lean_ctor_get(v_e_4995_, 0);
v___x_4998_ = lean_ptr_addr(v_u_4997_);
v___x_4999_ = lean_ptr_addr(v_u_x27_4996_);
v___x_5000_ = lean_usize_dec_eq(v___x_4998_, v___x_4999_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Lean_Expr_sort___override(v_u_x27_4996_);
return v___x_5001_;
}
else
{
lean_dec(v_u_x27_4996_);
lean_inc_ref(v_e_4995_);
return v_e_4995_;
}
}
else
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
lean_dec(v_u_x27_4996_);
v___x_5002_ = l_Lean_instInhabitedExpr;
v___x_5003_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5004_ = l_panic___redArg(v___x_5002_, v___x_5003_);
return v___x_5004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5005_, lean_object* v_u_x27_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5005_, v_u_x27_5006_);
lean_dec_ref(v_e_5005_);
return v_res_5007_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5010_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5011_ = lean_unsigned_to_nat(17u);
v___x_5012_ = lean_unsigned_to_nat(1885u);
v___x_5013_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5014_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5015_ = l_mkPanicMessageWithDecl(v___x_5014_, v___x_5013_, v___x_5012_, v___x_5011_, v___x_5010_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5016_, lean_object* v_newExpr_5017_){
_start:
{
if (lean_obj_tag(v_e_5016_) == 10)
{
lean_object* v_data_5018_; lean_object* v_expr_5019_; size_t v___x_5020_; size_t v___x_5021_; uint8_t v___x_5022_; 
v_data_5018_ = lean_ctor_get(v_e_5016_, 0);
v_expr_5019_ = lean_ctor_get(v_e_5016_, 1);
v___x_5020_ = lean_ptr_addr(v_expr_5019_);
v___x_5021_ = lean_ptr_addr(v_newExpr_5017_);
v___x_5022_ = lean_usize_dec_eq(v___x_5020_, v___x_5021_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; 
lean_inc(v_data_5018_);
lean_dec_ref_known(v_e_5016_, 2);
v___x_5023_ = l_Lean_Expr_mdata___override(v_data_5018_, v_newExpr_5017_);
return v___x_5023_;
}
else
{
lean_dec_ref(v_newExpr_5017_);
return v_e_5016_;
}
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_dec_ref(v_newExpr_5017_);
lean_dec_ref(v_e_5016_);
v___x_5024_ = l_Lean_instInhabitedExpr;
v___x_5025_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5026_ = l_panic___redArg(v___x_5024_, v___x_5025_);
return v___x_5026_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5029_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5030_ = lean_unsigned_to_nat(18u);
v___x_5031_ = lean_unsigned_to_nat(1896u);
v___x_5032_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5033_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5034_ = l_mkPanicMessageWithDecl(v___x_5033_, v___x_5032_, v___x_5031_, v___x_5030_, v___x_5029_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5035_, lean_object* v_newExpr_5036_){
_start:
{
if (lean_obj_tag(v_e_5035_) == 11)
{
lean_object* v_typeName_5037_; lean_object* v_idx_5038_; lean_object* v_struct_5039_; size_t v___x_5040_; size_t v___x_5041_; uint8_t v___x_5042_; 
v_typeName_5037_ = lean_ctor_get(v_e_5035_, 0);
v_idx_5038_ = lean_ctor_get(v_e_5035_, 1);
v_struct_5039_ = lean_ctor_get(v_e_5035_, 2);
v___x_5040_ = lean_ptr_addr(v_struct_5039_);
v___x_5041_ = lean_ptr_addr(v_newExpr_5036_);
v___x_5042_ = lean_usize_dec_eq(v___x_5040_, v___x_5041_);
if (v___x_5042_ == 0)
{
lean_object* v___x_5043_; 
lean_inc(v_idx_5038_);
lean_inc(v_typeName_5037_);
lean_dec_ref_known(v_e_5035_, 3);
v___x_5043_ = l_Lean_Expr_proj___override(v_typeName_5037_, v_idx_5038_, v_newExpr_5036_);
return v___x_5043_;
}
else
{
lean_dec_ref(v_newExpr_5036_);
return v_e_5035_;
}
}
else
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec_ref(v_newExpr_5036_);
lean_dec_ref(v_e_5035_);
v___x_5044_ = l_Lean_instInhabitedExpr;
v___x_5045_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5046_ = l_panic___redArg(v___x_5044_, v___x_5045_);
return v___x_5046_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5049_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5050_ = lean_unsigned_to_nat(23u);
v___x_5051_ = lean_unsigned_to_nat(1911u);
v___x_5052_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5053_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5054_ = l_mkPanicMessageWithDecl(v___x_5053_, v___x_5052_, v___x_5051_, v___x_5050_, v___x_5049_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5055_, uint8_t v_newBinfo_5056_, lean_object* v_newDomain_5057_, lean_object* v_newBody_5058_){
_start:
{
if (lean_obj_tag(v_e_5055_) == 7)
{
lean_object* v_binderName_5059_; lean_object* v_binderType_5060_; lean_object* v_body_5061_; uint8_t v_binderInfo_5062_; uint8_t v___y_5064_; size_t v___x_5068_; size_t v___x_5069_; uint8_t v___x_5070_; 
v_binderName_5059_ = lean_ctor_get(v_e_5055_, 0);
v_binderType_5060_ = lean_ctor_get(v_e_5055_, 1);
v_body_5061_ = lean_ctor_get(v_e_5055_, 2);
v_binderInfo_5062_ = lean_ctor_get_uint8(v_e_5055_, sizeof(void*)*3 + 8);
v___x_5068_ = lean_ptr_addr(v_binderType_5060_);
v___x_5069_ = lean_ptr_addr(v_newDomain_5057_);
v___x_5070_ = lean_usize_dec_eq(v___x_5068_, v___x_5069_);
if (v___x_5070_ == 0)
{
v___y_5064_ = v___x_5070_;
goto v___jp_5063_;
}
else
{
size_t v___x_5071_; size_t v___x_5072_; uint8_t v___x_5073_; 
v___x_5071_ = lean_ptr_addr(v_body_5061_);
v___x_5072_ = lean_ptr_addr(v_newBody_5058_);
v___x_5073_ = lean_usize_dec_eq(v___x_5071_, v___x_5072_);
v___y_5064_ = v___x_5073_;
goto v___jp_5063_;
}
v___jp_5063_:
{
if (v___y_5064_ == 0)
{
lean_object* v___x_5065_; 
lean_inc(v_binderName_5059_);
lean_dec_ref_known(v_e_5055_, 3);
v___x_5065_ = l_Lean_Expr_forallE___override(v_binderName_5059_, v_newDomain_5057_, v_newBody_5058_, v_newBinfo_5056_);
return v___x_5065_;
}
else
{
uint8_t v___x_5066_; 
v___x_5066_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5062_, v_newBinfo_5056_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; 
lean_inc(v_binderName_5059_);
lean_dec_ref_known(v_e_5055_, 3);
v___x_5067_ = l_Lean_Expr_forallE___override(v_binderName_5059_, v_newDomain_5057_, v_newBody_5058_, v_newBinfo_5056_);
return v___x_5067_;
}
else
{
lean_dec_ref(v_newBody_5058_);
lean_dec_ref(v_newDomain_5057_);
return v_e_5055_;
}
}
}
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
lean_dec_ref(v_newBody_5058_);
lean_dec_ref(v_newDomain_5057_);
lean_dec_ref(v_e_5055_);
v___x_5074_ = l_Lean_instInhabitedExpr;
v___x_5075_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5076_ = l_panic___redArg(v___x_5074_, v___x_5075_);
return v___x_5076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5077_, lean_object* v_newBinfo_5078_, lean_object* v_newDomain_5079_, lean_object* v_newBody_5080_){
_start:
{
uint8_t v_newBinfo_boxed_5081_; lean_object* v_res_5082_; 
v_newBinfo_boxed_5081_ = lean_unbox(v_newBinfo_5078_);
v_res_5082_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5077_, v_newBinfo_boxed_5081_, v_newDomain_5079_, v_newBody_5080_);
return v_res_5082_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5084_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5085_ = lean_unsigned_to_nat(24u);
v___x_5086_ = lean_unsigned_to_nat(1922u);
v___x_5087_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5088_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5089_ = l_mkPanicMessageWithDecl(v___x_5088_, v___x_5087_, v___x_5086_, v___x_5085_, v___x_5084_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5090_, lean_object* v_newDomain_5091_, lean_object* v_newBody_5092_){
_start:
{
if (lean_obj_tag(v_e_5090_) == 7)
{
lean_object* v_binderName_5093_; lean_object* v_binderType_5094_; lean_object* v_body_5095_; uint8_t v_binderInfo_5096_; uint8_t v___y_5098_; size_t v___x_5102_; size_t v___x_5103_; uint8_t v___x_5104_; 
v_binderName_5093_ = lean_ctor_get(v_e_5090_, 0);
v_binderType_5094_ = lean_ctor_get(v_e_5090_, 1);
v_body_5095_ = lean_ctor_get(v_e_5090_, 2);
v_binderInfo_5096_ = lean_ctor_get_uint8(v_e_5090_, sizeof(void*)*3 + 8);
v___x_5102_ = lean_ptr_addr(v_binderType_5094_);
v___x_5103_ = lean_ptr_addr(v_newDomain_5091_);
v___x_5104_ = lean_usize_dec_eq(v___x_5102_, v___x_5103_);
if (v___x_5104_ == 0)
{
v___y_5098_ = v___x_5104_;
goto v___jp_5097_;
}
else
{
size_t v___x_5105_; size_t v___x_5106_; uint8_t v___x_5107_; 
v___x_5105_ = lean_ptr_addr(v_body_5095_);
v___x_5106_ = lean_ptr_addr(v_newBody_5092_);
v___x_5107_ = lean_usize_dec_eq(v___x_5105_, v___x_5106_);
v___y_5098_ = v___x_5107_;
goto v___jp_5097_;
}
v___jp_5097_:
{
if (v___y_5098_ == 0)
{
lean_object* v___x_5099_; 
lean_inc(v_binderName_5093_);
lean_dec_ref_known(v_e_5090_, 3);
v___x_5099_ = l_Lean_Expr_forallE___override(v_binderName_5093_, v_newDomain_5091_, v_newBody_5092_, v_binderInfo_5096_);
return v___x_5099_;
}
else
{
uint8_t v___x_5100_; 
v___x_5100_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5096_, v_binderInfo_5096_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; 
lean_inc(v_binderName_5093_);
lean_dec_ref_known(v_e_5090_, 3);
v___x_5101_ = l_Lean_Expr_forallE___override(v_binderName_5093_, v_newDomain_5091_, v_newBody_5092_, v_binderInfo_5096_);
return v___x_5101_;
}
else
{
lean_dec_ref(v_newBody_5092_);
lean_dec_ref(v_newDomain_5091_);
return v_e_5090_;
}
}
}
}
else
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
lean_dec_ref(v_newBody_5092_);
lean_dec_ref(v_newDomain_5091_);
lean_dec_ref(v_e_5090_);
v___x_5108_ = l_Lean_instInhabitedExpr;
v___x_5109_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5110_ = l_panic___redArg(v___x_5108_, v___x_5109_);
return v___x_5110_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___x_5113_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5114_ = lean_unsigned_to_nat(19u);
v___x_5115_ = lean_unsigned_to_nat(1931u);
v___x_5116_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5117_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5118_ = l_mkPanicMessageWithDecl(v___x_5117_, v___x_5116_, v___x_5115_, v___x_5114_, v___x_5113_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5119_, uint8_t v_newBinfo_5120_, lean_object* v_newDomain_5121_, lean_object* v_newBody_5122_){
_start:
{
if (lean_obj_tag(v_e_5119_) == 6)
{
lean_object* v_binderName_5123_; lean_object* v_binderType_5124_; lean_object* v_body_5125_; uint8_t v_binderInfo_5126_; uint8_t v___y_5128_; size_t v___x_5132_; size_t v___x_5133_; uint8_t v___x_5134_; 
v_binderName_5123_ = lean_ctor_get(v_e_5119_, 0);
v_binderType_5124_ = lean_ctor_get(v_e_5119_, 1);
v_body_5125_ = lean_ctor_get(v_e_5119_, 2);
v_binderInfo_5126_ = lean_ctor_get_uint8(v_e_5119_, sizeof(void*)*3 + 8);
v___x_5132_ = lean_ptr_addr(v_binderType_5124_);
v___x_5133_ = lean_ptr_addr(v_newDomain_5121_);
v___x_5134_ = lean_usize_dec_eq(v___x_5132_, v___x_5133_);
if (v___x_5134_ == 0)
{
v___y_5128_ = v___x_5134_;
goto v___jp_5127_;
}
else
{
size_t v___x_5135_; size_t v___x_5136_; uint8_t v___x_5137_; 
v___x_5135_ = lean_ptr_addr(v_body_5125_);
v___x_5136_ = lean_ptr_addr(v_newBody_5122_);
v___x_5137_ = lean_usize_dec_eq(v___x_5135_, v___x_5136_);
v___y_5128_ = v___x_5137_;
goto v___jp_5127_;
}
v___jp_5127_:
{
if (v___y_5128_ == 0)
{
lean_object* v___x_5129_; 
lean_inc(v_binderName_5123_);
lean_dec_ref_known(v_e_5119_, 3);
v___x_5129_ = l_Lean_Expr_lam___override(v_binderName_5123_, v_newDomain_5121_, v_newBody_5122_, v_newBinfo_5120_);
return v___x_5129_;
}
else
{
uint8_t v___x_5130_; 
v___x_5130_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5126_, v_newBinfo_5120_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; 
lean_inc(v_binderName_5123_);
lean_dec_ref_known(v_e_5119_, 3);
v___x_5131_ = l_Lean_Expr_lam___override(v_binderName_5123_, v_newDomain_5121_, v_newBody_5122_, v_newBinfo_5120_);
return v___x_5131_;
}
else
{
lean_dec_ref(v_newBody_5122_);
lean_dec_ref(v_newDomain_5121_);
return v_e_5119_;
}
}
}
}
else
{
lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
lean_dec_ref(v_newBody_5122_);
lean_dec_ref(v_newDomain_5121_);
lean_dec_ref(v_e_5119_);
v___x_5138_ = l_Lean_instInhabitedExpr;
v___x_5139_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5140_ = l_panic___redArg(v___x_5138_, v___x_5139_);
return v___x_5140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5141_, lean_object* v_newBinfo_5142_, lean_object* v_newDomain_5143_, lean_object* v_newBody_5144_){
_start:
{
uint8_t v_newBinfo_boxed_5145_; lean_object* v_res_5146_; 
v_newBinfo_boxed_5145_ = lean_unbox(v_newBinfo_5142_);
v_res_5146_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5141_, v_newBinfo_boxed_5145_, v_newDomain_5143_, v_newBody_5144_);
return v_res_5146_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5148_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5149_ = lean_unsigned_to_nat(20u);
v___x_5150_ = lean_unsigned_to_nat(1942u);
v___x_5151_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5152_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5153_ = l_mkPanicMessageWithDecl(v___x_5152_, v___x_5151_, v___x_5150_, v___x_5149_, v___x_5148_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5154_, lean_object* v_newDomain_5155_, lean_object* v_newBody_5156_){
_start:
{
if (lean_obj_tag(v_e_5154_) == 6)
{
lean_object* v_binderName_5157_; lean_object* v_binderType_5158_; lean_object* v_body_5159_; uint8_t v_binderInfo_5160_; uint8_t v___y_5162_; size_t v___x_5166_; size_t v___x_5167_; uint8_t v___x_5168_; 
v_binderName_5157_ = lean_ctor_get(v_e_5154_, 0);
v_binderType_5158_ = lean_ctor_get(v_e_5154_, 1);
v_body_5159_ = lean_ctor_get(v_e_5154_, 2);
v_binderInfo_5160_ = lean_ctor_get_uint8(v_e_5154_, sizeof(void*)*3 + 8);
v___x_5166_ = lean_ptr_addr(v_binderType_5158_);
v___x_5167_ = lean_ptr_addr(v_newDomain_5155_);
v___x_5168_ = lean_usize_dec_eq(v___x_5166_, v___x_5167_);
if (v___x_5168_ == 0)
{
v___y_5162_ = v___x_5168_;
goto v___jp_5161_;
}
else
{
size_t v___x_5169_; size_t v___x_5170_; uint8_t v___x_5171_; 
v___x_5169_ = lean_ptr_addr(v_body_5159_);
v___x_5170_ = lean_ptr_addr(v_newBody_5156_);
v___x_5171_ = lean_usize_dec_eq(v___x_5169_, v___x_5170_);
v___y_5162_ = v___x_5171_;
goto v___jp_5161_;
}
v___jp_5161_:
{
if (v___y_5162_ == 0)
{
lean_object* v___x_5163_; 
lean_inc(v_binderName_5157_);
lean_dec_ref_known(v_e_5154_, 3);
v___x_5163_ = l_Lean_Expr_lam___override(v_binderName_5157_, v_newDomain_5155_, v_newBody_5156_, v_binderInfo_5160_);
return v___x_5163_;
}
else
{
uint8_t v___x_5164_; 
v___x_5164_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5160_, v_binderInfo_5160_);
if (v___x_5164_ == 0)
{
lean_object* v___x_5165_; 
lean_inc(v_binderName_5157_);
lean_dec_ref_known(v_e_5154_, 3);
v___x_5165_ = l_Lean_Expr_lam___override(v_binderName_5157_, v_newDomain_5155_, v_newBody_5156_, v_binderInfo_5160_);
return v___x_5165_;
}
else
{
lean_dec_ref(v_newBody_5156_);
lean_dec_ref(v_newDomain_5155_);
return v_e_5154_;
}
}
}
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
lean_dec_ref(v_newBody_5156_);
lean_dec_ref(v_newDomain_5155_);
lean_dec_ref(v_e_5154_);
v___x_5172_ = l_Lean_instInhabitedExpr;
v___x_5173_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5174_ = l_panic___redArg(v___x_5172_, v___x_5173_);
return v___x_5174_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5176_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5177_ = lean_unsigned_to_nat(22u);
v___x_5178_ = lean_unsigned_to_nat(1951u);
v___x_5179_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5180_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5181_ = l_mkPanicMessageWithDecl(v___x_5180_, v___x_5179_, v___x_5178_, v___x_5177_, v___x_5176_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5182_, lean_object* v_newType_5183_, lean_object* v_newVal_5184_, lean_object* v_newBody_5185_, uint8_t v_newNondep_5186_){
_start:
{
if (lean_obj_tag(v_e_5182_) == 8)
{
lean_object* v_declName_5187_; lean_object* v_type_5188_; lean_object* v_value_5189_; lean_object* v_body_5190_; uint8_t v_nondep_5191_; uint8_t v___y_5193_; size_t v___x_5201_; size_t v___x_5202_; uint8_t v___x_5203_; 
v_declName_5187_ = lean_ctor_get(v_e_5182_, 0);
v_type_5188_ = lean_ctor_get(v_e_5182_, 1);
v_value_5189_ = lean_ctor_get(v_e_5182_, 2);
v_body_5190_ = lean_ctor_get(v_e_5182_, 3);
v_nondep_5191_ = lean_ctor_get_uint8(v_e_5182_, sizeof(void*)*4 + 8);
v___x_5201_ = lean_ptr_addr(v_type_5188_);
v___x_5202_ = lean_ptr_addr(v_newType_5183_);
v___x_5203_ = lean_usize_dec_eq(v___x_5201_, v___x_5202_);
if (v___x_5203_ == 0)
{
v___y_5193_ = v___x_5203_;
goto v___jp_5192_;
}
else
{
size_t v___x_5204_; size_t v___x_5205_; uint8_t v___x_5206_; 
v___x_5204_ = lean_ptr_addr(v_value_5189_);
v___x_5205_ = lean_ptr_addr(v_newVal_5184_);
v___x_5206_ = lean_usize_dec_eq(v___x_5204_, v___x_5205_);
v___y_5193_ = v___x_5206_;
goto v___jp_5192_;
}
v___jp_5192_:
{
if (v___y_5193_ == 0)
{
lean_object* v___x_5194_; 
lean_inc(v_declName_5187_);
lean_dec_ref_known(v_e_5182_, 4);
v___x_5194_ = l_Lean_Expr_letE___override(v_declName_5187_, v_newType_5183_, v_newVal_5184_, v_newBody_5185_, v_newNondep_5186_);
return v___x_5194_;
}
else
{
size_t v___x_5195_; size_t v___x_5196_; uint8_t v___x_5197_; 
v___x_5195_ = lean_ptr_addr(v_body_5190_);
v___x_5196_ = lean_ptr_addr(v_newBody_5185_);
v___x_5197_ = lean_usize_dec_eq(v___x_5195_, v___x_5196_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; 
lean_inc(v_declName_5187_);
lean_dec_ref_known(v_e_5182_, 4);
v___x_5198_ = l_Lean_Expr_letE___override(v_declName_5187_, v_newType_5183_, v_newVal_5184_, v_newBody_5185_, v_newNondep_5186_);
return v___x_5198_;
}
else
{
if (v_nondep_5191_ == 0)
{
if (v_newNondep_5186_ == 0)
{
lean_dec_ref(v_newBody_5185_);
lean_dec_ref(v_newVal_5184_);
lean_dec_ref(v_newType_5183_);
return v_e_5182_;
}
else
{
lean_object* v___x_5199_; 
lean_inc(v_declName_5187_);
lean_dec_ref_known(v_e_5182_, 4);
v___x_5199_ = l_Lean_Expr_letE___override(v_declName_5187_, v_newType_5183_, v_newVal_5184_, v_newBody_5185_, v_newNondep_5186_);
return v___x_5199_;
}
}
else
{
if (v_newNondep_5186_ == 0)
{
lean_object* v___x_5200_; 
lean_inc(v_declName_5187_);
lean_dec_ref_known(v_e_5182_, 4);
v___x_5200_ = l_Lean_Expr_letE___override(v_declName_5187_, v_newType_5183_, v_newVal_5184_, v_newBody_5185_, v_newNondep_5186_);
return v___x_5200_;
}
else
{
lean_dec_ref(v_newBody_5185_);
lean_dec_ref(v_newVal_5184_);
lean_dec_ref(v_newType_5183_);
return v_e_5182_;
}
}
}
}
}
}
else
{
lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
lean_dec_ref(v_newBody_5185_);
lean_dec_ref(v_newVal_5184_);
lean_dec_ref(v_newType_5183_);
lean_dec_ref(v_e_5182_);
v___x_5207_ = l_Lean_instInhabitedExpr;
v___x_5208_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5209_ = l_panic___redArg(v___x_5207_, v___x_5208_);
return v___x_5209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5210_, lean_object* v_newType_5211_, lean_object* v_newVal_5212_, lean_object* v_newBody_5213_, lean_object* v_newNondep_5214_){
_start:
{
uint8_t v_newNondep_boxed_5215_; lean_object* v_res_5216_; 
v_newNondep_boxed_5215_ = lean_unbox(v_newNondep_5214_);
v_res_5216_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5210_, v_newType_5211_, v_newVal_5212_, v_newBody_5213_, v_newNondep_boxed_5215_);
return v_res_5216_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5218_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5219_ = lean_unsigned_to_nat(27u);
v___x_5220_ = lean_unsigned_to_nat(1964u);
v___x_5221_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5222_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5223_ = l_mkPanicMessageWithDecl(v___x_5222_, v___x_5221_, v___x_5220_, v___x_5219_, v___x_5218_);
return v___x_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5224_, lean_object* v_newType_5225_, lean_object* v_newVal_5226_, lean_object* v_newBody_5227_){
_start:
{
if (lean_obj_tag(v_e_5224_) == 8)
{
lean_object* v_declName_5228_; lean_object* v_type_5229_; lean_object* v_value_5230_; lean_object* v_body_5231_; uint8_t v_nondep_5232_; uint8_t v___y_5234_; size_t v___x_5240_; size_t v___x_5241_; uint8_t v___x_5242_; 
v_declName_5228_ = lean_ctor_get(v_e_5224_, 0);
v_type_5229_ = lean_ctor_get(v_e_5224_, 1);
v_value_5230_ = lean_ctor_get(v_e_5224_, 2);
v_body_5231_ = lean_ctor_get(v_e_5224_, 3);
v_nondep_5232_ = lean_ctor_get_uint8(v_e_5224_, sizeof(void*)*4 + 8);
v___x_5240_ = lean_ptr_addr(v_type_5229_);
v___x_5241_ = lean_ptr_addr(v_newType_5225_);
v___x_5242_ = lean_usize_dec_eq(v___x_5240_, v___x_5241_);
if (v___x_5242_ == 0)
{
v___y_5234_ = v___x_5242_;
goto v___jp_5233_;
}
else
{
size_t v___x_5243_; size_t v___x_5244_; uint8_t v___x_5245_; 
v___x_5243_ = lean_ptr_addr(v_value_5230_);
v___x_5244_ = lean_ptr_addr(v_newVal_5226_);
v___x_5245_ = lean_usize_dec_eq(v___x_5243_, v___x_5244_);
v___y_5234_ = v___x_5245_;
goto v___jp_5233_;
}
v___jp_5233_:
{
if (v___y_5234_ == 0)
{
lean_object* v___x_5235_; 
lean_inc(v_declName_5228_);
lean_dec_ref_known(v_e_5224_, 4);
v___x_5235_ = l_Lean_Expr_letE___override(v_declName_5228_, v_newType_5225_, v_newVal_5226_, v_newBody_5227_, v_nondep_5232_);
return v___x_5235_;
}
else
{
size_t v___x_5236_; size_t v___x_5237_; uint8_t v___x_5238_; 
v___x_5236_ = lean_ptr_addr(v_body_5231_);
v___x_5237_ = lean_ptr_addr(v_newBody_5227_);
v___x_5238_ = lean_usize_dec_eq(v___x_5236_, v___x_5237_);
if (v___x_5238_ == 0)
{
lean_object* v___x_5239_; 
lean_inc(v_declName_5228_);
lean_dec_ref_known(v_e_5224_, 4);
v___x_5239_ = l_Lean_Expr_letE___override(v_declName_5228_, v_newType_5225_, v_newVal_5226_, v_newBody_5227_, v_nondep_5232_);
return v___x_5239_;
}
else
{
lean_dec_ref(v_newBody_5227_);
lean_dec_ref(v_newVal_5226_);
lean_dec_ref(v_newType_5225_);
return v_e_5224_;
}
}
}
}
else
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
lean_dec_ref(v_newBody_5227_);
lean_dec_ref(v_newVal_5226_);
lean_dec_ref(v_newType_5225_);
lean_dec_ref(v_e_5224_);
v___x_5246_ = l_Lean_instInhabitedExpr;
v___x_5247_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5248_ = l_panic___redArg(v___x_5246_, v___x_5247_);
return v___x_5248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5249_, lean_object* v_x_5250_){
_start:
{
if (lean_obj_tag(v_x_5249_) == 5)
{
lean_object* v_fn_5251_; lean_object* v_arg_5252_; lean_object* v___x_5253_; uint8_t v___y_5255_; size_t v___x_5257_; size_t v___x_5258_; uint8_t v___x_5259_; 
v_fn_5251_ = lean_ctor_get(v_x_5249_, 0);
v_arg_5252_ = lean_ctor_get(v_x_5249_, 1);
lean_inc_ref(v_fn_5251_);
v___x_5253_ = l_Lean_Expr_updateFn(v_fn_5251_, v_x_5250_);
v___x_5257_ = lean_ptr_addr(v_fn_5251_);
v___x_5258_ = lean_ptr_addr(v___x_5253_);
v___x_5259_ = lean_usize_dec_eq(v___x_5257_, v___x_5258_);
if (v___x_5259_ == 0)
{
v___y_5255_ = v___x_5259_;
goto v___jp_5254_;
}
else
{
size_t v___x_5260_; uint8_t v___x_5261_; 
v___x_5260_ = lean_ptr_addr(v_arg_5252_);
v___x_5261_ = lean_usize_dec_eq(v___x_5260_, v___x_5260_);
v___y_5255_ = v___x_5261_;
goto v___jp_5254_;
}
v___jp_5254_:
{
if (v___y_5255_ == 0)
{
lean_object* v___x_5256_; 
lean_inc_ref(v_arg_5252_);
lean_dec_ref_known(v_x_5249_, 2);
v___x_5256_ = l_Lean_Expr_app___override(v___x_5253_, v_arg_5252_);
return v___x_5256_;
}
else
{
lean_dec_ref(v___x_5253_);
return v_x_5249_;
}
}
}
else
{
lean_dec_ref(v_x_5249_);
lean_inc_ref(v_x_5250_);
return v_x_5250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5262_, lean_object* v_x_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_Lean_Expr_updateFn(v_x_5262_, v_x_5263_);
lean_dec_ref(v_x_5263_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5265_){
_start:
{
if (lean_obj_tag(v_e_5265_) == 6)
{
lean_object* v_binderName_5266_; lean_object* v_binderType_5267_; lean_object* v_body_5268_; uint8_t v_binderInfo_5269_; lean_object* v_b_x27_5270_; uint8_t v___y_5272_; uint8_t v___y_5277_; 
v_binderName_5266_ = lean_ctor_get(v_e_5265_, 0);
v_binderType_5267_ = lean_ctor_get(v_e_5265_, 1);
v_body_5268_ = lean_ctor_get(v_e_5265_, 2);
v_binderInfo_5269_ = lean_ctor_get_uint8(v_e_5265_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5268_);
v_b_x27_5270_ = l_Lean_Expr_eta(v_body_5268_);
if (lean_obj_tag(v_b_x27_5270_) == 5)
{
lean_object* v_arg_5287_; 
v_arg_5287_ = lean_ctor_get(v_b_x27_5270_, 1);
lean_inc_ref(v_arg_5287_);
if (lean_obj_tag(v_arg_5287_) == 0)
{
lean_object* v_fn_5288_; lean_object* v_deBruijnIndex_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; 
v_fn_5288_ = lean_ctor_get(v_b_x27_5270_, 0);
lean_inc_ref(v_fn_5288_);
v_deBruijnIndex_5289_ = lean_ctor_get(v_arg_5287_, 0);
lean_inc(v_deBruijnIndex_5289_);
lean_dec_ref_known(v_arg_5287_, 1);
v___x_5290_ = lean_unsigned_to_nat(0u);
v___x_5291_ = lean_nat_dec_eq(v_deBruijnIndex_5289_, v___x_5290_);
lean_dec(v_deBruijnIndex_5289_);
if (v___x_5291_ == 0)
{
lean_dec_ref(v_fn_5288_);
goto v___jp_5281_;
}
else
{
uint8_t v___x_5292_; 
v___x_5292_ = lean_expr_has_loose_bvar(v_fn_5288_, v___x_5290_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; lean_object* v___x_5294_; 
lean_dec_ref_known(v_b_x27_5270_, 2);
lean_dec_ref_known(v_e_5265_, 3);
v___x_5293_ = lean_unsigned_to_nat(1u);
v___x_5294_ = lean_expr_lower_loose_bvars(v_fn_5288_, v___x_5293_, v___x_5293_);
lean_dec_ref(v_fn_5288_);
return v___x_5294_;
}
else
{
size_t v___x_5295_; uint8_t v___x_5296_; 
lean_dec_ref(v_fn_5288_);
v___x_5295_ = lean_ptr_addr(v_binderType_5267_);
v___x_5296_ = lean_usize_dec_eq(v___x_5295_, v___x_5295_);
if (v___x_5296_ == 0)
{
v___y_5272_ = v___x_5296_;
goto v___jp_5271_;
}
else
{
size_t v___x_5297_; size_t v___x_5298_; uint8_t v___x_5299_; 
v___x_5297_ = lean_ptr_addr(v_body_5268_);
v___x_5298_ = lean_ptr_addr(v_b_x27_5270_);
v___x_5299_ = lean_usize_dec_eq(v___x_5297_, v___x_5298_);
v___y_5272_ = v___x_5299_;
goto v___jp_5271_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5287_);
goto v___jp_5281_;
}
}
else
{
goto v___jp_5281_;
}
v___jp_5271_:
{
if (v___y_5272_ == 0)
{
lean_object* v___x_5273_; 
lean_inc_ref(v_binderType_5267_);
lean_inc(v_binderName_5266_);
lean_dec_ref_known(v_e_5265_, 3);
v___x_5273_ = l_Lean_Expr_lam___override(v_binderName_5266_, v_binderType_5267_, v_b_x27_5270_, v_binderInfo_5269_);
return v___x_5273_;
}
else
{
uint8_t v___x_5274_; 
v___x_5274_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5269_, v_binderInfo_5269_);
if (v___x_5274_ == 0)
{
lean_object* v___x_5275_; 
lean_inc_ref(v_binderType_5267_);
lean_inc(v_binderName_5266_);
lean_dec_ref_known(v_e_5265_, 3);
v___x_5275_ = l_Lean_Expr_lam___override(v_binderName_5266_, v_binderType_5267_, v_b_x27_5270_, v_binderInfo_5269_);
return v___x_5275_;
}
else
{
lean_dec_ref(v_b_x27_5270_);
return v_e_5265_;
}
}
}
v___jp_5276_:
{
if (v___y_5277_ == 0)
{
lean_object* v___x_5278_; 
lean_inc_ref(v_binderType_5267_);
lean_inc(v_binderName_5266_);
lean_dec_ref_known(v_e_5265_, 3);
v___x_5278_ = l_Lean_Expr_lam___override(v_binderName_5266_, v_binderType_5267_, v_b_x27_5270_, v_binderInfo_5269_);
return v___x_5278_;
}
else
{
uint8_t v___x_5279_; 
v___x_5279_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5269_, v_binderInfo_5269_);
if (v___x_5279_ == 0)
{
lean_object* v___x_5280_; 
lean_inc_ref(v_binderType_5267_);
lean_inc(v_binderName_5266_);
lean_dec_ref_known(v_e_5265_, 3);
v___x_5280_ = l_Lean_Expr_lam___override(v_binderName_5266_, v_binderType_5267_, v_b_x27_5270_, v_binderInfo_5269_);
return v___x_5280_;
}
else
{
lean_dec_ref(v_b_x27_5270_);
return v_e_5265_;
}
}
}
v___jp_5281_:
{
size_t v___x_5282_; uint8_t v___x_5283_; 
v___x_5282_ = lean_ptr_addr(v_binderType_5267_);
v___x_5283_ = lean_usize_dec_eq(v___x_5282_, v___x_5282_);
if (v___x_5283_ == 0)
{
v___y_5277_ = v___x_5283_;
goto v___jp_5276_;
}
else
{
size_t v___x_5284_; size_t v___x_5285_; uint8_t v___x_5286_; 
v___x_5284_ = lean_ptr_addr(v_body_5268_);
v___x_5285_ = lean_ptr_addr(v_b_x27_5270_);
v___x_5286_ = lean_usize_dec_eq(v___x_5284_, v___x_5285_);
v___y_5277_ = v___x_5286_;
goto v___jp_5276_;
}
}
}
else
{
return v_e_5265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5300_, lean_object* v_optionName_5301_, lean_object* v_inst_5302_, lean_object* v_val_5303_){
_start:
{
lean_object* v_toDataValue_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v_toDataValue_5304_ = lean_ctor_get(v_inst_5302_, 0);
lean_inc_ref(v_toDataValue_5304_);
lean_dec_ref(v_inst_5302_);
v___x_5305_ = lean_box(0);
v___x_5306_ = lean_apply_1(v_toDataValue_5304_, v_val_5303_);
v___x_5307_ = l_Lean_KVMap_insert(v___x_5305_, v_optionName_5301_, v___x_5306_);
v___x_5308_ = l_Lean_Expr_mdata___override(v___x_5307_, v_e_5300_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5309_, lean_object* v_e_5310_, lean_object* v_optionName_5311_, lean_object* v_inst_5312_, lean_object* v_val_5313_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l_Lean_Expr_setOption___redArg(v_e_5310_, v_optionName_5311_, v_inst_5312_, v_val_5313_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5315_, lean_object* v_optionName_5316_, uint8_t v_val_5317_){
_start:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5318_ = lean_box(0);
v___x_5319_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5319_, 0, v_val_5317_);
v___x_5320_ = l_Lean_KVMap_insert(v___x_5318_, v_optionName_5316_, v___x_5319_);
v___x_5321_ = l_Lean_Expr_mdata___override(v___x_5320_, v_e_5315_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5322_, lean_object* v_optionName_5323_, lean_object* v_val_5324_){
_start:
{
uint8_t v_val_boxed_5325_; lean_object* v_res_5326_; 
v_val_boxed_5325_ = lean_unbox(v_val_5324_);
v_res_5326_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5322_, v_optionName_5323_, v_val_boxed_5325_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5332_, uint8_t v_flag_5333_){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5334_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5335_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5332_, v___x_5334_, v_flag_5333_);
return v___x_5335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5336_, lean_object* v_flag_5337_){
_start:
{
uint8_t v_flag_boxed_5338_; lean_object* v_res_5339_; 
v_flag_boxed_5338_ = lean_unbox(v_flag_5337_);
v_res_5339_ = l_Lean_Expr_setPPExplicit(v_e_5336_, v_flag_boxed_5338_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5344_, uint8_t v_flag_5345_){
_start:
{
lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5346_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5347_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5344_, v___x_5346_, v_flag_5345_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5348_, lean_object* v_flag_5349_){
_start:
{
uint8_t v_flag_boxed_5350_; lean_object* v_res_5351_; 
v_flag_boxed_5350_ = lean_unbox(v_flag_5349_);
v_res_5351_ = l_Lean_Expr_setPPUniverses(v_e_5348_, v_flag_boxed_5350_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5356_, uint8_t v_flag_5357_){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5359_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5356_, v___x_5358_, v_flag_5357_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5360_, lean_object* v_flag_5361_){
_start:
{
uint8_t v_flag_boxed_5362_; lean_object* v_res_5363_; 
v_flag_boxed_5362_ = lean_unbox(v_flag_5361_);
v_res_5363_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5360_, v_flag_boxed_5362_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5368_, uint8_t v_flag_5369_){
_start:
{
lean_object* v___x_5370_; lean_object* v___x_5371_; 
v___x_5370_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5371_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5368_, v___x_5370_, v_flag_5369_);
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5372_, lean_object* v_flag_5373_){
_start:
{
uint8_t v_flag_boxed_5374_; lean_object* v_res_5375_; 
v_flag_boxed_5374_ = lean_unbox(v_flag_5373_);
v_res_5375_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5372_, v_flag_boxed_5374_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5380_, uint8_t v_flag_5381_){
_start:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5382_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5383_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5380_, v___x_5382_, v_flag_5381_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5384_, lean_object* v_flag_5385_){
_start:
{
uint8_t v_flag_boxed_5386_; lean_object* v_res_5387_; 
v_flag_boxed_5386_ = lean_unbox(v_flag_5385_);
v_res_5387_ = l_Lean_Expr_setPPNumericTypes(v_e_5384_, v_flag_boxed_5386_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5388_, size_t v_i_5389_, lean_object* v_bs_5390_){
_start:
{
uint8_t v___x_5391_; 
v___x_5391_ = lean_usize_dec_lt(v_i_5389_, v_sz_5388_);
if (v___x_5391_ == 0)
{
return v_bs_5390_;
}
else
{
uint8_t v___x_5392_; lean_object* v_v_5393_; lean_object* v___x_5394_; lean_object* v_bs_x27_5395_; lean_object* v___x_5396_; size_t v___x_5397_; size_t v___x_5398_; lean_object* v___x_5399_; 
v___x_5392_ = 0;
v_v_5393_ = lean_array_uget(v_bs_5390_, v_i_5389_);
v___x_5394_ = lean_unsigned_to_nat(0u);
v_bs_x27_5395_ = lean_array_uset(v_bs_5390_, v_i_5389_, v___x_5394_);
v___x_5396_ = l_Lean_Expr_setPPExplicit(v_v_5393_, v___x_5392_);
v___x_5397_ = ((size_t)1ULL);
v___x_5398_ = lean_usize_add(v_i_5389_, v___x_5397_);
v___x_5399_ = lean_array_uset(v_bs_x27_5395_, v_i_5389_, v___x_5396_);
v_i_5389_ = v___x_5398_;
v_bs_5390_ = v___x_5399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5401_, lean_object* v_i_5402_, lean_object* v_bs_5403_){
_start:
{
size_t v_sz_boxed_5404_; size_t v_i_boxed_5405_; lean_object* v_res_5406_; 
v_sz_boxed_5404_ = lean_unbox_usize(v_sz_5401_);
lean_dec(v_sz_5401_);
v_i_boxed_5405_ = lean_unbox_usize(v_i_5402_);
lean_dec(v_i_5402_);
v_res_5406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5404_, v_i_boxed_5405_, v_bs_5403_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5407_){
_start:
{
if (lean_obj_tag(v_e_5407_) == 5)
{
lean_object* v___x_5408_; uint8_t v___x_5409_; lean_object* v_f_5410_; lean_object* v_dummy_5411_; lean_object* v_nargs_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; size_t v_sz_5417_; size_t v___x_5418_; lean_object* v_args_5419_; lean_object* v___x_5420_; uint8_t v___x_5421_; lean_object* v___x_5422_; 
v___x_5408_ = l_Lean_Expr_getAppFn(v_e_5407_);
v___x_5409_ = 0;
v_f_5410_ = l_Lean_Expr_setPPExplicit(v___x_5408_, v___x_5409_);
v_dummy_5411_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5412_ = l_Lean_Expr_getAppNumArgs(v_e_5407_);
lean_inc(v_nargs_5412_);
v___x_5413_ = lean_mk_array(v_nargs_5412_, v_dummy_5411_);
v___x_5414_ = lean_unsigned_to_nat(1u);
v___x_5415_ = lean_nat_sub(v_nargs_5412_, v___x_5414_);
lean_dec(v_nargs_5412_);
v___x_5416_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5407_, v___x_5413_, v___x_5415_);
v_sz_5417_ = lean_array_size(v___x_5416_);
v___x_5418_ = ((size_t)0ULL);
v_args_5419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5417_, v___x_5418_, v___x_5416_);
v___x_5420_ = l_Lean_mkAppN(v_f_5410_, v_args_5419_);
lean_dec_ref(v_args_5419_);
v___x_5421_ = 1;
v___x_5422_ = l_Lean_Expr_setPPExplicit(v___x_5420_, v___x_5421_);
return v___x_5422_;
}
else
{
return v_e_5407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5423_, size_t v_i_5424_, lean_object* v_bs_5425_){
_start:
{
uint8_t v___x_5426_; 
v___x_5426_ = lean_usize_dec_lt(v_i_5424_, v_sz_5423_);
if (v___x_5426_ == 0)
{
return v_bs_5425_;
}
else
{
lean_object* v_v_5427_; lean_object* v___x_5428_; lean_object* v_bs_x27_5429_; lean_object* v___y_5431_; uint8_t v___x_5436_; 
v_v_5427_ = lean_array_uget(v_bs_5425_, v_i_5424_);
v___x_5428_ = lean_unsigned_to_nat(0u);
v_bs_x27_5429_ = lean_array_uset(v_bs_5425_, v_i_5424_, v___x_5428_);
v___x_5436_ = l_Lean_Expr_hasMVar(v_v_5427_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5437_; 
v___x_5437_ = l_Lean_Expr_setPPExplicit(v_v_5427_, v___x_5436_);
v___y_5431_ = v___x_5437_;
goto v___jp_5430_;
}
else
{
v___y_5431_ = v_v_5427_;
goto v___jp_5430_;
}
v___jp_5430_:
{
size_t v___x_5432_; size_t v___x_5433_; lean_object* v___x_5434_; 
v___x_5432_ = ((size_t)1ULL);
v___x_5433_ = lean_usize_add(v_i_5424_, v___x_5432_);
v___x_5434_ = lean_array_uset(v_bs_x27_5429_, v_i_5424_, v___y_5431_);
v_i_5424_ = v___x_5433_;
v_bs_5425_ = v___x_5434_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5438_, lean_object* v_i_5439_, lean_object* v_bs_5440_){
_start:
{
size_t v_sz_boxed_5441_; size_t v_i_boxed_5442_; lean_object* v_res_5443_; 
v_sz_boxed_5441_ = lean_unbox_usize(v_sz_5438_);
lean_dec(v_sz_5438_);
v_i_boxed_5442_ = lean_unbox_usize(v_i_5439_);
lean_dec(v_i_5439_);
v_res_5443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5441_, v_i_boxed_5442_, v_bs_5440_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5444_){
_start:
{
if (lean_obj_tag(v_e_5444_) == 5)
{
lean_object* v___x_5445_; uint8_t v___x_5446_; lean_object* v_f_5447_; lean_object* v_dummy_5448_; lean_object* v_nargs_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; size_t v_sz_5454_; size_t v___x_5455_; lean_object* v_args_5456_; lean_object* v___x_5457_; uint8_t v___x_5458_; lean_object* v___x_5459_; 
v___x_5445_ = l_Lean_Expr_getAppFn(v_e_5444_);
v___x_5446_ = 0;
v_f_5447_ = l_Lean_Expr_setPPExplicit(v___x_5445_, v___x_5446_);
v_dummy_5448_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5449_ = l_Lean_Expr_getAppNumArgs(v_e_5444_);
lean_inc(v_nargs_5449_);
v___x_5450_ = lean_mk_array(v_nargs_5449_, v_dummy_5448_);
v___x_5451_ = lean_unsigned_to_nat(1u);
v___x_5452_ = lean_nat_sub(v_nargs_5449_, v___x_5451_);
lean_dec(v_nargs_5449_);
v___x_5453_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5444_, v___x_5450_, v___x_5452_);
v_sz_5454_ = lean_array_size(v___x_5453_);
v___x_5455_ = ((size_t)0ULL);
v_args_5456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5454_, v___x_5455_, v___x_5453_);
v___x_5457_ = l_Lean_mkAppN(v_f_5447_, v_args_5456_);
lean_dec_ref(v_args_5456_);
v___x_5458_ = 1;
v___x_5459_ = l_Lean_Expr_setPPExplicit(v___x_5457_, v___x_5458_);
return v___x_5459_;
}
else
{
return v_e_5444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5460_, lean_object* v_body_5461_, lean_object* v_x_5462_){
_start:
{
lean_object* v___x_5463_; 
v___x_5463_ = lean_apply_1(v_f_5460_, v_body_5461_);
return v___x_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5464_, lean_object* v_binderType_5465_, lean_object* v_x_5466_){
_start:
{
lean_object* v___x_5467_; 
v___x_5467_ = lean_apply_1(v_f_5464_, v_binderType_5465_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5468_, lean_object* v_value_5469_, lean_object* v_x_5470_){
_start:
{
lean_object* v___x_5471_; 
v___x_5471_ = lean_apply_1(v_f_5468_, v_value_5469_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5472_, lean_object* v_type_5473_, lean_object* v_x_5474_){
_start:
{
lean_object* v___x_5475_; 
v___x_5475_ = lean_apply_1(v_f_5472_, v_type_5473_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5476_, lean_object* v_arg_5477_, lean_object* v_x_5478_){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = lean_apply_1(v_f_5476_, v_arg_5477_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5480_, lean_object* v_fn_5481_, lean_object* v_x_5482_){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = lean_apply_1(v_f_5480_, v_fn_5481_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5484_, lean_object* v_f_5485_, lean_object* v_x_5486_){
_start:
{
switch(lean_obj_tag(v_x_5486_))
{
case 7:
{
lean_object* v_toPure_5487_; lean_object* v_toSeq_5488_; lean_object* v_binderType_5489_; lean_object* v_body_5490_; lean_object* v___f_5491_; lean_object* v___f_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; 
v_toPure_5487_ = lean_ctor_get(v_inst_5484_, 1);
lean_inc(v_toPure_5487_);
v_toSeq_5488_ = lean_ctor_get(v_inst_5484_, 2);
lean_inc_n(v_toSeq_5488_, 2);
lean_dec_ref(v_inst_5484_);
v_binderType_5489_ = lean_ctor_get(v_x_5486_, 1);
v_body_5490_ = lean_ctor_get(v_x_5486_, 2);
lean_inc_ref(v_body_5490_);
lean_inc(v_f_5485_);
v___f_5491_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5491_, 0, v_f_5485_);
lean_closure_set(v___f_5491_, 1, v_body_5490_);
lean_inc_ref(v_binderType_5489_);
v___f_5492_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5492_, 0, v_f_5485_);
lean_closure_set(v___f_5492_, 1, v_binderType_5489_);
v___x_5493_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5493_, 0, v_x_5486_);
v___x_5494_ = lean_apply_2(v_toPure_5487_, lean_box(0), v___x_5493_);
v___x_5495_ = lean_apply_4(v_toSeq_5488_, lean_box(0), lean_box(0), v___x_5494_, v___f_5492_);
v___x_5496_ = lean_apply_4(v_toSeq_5488_, lean_box(0), lean_box(0), v___x_5495_, v___f_5491_);
return v___x_5496_;
}
case 6:
{
lean_object* v_toPure_5497_; lean_object* v_toSeq_5498_; lean_object* v_binderType_5499_; lean_object* v_body_5500_; lean_object* v___f_5501_; lean_object* v___f_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
v_toPure_5497_ = lean_ctor_get(v_inst_5484_, 1);
lean_inc(v_toPure_5497_);
v_toSeq_5498_ = lean_ctor_get(v_inst_5484_, 2);
lean_inc_n(v_toSeq_5498_, 2);
lean_dec_ref(v_inst_5484_);
v_binderType_5499_ = lean_ctor_get(v_x_5486_, 1);
v_body_5500_ = lean_ctor_get(v_x_5486_, 2);
lean_inc_ref(v_body_5500_);
lean_inc(v_f_5485_);
v___f_5501_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5501_, 0, v_f_5485_);
lean_closure_set(v___f_5501_, 1, v_body_5500_);
lean_inc_ref(v_binderType_5499_);
v___f_5502_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5502_, 0, v_f_5485_);
lean_closure_set(v___f_5502_, 1, v_binderType_5499_);
v___x_5503_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5503_, 0, v_x_5486_);
v___x_5504_ = lean_apply_2(v_toPure_5497_, lean_box(0), v___x_5503_);
v___x_5505_ = lean_apply_4(v_toSeq_5498_, lean_box(0), lean_box(0), v___x_5504_, v___f_5502_);
v___x_5506_ = lean_apply_4(v_toSeq_5498_, lean_box(0), lean_box(0), v___x_5505_, v___f_5501_);
return v___x_5506_;
}
case 10:
{
lean_object* v_toFunctor_5507_; lean_object* v_expr_5508_; lean_object* v_map_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; 
v_toFunctor_5507_ = lean_ctor_get(v_inst_5484_, 0);
lean_inc_ref(v_toFunctor_5507_);
lean_dec_ref(v_inst_5484_);
v_expr_5508_ = lean_ctor_get(v_x_5486_, 1);
lean_inc_ref(v_expr_5508_);
v_map_5509_ = lean_ctor_get(v_toFunctor_5507_, 0);
lean_inc(v_map_5509_);
lean_dec_ref(v_toFunctor_5507_);
v___x_5510_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5510_, 0, v_x_5486_);
v___x_5511_ = lean_apply_1(v_f_5485_, v_expr_5508_);
v___x_5512_ = lean_apply_4(v_map_5509_, lean_box(0), lean_box(0), v___x_5510_, v___x_5511_);
return v___x_5512_;
}
case 8:
{
lean_object* v_toPure_5513_; lean_object* v_toSeq_5514_; lean_object* v_type_5515_; lean_object* v_value_5516_; lean_object* v_body_5517_; lean_object* v___f_5518_; lean_object* v___f_5519_; lean_object* v___f_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v_toPure_5513_ = lean_ctor_get(v_inst_5484_, 1);
lean_inc(v_toPure_5513_);
v_toSeq_5514_ = lean_ctor_get(v_inst_5484_, 2);
lean_inc_n(v_toSeq_5514_, 3);
lean_dec_ref(v_inst_5484_);
v_type_5515_ = lean_ctor_get(v_x_5486_, 1);
v_value_5516_ = lean_ctor_get(v_x_5486_, 2);
v_body_5517_ = lean_ctor_get(v_x_5486_, 3);
lean_inc_ref(v_body_5517_);
lean_inc_n(v_f_5485_, 2);
v___f_5518_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5518_, 0, v_f_5485_);
lean_closure_set(v___f_5518_, 1, v_body_5517_);
lean_inc_ref(v_value_5516_);
v___f_5519_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5519_, 0, v_f_5485_);
lean_closure_set(v___f_5519_, 1, v_value_5516_);
lean_inc_ref(v_type_5515_);
v___f_5520_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5520_, 0, v_f_5485_);
lean_closure_set(v___f_5520_, 1, v_type_5515_);
v___x_5521_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5521_, 0, v_x_5486_);
v___x_5522_ = lean_apply_2(v_toPure_5513_, lean_box(0), v___x_5521_);
v___x_5523_ = lean_apply_4(v_toSeq_5514_, lean_box(0), lean_box(0), v___x_5522_, v___f_5520_);
v___x_5524_ = lean_apply_4(v_toSeq_5514_, lean_box(0), lean_box(0), v___x_5523_, v___f_5519_);
v___x_5525_ = lean_apply_4(v_toSeq_5514_, lean_box(0), lean_box(0), v___x_5524_, v___f_5518_);
return v___x_5525_;
}
case 5:
{
lean_object* v_toPure_5526_; lean_object* v_toSeq_5527_; lean_object* v_fn_5528_; lean_object* v_arg_5529_; lean_object* v___f_5530_; lean_object* v___f_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; 
v_toPure_5526_ = lean_ctor_get(v_inst_5484_, 1);
lean_inc(v_toPure_5526_);
v_toSeq_5527_ = lean_ctor_get(v_inst_5484_, 2);
lean_inc_n(v_toSeq_5527_, 2);
lean_dec_ref(v_inst_5484_);
v_fn_5528_ = lean_ctor_get(v_x_5486_, 0);
v_arg_5529_ = lean_ctor_get(v_x_5486_, 1);
lean_inc_ref(v_arg_5529_);
lean_inc(v_f_5485_);
v___f_5530_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5530_, 0, v_f_5485_);
lean_closure_set(v___f_5530_, 1, v_arg_5529_);
lean_inc_ref(v_fn_5528_);
v___f_5531_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5531_, 0, v_f_5485_);
lean_closure_set(v___f_5531_, 1, v_fn_5528_);
v___x_5532_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5532_, 0, v_x_5486_);
v___x_5533_ = lean_apply_2(v_toPure_5526_, lean_box(0), v___x_5532_);
v___x_5534_ = lean_apply_4(v_toSeq_5527_, lean_box(0), lean_box(0), v___x_5533_, v___f_5531_);
v___x_5535_ = lean_apply_4(v_toSeq_5527_, lean_box(0), lean_box(0), v___x_5534_, v___f_5530_);
return v___x_5535_;
}
case 11:
{
lean_object* v_toFunctor_5536_; lean_object* v_struct_5537_; lean_object* v_map_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; 
v_toFunctor_5536_ = lean_ctor_get(v_inst_5484_, 0);
lean_inc_ref(v_toFunctor_5536_);
lean_dec_ref(v_inst_5484_);
v_struct_5537_ = lean_ctor_get(v_x_5486_, 2);
lean_inc_ref(v_struct_5537_);
v_map_5538_ = lean_ctor_get(v_toFunctor_5536_, 0);
lean_inc(v_map_5538_);
lean_dec_ref(v_toFunctor_5536_);
v___x_5539_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5539_, 0, v_x_5486_);
v___x_5540_ = lean_apply_1(v_f_5485_, v_struct_5537_);
v___x_5541_ = lean_apply_4(v_map_5538_, lean_box(0), lean_box(0), v___x_5539_, v___x_5540_);
return v___x_5541_;
}
default: 
{
lean_object* v_toPure_5542_; lean_object* v___x_5543_; 
lean_dec(v_f_5485_);
v_toPure_5542_ = lean_ctor_get(v_inst_5484_, 1);
lean_inc(v_toPure_5542_);
lean_dec_ref(v_inst_5484_);
v___x_5543_ = lean_apply_2(v_toPure_5542_, lean_box(0), v_x_5486_);
return v___x_5543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5544_, lean_object* v_inst_5545_, lean_object* v_f_5546_, lean_object* v_x_5547_){
_start:
{
lean_object* v___x_5548_; 
v___x_5548_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5545_, v_f_5546_, v_x_5547_);
return v___x_5548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5549_){
_start:
{
lean_object* v_snd_5550_; 
v_snd_5550_ = lean_ctor_get(v_self_5549_, 1);
lean_inc(v_snd_5550_);
return v_snd_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5551_);
lean_dec_ref(v_self_5551_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5553_, lean_object* v_snd_5554_){
_start:
{
lean_object* v___x_5555_; 
v___x_5555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5555_, 0, v_e_x27_5553_);
lean_ctor_set(v___x_5555_, 1, v_snd_5554_);
return v___x_5555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5556_, lean_object* v_map_5557_, lean_object* v_e_x27_5558_, lean_object* v_a_5559_){
_start:
{
lean_object* v___f_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; 
lean_inc_ref(v_e_x27_5558_);
v___f_5560_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5560_, 0, v_e_x27_5558_);
v___x_5561_ = lean_apply_2(v_f_5556_, v_a_5559_, v_e_x27_5558_);
v___x_5562_ = lean_apply_4(v_map_5557_, lean_box(0), lean_box(0), v___f_5560_, v___x_5561_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5564_, lean_object* v_f_5565_, lean_object* v_init_5566_, lean_object* v_e_5567_){
_start:
{
lean_object* v_toApplicative_5568_; lean_object* v_toFunctor_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5596_; 
v_toApplicative_5568_ = lean_ctor_get(v_inst_5564_, 0);
lean_inc_ref(v_toApplicative_5568_);
v_toFunctor_5569_ = lean_ctor_get(v_toApplicative_5568_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_toApplicative_5568_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; lean_object* v_unused_5598_; lean_object* v_unused_5599_; lean_object* v_unused_5600_; 
v_unused_5597_ = lean_ctor_get(v_toApplicative_5568_, 4);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_toApplicative_5568_, 3);
lean_dec(v_unused_5598_);
v_unused_5599_ = lean_ctor_get(v_toApplicative_5568_, 2);
lean_dec(v_unused_5599_);
v_unused_5600_ = lean_ctor_get(v_toApplicative_5568_, 1);
lean_dec(v_unused_5600_);
v___x_5571_ = v_toApplicative_5568_;
v_isShared_5572_ = v_isSharedCheck_5596_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_toFunctor_5569_);
lean_dec(v_toApplicative_5568_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5596_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v_map_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5594_; 
v_map_5573_ = lean_ctor_get(v_toFunctor_5569_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_toFunctor_5569_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; 
v_unused_5595_ = lean_ctor_get(v_toFunctor_5569_, 1);
lean_dec(v_unused_5595_);
v___x_5575_ = v_toFunctor_5569_;
v_isShared_5576_ = v_isSharedCheck_5594_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_map_5573_);
lean_dec(v_toFunctor_5569_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5594_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___f_5577_; lean_object* v___f_5578_; lean_object* v___f_5579_; lean_object* v___f_5580_; lean_object* v___f_5581_; lean_object* v___f_5582_; lean_object* v___x_5583_; lean_object* v___x_5585_; 
v___f_5577_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5573_);
v___f_5578_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5578_, 0, v_f_5565_);
lean_closure_set(v___f_5578_, 1, v_map_5573_);
lean_inc_ref_n(v_inst_5564_, 5);
v___f_5579_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5579_, 0, v_inst_5564_);
v___f_5580_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5580_, 0, v_inst_5564_);
v___f_5581_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5581_, 0, v_inst_5564_);
v___f_5582_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5582_, 0, v_inst_5564_);
v___x_5583_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5583_, 0, lean_box(0));
lean_closure_set(v___x_5583_, 1, lean_box(0));
lean_closure_set(v___x_5583_, 2, v_inst_5564_);
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 1, v___f_5579_);
lean_ctor_set(v___x_5575_, 0, v___x_5583_);
v___x_5585_ = v___x_5575_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5583_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v___f_5579_);
v___x_5585_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
lean_object* v___x_5586_; lean_object* v___x_5588_; 
v___x_5586_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5586_, 0, lean_box(0));
lean_closure_set(v___x_5586_, 1, lean_box(0));
lean_closure_set(v___x_5586_, 2, v_inst_5564_);
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 4, v___f_5582_);
lean_ctor_set(v___x_5571_, 3, v___f_5581_);
lean_ctor_set(v___x_5571_, 2, v___f_5580_);
lean_ctor_set(v___x_5571_, 1, v___x_5586_);
lean_ctor_set(v___x_5571_, 0, v___x_5585_);
v___x_5588_ = v___x_5571_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v___x_5586_);
lean_ctor_set(v_reuseFailAlloc_5592_, 2, v___f_5580_);
lean_ctor_set(v_reuseFailAlloc_5592_, 3, v___f_5581_);
lean_ctor_set(v_reuseFailAlloc_5592_, 4, v___f_5582_);
v___x_5588_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
lean_object* v___x_18__overap_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_18__overap_5589_ = l_Lean_Expr_traverseChildren___redArg(v___x_5588_, v___f_5578_, v_e_5567_);
v___x_5590_ = lean_apply_1(v___x_18__overap_5589_, v_init_5566_);
v___x_5591_ = lean_apply_4(v_map_5573_, lean_box(0), lean_box(0), v___f_5577_, v___x_5590_);
return v___x_5591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5601_, lean_object* v_m_5602_, lean_object* v_inst_5603_, lean_object* v_f_5604_, lean_object* v_init_5605_, lean_object* v_e_5606_){
_start:
{
lean_object* v___x_5607_; 
v___x_5607_ = l_Lean_Expr_foldlM___redArg(v_inst_5603_, v_f_5604_, v_init_5605_, v_e_5606_);
return v___x_5607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5608_){
_start:
{
lean_object* v_d_5610_; lean_object* v_b_5611_; 
switch(lean_obj_tag(v_x_5608_))
{
case 5:
{
lean_object* v_fn_5617_; lean_object* v_arg_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; 
v_fn_5617_ = lean_ctor_get(v_x_5608_, 0);
v_arg_5618_ = lean_ctor_get(v_x_5608_, 1);
v___x_5619_ = lean_unsigned_to_nat(1u);
v___x_5620_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5617_);
v___x_5621_ = lean_nat_add(v___x_5619_, v___x_5620_);
lean_dec(v___x_5620_);
v___x_5622_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5618_);
v___x_5623_ = lean_nat_add(v___x_5621_, v___x_5622_);
lean_dec(v___x_5622_);
lean_dec(v___x_5621_);
return v___x_5623_;
}
case 6:
{
lean_object* v_binderType_5624_; lean_object* v_body_5625_; 
v_binderType_5624_ = lean_ctor_get(v_x_5608_, 1);
v_body_5625_ = lean_ctor_get(v_x_5608_, 2);
v_d_5610_ = v_binderType_5624_;
v_b_5611_ = v_body_5625_;
goto v___jp_5609_;
}
case 7:
{
lean_object* v_binderType_5626_; lean_object* v_body_5627_; 
v_binderType_5626_ = lean_ctor_get(v_x_5608_, 1);
v_body_5627_ = lean_ctor_get(v_x_5608_, 2);
v_d_5610_ = v_binderType_5626_;
v_b_5611_ = v_body_5627_;
goto v___jp_5609_;
}
case 8:
{
lean_object* v_type_5628_; lean_object* v_value_5629_; lean_object* v_body_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; 
v_type_5628_ = lean_ctor_get(v_x_5608_, 1);
v_value_5629_ = lean_ctor_get(v_x_5608_, 2);
v_body_5630_ = lean_ctor_get(v_x_5608_, 3);
v___x_5631_ = lean_unsigned_to_nat(1u);
v___x_5632_ = l_Lean_Expr_sizeWithoutSharing(v_type_5628_);
v___x_5633_ = lean_nat_add(v___x_5631_, v___x_5632_);
lean_dec(v___x_5632_);
v___x_5634_ = l_Lean_Expr_sizeWithoutSharing(v_value_5629_);
v___x_5635_ = lean_nat_add(v___x_5633_, v___x_5634_);
lean_dec(v___x_5634_);
lean_dec(v___x_5633_);
v___x_5636_ = l_Lean_Expr_sizeWithoutSharing(v_body_5630_);
v___x_5637_ = lean_nat_add(v___x_5635_, v___x_5636_);
lean_dec(v___x_5636_);
lean_dec(v___x_5635_);
return v___x_5637_;
}
case 10:
{
lean_object* v_expr_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; 
v_expr_5638_ = lean_ctor_get(v_x_5608_, 1);
v___x_5639_ = lean_unsigned_to_nat(1u);
v___x_5640_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5638_);
v___x_5641_ = lean_nat_add(v___x_5639_, v___x_5640_);
lean_dec(v___x_5640_);
return v___x_5641_;
}
case 11:
{
lean_object* v_struct_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; 
v_struct_5642_ = lean_ctor_get(v_x_5608_, 2);
v___x_5643_ = lean_unsigned_to_nat(1u);
v___x_5644_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5642_);
v___x_5645_ = lean_nat_add(v___x_5643_, v___x_5644_);
lean_dec(v___x_5644_);
return v___x_5645_;
}
default: 
{
lean_object* v___x_5646_; 
v___x_5646_ = lean_unsigned_to_nat(1u);
return v___x_5646_;
}
}
v___jp_5609_:
{
lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
v___x_5612_ = lean_unsigned_to_nat(1u);
v___x_5613_ = l_Lean_Expr_sizeWithoutSharing(v_d_5610_);
v___x_5614_ = lean_nat_add(v___x_5612_, v___x_5613_);
lean_dec(v___x_5613_);
v___x_5615_ = l_Lean_Expr_sizeWithoutSharing(v_b_5611_);
v___x_5616_ = lean_nat_add(v___x_5614_, v___x_5615_);
lean_dec(v___x_5615_);
lean_dec(v___x_5614_);
return v___x_5616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l_Lean_Expr_sizeWithoutSharing(v_x_5647_);
lean_dec_ref(v_x_5647_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5651_, lean_object* v_e_5652_){
_start:
{
lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v___x_5653_ = l_Lean_KVMap_empty;
v___x_5654_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5655_ = l_Lean_KVMap_insert(v___x_5653_, v_kind_5651_, v___x_5654_);
v___x_5656_ = l_Lean_Expr_mdata___override(v___x_5655_, v_e_5652_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5657_, lean_object* v_e_5658_){
_start:
{
if (lean_obj_tag(v_e_5658_) == 10)
{
lean_object* v_data_5659_; lean_object* v_expr_5660_; uint8_t v___y_5662_; lean_object* v___x_5665_; lean_object* v___x_5666_; uint8_t v___x_5667_; 
v_data_5659_ = lean_ctor_get(v_e_5658_, 0);
v_expr_5660_ = lean_ctor_get(v_e_5658_, 1);
v___x_5665_ = l_Lean_KVMap_size(v_data_5659_);
v___x_5666_ = lean_unsigned_to_nat(1u);
v___x_5667_ = lean_nat_dec_eq(v___x_5665_, v___x_5666_);
lean_dec(v___x_5665_);
if (v___x_5667_ == 0)
{
v___y_5662_ = v___x_5667_;
goto v___jp_5661_;
}
else
{
uint8_t v___x_5668_; uint8_t v___x_5669_; 
v___x_5668_ = 0;
v___x_5669_ = l_Lean_KVMap_getBool(v_data_5659_, v_kind_5657_, v___x_5668_);
v___y_5662_ = v___x_5669_;
goto v___jp_5661_;
}
v___jp_5661_:
{
if (v___y_5662_ == 0)
{
lean_object* v___x_5663_; 
v___x_5663_ = lean_box(0);
return v___x_5663_;
}
else
{
lean_object* v___x_5664_; 
lean_inc_ref(v_expr_5660_);
v___x_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5664_, 0, v_expr_5660_);
return v___x_5664_;
}
}
}
else
{
lean_object* v___x_5670_; 
v___x_5670_ = lean_box(0);
return v___x_5670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5671_, lean_object* v_e_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l_Lean_annotation_x3f(v_kind_5671_, v_e_5672_);
lean_dec_ref(v_e_5672_);
lean_dec(v_kind_5671_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5677_){
_start:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5678_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5679_ = l_Lean_mkAnnotation(v___x_5678_, v_e_5677_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5680_){
_start:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; 
v___x_5681_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5682_ = l_Lean_annotation_x3f(v___x_5681_, v_e_5680_);
return v___x_5682_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5683_){
_start:
{
lean_object* v_res_5684_; 
v_res_5684_ = l_Lean_inaccessible_x3f(v_e_5683_);
lean_dec_ref(v_e_5683_);
return v_res_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5689_){
_start:
{
if (lean_obj_tag(v_p_5689_) == 10)
{
lean_object* v_data_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v_data_5690_ = lean_ctor_get(v_p_5689_, 0);
v___x_5691_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5692_ = l_Lean_KVMap_find(v_data_5690_, v___x_5691_);
if (lean_obj_tag(v___x_5692_) == 1)
{
lean_object* v_val_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5704_; 
v_val_5693_ = lean_ctor_get(v___x_5692_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5695_ = v___x_5692_;
v_isShared_5696_ = v_isSharedCheck_5704_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_val_5693_);
lean_dec(v___x_5692_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5704_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
if (lean_obj_tag(v_val_5693_) == 5)
{
lean_object* v_v_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5701_; 
v_v_5697_ = lean_ctor_get(v_val_5693_, 0);
lean_inc(v_v_5697_);
lean_dec_ref_known(v_val_5693_, 1);
v___x_5698_ = l_Lean_Expr_mdataExpr_x21(v_p_5689_);
v___x_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5699_, 0, v_v_5697_);
lean_ctor_set(v___x_5699_, 1, v___x_5698_);
if (v_isShared_5696_ == 0)
{
lean_ctor_set(v___x_5695_, 0, v___x_5699_);
v___x_5701_ = v___x_5695_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5699_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
else
{
lean_object* v___x_5703_; 
lean_del_object(v___x_5695_);
lean_dec(v_val_5693_);
v___x_5703_ = lean_box(0);
return v___x_5703_;
}
}
}
else
{
lean_object* v___x_5705_; 
lean_dec(v___x_5692_);
v___x_5705_ = lean_box(0);
return v___x_5705_;
}
}
else
{
lean_object* v___x_5706_; 
v___x_5706_ = lean_box(0);
return v___x_5706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5707_){
_start:
{
lean_object* v_res_5708_; 
v_res_5708_ = l_Lean_patternWithRef_x3f(v_p_5707_);
lean_dec_ref(v_p_5707_);
return v_res_5708_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5709_){
_start:
{
lean_object* v___x_5710_; 
v___x_5710_ = l_Lean_patternWithRef_x3f(v_p_5709_);
if (lean_obj_tag(v___x_5710_) == 0)
{
uint8_t v___x_5711_; 
v___x_5711_ = 0;
return v___x_5711_;
}
else
{
uint8_t v___x_5712_; 
lean_dec_ref_known(v___x_5710_, 1);
v___x_5712_ = 1;
return v___x_5712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5713_){
_start:
{
uint8_t v_res_5714_; lean_object* v_r_5715_; 
v_res_5714_ = l_Lean_isPatternWithRef(v_p_5713_);
lean_dec_ref(v_p_5713_);
v_r_5715_ = lean_box(v_res_5714_);
return v_r_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5716_, lean_object* v_stx_5717_){
_start:
{
lean_object* v___x_5718_; 
v___x_5718_ = l_Lean_patternWithRef_x3f(v_p_5716_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
v___x_5719_ = l_Lean_KVMap_empty;
v___x_5720_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5721_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5721_, 0, v_stx_5717_);
v___x_5722_ = l_Lean_KVMap_insert(v___x_5719_, v___x_5720_, v___x_5721_);
v___x_5723_ = l_Lean_Expr_mdata___override(v___x_5722_, v_p_5716_);
return v___x_5723_;
}
else
{
lean_dec_ref_known(v___x_5718_, 1);
lean_dec(v_stx_5717_);
return v_p_5716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5724_){
_start:
{
lean_object* v___x_5725_; 
v___x_5725_ = l_Lean_inaccessible_x3f(v_e_5724_);
if (lean_obj_tag(v___x_5725_) == 1)
{
return v___x_5725_;
}
else
{
lean_object* v___x_5726_; 
lean_dec(v___x_5725_);
v___x_5726_ = l_Lean_patternWithRef_x3f(v_e_5724_);
if (lean_obj_tag(v___x_5726_) == 1)
{
lean_object* v_val_5727_; lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5735_; 
v_val_5727_ = lean_ctor_get(v___x_5726_, 0);
v_isSharedCheck_5735_ = !lean_is_exclusive(v___x_5726_);
if (v_isSharedCheck_5735_ == 0)
{
v___x_5729_ = v___x_5726_;
v_isShared_5730_ = v_isSharedCheck_5735_;
goto v_resetjp_5728_;
}
else
{
lean_inc(v_val_5727_);
lean_dec(v___x_5726_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5735_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v_snd_5731_; lean_object* v___x_5733_; 
v_snd_5731_ = lean_ctor_get(v_val_5727_, 1);
lean_inc(v_snd_5731_);
lean_dec(v_val_5727_);
if (v_isShared_5730_ == 0)
{
lean_ctor_set(v___x_5729_, 0, v_snd_5731_);
v___x_5733_ = v___x_5729_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v_snd_5731_);
v___x_5733_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
return v___x_5733_;
}
}
}
else
{
lean_object* v___x_5736_; 
lean_dec(v___x_5726_);
v___x_5736_ = lean_box(0);
return v___x_5736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l_Lean_patternAnnotation_x3f(v_e_5737_);
lean_dec_ref(v_e_5737_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5742_){
_start:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; 
v___x_5743_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5744_ = l_Lean_mkAnnotation(v___x_5743_, v_e_5742_);
return v___x_5744_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5748_){
_start:
{
lean_object* v___x_5749_; lean_object* v___x_5750_; 
v___x_5749_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5750_ = l_Lean_annotation_x3f(v___x_5749_, v_e_5748_);
if (lean_obj_tag(v___x_5750_) == 0)
{
return v___x_5750_;
}
else
{
lean_object* v_val_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5764_; 
v_val_5751_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5753_ = v___x_5750_;
v_isShared_5754_ = v_isSharedCheck_5764_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_val_5751_);
lean_dec(v___x_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5764_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; uint8_t v___x_5757_; 
v___x_5755_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5756_ = lean_unsigned_to_nat(3u);
v___x_5757_ = l_Lean_Expr_isAppOfArity(v_val_5751_, v___x_5755_, v___x_5756_);
if (v___x_5757_ == 0)
{
lean_object* v___x_5758_; 
lean_del_object(v___x_5753_);
lean_dec(v_val_5751_);
v___x_5758_ = lean_box(0);
return v___x_5758_;
}
else
{
lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5762_; 
v___x_5759_ = l_Lean_Expr_appFn_x21(v_val_5751_);
lean_dec(v_val_5751_);
v___x_5760_ = l_Lean_Expr_appArg_x21(v___x_5759_);
lean_dec_ref(v___x_5759_);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 0, v___x_5760_);
v___x_5762_ = v___x_5753_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v___x_5760_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5765_){
_start:
{
lean_object* v_res_5766_; 
v_res_5766_ = l_Lean_isLHSGoal_x3f(v_e_5765_);
lean_dec_ref(v_e_5765_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5767_, lean_object* v_____do__lift_5768_){
_start:
{
lean_object* v___x_5769_; 
v___x_5769_ = lean_apply_2(v_toPure_5767_, lean_box(0), v_____do__lift_5768_);
return v___x_5769_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5770_, lean_object* v_inst_5771_){
_start:
{
lean_object* v_toApplicative_5772_; lean_object* v_toBind_5773_; lean_object* v_toPure_5774_; lean_object* v___x_5775_; lean_object* v___f_5776_; lean_object* v___x_5777_; 
v_toApplicative_5772_ = lean_ctor_get(v_inst_5770_, 0);
v_toBind_5773_ = lean_ctor_get(v_inst_5770_, 1);
lean_inc(v_toBind_5773_);
v_toPure_5774_ = lean_ctor_get(v_toApplicative_5772_, 1);
lean_inc(v_toPure_5774_);
v___x_5775_ = l_Lean_mkFreshId___redArg(v_inst_5770_, v_inst_5771_);
v___f_5776_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5776_, 0, v_toPure_5774_);
v___x_5777_ = lean_apply_4(v_toBind_5773_, lean_box(0), lean_box(0), v___x_5775_, v___f_5776_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5778_, lean_object* v_inst_5779_, lean_object* v_inst_5780_){
_start:
{
lean_object* v___x_5781_; 
v___x_5781_ = l_Lean_mkFreshFVarId___redArg(v_inst_5779_, v_inst_5780_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5782_, lean_object* v_inst_5783_){
_start:
{
lean_object* v_toApplicative_5784_; lean_object* v_toBind_5785_; lean_object* v_toPure_5786_; lean_object* v___x_5787_; lean_object* v___f_5788_; lean_object* v___x_5789_; 
v_toApplicative_5784_ = lean_ctor_get(v_inst_5782_, 0);
v_toBind_5785_ = lean_ctor_get(v_inst_5782_, 1);
lean_inc(v_toBind_5785_);
v_toPure_5786_ = lean_ctor_get(v_toApplicative_5784_, 1);
lean_inc(v_toPure_5786_);
v___x_5787_ = l_Lean_mkFreshId___redArg(v_inst_5782_, v_inst_5783_);
v___f_5788_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5788_, 0, v_toPure_5786_);
v___x_5789_ = lean_apply_4(v_toBind_5785_, lean_box(0), lean_box(0), v___x_5787_, v___f_5788_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5790_, lean_object* v_inst_5791_, lean_object* v_inst_5792_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Lean_mkFreshMVarId___redArg(v_inst_5791_, v_inst_5792_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5794_, lean_object* v_inst_5795_){
_start:
{
lean_object* v_toApplicative_5796_; lean_object* v_toBind_5797_; lean_object* v_toPure_5798_; lean_object* v___x_5799_; lean_object* v___f_5800_; lean_object* v___x_5801_; 
v_toApplicative_5796_ = lean_ctor_get(v_inst_5794_, 0);
v_toBind_5797_ = lean_ctor_get(v_inst_5794_, 1);
lean_inc(v_toBind_5797_);
v_toPure_5798_ = lean_ctor_get(v_toApplicative_5796_, 1);
lean_inc(v_toPure_5798_);
v___x_5799_ = l_Lean_mkFreshId___redArg(v_inst_5794_, v_inst_5795_);
v___f_5800_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5800_, 0, v_toPure_5798_);
v___x_5801_ = lean_apply_4(v_toBind_5797_, lean_box(0), lean_box(0), v___x_5799_, v___f_5800_);
return v___x_5801_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5802_, lean_object* v_inst_5803_, lean_object* v_inst_5804_){
_start:
{
lean_object* v___x_5805_; 
v___x_5805_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5803_, v_inst_5804_);
return v___x_5805_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5809_ = lean_box(0);
v___x_5810_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5811_ = l_Lean_Expr_const___override(v___x_5810_, v___x_5809_);
return v___x_5811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5812_){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5814_ = l_Lean_Expr_app___override(v___x_5813_, v_p_5812_);
return v___x_5814_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5818_ = lean_box(0);
v___x_5819_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5820_ = l_Lean_Expr_const___override(v___x_5819_, v___x_5818_);
return v___x_5820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5821_, lean_object* v_q_5822_){
_start:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5823_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5824_ = l_Lean_mkAppB(v___x_5823_, v_p_5821_, v_q_5822_);
return v___x_5824_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5828_ = lean_box(0);
v___x_5829_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5830_ = l_Lean_Expr_const___override(v___x_5829_, v___x_5828_);
return v___x_5830_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5831_, lean_object* v_q_5832_){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5834_ = l_Lean_mkAppB(v___x_5833_, v_p_5831_, v_q_5832_);
return v___x_5834_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5835_ = lean_box(0);
v___x_5836_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5837_ = l_Lean_Expr_const___override(v___x_5836_, v___x_5835_);
return v___x_5837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5838_){
_start:
{
if (lean_obj_tag(v_x_5838_) == 0)
{
lean_object* v___x_5839_; 
v___x_5839_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5839_;
}
else
{
lean_object* v_tail_5840_; 
v_tail_5840_ = lean_ctor_get(v_x_5838_, 1);
if (lean_obj_tag(v_tail_5840_) == 0)
{
lean_object* v_head_5841_; 
v_head_5841_ = lean_ctor_get(v_x_5838_, 0);
lean_inc(v_head_5841_);
lean_dec_ref_known(v_x_5838_, 2);
return v_head_5841_;
}
else
{
lean_object* v_head_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; 
lean_inc(v_tail_5840_);
v_head_5842_ = lean_ctor_get(v_x_5838_, 0);
lean_inc(v_head_5842_);
lean_dec_ref_known(v_x_5838_, 2);
v___x_5843_ = l_Lean_mkAndN(v_tail_5840_);
v___x_5844_ = l_Lean_mkAnd(v_head_5842_, v___x_5843_);
return v___x_5844_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5850_ = lean_box(0);
v___x_5851_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5852_ = l_Lean_Expr_const___override(v___x_5851_, v___x_5850_);
return v___x_5852_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5853_){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; 
v___x_5854_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5855_ = l_Lean_Expr_app___override(v___x_5854_, v_p_5853_);
return v___x_5855_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5859_ = lean_box(0);
v___x_5860_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5861_ = l_Lean_Expr_const___override(v___x_5860_, v___x_5859_);
return v___x_5861_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5862_, lean_object* v_q_5863_){
_start:
{
lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5864_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5865_ = l_Lean_mkAppB(v___x_5864_, v_p_5862_, v_q_5863_);
return v___x_5865_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5866_; 
v___x_5866_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5866_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5870_ = lean_box(0);
v___x_5871_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5872_ = l_Lean_Expr_const___override(v___x_5871_, v___x_5870_);
return v___x_5872_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5873_; 
v___x_5873_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5873_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v___x_5877_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5878_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5879_ = l_Lean_Expr_const___override(v___x_5878_, v___x_5877_);
return v___x_5879_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; 
v___x_5880_ = l_Lean_Nat_mkInstAdd;
v___x_5881_ = l_Lean_Nat_mkType;
v___x_5882_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5883_ = l_Lean_mkAppB(v___x_5882_, v___x_5881_, v___x_5880_);
return v___x_5883_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5884_; 
v___x_5884_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5884_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5888_ = lean_box(0);
v___x_5889_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5890_ = l_Lean_Expr_const___override(v___x_5889_, v___x_5888_);
return v___x_5890_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5891_; 
v___x_5891_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5891_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5895_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5896_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5897_ = l_Lean_Expr_const___override(v___x_5896_, v___x_5895_);
return v___x_5897_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; 
v___x_5898_ = l_Lean_Nat_mkInstSub;
v___x_5899_ = l_Lean_Nat_mkType;
v___x_5900_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5901_ = l_Lean_mkAppB(v___x_5900_, v___x_5899_, v___x_5898_);
return v___x_5901_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5902_; 
v___x_5902_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5902_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5906_ = lean_box(0);
v___x_5907_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5908_ = l_Lean_Expr_const___override(v___x_5907_, v___x_5906_);
return v___x_5908_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5909_; 
v___x_5909_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5909_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; 
v___x_5913_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5914_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5915_ = l_Lean_Expr_const___override(v___x_5914_, v___x_5913_);
return v___x_5915_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5916_ = l_Lean_Nat_mkInstMul;
v___x_5917_ = l_Lean_Nat_mkType;
v___x_5918_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5919_ = l_Lean_mkAppB(v___x_5918_, v___x_5917_, v___x_5916_);
return v___x_5919_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5920_; 
v___x_5920_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5920_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5925_ = lean_box(0);
v___x_5926_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5927_ = l_Lean_Expr_const___override(v___x_5926_, v___x_5925_);
return v___x_5927_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5928_; 
v___x_5928_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5928_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5932_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5933_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5934_ = l_Lean_Expr_const___override(v___x_5933_, v___x_5932_);
return v___x_5934_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; 
v___x_5935_ = l_Lean_Nat_mkInstDiv;
v___x_5936_ = l_Lean_Nat_mkType;
v___x_5937_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5938_ = l_Lean_mkAppB(v___x_5937_, v___x_5936_, v___x_5935_);
return v___x_5938_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5939_; 
v___x_5939_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5939_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___x_5944_ = lean_box(0);
v___x_5945_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5946_ = l_Lean_Expr_const___override(v___x_5945_, v___x_5944_);
return v___x_5946_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5947_; 
v___x_5947_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5947_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5951_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5952_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5953_ = l_Lean_Expr_const___override(v___x_5952_, v___x_5951_);
return v___x_5953_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5954_ = l_Lean_Nat_mkInstMod;
v___x_5955_ = l_Lean_Nat_mkType;
v___x_5956_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5957_ = l_Lean_mkAppB(v___x_5956_, v___x_5955_, v___x_5954_);
return v___x_5957_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5958_; 
v___x_5958_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5958_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5962_ = lean_box(0);
v___x_5963_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5964_ = l_Lean_Expr_const___override(v___x_5963_, v___x_5962_);
return v___x_5964_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5965_; 
v___x_5965_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5965_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5969_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5970_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5971_ = l_Lean_Expr_const___override(v___x_5970_, v___x_5969_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5972_ = l_Lean_Nat_mkInstNatPow;
v___x_5973_ = l_Lean_Nat_mkType;
v___x_5974_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5975_ = l_Lean_mkAppB(v___x_5974_, v___x_5973_, v___x_5972_);
return v___x_5975_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5976_; 
v___x_5976_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5976_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5983_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5984_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5985_ = l_Lean_Expr_const___override(v___x_5984_, v___x_5983_);
return v___x_5985_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5986_ = l_Lean_Nat_mkInstPow;
v___x_5987_ = l_Lean_Nat_mkType;
v___x_5988_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_5989_ = l_Lean_mkApp3(v___x_5988_, v___x_5987_, v___x_5987_, v___x_5986_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_5990_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5994_ = lean_box(0);
v___x_5995_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_5996_ = l_Lean_Expr_const___override(v___x_5995_, v___x_5994_);
return v___x_5996_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_5997_; 
v___x_5997_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_5997_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6001_ = lean_box(0);
v___x_6002_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6003_ = l_Lean_Expr_const___override(v___x_6002_, v___x_6001_);
return v___x_6003_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6004_; 
v___x_6004_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6004_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; 
v___x_6010_ = lean_unsigned_to_nat(0u);
v___x_6011_ = l_Lean_Level_ofNat(v___x_6010_);
return v___x_6011_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; 
v___x_6012_ = lean_box(0);
v___x_6013_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set(v___x_6014_, 1, v___x_6012_);
return v___x_6014_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6015_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6016_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_6015_);
return v___x_6017_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6018_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6019_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_6018_);
return v___x_6020_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6021_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6022_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6023_ = l_Lean_Expr_const___override(v___x_6022_, v___x_6021_);
return v___x_6023_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6024_ = l_Lean_Nat_mkInstHAdd;
v___x_6025_ = l_Lean_Nat_mkType;
v___x_6026_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6027_ = l_Lean_mkApp4(v___x_6026_, v___x_6025_, v___x_6025_, v___x_6025_, v___x_6024_);
return v___x_6027_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6028_; 
v___x_6028_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6028_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6034_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6035_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6036_ = l_Lean_Expr_const___override(v___x_6035_, v___x_6034_);
return v___x_6036_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6037_ = l_Lean_Nat_mkInstHSub;
v___x_6038_ = l_Lean_Nat_mkType;
v___x_6039_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6040_ = l_Lean_mkApp4(v___x_6039_, v___x_6038_, v___x_6038_, v___x_6038_, v___x_6037_);
return v___x_6040_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6041_; 
v___x_6041_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6041_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6047_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6048_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6049_ = l_Lean_Expr_const___override(v___x_6048_, v___x_6047_);
return v___x_6049_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6050_ = l_Lean_Nat_mkInstHMul;
v___x_6051_ = l_Lean_Nat_mkType;
v___x_6052_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6053_ = l_Lean_mkApp4(v___x_6052_, v___x_6051_, v___x_6051_, v___x_6051_, v___x_6050_);
return v___x_6053_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6054_; 
v___x_6054_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6054_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6060_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6061_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6062_ = l_Lean_Expr_const___override(v___x_6061_, v___x_6060_);
return v___x_6062_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; 
v___x_6063_ = l_Lean_Nat_mkInstHPow;
v___x_6064_ = l_Lean_Nat_mkType;
v___x_6065_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6066_ = l_Lean_mkApp4(v___x_6065_, v___x_6064_, v___x_6064_, v___x_6064_, v___x_6063_);
return v___x_6066_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6067_; 
v___x_6067_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6067_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6072_ = lean_box(0);
v___x_6073_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6074_ = l_Lean_Expr_const___override(v___x_6073_, v___x_6072_);
return v___x_6074_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6075_){
_start:
{
lean_object* v___x_6076_; lean_object* v___x_6077_; 
v___x_6076_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6077_ = l_Lean_Expr_app___override(v___x_6076_, v_a_6075_);
return v___x_6077_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6078_, lean_object* v_b_6079_){
_start:
{
lean_object* v___x_6080_; lean_object* v___x_6081_; 
v___x_6080_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6081_ = l_Lean_mkAppB(v___x_6080_, v_a_6078_, v_b_6079_);
return v___x_6081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6082_, lean_object* v_b_6083_){
_start:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6084_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6085_ = l_Lean_mkAppB(v___x_6084_, v_a_6082_, v_b_6083_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6086_, lean_object* v_b_6087_){
_start:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; 
v___x_6088_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6089_ = l_Lean_mkAppB(v___x_6088_, v_a_6086_, v_b_6087_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6090_, lean_object* v_b_6091_){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6093_ = l_Lean_mkAppB(v___x_6092_, v_a_6090_, v_b_6091_);
return v___x_6093_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; 
v___x_6099_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6100_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6101_ = l_Lean_Expr_const___override(v___x_6100_, v___x_6099_);
return v___x_6101_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6102_ = l_Lean_Nat_mkInstLE;
v___x_6103_ = l_Lean_Nat_mkType;
v___x_6104_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6105_ = l_Lean_mkAppB(v___x_6104_, v___x_6103_, v___x_6102_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6106_; 
v___x_6106_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6107_, lean_object* v_b_6108_){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6109_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6110_ = l_Lean_mkAppB(v___x_6109_, v_a_6107_, v_b_6108_);
return v___x_6110_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; 
v___x_6111_ = lean_unsigned_to_nat(1u);
v___x_6112_ = l_Lean_Level_ofNat(v___x_6111_);
return v___x_6112_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6113_ = lean_box(0);
v___x_6114_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_6113_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6116_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6117_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6118_ = l_Lean_Expr_const___override(v___x_6117_, v___x_6116_);
return v___x_6118_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v___x_6119_ = l_Lean_Nat_mkType;
v___x_6120_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6121_ = l_Lean_Expr_app___override(v___x_6120_, v___x_6119_);
return v___x_6121_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6122_; 
v___x_6122_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6122_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6123_, lean_object* v_b_6124_){
_start:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6125_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6126_ = l_Lean_mkAppB(v___x_6125_, v_a_6123_, v_b_6124_);
return v___x_6126_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6127_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6128_ = l_Lean_Expr_sort___override(v___x_6127_);
return v___x_6128_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; 
v___x_6129_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6130_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6131_ = l_Lean_Expr_app___override(v___x_6130_, v___x_6129_);
return v___x_6131_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6132_; 
v___x_6132_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6132_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6133_, lean_object* v_b_6134_){
_start:
{
lean_object* v___x_6135_; lean_object* v___x_6136_; 
v___x_6135_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6136_ = l_Lean_mkAppB(v___x_6135_, v_a_6133_, v_b_6134_);
return v___x_6136_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; 
v___x_6140_ = lean_box(0);
v___x_6141_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6142_ = l_Lean_Expr_const___override(v___x_6141_, v___x_6140_);
return v___x_6142_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6143_; 
v___x_6143_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6143_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6148_ = lean_box(0);
v___x_6149_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6150_ = l_Lean_Expr_const___override(v___x_6149_, v___x_6148_);
return v___x_6150_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6151_; 
v___x_6151_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6151_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; 
v___x_6156_ = lean_box(0);
v___x_6157_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6158_ = l_Lean_Expr_const___override(v___x_6157_, v___x_6156_);
return v___x_6158_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6159_; 
v___x_6159_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6159_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6160_ = l_Lean_Int_mkInstAdd;
v___x_6161_ = l_Lean_Int_mkType;
v___x_6162_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6163_ = l_Lean_mkAppB(v___x_6162_, v___x_6161_, v___x_6160_);
return v___x_6163_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6164_; 
v___x_6164_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6164_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6169_ = lean_box(0);
v___x_6170_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6171_ = l_Lean_Expr_const___override(v___x_6170_, v___x_6169_);
return v___x_6171_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6172_; 
v___x_6172_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6172_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
v___x_6173_ = l_Lean_Int_mkInstSub;
v___x_6174_ = l_Lean_Int_mkType;
v___x_6175_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6176_ = l_Lean_mkAppB(v___x_6175_, v___x_6174_, v___x_6173_);
return v___x_6176_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6177_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; 
v___x_6182_ = lean_box(0);
v___x_6183_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6184_ = l_Lean_Expr_const___override(v___x_6183_, v___x_6182_);
return v___x_6184_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6185_; 
v___x_6185_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6185_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6186_ = l_Lean_Int_mkInstMul;
v___x_6187_ = l_Lean_Int_mkType;
v___x_6188_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6189_ = l_Lean_mkAppB(v___x_6188_, v___x_6187_, v___x_6186_);
return v___x_6189_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6190_; 
v___x_6190_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6190_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = lean_box(0);
v___x_6195_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6196_ = l_Lean_Expr_const___override(v___x_6195_, v___x_6194_);
return v___x_6196_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6197_; 
v___x_6197_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6197_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; 
v___x_6198_ = l_Lean_Int_mkInstDiv;
v___x_6199_ = l_Lean_Int_mkType;
v___x_6200_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6201_ = l_Lean_mkAppB(v___x_6200_, v___x_6199_, v___x_6198_);
return v___x_6201_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6202_; 
v___x_6202_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6202_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6206_ = lean_box(0);
v___x_6207_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6208_ = l_Lean_Expr_const___override(v___x_6207_, v___x_6206_);
return v___x_6208_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6209_; 
v___x_6209_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6209_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6210_ = l_Lean_Int_mkInstMod;
v___x_6211_ = l_Lean_Int_mkType;
v___x_6212_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6213_ = l_Lean_mkAppB(v___x_6212_, v___x_6211_, v___x_6210_);
return v___x_6213_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6214_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; 
v___x_6219_ = lean_box(0);
v___x_6220_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6221_ = l_Lean_Expr_const___override(v___x_6220_, v___x_6219_);
return v___x_6221_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6222_; 
v___x_6222_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6222_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; 
v___x_6223_ = l_Lean_Int_mkInstPow;
v___x_6224_ = l_Lean_Int_mkType;
v___x_6225_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6226_ = l_Lean_mkAppB(v___x_6225_, v___x_6224_, v___x_6223_);
return v___x_6226_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6227_; 
v___x_6227_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6227_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; 
v___x_6228_ = l_Lean_Int_mkInstPowNat;
v___x_6229_ = l_Lean_Nat_mkType;
v___x_6230_ = l_Lean_Int_mkType;
v___x_6231_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6232_ = l_Lean_mkApp3(v___x_6231_, v___x_6230_, v___x_6229_, v___x_6228_);
return v___x_6232_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6233_; 
v___x_6233_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6233_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; 
v___x_6238_ = lean_box(0);
v___x_6239_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6240_ = l_Lean_Expr_const___override(v___x_6239_, v___x_6238_);
return v___x_6240_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6241_; 
v___x_6241_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6241_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; 
v___x_6246_ = lean_box(0);
v___x_6247_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6248_ = l_Lean_Expr_const___override(v___x_6247_, v___x_6246_);
return v___x_6248_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6249_; 
v___x_6249_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6249_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6253_ = lean_box(0);
v___x_6254_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6255_ = l_Lean_Expr_const___override(v___x_6254_, v___x_6253_);
return v___x_6255_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6256_; 
v___x_6256_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6256_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; 
v___x_6257_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6258_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6259_ = l_Lean_Expr_const___override(v___x_6258_, v___x_6257_);
return v___x_6259_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; 
v___x_6260_ = l_Lean_Int_mkInstNeg;
v___x_6261_ = l_Lean_Int_mkType;
v___x_6262_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6263_ = l_Lean_mkAppB(v___x_6262_, v___x_6261_, v___x_6260_);
return v___x_6263_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6264_; 
v___x_6264_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6264_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; 
v___x_6265_ = l_Lean_Int_mkInstHAdd;
v___x_6266_ = l_Lean_Int_mkType;
v___x_6267_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6268_ = l_Lean_mkApp4(v___x_6267_, v___x_6266_, v___x_6266_, v___x_6266_, v___x_6265_);
return v___x_6268_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6269_; 
v___x_6269_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6269_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6270_ = l_Lean_Int_mkInstHSub;
v___x_6271_ = l_Lean_Int_mkType;
v___x_6272_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6273_ = l_Lean_mkApp4(v___x_6272_, v___x_6271_, v___x_6271_, v___x_6271_, v___x_6270_);
return v___x_6273_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6274_; 
v___x_6274_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6274_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6275_ = l_Lean_Int_mkInstHMul;
v___x_6276_ = l_Lean_Int_mkType;
v___x_6277_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6278_ = l_Lean_mkApp4(v___x_6277_, v___x_6276_, v___x_6276_, v___x_6276_, v___x_6275_);
return v___x_6278_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6279_; 
v___x_6279_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6279_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6285_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6286_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6287_ = l_Lean_Expr_const___override(v___x_6286_, v___x_6285_);
return v___x_6287_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; 
v___x_6288_ = l_Lean_Int_mkInstHDiv;
v___x_6289_ = l_Lean_Int_mkType;
v___x_6290_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6291_ = l_Lean_mkApp4(v___x_6290_, v___x_6289_, v___x_6289_, v___x_6289_, v___x_6288_);
return v___x_6291_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6292_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; 
v___x_6298_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6299_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6300_ = l_Lean_Expr_const___override(v___x_6299_, v___x_6298_);
return v___x_6300_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; 
v___x_6301_ = l_Lean_Int_mkInstHMod;
v___x_6302_ = l_Lean_Int_mkType;
v___x_6303_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6304_ = l_Lean_mkApp4(v___x_6303_, v___x_6302_, v___x_6302_, v___x_6302_, v___x_6301_);
return v___x_6304_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6305_; 
v___x_6305_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6305_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6306_ = l_Lean_Int_mkInstHPow;
v___x_6307_ = l_Lean_Nat_mkType;
v___x_6308_ = l_Lean_Int_mkType;
v___x_6309_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6310_ = l_Lean_mkApp4(v___x_6309_, v___x_6308_, v___x_6307_, v___x_6308_, v___x_6306_);
return v___x_6310_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6311_; 
v___x_6311_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6311_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6317_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6318_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6319_ = l_Lean_Expr_const___override(v___x_6318_, v___x_6317_);
return v___x_6319_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6320_ = l_Lean_Int_mkInstNatCast;
v___x_6321_ = l_Lean_Int_mkType;
v___x_6322_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6323_ = l_Lean_mkAppB(v___x_6322_, v___x_6321_, v___x_6320_);
return v___x_6323_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6324_; 
v___x_6324_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6325_){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6326_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6327_ = l_Lean_Expr_app___override(v___x_6326_, v_a_6325_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6328_, lean_object* v_b_6329_){
_start:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6330_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6331_ = l_Lean_mkAppB(v___x_6330_, v_a_6328_, v_b_6329_);
return v___x_6331_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6332_, lean_object* v_b_6333_){
_start:
{
lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6334_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6335_ = l_Lean_mkAppB(v___x_6334_, v_a_6332_, v_b_6333_);
return v___x_6335_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6336_, lean_object* v_b_6337_){
_start:
{
lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6338_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6339_ = l_Lean_mkAppB(v___x_6338_, v_a_6336_, v_b_6337_);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6340_, lean_object* v_b_6341_){
_start:
{
lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6342_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6343_ = l_Lean_mkAppB(v___x_6342_, v_a_6340_, v_b_6341_);
return v___x_6343_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6344_, lean_object* v_b_6345_){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; 
v___x_6346_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6347_ = l_Lean_mkAppB(v___x_6346_, v_a_6344_, v_b_6345_);
return v___x_6347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6348_){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6349_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6350_ = l_Lean_Expr_app___override(v___x_6349_, v_a_6348_);
return v___x_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6351_, lean_object* v_b_6352_){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6353_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6354_ = l_Lean_mkAppB(v___x_6353_, v_a_6351_, v_b_6352_);
return v___x_6354_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6355_ = l_Lean_Int_mkInstLE;
v___x_6356_ = l_Lean_Int_mkType;
v___x_6357_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6358_ = l_Lean_mkAppB(v___x_6357_, v___x_6356_, v___x_6355_);
return v___x_6358_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6359_; 
v___x_6359_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6360_, lean_object* v_b_6361_){
_start:
{
lean_object* v___x_6362_; lean_object* v___x_6363_; 
v___x_6362_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6363_ = l_Lean_mkAppB(v___x_6362_, v_a_6360_, v_b_6361_);
return v___x_6363_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; 
v___x_6369_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6370_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6371_ = l_Lean_Expr_const___override(v___x_6370_, v___x_6369_);
return v___x_6371_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6372_ = l_Lean_Int_mkInstLT;
v___x_6373_ = l_Lean_Int_mkType;
v___x_6374_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6375_ = l_Lean_mkAppB(v___x_6374_, v___x_6373_, v___x_6372_);
return v___x_6375_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6376_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6377_, lean_object* v_b_6378_){
_start:
{
lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6379_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6380_ = l_Lean_mkAppB(v___x_6379_, v_a_6377_, v_b_6378_);
return v___x_6380_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6381_ = l_Lean_Int_mkType;
v___x_6382_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6383_ = l_Lean_Expr_app___override(v___x_6382_, v___x_6381_);
return v___x_6383_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6384_; 
v___x_6384_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6385_, lean_object* v_b_6386_){
_start:
{
lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6387_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6388_ = l_Lean_mkAppB(v___x_6387_, v_a_6385_, v_b_6386_);
return v___x_6388_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6394_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6395_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6396_ = l_Lean_Expr_const___override(v___x_6395_, v___x_6394_);
return v___x_6396_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6401_ = lean_box(0);
v___x_6402_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6403_ = l_Lean_Expr_const___override(v___x_6402_, v___x_6401_);
return v___x_6403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6404_, lean_object* v_b_6405_){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; 
v___x_6406_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6407_ = l_Lean_Int_mkType;
v___x_6408_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6409_ = l_Lean_mkApp4(v___x_6406_, v___x_6407_, v___x_6408_, v_a_6404_, v_b_6405_);
return v___x_6409_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6413_ = lean_box(0);
v___x_6414_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6415_ = l_Lean_Expr_const___override(v___x_6414_, v___x_6413_);
return v___x_6415_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6416_; lean_object* v___x_6417_; 
v___x_6416_ = lean_unsigned_to_nat(0u);
v___x_6417_ = lean_nat_to_int(v___x_6416_);
return v___x_6417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6418_){
_start:
{
lean_object* v___x_6419_; lean_object* v_r_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v_r_6425_; lean_object* v___x_6426_; uint8_t v___x_6427_; 
v___x_6419_ = lean_nat_abs(v_n_6418_);
v_r_6420_ = l_Lean_mkRawNatLit(v___x_6419_);
v___x_6421_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6422_ = l_Lean_Int_mkType;
v___x_6423_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6420_);
v___x_6424_ = l_Lean_Expr_app___override(v___x_6423_, v_r_6420_);
v_r_6425_ = l_Lean_mkApp3(v___x_6421_, v___x_6422_, v_r_6420_, v___x_6424_);
v___x_6426_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6427_ = lean_int_dec_lt(v_n_6418_, v___x_6426_);
if (v___x_6427_ == 0)
{
return v_r_6425_;
}
else
{
lean_object* v___x_6428_; 
v___x_6428_ = l_Lean_mkIntNeg(v_r_6425_);
return v___x_6428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6429_){
_start:
{
lean_object* v_res_6430_; 
v_res_6430_ = l_Lean_mkIntLit(v_n_6429_);
lean_dec(v_n_6429_);
return v_res_6430_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6435_; lean_object* v___x_6436_; 
v___x_6435_ = lean_box(0);
v___x_6436_ = l_Lean_Level_succ___override(v___x_6435_);
return v___x_6436_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; 
v___x_6437_ = lean_box(0);
v___x_6438_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6439_, 0, v___x_6438_);
lean_ctor_set(v___x_6439_, 1, v___x_6437_);
return v___x_6439_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; 
v___x_6440_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6441_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6442_ = l_Lean_Expr_const___override(v___x_6441_, v___x_6440_);
return v___x_6442_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; 
v___x_6445_ = lean_box(0);
v___x_6446_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6447_ = l_Lean_Expr_const___override(v___x_6446_, v___x_6445_);
return v___x_6447_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; 
v___x_6448_ = lean_box(0);
v___x_6449_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6450_ = l_Lean_Expr_const___override(v___x_6449_, v___x_6448_);
return v___x_6450_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6451_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6452_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6453_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6454_ = l_Lean_mkAppB(v___x_6453_, v___x_6452_, v___x_6451_);
return v___x_6454_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6455_; 
v___x_6455_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6455_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; lean_object* v___x_6458_; 
v___x_6456_ = lean_box(0);
v___x_6457_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6458_ = l_Lean_Expr_const___override(v___x_6457_, v___x_6456_);
return v___x_6458_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; 
v___x_6459_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6460_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6461_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6462_ = l_Lean_mkAppB(v___x_6461_, v___x_6460_, v___x_6459_);
return v___x_6462_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6463_; 
v___x_6463_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6463_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6467_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6468_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6469_ = l_Lean_Expr_const___override(v___x_6468_, v___x_6467_);
return v___x_6469_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; 
v___x_6470_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6471_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6472_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6473_ = l_Lean_mkApp3(v___x_6472_, v___x_6471_, v___x_6470_, v___x_6470_);
return v___x_6473_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; 
v___x_6474_ = l_Lean_reflBoolTrue;
v___x_6475_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6476_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6477_ = l_Lean_mkAppB(v___x_6476_, v___x_6475_, v___x_6474_);
return v___x_6477_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6478_; 
v___x_6478_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6478_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6479_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6480_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6481_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6482_ = l_Lean_mkApp3(v___x_6481_, v___x_6480_, v___x_6479_, v___x_6479_);
return v___x_6482_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v___x_6483_ = l_Lean_reflBoolFalse;
v___x_6484_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6485_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6486_ = l_Lean_mkAppB(v___x_6485_, v___x_6484_, v___x_6483_);
return v___x_6486_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6487_; 
v___x_6487_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6487_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
v___x_6490_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6491_ = lean_unsigned_to_nat(9u);
v___x_6492_ = lean_unsigned_to_nat(2441u);
v___x_6493_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6494_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6495_ = l_mkPanicMessageWithDecl(v___x_6494_, v___x_6493_, v___x_6492_, v___x_6491_, v___x_6490_);
return v___x_6495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6496_, lean_object* v_declName_6497_){
_start:
{
switch(lean_obj_tag(v_e_6496_))
{
case 5:
{
lean_object* v_fn_6498_; lean_object* v_arg_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; 
v_fn_6498_ = lean_ctor_get(v_e_6496_, 0);
lean_inc_ref(v_fn_6498_);
v_arg_6499_ = lean_ctor_get(v_e_6496_, 1);
lean_inc_ref(v_arg_6499_);
lean_dec_ref_known(v_e_6496_, 2);
v___x_6500_ = l_Lean_Expr_replaceFn(v_fn_6498_, v_declName_6497_);
v___x_6501_ = l_Lean_Expr_app___override(v___x_6500_, v_arg_6499_);
return v___x_6501_;
}
case 4:
{
lean_object* v_us_6502_; lean_object* v___x_6503_; 
v_us_6502_ = lean_ctor_get(v_e_6496_, 1);
lean_inc(v_us_6502_);
lean_dec_ref_known(v_e_6496_, 2);
v___x_6503_ = l_Lean_Expr_const___override(v_declName_6497_, v_us_6502_);
return v___x_6503_;
}
default: 
{
lean_object* v___x_6504_; lean_object* v___x_6505_; 
lean_dec(v_declName_6497_);
lean_dec_ref(v_e_6496_);
v___x_6504_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6505_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6504_);
return v___x_6505_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Level(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instLTLiteral = _init_l_Lean_instLTLiteral();
lean_mark_persistent(l_Lean_instLTLiteral);
l_Lean_instInhabitedBinderInfo_default = _init_l_Lean_instInhabitedBinderInfo_default();
l_Lean_instInhabitedBinderInfo = _init_l_Lean_instInhabitedBinderInfo();
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean_mark_persistent(l_Lean_MData_empty);
l_Lean_instInhabitedData__1___aux__1 = _init_l_Lean_instInhabitedData__1___aux__1();
l_Lean_instInhabitedData__1 = _init_l_Lean_instInhabitedData__1();
l_Lean_instInhabitedFVarId_default = _init_l_Lean_instInhabitedFVarId_default();
lean_mark_persistent(l_Lean_instInhabitedFVarId_default);
l_Lean_instInhabitedFVarId = _init_l_Lean_instInhabitedFVarId();
lean_mark_persistent(l_Lean_instInhabitedFVarId);
l_Lean_instInhabitedFVarIdSet___aux__1 = _init_l_Lean_instInhabitedFVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedFVarIdSet___aux__1);
l_Lean_instInhabitedFVarIdSet = _init_l_Lean_instInhabitedFVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedFVarIdSet);
l_Lean_instEmptyCollectionFVarIdSet___aux__1 = _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdSet___aux__1);
l_Lean_instEmptyCollectionFVarIdSet = _init_l_Lean_instEmptyCollectionFVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdSet);
l_Lean_instInhabitedFVarIdHashSet___aux__1 = _init_l_Lean_instInhabitedFVarIdHashSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedFVarIdHashSet___aux__1);
l_Lean_instInhabitedFVarIdHashSet = _init_l_Lean_instInhabitedFVarIdHashSet();
lean_mark_persistent(l_Lean_instInhabitedFVarIdHashSet);
l_Lean_instEmptyCollectionFVarIdHashSet___aux__1 = _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdHashSet___aux__1);
l_Lean_instEmptyCollectionFVarIdHashSet = _init_l_Lean_instEmptyCollectionFVarIdHashSet();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdHashSet);
l_Lean_instInhabitedMVarId_default = _init_l_Lean_instInhabitedMVarId_default();
lean_mark_persistent(l_Lean_instInhabitedMVarId_default);
l_Lean_instInhabitedMVarId = _init_l_Lean_instInhabitedMVarId();
lean_mark_persistent(l_Lean_instInhabitedMVarId);
l_Lean_instInhabitedMVarIdSet___aux__1 = _init_l_Lean_instInhabitedMVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedMVarIdSet___aux__1);
l_Lean_instInhabitedMVarIdSet = _init_l_Lean_instInhabitedMVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedMVarIdSet);
l_Lean_instEmptyCollectionMVarIdSet___aux__1 = _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionMVarIdSet___aux__1);
l_Lean_instEmptyCollectionMVarIdSet = _init_l_Lean_instEmptyCollectionMVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionMVarIdSet);
l_Lean_instInhabitedExpr = _init_l_Lean_instInhabitedExpr();
lean_mark_persistent(l_Lean_instInhabitedExpr);
l_Lean_instInhabitedExprStructEq_default = _init_l_Lean_instInhabitedExprStructEq_default();
lean_mark_persistent(l_Lean_instInhabitedExprStructEq_default);
l_Lean_instInhabitedExprStructEq = _init_l_Lean_instInhabitedExprStructEq();
lean_mark_persistent(l_Lean_instInhabitedExprStructEq);
l_Lean_Nat_mkType = _init_l_Lean_Nat_mkType();
lean_mark_persistent(l_Lean_Nat_mkType);
l_Lean_Nat_mkInstAdd = _init_l_Lean_Nat_mkInstAdd();
lean_mark_persistent(l_Lean_Nat_mkInstAdd);
l_Lean_Nat_mkInstHAdd = _init_l_Lean_Nat_mkInstHAdd();
lean_mark_persistent(l_Lean_Nat_mkInstHAdd);
l_Lean_Nat_mkInstSub = _init_l_Lean_Nat_mkInstSub();
lean_mark_persistent(l_Lean_Nat_mkInstSub);
l_Lean_Nat_mkInstHSub = _init_l_Lean_Nat_mkInstHSub();
lean_mark_persistent(l_Lean_Nat_mkInstHSub);
l_Lean_Nat_mkInstMul = _init_l_Lean_Nat_mkInstMul();
lean_mark_persistent(l_Lean_Nat_mkInstMul);
l_Lean_Nat_mkInstHMul = _init_l_Lean_Nat_mkInstHMul();
lean_mark_persistent(l_Lean_Nat_mkInstHMul);
l_Lean_Nat_mkInstDiv = _init_l_Lean_Nat_mkInstDiv();
lean_mark_persistent(l_Lean_Nat_mkInstDiv);
l_Lean_Nat_mkInstHDiv = _init_l_Lean_Nat_mkInstHDiv();
lean_mark_persistent(l_Lean_Nat_mkInstHDiv);
l_Lean_Nat_mkInstMod = _init_l_Lean_Nat_mkInstMod();
lean_mark_persistent(l_Lean_Nat_mkInstMod);
l_Lean_Nat_mkInstHMod = _init_l_Lean_Nat_mkInstHMod();
lean_mark_persistent(l_Lean_Nat_mkInstHMod);
l_Lean_Nat_mkInstNatPow = _init_l_Lean_Nat_mkInstNatPow();
lean_mark_persistent(l_Lean_Nat_mkInstNatPow);
l_Lean_Nat_mkInstPow = _init_l_Lean_Nat_mkInstPow();
lean_mark_persistent(l_Lean_Nat_mkInstPow);
l_Lean_Nat_mkInstHPow = _init_l_Lean_Nat_mkInstHPow();
lean_mark_persistent(l_Lean_Nat_mkInstHPow);
l_Lean_Nat_mkInstLT = _init_l_Lean_Nat_mkInstLT();
lean_mark_persistent(l_Lean_Nat_mkInstLT);
l_Lean_Nat_mkInstLE = _init_l_Lean_Nat_mkInstLE();
lean_mark_persistent(l_Lean_Nat_mkInstLE);
l___private_Lean_Expr_0__Lean_natAddFn = _init_l___private_Lean_Expr_0__Lean_natAddFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natAddFn);
l___private_Lean_Expr_0__Lean_natSubFn = _init_l___private_Lean_Expr_0__Lean_natSubFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natSubFn);
l___private_Lean_Expr_0__Lean_natMulFn = _init_l___private_Lean_Expr_0__Lean_natMulFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natMulFn);
l___private_Lean_Expr_0__Lean_natPowFn = _init_l___private_Lean_Expr_0__Lean_natPowFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natPowFn);
l___private_Lean_Expr_0__Lean_natLEPred = _init_l___private_Lean_Expr_0__Lean_natLEPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natLEPred);
l___private_Lean_Expr_0__Lean_natEqPred = _init_l___private_Lean_Expr_0__Lean_natEqPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natEqPred);
l___private_Lean_Expr_0__Lean_propEq = _init_l___private_Lean_Expr_0__Lean_propEq();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_propEq);
l_Lean_Int_mkType = _init_l_Lean_Int_mkType();
lean_mark_persistent(l_Lean_Int_mkType);
l_Lean_Int_mkInstNeg = _init_l_Lean_Int_mkInstNeg();
lean_mark_persistent(l_Lean_Int_mkInstNeg);
l_Lean_Int_mkInstAdd = _init_l_Lean_Int_mkInstAdd();
lean_mark_persistent(l_Lean_Int_mkInstAdd);
l_Lean_Int_mkInstHAdd = _init_l_Lean_Int_mkInstHAdd();
lean_mark_persistent(l_Lean_Int_mkInstHAdd);
l_Lean_Int_mkInstSub = _init_l_Lean_Int_mkInstSub();
lean_mark_persistent(l_Lean_Int_mkInstSub);
l_Lean_Int_mkInstHSub = _init_l_Lean_Int_mkInstHSub();
lean_mark_persistent(l_Lean_Int_mkInstHSub);
l_Lean_Int_mkInstMul = _init_l_Lean_Int_mkInstMul();
lean_mark_persistent(l_Lean_Int_mkInstMul);
l_Lean_Int_mkInstHMul = _init_l_Lean_Int_mkInstHMul();
lean_mark_persistent(l_Lean_Int_mkInstHMul);
l_Lean_Int_mkInstDiv = _init_l_Lean_Int_mkInstDiv();
lean_mark_persistent(l_Lean_Int_mkInstDiv);
l_Lean_Int_mkInstHDiv = _init_l_Lean_Int_mkInstHDiv();
lean_mark_persistent(l_Lean_Int_mkInstHDiv);
l_Lean_Int_mkInstMod = _init_l_Lean_Int_mkInstMod();
lean_mark_persistent(l_Lean_Int_mkInstMod);
l_Lean_Int_mkInstHMod = _init_l_Lean_Int_mkInstHMod();
lean_mark_persistent(l_Lean_Int_mkInstHMod);
l_Lean_Int_mkInstPow = _init_l_Lean_Int_mkInstPow();
lean_mark_persistent(l_Lean_Int_mkInstPow);
l_Lean_Int_mkInstPowNat = _init_l_Lean_Int_mkInstPowNat();
lean_mark_persistent(l_Lean_Int_mkInstPowNat);
l_Lean_Int_mkInstHPow = _init_l_Lean_Int_mkInstHPow();
lean_mark_persistent(l_Lean_Int_mkInstHPow);
l_Lean_Int_mkInstLT = _init_l_Lean_Int_mkInstLT();
lean_mark_persistent(l_Lean_Int_mkInstLT);
l_Lean_Int_mkInstLE = _init_l_Lean_Int_mkInstLE();
lean_mark_persistent(l_Lean_Int_mkInstLE);
l_Lean_Int_mkInstNatCast = _init_l_Lean_Int_mkInstNatCast();
lean_mark_persistent(l_Lean_Int_mkInstNatCast);
l___private_Lean_Expr_0__Lean_intNegFn = _init_l___private_Lean_Expr_0__Lean_intNegFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intNegFn);
l___private_Lean_Expr_0__Lean_intAddFn = _init_l___private_Lean_Expr_0__Lean_intAddFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intAddFn);
l___private_Lean_Expr_0__Lean_intSubFn = _init_l___private_Lean_Expr_0__Lean_intSubFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intSubFn);
l___private_Lean_Expr_0__Lean_intMulFn = _init_l___private_Lean_Expr_0__Lean_intMulFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intMulFn);
l___private_Lean_Expr_0__Lean_intDivFn = _init_l___private_Lean_Expr_0__Lean_intDivFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intDivFn);
l___private_Lean_Expr_0__Lean_intModFn = _init_l___private_Lean_Expr_0__Lean_intModFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intModFn);
l___private_Lean_Expr_0__Lean_intPowNatFn = _init_l___private_Lean_Expr_0__Lean_intPowNatFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intPowNatFn);
l___private_Lean_Expr_0__Lean_intNatCastFn = _init_l___private_Lean_Expr_0__Lean_intNatCastFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intNatCastFn);
l___private_Lean_Expr_0__Lean_intLEPred = _init_l___private_Lean_Expr_0__Lean_intLEPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intLEPred);
l___private_Lean_Expr_0__Lean_intLTPred = _init_l___private_Lean_Expr_0__Lean_intLTPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intLTPred);
l___private_Lean_Expr_0__Lean_intEqPred = _init_l___private_Lean_Expr_0__Lean_intEqPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intEqPred);
l_Lean_reflBoolTrue = _init_l_Lean_reflBoolTrue();
lean_mark_persistent(l_Lean_reflBoolTrue);
l_Lean_reflBoolFalse = _init_l_Lean_reflBoolFalse();
lean_mark_persistent(l_Lean_reflBoolFalse);
l_Lean_eagerReflBoolTrue = _init_l_Lean_eagerReflBoolTrue();
lean_mark_persistent(l_Lean_eagerReflBoolTrue);
l_Lean_eagerReflBoolFalse = _init_l_Lean_eagerReflBoolFalse();
lean_mark_persistent(l_Lean_eagerReflBoolFalse);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Lean_Level(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Expr(builtin);
}
#ifdef __cplusplus
}
#endif
