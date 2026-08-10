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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object*, lean_object*);
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
v___x_676_ = lean_nat_add(v___y_673_, v___y_675_);
lean_dec(v___y_675_);
lean_dec(v___y_673_);
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
lean_ctor_set(v___x_656_, 3, v___y_674_);
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
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___y_674_);
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
v___y_673_ = v___x_689_;
v___y_674_ = v___x_688_;
v___y_675_ = v_size_690_;
goto v___jp_672_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_673_ = v___x_689_;
v___y_674_ = v___x_688_;
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
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_unsigned_to_nat(16u);
v___x_1022_ = lean_mk_array(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1030_, lean_object* v_fvarId_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1031_, v_a_1032_, v_s_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1034_, lean_object* v_s_1035_, lean_object* v_fvarId_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1036_, v_a_1037_, v_s_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(1);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(1);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_box(1);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_box(0);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_box(0);
return v___x_1046_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_name_eq(v_x_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l_Lean_instBEqMVarId_beq(v_x_1050_, v_x_1051_);
lean_dec(v_x_1051_);
lean_dec(v_x_1050_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1056_){
_start:
{
uint64_t v___x_1057_; 
v___x_1057_ = 0ULL;
if (lean_obj_tag(v_x_1056_) == 0)
{
uint64_t v___x_1058_; 
v___x_1058_ = lean_uint64_once(&l_Lean_instHashableFVarId_hash___closed__0, &l_Lean_instHashableFVarId_hash___closed__0_once, _init_l_Lean_instHashableFVarId_hash___closed__0);
return v___x_1058_;
}
else
{
uint64_t v_hash_1059_; uint64_t v___x_1060_; 
v_hash_1059_ = lean_ctor_get_uint64(v_x_1056_, sizeof(void*)*2);
v___x_1060_ = lean_uint64_mix_hash(v___x_1057_, v_hash_1059_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1061_){
_start:
{
uint64_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lean_instHashableMVarId_hash(v_x_1061_);
lean_dec(v_x_1061_);
v_r_1063_ = lean_box_uint64(v_res_1062_);
return v_r_1063_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(1);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_box(1);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_box(1);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(1);
return v___x_1070_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1071_, lean_object* v_t_1072_){
_start:
{
if (lean_obj_tag(v_t_1072_) == 0)
{
lean_object* v_k_1073_; lean_object* v_l_1074_; lean_object* v_r_1075_; uint8_t v___x_1076_; 
v_k_1073_ = lean_ctor_get(v_t_1072_, 1);
v_l_1074_ = lean_ctor_get(v_t_1072_, 3);
v_r_1075_ = lean_ctor_get(v_t_1072_, 4);
v___x_1076_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1071_, v_k_1073_);
switch(v___x_1076_)
{
case 0:
{
v_t_1072_ = v_l_1074_;
goto _start;
}
case 1:
{
uint8_t v___x_1078_; 
v___x_1078_ = 1;
return v___x_1078_;
}
default: 
{
v_t_1072_ = v_r_1075_;
goto _start;
}
}
}
else
{
uint8_t v___x_1080_; 
v___x_1080_ = 0;
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1081_, lean_object* v_t_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1081_, v_t_1082_);
lean_dec(v_t_1082_);
lean_dec(v_k_1081_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1085_, lean_object* v_v_1086_, lean_object* v_t_1087_){
_start:
{
if (lean_obj_tag(v_t_1087_) == 0)
{
lean_object* v_size_1088_; lean_object* v_k_1089_; lean_object* v_v_1090_; lean_object* v_l_1091_; lean_object* v_r_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1372_; 
v_size_1088_ = lean_ctor_get(v_t_1087_, 0);
v_k_1089_ = lean_ctor_get(v_t_1087_, 1);
v_v_1090_ = lean_ctor_get(v_t_1087_, 2);
v_l_1091_ = lean_ctor_get(v_t_1087_, 3);
v_r_1092_ = lean_ctor_get(v_t_1087_, 4);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_t_1087_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1094_ = v_t_1087_;
v_isShared_1095_ = v_isSharedCheck_1372_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_r_1092_);
lean_inc(v_l_1091_);
lean_inc(v_v_1090_);
lean_inc(v_k_1089_);
lean_inc(v_size_1088_);
lean_dec(v_t_1087_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1372_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1085_, v_k_1089_);
switch(v___x_1096_)
{
case 0:
{
lean_object* v_impl_1097_; lean_object* v___x_1098_; 
lean_dec(v_size_1088_);
v_impl_1097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1085_, v_v_1086_, v_l_1091_);
v___x_1098_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1092_) == 0)
{
lean_object* v_size_1099_; lean_object* v_size_1100_; lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v_l_1103_; lean_object* v_r_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_size_1099_ = lean_ctor_get(v_r_1092_, 0);
v_size_1100_ = lean_ctor_get(v_impl_1097_, 0);
lean_inc(v_size_1100_);
v_k_1101_ = lean_ctor_get(v_impl_1097_, 1);
lean_inc(v_k_1101_);
v_v_1102_ = lean_ctor_get(v_impl_1097_, 2);
lean_inc(v_v_1102_);
v_l_1103_ = lean_ctor_get(v_impl_1097_, 3);
lean_inc(v_l_1103_);
v_r_1104_ = lean_ctor_get(v_impl_1097_, 4);
lean_inc(v_r_1104_);
v___x_1105_ = lean_unsigned_to_nat(3u);
v___x_1106_ = lean_nat_mul(v___x_1105_, v_size_1099_);
v___x_1107_ = lean_nat_dec_lt(v___x_1106_, v_size_1100_);
lean_dec(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec(v_r_1104_);
lean_dec(v_l_1103_);
lean_dec(v_v_1102_);
lean_dec(v_k_1101_);
v___x_1108_ = lean_nat_add(v___x_1098_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1109_ = lean_nat_add(v___x_1108_, v_size_1099_);
lean_dec(v___x_1108_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 3, v_impl_1097_);
lean_ctor_set(v___x_1094_, 0, v___x_1109_);
v___x_1111_ = v___x_1094_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_1092_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1178_; 
v_isSharedCheck_1178_ = !lean_is_exclusive(v_impl_1097_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1179_ = lean_ctor_get(v_impl_1097_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_impl_1097_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_impl_1097_, 2);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_impl_1097_, 1);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_impl_1097_, 0);
lean_dec(v_unused_1183_);
v___x_1114_ = v_impl_1097_;
v_isShared_1115_ = v_isSharedCheck_1178_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v_impl_1097_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1178_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_size_1116_; lean_object* v_size_1117_; lean_object* v_k_1118_; lean_object* v_v_1119_; lean_object* v_l_1120_; lean_object* v_r_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_size_1116_ = lean_ctor_get(v_l_1103_, 0);
v_size_1117_ = lean_ctor_get(v_r_1104_, 0);
v_k_1118_ = lean_ctor_get(v_r_1104_, 1);
v_v_1119_ = lean_ctor_get(v_r_1104_, 2);
v_l_1120_ = lean_ctor_get(v_r_1104_, 3);
v_r_1121_ = lean_ctor_get(v_r_1104_, 4);
v___x_1122_ = lean_unsigned_to_nat(2u);
v___x_1123_ = lean_nat_mul(v___x_1122_, v_size_1116_);
v___x_1124_ = lean_nat_dec_lt(v_size_1117_, v___x_1123_);
lean_dec(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1153_; 
lean_inc(v_r_1121_);
lean_inc(v_l_1120_);
lean_inc(v_v_1119_);
lean_inc(v_k_1118_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_r_1104_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1154_ = lean_ctor_get(v_r_1104_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_r_1104_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_r_1104_, 2);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_r_1104_, 1);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_r_1104_, 0);
lean_dec(v_unused_1158_);
v___x_1126_ = v_r_1104_;
v_isShared_1127_ = v_isSharedCheck_1153_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_r_1104_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1153_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___x_1141_; lean_object* v___y_1143_; 
v___x_1128_ = lean_nat_add(v___x_1098_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1129_ = lean_nat_add(v___x_1128_, v_size_1099_);
lean_dec(v___x_1128_);
v___x_1141_ = lean_nat_add(v___x_1098_, v_size_1116_);
if (lean_obj_tag(v_l_1120_) == 0)
{
lean_object* v_size_1151_; 
v_size_1151_ = lean_ctor_get(v_l_1120_, 0);
lean_inc(v_size_1151_);
v___y_1143_ = v_size_1151_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v___y_1143_ = v___x_1152_;
goto v___jp_1142_;
}
v___jp_1130_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_nat_add(v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec(v___y_1132_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1092_);
lean_ctor_set(v___x_1126_, 3, v_r_1121_);
lean_ctor_set(v___x_1126_, 2, v_v_1090_);
lean_ctor_set(v___x_1126_, 1, v_k_1089_);
lean_ctor_set(v___x_1126_, 0, v___x_1134_);
v___x_1136_ = v___x_1126_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_r_1092_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1136_);
lean_ctor_set(v___x_1114_, 3, v___y_1131_);
lean_ctor_set(v___x_1114_, 2, v_v_1119_);
lean_ctor_set(v___x_1114_, 1, v_k_1118_);
lean_ctor_set(v___x_1114_, 0, v___x_1129_);
v___x_1138_ = v___x_1114_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1118_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1119_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___y_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
v___jp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_nat_add(v___x_1141_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec(v___x_1141_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_l_1120_);
lean_ctor_set(v___x_1094_, 3, v_l_1103_);
lean_ctor_set(v___x_1094_, 2, v_v_1102_);
lean_ctor_set(v___x_1094_, 1, v_k_1101_);
lean_ctor_set(v___x_1094_, 0, v___x_1144_);
v___x_1146_ = v___x_1094_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_l_1120_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_nat_add(v___x_1098_, v_size_1099_);
if (lean_obj_tag(v_r_1121_) == 0)
{
lean_object* v_size_1148_; 
v_size_1148_ = lean_ctor_get(v_r_1121_, 0);
lean_inc(v_size_1148_);
v___y_1131_ = v___x_1146_;
v___y_1132_ = v___x_1147_;
v___y_1133_ = v_size_1148_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___y_1131_ = v___x_1146_;
v___y_1132_ = v___x_1147_;
v___y_1133_ = v___x_1149_;
goto v___jp_1130_;
}
}
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_del_object(v___x_1094_);
v___x_1159_ = lean_nat_add(v___x_1098_, v_size_1100_);
lean_dec(v_size_1100_);
v___x_1160_ = lean_nat_add(v___x_1159_, v_size_1099_);
lean_dec(v___x_1159_);
v___x_1161_ = lean_nat_add(v___x_1098_, v_size_1099_);
v___x_1162_ = lean_nat_add(v___x_1161_, v_size_1117_);
lean_dec(v___x_1161_);
lean_inc_ref(v_r_1092_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_r_1092_);
lean_ctor_set(v___x_1114_, 3, v_r_1104_);
lean_ctor_set(v___x_1114_, 2, v_v_1090_);
lean_ctor_set(v___x_1114_, 1, v_k_1089_);
lean_ctor_set(v___x_1114_, 0, v___x_1162_);
v___x_1164_ = v___x_1114_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_r_1104_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_r_1092_);
v___x_1164_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_isSharedCheck_1171_ = !lean_is_exclusive(v_r_1092_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1172_ = lean_ctor_get(v_r_1092_, 4);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_r_1092_, 3);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_r_1092_, 2);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_r_1092_, 1);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_r_1092_, 0);
lean_dec(v_unused_1176_);
v___x_1166_ = v_r_1092_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_dec(v_r_1092_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 4, v___x_1164_);
lean_ctor_set(v___x_1166_, 3, v_l_1103_);
lean_ctor_set(v___x_1166_, 2, v_v_1102_);
lean_ctor_set(v___x_1166_, 1, v_k_1101_);
lean_ctor_set(v___x_1166_, 0, v___x_1160_);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v___x_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1184_; 
v_l_1184_ = lean_ctor_get(v_impl_1097_, 3);
lean_inc(v_l_1184_);
if (lean_obj_tag(v_l_1184_) == 0)
{
lean_object* v_r_1185_; lean_object* v_k_1186_; lean_object* v_v_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1198_; 
v_r_1185_ = lean_ctor_get(v_impl_1097_, 4);
v_k_1186_ = lean_ctor_get(v_impl_1097_, 1);
v_v_1187_ = lean_ctor_get(v_impl_1097_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_impl_1097_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1199_ = lean_ctor_get(v_impl_1097_, 3);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_impl_1097_, 0);
lean_dec(v_unused_1200_);
v___x_1189_ = v_impl_1097_;
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_r_1185_);
lean_inc(v_v_1187_);
lean_inc(v_k_1186_);
lean_dec(v_impl_1097_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1185_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 3, v_r_1185_);
lean_ctor_set(v___x_1189_, 2, v_v_1090_);
lean_ctor_set(v___x_1189_, 1, v_k_1089_);
lean_ctor_set(v___x_1189_, 0, v___x_1098_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_r_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_r_1185_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v___x_1193_);
lean_ctor_set(v___x_1094_, 3, v_l_1184_);
lean_ctor_set(v___x_1094_, 2, v_v_1187_);
lean_ctor_set(v___x_1094_, 1, v_k_1186_);
lean_ctor_set(v___x_1094_, 0, v___x_1191_);
v___x_1195_ = v___x_1094_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_k_1186_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_v_1187_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_l_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_r_1201_; 
v_r_1201_ = lean_ctor_get(v_impl_1097_, 4);
lean_inc(v_r_1201_);
if (lean_obj_tag(v_r_1201_) == 0)
{
lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1226_; 
v_k_1202_ = lean_ctor_get(v_impl_1097_, 1);
v_v_1203_ = lean_ctor_get(v_impl_1097_, 2);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_impl_1097_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; lean_object* v_unused_1228_; lean_object* v_unused_1229_; 
v_unused_1227_ = lean_ctor_get(v_impl_1097_, 4);
lean_dec(v_unused_1227_);
v_unused_1228_ = lean_ctor_get(v_impl_1097_, 3);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_impl_1097_, 0);
lean_dec(v_unused_1229_);
v___x_1205_ = v_impl_1097_;
v_isShared_1206_ = v_isSharedCheck_1226_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_v_1203_);
lean_inc(v_k_1202_);
lean_dec(v_impl_1097_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1226_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_k_1207_; lean_object* v_v_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1222_; 
v_k_1207_ = lean_ctor_get(v_r_1201_, 1);
v_v_1208_ = lean_ctor_get(v_r_1201_, 2);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_r_1201_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; lean_object* v_unused_1224_; lean_object* v_unused_1225_; 
v_unused_1223_ = lean_ctor_get(v_r_1201_, 4);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_r_1201_, 3);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_r_1201_, 0);
lean_dec(v_unused_1225_);
v___x_1210_ = v_r_1201_;
v_isShared_1211_ = v_isSharedCheck_1222_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_v_1208_);
lean_inc(v_k_1207_);
lean_dec(v_r_1201_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1222_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_unsigned_to_nat(3u);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v_l_1184_);
lean_ctor_set(v___x_1210_, 3, v_l_1184_);
lean_ctor_set(v___x_1210_, 2, v_v_1203_);
lean_ctor_set(v___x_1210_, 1, v_k_1202_);
lean_ctor_set(v___x_1210_, 0, v___x_1098_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_l_1184_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_l_1184_);
v___x_1214_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 4, v_l_1184_);
lean_ctor_set(v___x_1205_, 2, v_v_1090_);
lean_ctor_set(v___x_1205_, 1, v_k_1089_);
lean_ctor_set(v___x_1205_, 0, v___x_1098_);
v___x_1216_ = v___x_1205_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_l_1184_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_l_1184_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v___x_1216_);
lean_ctor_set(v___x_1094_, 3, v___x_1214_);
lean_ctor_set(v___x_1094_, 2, v_v_1208_);
lean_ctor_set(v___x_1094_, 1, v_k_1207_);
lean_ctor_set(v___x_1094_, 0, v___x_1212_);
v___x_1218_ = v___x_1094_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_unsigned_to_nat(2u);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_r_1201_);
lean_ctor_set(v___x_1094_, 3, v_impl_1097_);
lean_ctor_set(v___x_1094_, 0, v___x_1230_);
v___x_1232_ = v___x_1094_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_impl_1097_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_r_1201_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1235_; 
lean_dec(v_v_1090_);
lean_dec(v_k_1089_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v_v_1086_);
lean_ctor_set(v___x_1094_, 1, v_k_1085_);
v___x_1235_ = v___x_1094_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_size_1088_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_l_1091_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_r_1092_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
default: 
{
lean_object* v_impl_1237_; lean_object* v___x_1238_; 
lean_dec(v_size_1088_);
v_impl_1237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1085_, v_v_1086_, v_r_1092_);
v___x_1238_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1091_) == 0)
{
lean_object* v_size_1239_; lean_object* v_size_1240_; lean_object* v_k_1241_; lean_object* v_v_1242_; lean_object* v_l_1243_; lean_object* v_r_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_size_1239_ = lean_ctor_get(v_l_1091_, 0);
v_size_1240_ = lean_ctor_get(v_impl_1237_, 0);
lean_inc(v_size_1240_);
v_k_1241_ = lean_ctor_get(v_impl_1237_, 1);
lean_inc(v_k_1241_);
v_v_1242_ = lean_ctor_get(v_impl_1237_, 2);
lean_inc(v_v_1242_);
v_l_1243_ = lean_ctor_get(v_impl_1237_, 3);
lean_inc(v_l_1243_);
v_r_1244_ = lean_ctor_get(v_impl_1237_, 4);
lean_inc(v_r_1244_);
v___x_1245_ = lean_unsigned_to_nat(3u);
v___x_1246_ = lean_nat_mul(v___x_1245_, v_size_1239_);
v___x_1247_ = lean_nat_dec_lt(v___x_1246_, v_size_1240_);
lean_dec(v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_dec(v_r_1244_);
lean_dec(v_l_1243_);
lean_dec(v_v_1242_);
lean_dec(v_k_1241_);
v___x_1248_ = lean_nat_add(v___x_1238_, v_size_1239_);
v___x_1249_ = lean_nat_add(v___x_1248_, v_size_1240_);
lean_dec(v_size_1240_);
lean_dec(v___x_1248_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_impl_1237_);
lean_ctor_set(v___x_1094_, 0, v___x_1249_);
v___x_1251_ = v___x_1094_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_l_1091_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_impl_1237_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
else
{
lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v_impl_1237_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; lean_object* v_unused_1318_; lean_object* v_unused_1319_; lean_object* v_unused_1320_; lean_object* v_unused_1321_; 
v_unused_1317_ = lean_ctor_get(v_impl_1237_, 4);
lean_dec(v_unused_1317_);
v_unused_1318_ = lean_ctor_get(v_impl_1237_, 3);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_impl_1237_, 2);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_impl_1237_, 1);
lean_dec(v_unused_1320_);
v_unused_1321_ = lean_ctor_get(v_impl_1237_, 0);
lean_dec(v_unused_1321_);
v___x_1254_ = v_impl_1237_;
v_isShared_1255_ = v_isSharedCheck_1316_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v_impl_1237_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1316_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_size_1256_; lean_object* v_k_1257_; lean_object* v_v_1258_; lean_object* v_l_1259_; lean_object* v_r_1260_; lean_object* v_size_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_size_1256_ = lean_ctor_get(v_l_1243_, 0);
v_k_1257_ = lean_ctor_get(v_l_1243_, 1);
v_v_1258_ = lean_ctor_get(v_l_1243_, 2);
v_l_1259_ = lean_ctor_get(v_l_1243_, 3);
v_r_1260_ = lean_ctor_get(v_l_1243_, 4);
v_size_1261_ = lean_ctor_get(v_r_1244_, 0);
v___x_1262_ = lean_unsigned_to_nat(2u);
v___x_1263_ = lean_nat_mul(v___x_1262_, v_size_1261_);
v___x_1264_ = lean_nat_dec_lt(v_size_1256_, v___x_1263_);
lean_dec(v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1292_; 
lean_inc(v_r_1260_);
lean_inc(v_l_1259_);
lean_inc(v_v_1258_);
lean_inc(v_k_1257_);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_l_1243_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1293_ = lean_ctor_get(v_l_1243_, 4);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_l_1243_, 3);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_l_1243_, 2);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_l_1243_, 1);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_l_1243_, 0);
lean_dec(v_unused_1297_);
v___x_1266_ = v_l_1243_;
v_isShared_1267_ = v_isSharedCheck_1292_;
goto v_resetjp_1265_;
}
else
{
lean_dec(v_l_1243_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1292_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1282_; 
v___x_1268_ = lean_nat_add(v___x_1238_, v_size_1239_);
v___x_1269_ = lean_nat_add(v___x_1268_, v_size_1240_);
lean_dec(v_size_1240_);
if (lean_obj_tag(v_l_1259_) == 0)
{
lean_object* v_size_1290_; 
v_size_1290_ = lean_ctor_get(v_l_1259_, 0);
lean_inc(v_size_1290_);
v___y_1282_ = v_size_1290_;
goto v___jp_1281_;
}
else
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___y_1282_ = v___x_1291_;
goto v___jp_1281_;
}
v___jp_1270_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_nat_add(v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 4, v_r_1244_);
lean_ctor_set(v___x_1266_, 3, v_r_1260_);
lean_ctor_set(v___x_1266_, 2, v_v_1242_);
lean_ctor_set(v___x_1266_, 1, v_k_1241_);
lean_ctor_set(v___x_1266_, 0, v___x_1274_);
v___x_1276_ = v___x_1266_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_1241_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_1242_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_r_1260_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_r_1244_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v___x_1276_);
lean_ctor_set(v___x_1254_, 3, v___y_1271_);
lean_ctor_set(v___x_1254_, 2, v_v_1258_);
lean_ctor_set(v___x_1254_, 1, v_k_1257_);
lean_ctor_set(v___x_1254_, 0, v___x_1269_);
v___x_1278_ = v___x_1254_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_k_1257_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_v_1258_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v___y_1271_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_nat_add(v___x_1268_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec(v___x_1268_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_l_1259_);
lean_ctor_set(v___x_1094_, 0, v___x_1283_);
v___x_1285_ = v___x_1094_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_l_1091_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_l_1259_);
v___x_1285_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_nat_add(v___x_1238_, v_size_1261_);
if (lean_obj_tag(v_r_1260_) == 0)
{
lean_object* v_size_1287_; 
v_size_1287_ = lean_ctor_get(v_r_1260_, 0);
lean_inc(v_size_1287_);
v___y_1271_ = v___x_1285_;
v___y_1272_ = v___x_1286_;
v___y_1273_ = v_size_1287_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___y_1271_ = v___x_1285_;
v___y_1272_ = v___x_1286_;
v___y_1273_ = v___x_1288_;
goto v___jp_1270_;
}
}
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_del_object(v___x_1094_);
v___x_1298_ = lean_nat_add(v___x_1238_, v_size_1239_);
v___x_1299_ = lean_nat_add(v___x_1298_, v_size_1240_);
lean_dec(v_size_1240_);
v___x_1300_ = lean_nat_add(v___x_1298_, v_size_1256_);
lean_dec(v___x_1298_);
lean_inc_ref(v_l_1091_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_l_1243_);
lean_ctor_set(v___x_1254_, 3, v_l_1091_);
lean_ctor_set(v___x_1254_, 2, v_v_1090_);
lean_ctor_set(v___x_1254_, 1, v_k_1089_);
lean_ctor_set(v___x_1254_, 0, v___x_1300_);
v___x_1302_ = v___x_1254_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_l_1091_);
lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_l_1243_);
v___x_1302_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_isSharedCheck_1309_ = !lean_is_exclusive(v_l_1091_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; 
v_unused_1310_ = lean_ctor_get(v_l_1091_, 4);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v_l_1091_, 3);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_l_1091_, 2);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_l_1091_, 1);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_l_1091_, 0);
lean_dec(v_unused_1314_);
v___x_1304_ = v_l_1091_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v_l_1091_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v_r_1244_);
lean_ctor_set(v___x_1304_, 3, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v_v_1242_);
lean_ctor_set(v___x_1304_, 1, v_k_1241_);
lean_ctor_set(v___x_1304_, 0, v___x_1299_);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_k_1241_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_v_1242_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_r_1244_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1322_; 
v_l_1322_ = lean_ctor_get(v_impl_1237_, 3);
lean_inc(v_l_1322_);
if (lean_obj_tag(v_l_1322_) == 0)
{
lean_object* v_r_1323_; lean_object* v_k_1324_; lean_object* v_v_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1348_; 
v_r_1323_ = lean_ctor_get(v_impl_1237_, 4);
v_k_1324_ = lean_ctor_get(v_impl_1237_, 1);
v_v_1325_ = lean_ctor_get(v_impl_1237_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_impl_1237_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1349_ = lean_ctor_get(v_impl_1237_, 3);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_impl_1237_, 0);
lean_dec(v_unused_1350_);
v___x_1327_ = v_impl_1237_;
v_isShared_1328_ = v_isSharedCheck_1348_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_r_1323_);
lean_inc(v_v_1325_);
lean_inc(v_k_1324_);
lean_dec(v_impl_1237_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1348_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_k_1329_; lean_object* v_v_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1344_; 
v_k_1329_ = lean_ctor_get(v_l_1322_, 1);
v_v_1330_ = lean_ctor_get(v_l_1322_, 2);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_l_1322_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; lean_object* v_unused_1346_; lean_object* v_unused_1347_; 
v_unused_1345_ = lean_ctor_get(v_l_1322_, 4);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_l_1322_, 3);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v_l_1322_, 0);
lean_dec(v_unused_1347_);
v___x_1332_ = v_l_1322_;
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_v_1330_);
lean_inc(v_k_1329_);
lean_dec(v_l_1322_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1323_, 2);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_r_1323_);
lean_ctor_set(v___x_1332_, 3, v_r_1323_);
lean_ctor_set(v___x_1332_, 2, v_v_1090_);
lean_ctor_set(v___x_1332_, 1, v_k_1089_);
lean_ctor_set(v___x_1332_, 0, v___x_1238_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_r_1323_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_r_1323_);
v___x_1336_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
lean_inc(v_r_1323_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 3, v_r_1323_);
lean_ctor_set(v___x_1327_, 0, v___x_1238_);
v___x_1338_ = v___x_1327_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1324_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1325_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_r_1323_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1323_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v___x_1338_);
lean_ctor_set(v___x_1094_, 3, v___x_1336_);
lean_ctor_set(v___x_1094_, 2, v_v_1330_);
lean_ctor_set(v___x_1094_, 1, v_k_1329_);
lean_ctor_set(v___x_1094_, 0, v___x_1334_);
v___x_1340_ = v___x_1094_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_k_1329_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_v_1330_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
else
{
lean_object* v_r_1351_; 
v_r_1351_ = lean_ctor_get(v_impl_1237_, 4);
lean_inc(v_r_1351_);
if (lean_obj_tag(v_r_1351_) == 0)
{
lean_object* v_k_1352_; lean_object* v_v_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1364_; 
v_k_1352_ = lean_ctor_get(v_impl_1237_, 1);
v_v_1353_ = lean_ctor_get(v_impl_1237_, 2);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_impl_1237_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1365_ = lean_ctor_get(v_impl_1237_, 4);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_impl_1237_, 3);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_impl_1237_, 0);
lean_dec(v_unused_1367_);
v___x_1355_ = v_impl_1237_;
v_isShared_1356_ = v_isSharedCheck_1364_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_v_1353_);
lean_inc(v_k_1352_);
lean_dec(v_impl_1237_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1364_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_unsigned_to_nat(3u);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v_l_1322_);
lean_ctor_set(v___x_1355_, 2, v_v_1090_);
lean_ctor_set(v___x_1355_, 1, v_k_1089_);
lean_ctor_set(v___x_1355_, 0, v___x_1238_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_l_1322_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_l_1322_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_r_1351_);
lean_ctor_set(v___x_1094_, 3, v___x_1359_);
lean_ctor_set(v___x_1094_, 2, v_v_1353_);
lean_ctor_set(v___x_1094_, 1, v_k_1352_);
lean_ctor_set(v___x_1094_, 0, v___x_1357_);
v___x_1361_ = v___x_1094_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1351_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(2u);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_impl_1237_);
lean_ctor_set(v___x_1094_, 3, v_r_1351_);
lean_ctor_set(v___x_1094_, 0, v___x_1368_);
v___x_1370_ = v___x_1094_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1089_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1090_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_r_1351_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_impl_1237_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
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
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v_k_1085_);
lean_ctor_set(v___x_1374_, 2, v_v_1086_);
lean_ctor_set(v___x_1374_, 3, v_t_1087_);
lean_ctor_set(v___x_1374_, 4, v_t_1087_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1375_, lean_object* v_mvarId_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1376_, v_s_1375_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1376_, v___x_1378_, v_s_1375_);
return v___x_1379_;
}
else
{
lean_dec(v_mvarId_1376_);
return v_s_1375_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1380_, lean_object* v_k_1381_, lean_object* v_t_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1381_, v_t_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1384_, lean_object* v_k_1385_, lean_object* v_t_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1384_, v_k_1385_, v_t_1386_);
lean_dec(v_t_1386_);
lean_dec(v_k_1385_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1389_, lean_object* v_k_1390_, lean_object* v_v_1391_, lean_object* v_t_1392_, lean_object* v_hl_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1390_, v_v_1391_, v_t_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1395_){
_start:
{
lean_object* v___f_1396_; lean_object* v___x_1397_; 
v___f_1396_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1397_ = l_Std_TreeSet_ofList___redArg(v_l_1395_, v___f_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_MVarIdSet_ofList(v_l_1398_);
lean_dec(v_l_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1400_){
_start:
{
lean_object* v___f_1401_; lean_object* v___x_1402_; 
v___f_1401_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1402_ = l_Std_TreeSet_ofArray___redArg(v_l_1400_, v___f_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_MVarIdSet_ofArray(v_l_1403_);
lean_dec_ref(v_l_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1405_, lean_object* v_m_1406_, lean_object* v_init_1407_, lean_object* v_f_1408_){
_start:
{
lean_object* v_toApplicative_1409_; lean_object* v_toBind_1410_; lean_object* v_toPure_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; 
v_toApplicative_1409_ = lean_ctor_get(v_inst_1405_, 0);
v_toBind_1410_ = lean_ctor_get(v_inst_1405_, 1);
lean_inc(v_toBind_1410_);
v_toPure_1411_ = lean_ctor_get(v_toApplicative_1409_, 1);
lean_inc(v_toPure_1411_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1412_, 0, v_f_1408_);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1405_, v___f_1412_, v_init_1407_, v_m_1406_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1414_, 0, v_toPure_1411_);
v___x_1415_ = lean_apply_4(v_toBind_1410_, lean_box(0), lean_box(0), v___x_1413_, v___f_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1416_, lean_object* v_inst_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_m_1419_, lean_object* v_init_1420_, lean_object* v_f_1421_){
_start:
{
lean_object* v_toApplicative_1422_; lean_object* v_toBind_1423_; lean_object* v_toPure_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; 
v_toApplicative_1422_ = lean_ctor_get(v_inst_1417_, 0);
v_toBind_1423_ = lean_ctor_get(v_inst_1417_, 1);
lean_inc(v_toBind_1423_);
v_toPure_1424_ = lean_ctor_get(v_toApplicative_1422_, 1);
lean_inc(v_toPure_1424_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1425_, 0, v_f_1421_);
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1417_, v___f_1425_, v_init_1420_, v_m_1419_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1427_, 0, v_toPure_1424_);
v___x_1428_ = lean_apply_4(v_toBind_1423_, lean_box(0), lean_box(0), v___x_1426_, v___f_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1430_, 0, lean_box(0));
lean_closure_set(v___x_1430_, 1, v_inst_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1431_, lean_object* v_inst_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1433_, 0, lean_box(0));
lean_closure_set(v___x_1433_, 1, v_inst_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1434_, lean_object* v_mvarId_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1435_, v_a_1436_, v_s_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1438_, lean_object* v_s_1439_, lean_object* v_mvarId_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1440_, v_a_1441_, v_s_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_box(1);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_box(1);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1447_, lean_object* v_a_1448_, lean_object* v_b_1449_, lean_object* v_c_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1448_);
lean_ctor_set(v___x_1451_, 1, v_b_1449_);
v___x_1452_ = lean_apply_2(v_f_1447_, v___x_1451_, v_c_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1453_, lean_object* v_m_1454_, lean_object* v_init_1455_, lean_object* v_f_1456_){
_start:
{
lean_object* v_toApplicative_1457_; lean_object* v_toBind_1458_; lean_object* v_toPure_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; 
v_toApplicative_1457_ = lean_ctor_get(v_inst_1453_, 0);
v_toBind_1458_ = lean_ctor_get(v_inst_1453_, 1);
lean_inc(v_toBind_1458_);
v_toPure_1459_ = lean_ctor_get(v_toApplicative_1457_, 1);
lean_inc(v_toPure_1459_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1460_, 0, v_f_1456_);
v___x_1461_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1453_, v___f_1460_, v_init_1455_, v_m_1454_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1462_, 0, v_toPure_1459_);
v___x_1463_ = lean_apply_4(v_toBind_1458_, lean_box(0), lean_box(0), v___x_1461_, v___f_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1464_, lean_object* v_00_u03b1_1465_, lean_object* v_inst_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_init_1469_, lean_object* v_f_1470_){
_start:
{
lean_object* v_toApplicative_1471_; lean_object* v_toBind_1472_; lean_object* v_toPure_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; 
v_toApplicative_1471_ = lean_ctor_get(v_inst_1466_, 0);
v_toBind_1472_ = lean_ctor_get(v_inst_1466_, 1);
lean_inc(v_toBind_1472_);
v_toPure_1473_ = lean_ctor_get(v_toApplicative_1471_, 1);
lean_inc(v_toPure_1473_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1474_, 0, v_f_1470_);
v___x_1475_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1466_, v___f_1474_, v_init_1469_, v_m_1468_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1476_, 0, v_toPure_1473_);
v___x_1477_ = lean_apply_4(v_toBind_1472_, lean_box(0), lean_box(0), v___x_1475_, v___f_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1479_, 0, lean_box(0));
lean_closure_set(v___x_1479_, 1, lean_box(0));
lean_closure_set(v___x_1479_, 2, v_inst_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1480_, lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1483_, 0, lean_box(0));
lean_closure_set(v___x_1483_, 1, lean_box(0));
lean_closure_set(v___x_1483_, 2, v_inst_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_box(1);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx(lean_object* v_x_1486_){
_start:
{
switch(lean_obj_tag(v_x_1486_))
{
case 0:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
return v___x_1487_;
}
case 1:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
return v___x_1488_;
}
case 2:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(2u);
return v___x_1489_;
}
case 3:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(3u);
return v___x_1490_;
}
case 4:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(4u);
return v___x_1491_;
}
case 5:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_unsigned_to_nat(5u);
return v___x_1492_;
}
case 6:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(6u);
return v___x_1493_;
}
case 7:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(7u);
return v___x_1494_;
}
case 8:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_unsigned_to_nat(8u);
return v___x_1495_;
}
case 9:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(9u);
return v___x_1496_;
}
case 10:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(10u);
return v___x_1497_;
}
default: 
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(11u);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___boxed(lean_object* v_x_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Expr_ctorIdx(v_x_1499_);
lean_dec_ref(v_x_1499_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1501_, lean_object* v_k_1502_){
_start:
{
switch(lean_obj_tag(v_t_1501_))
{
case 4:
{
lean_object* v_declName_1503_; lean_object* v_us_1504_; lean_object* v___x_1505_; 
v_declName_1503_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_declName_1503_);
v_us_1504_ = lean_ctor_get(v_t_1501_, 1);
lean_inc(v_us_1504_);
lean_dec_ref_known(v_t_1501_, 2);
v___x_1505_ = lean_apply_2(v_k_1502_, v_declName_1503_, v_us_1504_);
return v___x_1505_;
}
case 5:
{
lean_object* v_fn_1506_; lean_object* v_arg_1507_; lean_object* v___x_1508_; 
v_fn_1506_ = lean_ctor_get(v_t_1501_, 0);
lean_inc_ref(v_fn_1506_);
v_arg_1507_ = lean_ctor_get(v_t_1501_, 1);
lean_inc_ref(v_arg_1507_);
lean_dec_ref_known(v_t_1501_, 2);
v___x_1508_ = lean_apply_2(v_k_1502_, v_fn_1506_, v_arg_1507_);
return v___x_1508_;
}
case 6:
{
lean_object* v_binderName_1509_; lean_object* v_binderType_1510_; lean_object* v_body_1511_; uint8_t v_binderInfo_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_binderName_1509_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_binderName_1509_);
v_binderType_1510_ = lean_ctor_get(v_t_1501_, 1);
lean_inc_ref(v_binderType_1510_);
v_body_1511_ = lean_ctor_get(v_t_1501_, 2);
lean_inc_ref(v_body_1511_);
v_binderInfo_1512_ = lean_ctor_get_uint8(v_t_1501_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1501_, 3);
v___x_1513_ = lean_box(v_binderInfo_1512_);
v___x_1514_ = lean_apply_4(v_k_1502_, v_binderName_1509_, v_binderType_1510_, v_body_1511_, v___x_1513_);
return v___x_1514_;
}
case 7:
{
lean_object* v_binderName_1515_; lean_object* v_binderType_1516_; lean_object* v_body_1517_; uint8_t v_binderInfo_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_binderName_1515_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_binderName_1515_);
v_binderType_1516_ = lean_ctor_get(v_t_1501_, 1);
lean_inc_ref(v_binderType_1516_);
v_body_1517_ = lean_ctor_get(v_t_1501_, 2);
lean_inc_ref(v_body_1517_);
v_binderInfo_1518_ = lean_ctor_get_uint8(v_t_1501_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1501_, 3);
v___x_1519_ = lean_box(v_binderInfo_1518_);
v___x_1520_ = lean_apply_4(v_k_1502_, v_binderName_1515_, v_binderType_1516_, v_body_1517_, v___x_1519_);
return v___x_1520_;
}
case 8:
{
lean_object* v_declName_1521_; lean_object* v_type_1522_; lean_object* v_value_1523_; lean_object* v_body_1524_; uint8_t v_nondep_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_declName_1521_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_declName_1521_);
v_type_1522_ = lean_ctor_get(v_t_1501_, 1);
lean_inc_ref(v_type_1522_);
v_value_1523_ = lean_ctor_get(v_t_1501_, 2);
lean_inc_ref(v_value_1523_);
v_body_1524_ = lean_ctor_get(v_t_1501_, 3);
lean_inc_ref(v_body_1524_);
v_nondep_1525_ = lean_ctor_get_uint8(v_t_1501_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1501_, 4);
v___x_1526_ = lean_box(v_nondep_1525_);
v___x_1527_ = lean_apply_5(v_k_1502_, v_declName_1521_, v_type_1522_, v_value_1523_, v_body_1524_, v___x_1526_);
return v___x_1527_;
}
case 9:
{
lean_object* v_a_1528_; lean_object* v___x_1529_; 
v_a_1528_ = lean_ctor_get(v_t_1501_, 0);
lean_inc_ref(v_a_1528_);
lean_dec_ref_known(v_t_1501_, 1);
v___x_1529_ = lean_apply_1(v_k_1502_, v_a_1528_);
return v___x_1529_;
}
case 10:
{
lean_object* v_data_1530_; lean_object* v_expr_1531_; lean_object* v___x_1532_; 
v_data_1530_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_data_1530_);
v_expr_1531_ = lean_ctor_get(v_t_1501_, 1);
lean_inc_ref(v_expr_1531_);
lean_dec_ref_known(v_t_1501_, 2);
v___x_1532_ = lean_apply_2(v_k_1502_, v_data_1530_, v_expr_1531_);
return v___x_1532_;
}
case 11:
{
lean_object* v_typeName_1533_; lean_object* v_idx_1534_; lean_object* v_struct_1535_; lean_object* v___x_1536_; 
v_typeName_1533_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_typeName_1533_);
v_idx_1534_ = lean_ctor_get(v_t_1501_, 1);
lean_inc(v_idx_1534_);
v_struct_1535_ = lean_ctor_get(v_t_1501_, 2);
lean_inc_ref(v_struct_1535_);
lean_dec_ref_known(v_t_1501_, 3);
v___x_1536_ = lean_apply_3(v_k_1502_, v_typeName_1533_, v_idx_1534_, v_struct_1535_);
return v___x_1536_;
}
default: 
{
lean_object* v_deBruijnIndex_1537_; lean_object* v___x_1538_; 
v_deBruijnIndex_1537_ = lean_ctor_get(v_t_1501_, 0);
lean_inc(v_deBruijnIndex_1537_);
lean_dec_ref(v_t_1501_);
v___x_1538_ = lean_apply_1(v_k_1502_, v_deBruijnIndex_1537_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1539_, lean_object* v_ctorIdx_1540_, lean_object* v_t_1541_, lean_object* v_h_1542_, lean_object* v_k_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Expr_ctorElim___redArg(v_t_1541_, v_k_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1545_, lean_object* v_ctorIdx_1546_, lean_object* v_t_1547_, lean_object* v_h_1548_, lean_object* v_k_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Expr_ctorElim(v_motive_1545_, v_ctorIdx_1546_, v_t_1547_, v_h_1548_, v_k_1549_);
lean_dec(v_ctorIdx_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1551_, lean_object* v_bvar_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Expr_ctorElim___redArg(v_t_1551_, v_bvar_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1554_, lean_object* v_t_1555_, lean_object* v_h_1556_, lean_object* v_bvar_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Expr_ctorElim___redArg(v_t_1555_, v_bvar_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1559_, lean_object* v_fvar_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Expr_ctorElim___redArg(v_t_1559_, v_fvar_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_fvar_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Expr_ctorElim___redArg(v_t_1563_, v_fvar_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1567_, lean_object* v_mvar_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Expr_ctorElim___redArg(v_t_1567_, v_mvar_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1570_, lean_object* v_t_1571_, lean_object* v_h_1572_, lean_object* v_mvar_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Expr_ctorElim___redArg(v_t_1571_, v_mvar_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1575_, lean_object* v_sort_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Expr_ctorElim___redArg(v_t_1575_, v_sort_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1578_, lean_object* v_t_1579_, lean_object* v_h_1580_, lean_object* v_sort_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Expr_ctorElim___redArg(v_t_1579_, v_sort_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1583_, lean_object* v_const_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Expr_ctorElim___redArg(v_t_1583_, v_const_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1586_, lean_object* v_t_1587_, lean_object* v_h_1588_, lean_object* v_const_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Expr_ctorElim___redArg(v_t_1587_, v_const_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1591_, lean_object* v_app_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Expr_ctorElim___redArg(v_t_1591_, v_app_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1594_, lean_object* v_t_1595_, lean_object* v_h_1596_, lean_object* v_app_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Expr_ctorElim___redArg(v_t_1595_, v_app_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1599_, lean_object* v_lam_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Expr_ctorElim___redArg(v_t_1599_, v_lam_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1602_, lean_object* v_t_1603_, lean_object* v_h_1604_, lean_object* v_lam_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Expr_ctorElim___redArg(v_t_1603_, v_lam_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1607_, lean_object* v_forallE_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Expr_ctorElim___redArg(v_t_1607_, v_forallE_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1610_, lean_object* v_t_1611_, lean_object* v_h_1612_, lean_object* v_forallE_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Expr_ctorElim___redArg(v_t_1611_, v_forallE_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1615_, lean_object* v_letE_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Expr_ctorElim___redArg(v_t_1615_, v_letE_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1618_, lean_object* v_t_1619_, lean_object* v_h_1620_, lean_object* v_letE_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Expr_ctorElim___redArg(v_t_1619_, v_letE_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1623_, lean_object* v_lit_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Expr_ctorElim___redArg(v_t_1623_, v_lit_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1626_, lean_object* v_t_1627_, lean_object* v_h_1628_, lean_object* v_lit_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Expr_ctorElim___redArg(v_t_1627_, v_lit_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1631_, lean_object* v_mdata_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_ctorElim___redArg(v_t_1631_, v_mdata_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1634_, lean_object* v_t_1635_, lean_object* v_h_1636_, lean_object* v_mdata_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Expr_ctorElim___redArg(v_t_1635_, v_mdata_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1639_, lean_object* v_proj_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Expr_ctorElim___redArg(v_t_1639_, v_proj_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1642_, lean_object* v_t_1643_, lean_object* v_h_1644_, lean_object* v_proj_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Expr_ctorElim___redArg(v_t_1643_, v_proj_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1648_){
_start:
{
uint64_t v_res_1649_; lean_object* v_r_1650_; 
v_res_1649_ = lean_expr_data(v_a_00___x40___internal___hyg_1648_);
lean_dec_ref(v_a_00___x40___internal___hyg_1648_);
v_r_1650_ = lean_box_uint64(v_res_1649_);
return v_r_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1651_, lean_object* v_bvar_1652_, lean_object* v_fvar_1653_, lean_object* v_mvar_1654_, lean_object* v_sort_1655_, lean_object* v_const_1656_, lean_object* v_app_1657_, lean_object* v_lam_1658_, lean_object* v_forallE_1659_, lean_object* v_letE_1660_, lean_object* v_lit_1661_, lean_object* v_mdata_1662_, lean_object* v_proj_1663_){
_start:
{
switch(lean_obj_tag(v_t_1651_))
{
case 0:
{
lean_object* v_deBruijnIndex_1664_; lean_object* v___x_1665_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
v_deBruijnIndex_1664_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_deBruijnIndex_1664_);
lean_dec_ref_known(v_t_1651_, 1);
v___x_1665_ = lean_apply_1(v_bvar_1652_, v_deBruijnIndex_1664_);
return v___x_1665_;
}
case 1:
{
lean_object* v_fvarId_1666_; lean_object* v___x_1667_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_bvar_1652_);
v_fvarId_1666_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_fvarId_1666_);
lean_dec_ref_known(v_t_1651_, 1);
v___x_1667_ = lean_apply_1(v_fvar_1653_, v_fvarId_1666_);
return v___x_1667_;
}
case 2:
{
lean_object* v_mvarId_1668_; lean_object* v___x_1669_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_mvarId_1668_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_mvarId_1668_);
lean_dec_ref_known(v_t_1651_, 1);
v___x_1669_ = lean_apply_1(v_mvar_1654_, v_mvarId_1668_);
return v___x_1669_;
}
case 3:
{
lean_object* v_u_1670_; lean_object* v___x_1671_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_u_1670_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_u_1670_);
lean_dec_ref_known(v_t_1651_, 1);
v___x_1671_ = lean_apply_1(v_sort_1655_, v_u_1670_);
return v___x_1671_;
}
case 4:
{
lean_object* v_declName_1672_; lean_object* v_us_1673_; lean_object* v___x_1674_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_declName_1672_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_declName_1672_);
v_us_1673_ = lean_ctor_get(v_t_1651_, 1);
lean_inc(v_us_1673_);
lean_dec_ref_known(v_t_1651_, 2);
v___x_1674_ = lean_apply_2(v_const_1656_, v_declName_1672_, v_us_1673_);
return v___x_1674_;
}
case 5:
{
lean_object* v_fn_1675_; lean_object* v_arg_1676_; lean_object* v___x_1677_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_fn_1675_ = lean_ctor_get(v_t_1651_, 0);
lean_inc_ref(v_fn_1675_);
v_arg_1676_ = lean_ctor_get(v_t_1651_, 1);
lean_inc_ref(v_arg_1676_);
lean_dec_ref_known(v_t_1651_, 2);
v___x_1677_ = lean_apply_2(v_app_1657_, v_fn_1675_, v_arg_1676_);
return v___x_1677_;
}
case 6:
{
lean_object* v_binderName_1678_; lean_object* v_binderType_1679_; lean_object* v_body_1680_; uint8_t v_binderInfo_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_binderName_1678_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_binderName_1678_);
v_binderType_1679_ = lean_ctor_get(v_t_1651_, 1);
lean_inc_ref(v_binderType_1679_);
v_body_1680_ = lean_ctor_get(v_t_1651_, 2);
lean_inc_ref(v_body_1680_);
v_binderInfo_1681_ = lean_ctor_get_uint8(v_t_1651_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1651_, 3);
v___x_1682_ = lean_box(v_binderInfo_1681_);
v___x_1683_ = lean_apply_4(v_lam_1658_, v_binderName_1678_, v_binderType_1679_, v_body_1680_, v___x_1682_);
return v___x_1683_;
}
case 7:
{
lean_object* v_binderName_1684_; lean_object* v_binderType_1685_; lean_object* v_body_1686_; uint8_t v_binderInfo_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_binderName_1684_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_binderName_1684_);
v_binderType_1685_ = lean_ctor_get(v_t_1651_, 1);
lean_inc_ref(v_binderType_1685_);
v_body_1686_ = lean_ctor_get(v_t_1651_, 2);
lean_inc_ref(v_body_1686_);
v_binderInfo_1687_ = lean_ctor_get_uint8(v_t_1651_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1651_, 3);
v___x_1688_ = lean_box(v_binderInfo_1687_);
v___x_1689_ = lean_apply_4(v_forallE_1659_, v_binderName_1684_, v_binderType_1685_, v_body_1686_, v___x_1688_);
return v___x_1689_;
}
case 8:
{
lean_object* v_declName_1690_; lean_object* v_type_1691_; lean_object* v_value_1692_; lean_object* v_body_1693_; uint8_t v_nondep_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_declName_1690_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_declName_1690_);
v_type_1691_ = lean_ctor_get(v_t_1651_, 1);
lean_inc_ref(v_type_1691_);
v_value_1692_ = lean_ctor_get(v_t_1651_, 2);
lean_inc_ref(v_value_1692_);
v_body_1693_ = lean_ctor_get(v_t_1651_, 3);
lean_inc_ref(v_body_1693_);
v_nondep_1694_ = lean_ctor_get_uint8(v_t_1651_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1651_, 4);
v___x_1695_ = lean_box(v_nondep_1694_);
v___x_1696_ = lean_apply_5(v_letE_1660_, v_declName_1690_, v_type_1691_, v_value_1692_, v_body_1693_, v___x_1695_);
return v___x_1696_;
}
case 9:
{
lean_object* v_a_1697_; lean_object* v___x_1698_; 
lean_dec(v_proj_1663_);
lean_dec(v_mdata_1662_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_a_1697_ = lean_ctor_get(v_t_1651_, 0);
lean_inc_ref(v_a_1697_);
lean_dec_ref_known(v_t_1651_, 1);
v___x_1698_ = lean_apply_1(v_lit_1661_, v_a_1697_);
return v___x_1698_;
}
case 10:
{
lean_object* v_data_1699_; lean_object* v_expr_1700_; lean_object* v___x_1701_; 
lean_dec(v_proj_1663_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_data_1699_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_data_1699_);
v_expr_1700_ = lean_ctor_get(v_t_1651_, 1);
lean_inc_ref(v_expr_1700_);
lean_dec_ref_known(v_t_1651_, 2);
v___x_1701_ = lean_apply_2(v_mdata_1662_, v_data_1699_, v_expr_1700_);
return v___x_1701_;
}
default: 
{
lean_object* v_typeName_1702_; lean_object* v_idx_1703_; lean_object* v_struct_1704_; lean_object* v___x_1705_; 
lean_dec(v_mdata_1662_);
lean_dec(v_lit_1661_);
lean_dec(v_letE_1660_);
lean_dec(v_forallE_1659_);
lean_dec(v_lam_1658_);
lean_dec(v_app_1657_);
lean_dec(v_const_1656_);
lean_dec(v_sort_1655_);
lean_dec(v_mvar_1654_);
lean_dec(v_fvar_1653_);
lean_dec(v_bvar_1652_);
v_typeName_1702_ = lean_ctor_get(v_t_1651_, 0);
lean_inc(v_typeName_1702_);
v_idx_1703_ = lean_ctor_get(v_t_1651_, 1);
lean_inc(v_idx_1703_);
v_struct_1704_ = lean_ctor_get(v_t_1651_, 2);
lean_inc_ref(v_struct_1704_);
lean_dec_ref_known(v_t_1651_, 3);
v___x_1705_ = lean_apply_3(v_proj_1663_, v_typeName_1702_, v_idx_1703_, v_struct_1704_);
return v___x_1705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1706_, lean_object* v_t_1707_, lean_object* v_bvar_1708_, lean_object* v_fvar_1709_, lean_object* v_mvar_1710_, lean_object* v_sort_1711_, lean_object* v_const_1712_, lean_object* v_app_1713_, lean_object* v_lam_1714_, lean_object* v_forallE_1715_, lean_object* v_letE_1716_, lean_object* v_lit_1717_, lean_object* v_mdata_1718_, lean_object* v_proj_1719_){
_start:
{
switch(lean_obj_tag(v_t_1707_))
{
case 0:
{
lean_object* v_deBruijnIndex_1720_; lean_object* v___x_1721_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
v_deBruijnIndex_1720_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_deBruijnIndex_1720_);
lean_dec_ref_known(v_t_1707_, 1);
v___x_1721_ = lean_apply_1(v_bvar_1708_, v_deBruijnIndex_1720_);
return v___x_1721_;
}
case 1:
{
lean_object* v_fvarId_1722_; lean_object* v___x_1723_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_bvar_1708_);
v_fvarId_1722_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_fvarId_1722_);
lean_dec_ref_known(v_t_1707_, 1);
v___x_1723_ = lean_apply_1(v_fvar_1709_, v_fvarId_1722_);
return v___x_1723_;
}
case 2:
{
lean_object* v_mvarId_1724_; lean_object* v___x_1725_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_mvarId_1724_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_mvarId_1724_);
lean_dec_ref_known(v_t_1707_, 1);
v___x_1725_ = lean_apply_1(v_mvar_1710_, v_mvarId_1724_);
return v___x_1725_;
}
case 3:
{
lean_object* v_u_1726_; lean_object* v___x_1727_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_u_1726_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_u_1726_);
lean_dec_ref_known(v_t_1707_, 1);
v___x_1727_ = lean_apply_1(v_sort_1711_, v_u_1726_);
return v___x_1727_;
}
case 4:
{
lean_object* v_declName_1728_; lean_object* v_us_1729_; lean_object* v___x_1730_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_declName_1728_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_declName_1728_);
v_us_1729_ = lean_ctor_get(v_t_1707_, 1);
lean_inc(v_us_1729_);
lean_dec_ref_known(v_t_1707_, 2);
v___x_1730_ = lean_apply_2(v_const_1712_, v_declName_1728_, v_us_1729_);
return v___x_1730_;
}
case 5:
{
lean_object* v_fn_1731_; lean_object* v_arg_1732_; lean_object* v___x_1733_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_fn_1731_ = lean_ctor_get(v_t_1707_, 0);
lean_inc_ref(v_fn_1731_);
v_arg_1732_ = lean_ctor_get(v_t_1707_, 1);
lean_inc_ref(v_arg_1732_);
lean_dec_ref_known(v_t_1707_, 2);
v___x_1733_ = lean_apply_2(v_app_1713_, v_fn_1731_, v_arg_1732_);
return v___x_1733_;
}
case 6:
{
lean_object* v_binderName_1734_; lean_object* v_binderType_1735_; lean_object* v_body_1736_; uint8_t v_binderInfo_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_binderName_1734_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_binderName_1734_);
v_binderType_1735_ = lean_ctor_get(v_t_1707_, 1);
lean_inc_ref(v_binderType_1735_);
v_body_1736_ = lean_ctor_get(v_t_1707_, 2);
lean_inc_ref(v_body_1736_);
v_binderInfo_1737_ = lean_ctor_get_uint8(v_t_1707_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1707_, 3);
v___x_1738_ = lean_box(v_binderInfo_1737_);
v___x_1739_ = lean_apply_4(v_lam_1714_, v_binderName_1734_, v_binderType_1735_, v_body_1736_, v___x_1738_);
return v___x_1739_;
}
case 7:
{
lean_object* v_binderName_1740_; lean_object* v_binderType_1741_; lean_object* v_body_1742_; uint8_t v_binderInfo_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_binderName_1740_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_binderName_1740_);
v_binderType_1741_ = lean_ctor_get(v_t_1707_, 1);
lean_inc_ref(v_binderType_1741_);
v_body_1742_ = lean_ctor_get(v_t_1707_, 2);
lean_inc_ref(v_body_1742_);
v_binderInfo_1743_ = lean_ctor_get_uint8(v_t_1707_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1707_, 3);
v___x_1744_ = lean_box(v_binderInfo_1743_);
v___x_1745_ = lean_apply_4(v_forallE_1715_, v_binderName_1740_, v_binderType_1741_, v_body_1742_, v___x_1744_);
return v___x_1745_;
}
case 8:
{
lean_object* v_declName_1746_; lean_object* v_type_1747_; lean_object* v_value_1748_; lean_object* v_body_1749_; uint8_t v_nondep_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_declName_1746_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_declName_1746_);
v_type_1747_ = lean_ctor_get(v_t_1707_, 1);
lean_inc_ref(v_type_1747_);
v_value_1748_ = lean_ctor_get(v_t_1707_, 2);
lean_inc_ref(v_value_1748_);
v_body_1749_ = lean_ctor_get(v_t_1707_, 3);
lean_inc_ref(v_body_1749_);
v_nondep_1750_ = lean_ctor_get_uint8(v_t_1707_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1707_, 4);
v___x_1751_ = lean_box(v_nondep_1750_);
v___x_1752_ = lean_apply_5(v_letE_1716_, v_declName_1746_, v_type_1747_, v_value_1748_, v_body_1749_, v___x_1751_);
return v___x_1752_;
}
case 9:
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
lean_dec(v_proj_1719_);
lean_dec(v_mdata_1718_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_a_1753_ = lean_ctor_get(v_t_1707_, 0);
lean_inc_ref(v_a_1753_);
lean_dec_ref_known(v_t_1707_, 1);
v___x_1754_ = lean_apply_1(v_lit_1717_, v_a_1753_);
return v___x_1754_;
}
case 10:
{
lean_object* v_data_1755_; lean_object* v_expr_1756_; lean_object* v___x_1757_; 
lean_dec(v_proj_1719_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_data_1755_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_data_1755_);
v_expr_1756_ = lean_ctor_get(v_t_1707_, 1);
lean_inc_ref(v_expr_1756_);
lean_dec_ref_known(v_t_1707_, 2);
v___x_1757_ = lean_apply_2(v_mdata_1718_, v_data_1755_, v_expr_1756_);
return v___x_1757_;
}
default: 
{
lean_object* v_typeName_1758_; lean_object* v_idx_1759_; lean_object* v_struct_1760_; lean_object* v___x_1761_; 
lean_dec(v_mdata_1718_);
lean_dec(v_lit_1717_);
lean_dec(v_letE_1716_);
lean_dec(v_forallE_1715_);
lean_dec(v_lam_1714_);
lean_dec(v_app_1713_);
lean_dec(v_const_1712_);
lean_dec(v_sort_1711_);
lean_dec(v_mvar_1710_);
lean_dec(v_fvar_1709_);
lean_dec(v_bvar_1708_);
v_typeName_1758_ = lean_ctor_get(v_t_1707_, 0);
lean_inc(v_typeName_1758_);
v_idx_1759_ = lean_ctor_get(v_t_1707_, 1);
lean_inc(v_idx_1759_);
v_struct_1760_ = lean_ctor_get(v_t_1707_, 2);
lean_inc_ref(v_struct_1760_);
lean_dec_ref_known(v_t_1707_, 3);
v___x_1761_ = lean_apply_3(v_proj_1719_, v_typeName_1758_, v_idx_1759_, v_struct_1760_);
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1762_){
_start:
{
uint64_t v___x_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint32_t v___x_1768_; uint8_t v___x_1769_; uint64_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1763_ = 7ULL;
v___x_1764_ = lean_uint64_of_nat(v_deBruijnIndex_1762_);
v___x_1765_ = lean_uint64_mix_hash(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_nat_add(v_deBruijnIndex_1762_, v___x_1766_);
v___x_1768_ = 0;
v___x_1769_ = 0;
v___x_1770_ = lean_expr_mk_data(v___x_1765_, v___x_1767_, v___x_1768_, v___x_1769_, v___x_1769_, v___x_1769_, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1771_, 0, v_deBruijnIndex_1762_);
lean_ctor_set_uint64(v___x_1771_, sizeof(void*)*1, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1772_){
_start:
{
uint64_t v___x_1773_; uint64_t v___x_1774_; uint64_t v___x_1775_; lean_object* v___x_1776_; uint32_t v___x_1777_; uint8_t v___x_1778_; uint8_t v___x_1779_; uint64_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1773_ = 13ULL;
v___x_1774_ = l_Lean_instHashableFVarId_hash(v_fvarId_1772_);
v___x_1775_ = lean_uint64_mix_hash(v___x_1773_, v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = 0;
v___x_1778_ = 1;
v___x_1779_ = 0;
v___x_1780_ = lean_expr_mk_data(v___x_1775_, v___x_1776_, v___x_1777_, v___x_1778_, v___x_1779_, v___x_1779_, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1781_, 0, v_fvarId_1772_);
lean_ctor_set_uint64(v___x_1781_, sizeof(void*)*1, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1782_){
_start:
{
uint64_t v___x_1783_; uint64_t v___x_1784_; uint64_t v___x_1785_; lean_object* v___x_1786_; uint32_t v___x_1787_; uint8_t v___x_1788_; uint8_t v___x_1789_; uint64_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1783_ = 17ULL;
v___x_1784_ = l_Lean_instHashableMVarId_hash(v_mvarId_1782_);
v___x_1785_ = lean_uint64_mix_hash(v___x_1783_, v___x_1784_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = 0;
v___x_1788_ = 0;
v___x_1789_ = 1;
v___x_1790_ = lean_expr_mk_data(v___x_1785_, v___x_1786_, v___x_1787_, v___x_1788_, v___x_1789_, v___x_1788_, v___x_1788_);
v___x_1791_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1791_, 0, v_mvarId_1782_);
lean_ctor_set_uint64(v___x_1791_, sizeof(void*)*1, v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1792_){
_start:
{
uint64_t v___x_1793_; uint64_t v___x_1794_; uint64_t v___x_1795_; lean_object* v___x_1796_; uint32_t v___x_1797_; uint8_t v___x_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; uint64_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1793_ = 11ULL;
v___x_1794_ = l_Lean_Level_hash(v_u_1792_);
v___x_1795_ = lean_uint64_mix_hash(v___x_1793_, v___x_1794_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = 0;
v___x_1798_ = 0;
v___x_1799_ = l_Lean_Level_hasMVar(v_u_1792_);
v___x_1800_ = l_Lean_Level_hasParam(v_u_1792_);
v___x_1801_ = lean_expr_mk_data(v___x_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1798_, v___x_1799_, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1802_, 0, v_u_1792_);
lean_ctor_set_uint64(v___x_1802_, sizeof(void*)*1, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1803_, lean_object* v_arg_1804_){
_start:
{
uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_expr_data(v_fn_1803_);
v___x_1806_ = lean_expr_data(v_arg_1804_);
v___x_1807_ = lean_expr_mk_app_data(v___x_1805_, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1808_, 0, v_fn_1803_);
lean_ctor_set(v___x_1808_, 1, v_arg_1804_);
lean_ctor_set_uint64(v___x_1808_, sizeof(void*)*2, v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1809_, lean_object* v_binderType_1810_, lean_object* v_body_1811_, uint8_t v_binderInfo_1812_){
_start:
{
uint8_t v___y_1814_; uint8_t v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; uint64_t v___y_1818_; uint32_t v___y_1819_; uint8_t v___y_1820_; uint64_t v___x_1823_; uint8_t v___x_1824_; uint32_t v___x_1825_; uint64_t v___x_1826_; uint8_t v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; uint64_t v___y_1831_; uint32_t v___y_1832_; uint8_t v___y_1833_; uint8_t v___y_1837_; lean_object* v___y_1838_; uint64_t v___y_1839_; uint32_t v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1845_; uint64_t v___y_1846_; uint32_t v___y_1847_; uint8_t v___y_1848_; uint64_t v___y_1852_; uint32_t v___y_1853_; lean_object* v___y_1854_; uint32_t v___y_1858_; uint8_t v___x_1873_; uint32_t v___x_1874_; uint8_t v___x_1875_; 
v___x_1823_ = lean_expr_data(v_binderType_1810_);
v___x_1824_ = l_Lean_Expr_Data_approxDepth(v___x_1823_);
v___x_1825_ = lean_uint8_to_uint32(v___x_1824_);
v___x_1826_ = lean_expr_data(v_body_1811_);
v___x_1873_ = l_Lean_Expr_Data_approxDepth(v___x_1826_);
v___x_1874_ = lean_uint8_to_uint32(v___x_1873_);
v___x_1875_ = lean_uint32_dec_le(v___x_1825_, v___x_1874_);
if (v___x_1875_ == 0)
{
v___y_1858_ = v___x_1825_;
goto v___jp_1857_;
}
else
{
v___y_1858_ = v___x_1874_;
goto v___jp_1857_;
}
v___jp_1813_:
{
uint64_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_expr_mk_data(v___y_1818_, v___y_1816_, v___y_1819_, v___y_1814_, v___y_1815_, v___y_1817_, v___y_1820_);
v___x_1822_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1822_, 0, v_binderName_1809_);
lean_ctor_set(v___x_1822_, 1, v_binderType_1810_);
lean_ctor_set(v___x_1822_, 2, v_body_1811_);
lean_ctor_set_uint64(v___x_1822_, sizeof(void*)*3, v___x_1821_);
lean_ctor_set_uint8(v___x_1822_, sizeof(void*)*3 + 8, v_binderInfo_1812_);
return v___x_1822_;
}
v___jp_1827_:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Lean_Expr_Data_hasLevelParam(v___x_1823_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_Data_hasLevelParam(v___x_1826_);
v___y_1814_ = v___y_1828_;
v___y_1815_ = v___y_1830_;
v___y_1816_ = v___y_1829_;
v___y_1817_ = v___y_1833_;
v___y_1818_ = v___y_1831_;
v___y_1819_ = v___y_1832_;
v___y_1820_ = v___x_1835_;
goto v___jp_1813_;
}
else
{
v___y_1814_ = v___y_1828_;
v___y_1815_ = v___y_1830_;
v___y_1816_ = v___y_1829_;
v___y_1817_ = v___y_1833_;
v___y_1818_ = v___y_1831_;
v___y_1819_ = v___y_1832_;
v___y_1820_ = v___x_1834_;
goto v___jp_1813_;
}
}
v___jp_1836_:
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1823_);
if (v___x_1842_ == 0)
{
uint8_t v___x_1843_; 
v___x_1843_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1826_);
v___y_1828_ = v___y_1837_;
v___y_1829_ = v___y_1838_;
v___y_1830_ = v___y_1841_;
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___y_1840_;
v___y_1833_ = v___x_1843_;
goto v___jp_1827_;
}
else
{
v___y_1828_ = v___y_1837_;
v___y_1829_ = v___y_1838_;
v___y_1830_ = v___y_1841_;
v___y_1831_ = v___y_1839_;
v___y_1832_ = v___y_1840_;
v___y_1833_ = v___x_1842_;
goto v___jp_1827_;
}
}
v___jp_1844_:
{
uint8_t v___x_1849_; 
v___x_1849_ = l_Lean_Expr_Data_hasExprMVar(v___x_1823_);
if (v___x_1849_ == 0)
{
uint8_t v___x_1850_; 
v___x_1850_ = l_Lean_Expr_Data_hasExprMVar(v___x_1826_);
v___y_1837_ = v___y_1848_;
v___y_1838_ = v___y_1845_;
v___y_1839_ = v___y_1846_;
v___y_1840_ = v___y_1847_;
v___y_1841_ = v___x_1850_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___y_1848_;
v___y_1838_ = v___y_1845_;
v___y_1839_ = v___y_1846_;
v___y_1840_ = v___y_1847_;
v___y_1841_ = v___x_1849_;
goto v___jp_1836_;
}
}
v___jp_1851_:
{
uint8_t v___x_1855_; 
v___x_1855_ = l_Lean_Expr_Data_hasFVar(v___x_1823_);
if (v___x_1855_ == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Lean_Expr_Data_hasFVar(v___x_1826_);
v___y_1845_ = v___y_1854_;
v___y_1846_ = v___y_1852_;
v___y_1847_ = v___y_1853_;
v___y_1848_ = v___x_1856_;
goto v___jp_1844_;
}
else
{
v___y_1845_ = v___y_1854_;
v___y_1846_ = v___y_1852_;
v___y_1847_ = v___y_1853_;
v___y_1848_ = v___x_1855_;
goto v___jp_1844_;
}
}
v___jp_1857_:
{
lean_object* v___x_1859_; uint32_t v___x_1860_; uint32_t v___x_1861_; uint64_t v___x_1862_; uint64_t v___x_1863_; uint64_t v___x_1864_; uint64_t v___x_1865_; uint64_t v___x_1866_; uint32_t v___x_1867_; lean_object* v___x_1868_; uint32_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = 1;
v___x_1861_ = lean_uint32_add(v___y_1858_, v___x_1860_);
v___x_1862_ = lean_uint32_to_uint64(v___x_1861_);
v___x_1863_ = l_Lean_Expr_Data_hash(v___x_1823_);
v___x_1864_ = l_Lean_Expr_Data_hash(v___x_1826_);
v___x_1865_ = lean_uint64_mix_hash(v___x_1863_, v___x_1864_);
v___x_1866_ = lean_uint64_mix_hash(v___x_1862_, v___x_1865_);
v___x_1867_ = l_Lean_Expr_Data_looseBVarRange(v___x_1823_);
v___x_1868_ = lean_uint32_to_nat(v___x_1867_);
v___x_1869_ = l_Lean_Expr_Data_looseBVarRange(v___x_1826_);
v___x_1870_ = lean_uint32_to_nat(v___x_1869_);
v___x_1871_ = lean_nat_sub(v___x_1870_, v___x_1859_);
lean_dec(v___x_1870_);
v___x_1872_ = lean_nat_dec_le(v___x_1868_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_dec(v___x_1871_);
v___y_1852_ = v___x_1866_;
v___y_1853_ = v___x_1861_;
v___y_1854_ = v___x_1868_;
goto v___jp_1851_;
}
else
{
lean_dec(v___x_1868_);
v___y_1852_ = v___x_1866_;
v___y_1853_ = v___x_1861_;
v___y_1854_ = v___x_1871_;
goto v___jp_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1876_, lean_object* v_binderType_1877_, lean_object* v_body_1878_, lean_object* v_binderInfo_1879_){
_start:
{
uint8_t v_binderInfo_boxed_1880_; lean_object* v_res_1881_; 
v_binderInfo_boxed_1880_ = lean_unbox(v_binderInfo_1879_);
v_res_1881_ = l_Lean_Expr_lam___override(v_binderName_1876_, v_binderType_1877_, v_body_1878_, v_binderInfo_boxed_1880_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1882_, lean_object* v_binderType_1883_, lean_object* v_body_1884_, uint8_t v_binderInfo_1885_){
_start:
{
uint64_t v___y_1887_; uint8_t v___y_1888_; lean_object* v___y_1889_; uint8_t v___y_1890_; uint32_t v___y_1891_; uint8_t v___y_1892_; uint8_t v___y_1893_; uint64_t v___x_1896_; uint8_t v___x_1897_; uint32_t v___x_1898_; uint64_t v___x_1899_; uint64_t v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; uint32_t v___y_1904_; uint8_t v___y_1905_; uint8_t v___y_1906_; uint64_t v___y_1910_; lean_object* v___y_1911_; uint32_t v___y_1912_; uint8_t v___y_1913_; uint8_t v___y_1914_; uint64_t v___y_1918_; lean_object* v___y_1919_; uint32_t v___y_1920_; uint8_t v___y_1921_; uint64_t v___y_1925_; uint32_t v___y_1926_; lean_object* v___y_1927_; uint32_t v___y_1931_; uint8_t v___x_1946_; uint32_t v___x_1947_; uint8_t v___x_1948_; 
v___x_1896_ = lean_expr_data(v_binderType_1883_);
v___x_1897_ = l_Lean_Expr_Data_approxDepth(v___x_1896_);
v___x_1898_ = lean_uint8_to_uint32(v___x_1897_);
v___x_1899_ = lean_expr_data(v_body_1884_);
v___x_1946_ = l_Lean_Expr_Data_approxDepth(v___x_1899_);
v___x_1947_ = lean_uint8_to_uint32(v___x_1946_);
v___x_1948_ = lean_uint32_dec_le(v___x_1898_, v___x_1947_);
if (v___x_1948_ == 0)
{
v___y_1931_ = v___x_1898_;
goto v___jp_1930_;
}
else
{
v___y_1931_ = v___x_1947_;
goto v___jp_1930_;
}
v___jp_1886_:
{
uint64_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_expr_mk_data(v___y_1887_, v___y_1889_, v___y_1891_, v___y_1892_, v___y_1888_, v___y_1890_, v___y_1893_);
v___x_1895_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1895_, 0, v_binderName_1882_);
lean_ctor_set(v___x_1895_, 1, v_binderType_1883_);
lean_ctor_set(v___x_1895_, 2, v_body_1884_);
lean_ctor_set_uint64(v___x_1895_, sizeof(void*)*3, v___x_1894_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 8, v_binderInfo_1885_);
return v___x_1895_;
}
v___jp_1900_:
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Expr_Data_hasLevelParam(v___x_1896_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Expr_Data_hasLevelParam(v___x_1899_);
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1902_;
v___y_1889_ = v___y_1903_;
v___y_1890_ = v___y_1906_;
v___y_1891_ = v___y_1904_;
v___y_1892_ = v___y_1905_;
v___y_1893_ = v___x_1908_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1902_;
v___y_1889_ = v___y_1903_;
v___y_1890_ = v___y_1906_;
v___y_1891_ = v___y_1904_;
v___y_1892_ = v___y_1905_;
v___y_1893_ = v___x_1907_;
goto v___jp_1886_;
}
}
v___jp_1909_:
{
uint8_t v___x_1915_; 
v___x_1915_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1896_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1899_);
v___y_1901_ = v___y_1910_;
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1911_;
v___y_1904_ = v___y_1912_;
v___y_1905_ = v___y_1913_;
v___y_1906_ = v___x_1916_;
goto v___jp_1900_;
}
else
{
v___y_1901_ = v___y_1910_;
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1911_;
v___y_1904_ = v___y_1912_;
v___y_1905_ = v___y_1913_;
v___y_1906_ = v___x_1915_;
goto v___jp_1900_;
}
}
v___jp_1917_:
{
uint8_t v___x_1922_; 
v___x_1922_ = l_Lean_Expr_Data_hasExprMVar(v___x_1896_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
v___x_1923_ = l_Lean_Expr_Data_hasExprMVar(v___x_1899_);
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___y_1920_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___x_1923_;
goto v___jp_1909_;
}
else
{
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___y_1920_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___x_1922_;
goto v___jp_1909_;
}
}
v___jp_1924_:
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_Data_hasFVar(v___x_1896_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = l_Lean_Expr_Data_hasFVar(v___x_1899_);
v___y_1918_ = v___y_1925_;
v___y_1919_ = v___y_1927_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___x_1929_;
goto v___jp_1917_;
}
else
{
v___y_1918_ = v___y_1925_;
v___y_1919_ = v___y_1927_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___x_1928_;
goto v___jp_1917_;
}
}
v___jp_1930_:
{
lean_object* v___x_1932_; uint32_t v___x_1933_; uint32_t v___x_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; uint64_t v___x_1938_; uint64_t v___x_1939_; uint32_t v___x_1940_; lean_object* v___x_1941_; uint32_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = 1;
v___x_1934_ = lean_uint32_add(v___y_1931_, v___x_1933_);
v___x_1935_ = lean_uint32_to_uint64(v___x_1934_);
v___x_1936_ = l_Lean_Expr_Data_hash(v___x_1896_);
v___x_1937_ = l_Lean_Expr_Data_hash(v___x_1899_);
v___x_1938_ = lean_uint64_mix_hash(v___x_1936_, v___x_1937_);
v___x_1939_ = lean_uint64_mix_hash(v___x_1935_, v___x_1938_);
v___x_1940_ = l_Lean_Expr_Data_looseBVarRange(v___x_1896_);
v___x_1941_ = lean_uint32_to_nat(v___x_1940_);
v___x_1942_ = l_Lean_Expr_Data_looseBVarRange(v___x_1899_);
v___x_1943_ = lean_uint32_to_nat(v___x_1942_);
v___x_1944_ = lean_nat_sub(v___x_1943_, v___x_1932_);
lean_dec(v___x_1943_);
v___x_1945_ = lean_nat_dec_le(v___x_1941_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_dec(v___x_1944_);
v___y_1925_ = v___x_1939_;
v___y_1926_ = v___x_1934_;
v___y_1927_ = v___x_1941_;
goto v___jp_1924_;
}
else
{
lean_dec(v___x_1941_);
v___y_1925_ = v___x_1939_;
v___y_1926_ = v___x_1934_;
v___y_1927_ = v___x_1944_;
goto v___jp_1924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1949_, lean_object* v_binderType_1950_, lean_object* v_body_1951_, lean_object* v_binderInfo_1952_){
_start:
{
uint8_t v_binderInfo_boxed_1953_; lean_object* v_res_1954_; 
v_binderInfo_boxed_1953_ = lean_unbox(v_binderInfo_1952_);
v_res_1954_ = l_Lean_Expr_forallE___override(v_binderName_1949_, v_binderType_1950_, v_body_1951_, v_binderInfo_boxed_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1955_, lean_object* v_type_1956_, lean_object* v_value_1957_, lean_object* v_body_1958_, uint8_t v_nondep_1959_){
_start:
{
uint8_t v___y_1961_; uint64_t v___y_1962_; uint8_t v___y_1963_; uint32_t v___y_1964_; lean_object* v___y_1965_; uint8_t v___y_1966_; uint8_t v___y_1967_; uint8_t v___y_1971_; uint64_t v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1974_; uint32_t v___y_1975_; uint8_t v___y_1976_; uint64_t v___y_1977_; uint8_t v___y_1978_; uint64_t v___x_1980_; uint8_t v___x_1981_; uint32_t v___x_1982_; uint64_t v___x_1983_; uint8_t v___y_1985_; uint64_t v___y_1986_; uint8_t v___y_1987_; lean_object* v___y_1988_; uint32_t v___y_1989_; uint64_t v___y_1990_; uint8_t v___y_1991_; uint8_t v___y_1995_; uint64_t v___y_1996_; uint8_t v___y_1997_; uint32_t v___y_1998_; lean_object* v___y_1999_; uint64_t v___y_2000_; uint8_t v___y_2001_; uint8_t v___y_2004_; uint64_t v___y_2005_; uint32_t v___y_2006_; lean_object* v___y_2007_; uint64_t v___y_2008_; uint8_t v___y_2009_; uint8_t v___y_2013_; uint64_t v___y_2014_; lean_object* v___y_2015_; uint32_t v___y_2016_; uint64_t v___y_2017_; uint8_t v___y_2018_; uint64_t v___y_2021_; lean_object* v___y_2022_; uint32_t v___y_2023_; uint64_t v___y_2024_; uint8_t v___y_2025_; uint64_t v___y_2029_; uint32_t v___y_2030_; lean_object* v___y_2031_; uint64_t v___y_2032_; uint8_t v___y_2033_; uint64_t v___y_2036_; uint32_t v___y_2037_; uint64_t v___y_2038_; lean_object* v___y_2039_; uint64_t v___y_2043_; lean_object* v___y_2044_; uint32_t v___y_2045_; uint64_t v___y_2046_; lean_object* v___y_2047_; uint64_t v___y_2053_; uint32_t v___y_2054_; uint32_t v___y_2071_; uint8_t v___x_2076_; uint32_t v___x_2077_; uint8_t v___x_2078_; 
v___x_1980_ = lean_expr_data(v_type_1956_);
v___x_1981_ = l_Lean_Expr_Data_approxDepth(v___x_1980_);
v___x_1982_ = lean_uint8_to_uint32(v___x_1981_);
v___x_1983_ = lean_expr_data(v_value_1957_);
v___x_2076_ = l_Lean_Expr_Data_approxDepth(v___x_1983_);
v___x_2077_ = lean_uint8_to_uint32(v___x_2076_);
v___x_2078_ = lean_uint32_dec_le(v___x_1982_, v___x_2077_);
if (v___x_2078_ == 0)
{
v___y_2071_ = v___x_1982_;
goto v___jp_2070_;
}
else
{
v___y_2071_ = v___x_2077_;
goto v___jp_2070_;
}
v___jp_1960_:
{
uint64_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_expr_mk_data(v___y_1962_, v___y_1965_, v___y_1964_, v___y_1961_, v___y_1963_, v___y_1966_, v___y_1967_);
v___x_1969_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1969_, 0, v_declName_1955_);
lean_ctor_set(v___x_1969_, 1, v_type_1956_);
lean_ctor_set(v___x_1969_, 2, v_value_1957_);
lean_ctor_set(v___x_1969_, 3, v_body_1958_);
lean_ctor_set_uint64(v___x_1969_, sizeof(void*)*4, v___x_1968_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*4 + 8, v_nondep_1959_);
return v___x_1969_;
}
v___jp_1970_:
{
if (v___y_1978_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_Expr_Data_hasLevelParam(v___y_1977_);
v___y_1961_ = v___y_1971_;
v___y_1962_ = v___y_1972_;
v___y_1963_ = v___y_1973_;
v___y_1964_ = v___y_1975_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___x_1979_;
goto v___jp_1960_;
}
else
{
v___y_1961_ = v___y_1971_;
v___y_1962_ = v___y_1972_;
v___y_1963_ = v___y_1973_;
v___y_1964_ = v___y_1975_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1978_;
goto v___jp_1960_;
}
}
v___jp_1984_:
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Lean_Expr_Data_hasLevelParam(v___x_1980_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Expr_Data_hasLevelParam(v___x_1983_);
v___y_1971_ = v___y_1985_;
v___y_1972_ = v___y_1986_;
v___y_1973_ = v___y_1987_;
v___y_1974_ = v___y_1988_;
v___y_1975_ = v___y_1989_;
v___y_1976_ = v___y_1991_;
v___y_1977_ = v___y_1990_;
v___y_1978_ = v___x_1993_;
goto v___jp_1970_;
}
else
{
v___y_1971_ = v___y_1985_;
v___y_1972_ = v___y_1986_;
v___y_1973_ = v___y_1987_;
v___y_1974_ = v___y_1988_;
v___y_1975_ = v___y_1989_;
v___y_1976_ = v___y_1991_;
v___y_1977_ = v___y_1990_;
v___y_1978_ = v___x_1992_;
goto v___jp_1970_;
}
}
v___jp_1994_:
{
if (v___y_2001_ == 0)
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Expr_Data_hasLevelMVar(v___y_2000_);
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_1998_;
v___y_1990_ = v___y_2000_;
v___y_1991_ = v___x_2002_;
goto v___jp_1984_;
}
else
{
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v___y_1988_ = v___y_1999_;
v___y_1989_ = v___y_1998_;
v___y_1990_ = v___y_2000_;
v___y_1991_ = v___y_2001_;
goto v___jp_1984_;
}
}
v___jp_2003_:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1980_);
if (v___x_2010_ == 0)
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1983_);
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2005_;
v___y_1997_ = v___y_2009_;
v___y_1998_ = v___y_2006_;
v___y_1999_ = v___y_2007_;
v___y_2000_ = v___y_2008_;
v___y_2001_ = v___x_2011_;
goto v___jp_1994_;
}
else
{
v___y_1995_ = v___y_2004_;
v___y_1996_ = v___y_2005_;
v___y_1997_ = v___y_2009_;
v___y_1998_ = v___y_2006_;
v___y_1999_ = v___y_2007_;
v___y_2000_ = v___y_2008_;
v___y_2001_ = v___x_2010_;
goto v___jp_1994_;
}
}
v___jp_2012_:
{
if (v___y_2018_ == 0)
{
uint8_t v___x_2019_; 
v___x_2019_ = l_Lean_Expr_Data_hasExprMVar(v___y_2017_);
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___y_2014_;
v___y_2006_ = v___y_2016_;
v___y_2007_ = v___y_2015_;
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___x_2019_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___y_2014_;
v___y_2006_ = v___y_2016_;
v___y_2007_ = v___y_2015_;
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2018_;
goto v___jp_2003_;
}
}
v___jp_2020_:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Expr_Data_hasExprMVar(v___x_1980_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; 
v___x_2027_ = l_Lean_Expr_Data_hasExprMVar(v___x_1983_);
v___y_2013_ = v___y_2025_;
v___y_2014_ = v___y_2021_;
v___y_2015_ = v___y_2022_;
v___y_2016_ = v___y_2023_;
v___y_2017_ = v___y_2024_;
v___y_2018_ = v___x_2027_;
goto v___jp_2012_;
}
else
{
v___y_2013_ = v___y_2025_;
v___y_2014_ = v___y_2021_;
v___y_2015_ = v___y_2022_;
v___y_2016_ = v___y_2023_;
v___y_2017_ = v___y_2024_;
v___y_2018_ = v___x_2026_;
goto v___jp_2012_;
}
}
v___jp_2028_:
{
if (v___y_2033_ == 0)
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Expr_Data_hasFVar(v___y_2032_);
v___y_2021_ = v___y_2029_;
v___y_2022_ = v___y_2031_;
v___y_2023_ = v___y_2030_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___x_2034_;
goto v___jp_2020_;
}
else
{
v___y_2021_ = v___y_2029_;
v___y_2022_ = v___y_2031_;
v___y_2023_ = v___y_2030_;
v___y_2024_ = v___y_2032_;
v___y_2025_ = v___y_2033_;
goto v___jp_2020_;
}
}
v___jp_2035_:
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_Expr_Data_hasFVar(v___x_1980_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_Expr_Data_hasFVar(v___x_1983_);
v___y_2029_ = v___y_2036_;
v___y_2030_ = v___y_2037_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2038_;
v___y_2033_ = v___x_2041_;
goto v___jp_2028_;
}
else
{
v___y_2029_ = v___y_2036_;
v___y_2030_ = v___y_2037_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2038_;
v___y_2033_ = v___x_2040_;
goto v___jp_2028_;
}
}
v___jp_2042_:
{
uint32_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2048_ = l_Lean_Expr_Data_looseBVarRange(v___y_2046_);
v___x_2049_ = lean_uint32_to_nat(v___x_2048_);
v___x_2050_ = lean_nat_sub(v___x_2049_, v___y_2044_);
lean_dec(v___x_2049_);
v___x_2051_ = lean_nat_dec_le(v___y_2047_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec(v___x_2050_);
v___y_2036_ = v___y_2043_;
v___y_2037_ = v___y_2045_;
v___y_2038_ = v___y_2046_;
v___y_2039_ = v___y_2047_;
goto v___jp_2035_;
}
else
{
lean_dec(v___y_2047_);
v___y_2036_ = v___y_2043_;
v___y_2037_ = v___y_2045_;
v___y_2038_ = v___y_2046_;
v___y_2039_ = v___x_2050_;
goto v___jp_2035_;
}
}
v___jp_2052_:
{
lean_object* v___x_2055_; uint32_t v___x_2056_; uint32_t v___x_2057_; uint64_t v___x_2058_; uint64_t v___x_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v___x_2063_; uint64_t v___x_2064_; uint32_t v___x_2065_; lean_object* v___x_2066_; uint32_t v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = 1;
v___x_2057_ = lean_uint32_add(v___y_2054_, v___x_2056_);
v___x_2058_ = lean_uint32_to_uint64(v___x_2057_);
v___x_2059_ = l_Lean_Expr_Data_hash(v___x_1980_);
v___x_2060_ = l_Lean_Expr_Data_hash(v___x_1983_);
v___x_2061_ = l_Lean_Expr_Data_hash(v___y_2053_);
v___x_2062_ = lean_uint64_mix_hash(v___x_2060_, v___x_2061_);
v___x_2063_ = lean_uint64_mix_hash(v___x_2059_, v___x_2062_);
v___x_2064_ = lean_uint64_mix_hash(v___x_2058_, v___x_2063_);
v___x_2065_ = l_Lean_Expr_Data_looseBVarRange(v___x_1980_);
v___x_2066_ = lean_uint32_to_nat(v___x_2065_);
v___x_2067_ = l_Lean_Expr_Data_looseBVarRange(v___x_1983_);
v___x_2068_ = lean_uint32_to_nat(v___x_2067_);
v___x_2069_ = lean_nat_dec_le(v___x_2066_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec(v___x_2068_);
v___y_2043_ = v___x_2064_;
v___y_2044_ = v___x_2055_;
v___y_2045_ = v___x_2057_;
v___y_2046_ = v___y_2053_;
v___y_2047_ = v___x_2066_;
goto v___jp_2042_;
}
else
{
lean_dec(v___x_2066_);
v___y_2043_ = v___x_2064_;
v___y_2044_ = v___x_2055_;
v___y_2045_ = v___x_2057_;
v___y_2046_ = v___y_2053_;
v___y_2047_ = v___x_2068_;
goto v___jp_2042_;
}
}
v___jp_2070_:
{
uint64_t v___x_2072_; uint8_t v___x_2073_; uint32_t v___x_2074_; uint8_t v___x_2075_; 
v___x_2072_ = lean_expr_data(v_body_1958_);
v___x_2073_ = l_Lean_Expr_Data_approxDepth(v___x_2072_);
v___x_2074_ = lean_uint8_to_uint32(v___x_2073_);
v___x_2075_ = lean_uint32_dec_le(v___y_2071_, v___x_2074_);
if (v___x_2075_ == 0)
{
v___y_2053_ = v___x_2072_;
v___y_2054_ = v___y_2071_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v___x_2072_;
v___y_2054_ = v___x_2074_;
goto v___jp_2052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2079_, lean_object* v_type_2080_, lean_object* v_value_2081_, lean_object* v_body_2082_, lean_object* v_nondep_2083_){
_start:
{
uint8_t v_nondep_boxed_2084_; lean_object* v_res_2085_; 
v_nondep_boxed_2084_ = lean_unbox(v_nondep_2083_);
v_res_2085_ = l_Lean_Expr_letE___override(v_declName_2079_, v_type_2080_, v_value_2081_, v_body_2082_, v_nondep_boxed_2084_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2086_){
_start:
{
uint64_t v___x_2087_; uint64_t v___x_2088_; uint64_t v___x_2089_; lean_object* v___x_2090_; uint32_t v___x_2091_; uint8_t v___x_2092_; uint64_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2087_ = 3ULL;
v___x_2088_ = l_Lean_Literal_hash(v_a_2086_);
v___x_2089_ = lean_uint64_mix_hash(v___x_2087_, v___x_2088_);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = 0;
v___x_2092_ = 0;
v___x_2093_ = lean_expr_mk_data(v___x_2089_, v___x_2090_, v___x_2091_, v___x_2092_, v___x_2092_, v___x_2092_, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2094_, 0, v_a_2086_);
lean_ctor_set_uint64(v___x_2094_, sizeof(void*)*1, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2095_, lean_object* v_expr_2096_){
_start:
{
uint64_t v___x_2097_; uint8_t v___x_2098_; uint32_t v___x_2099_; uint32_t v___x_2100_; uint32_t v___x_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; uint64_t v___x_2104_; uint32_t v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; uint8_t v___x_2108_; uint8_t v___x_2109_; uint8_t v___x_2110_; uint64_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2097_ = lean_expr_data(v_expr_2096_);
v___x_2098_ = l_Lean_Expr_Data_approxDepth(v___x_2097_);
v___x_2099_ = lean_uint8_to_uint32(v___x_2098_);
v___x_2100_ = 1;
v___x_2101_ = lean_uint32_add(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_uint32_to_uint64(v___x_2101_);
v___x_2103_ = l_Lean_Expr_Data_hash(v___x_2097_);
v___x_2104_ = lean_uint64_mix_hash(v___x_2102_, v___x_2103_);
v___x_2105_ = l_Lean_Expr_Data_looseBVarRange(v___x_2097_);
v___x_2106_ = lean_uint32_to_nat(v___x_2105_);
v___x_2107_ = l_Lean_Expr_Data_hasFVar(v___x_2097_);
v___x_2108_ = l_Lean_Expr_Data_hasExprMVar(v___x_2097_);
v___x_2109_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2097_);
v___x_2110_ = l_Lean_Expr_Data_hasLevelParam(v___x_2097_);
v___x_2111_ = lean_expr_mk_data(v___x_2104_, v___x_2106_, v___x_2101_, v___x_2107_, v___x_2108_, v___x_2109_, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2112_, 0, v_data_2095_);
lean_ctor_set(v___x_2112_, 1, v_expr_2096_);
lean_ctor_set_uint64(v___x_2112_, sizeof(void*)*2, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2113_, lean_object* v_idx_2114_, lean_object* v_struct_2115_){
_start:
{
uint64_t v___x_2116_; uint8_t v___x_2117_; uint32_t v___x_2118_; uint32_t v___x_2119_; uint32_t v___x_2120_; uint64_t v___x_2121_; uint64_t v___y_2123_; 
v___x_2116_ = lean_expr_data(v_struct_2115_);
v___x_2117_ = l_Lean_Expr_Data_approxDepth(v___x_2116_);
v___x_2118_ = lean_uint8_to_uint32(v___x_2117_);
v___x_2119_ = 1;
v___x_2120_ = lean_uint32_add(v___x_2118_, v___x_2119_);
v___x_2121_ = lean_uint32_to_uint64(v___x_2120_);
if (lean_obj_tag(v_typeName_2113_) == 0)
{
uint64_t v___x_2137_; 
v___x_2137_ = 1723ULL;
v___y_2123_ = v___x_2137_;
goto v___jp_2122_;
}
else
{
uint64_t v_hash_2138_; 
v_hash_2138_ = lean_ctor_get_uint64(v_typeName_2113_, sizeof(void*)*2);
v___y_2123_ = v_hash_2138_;
goto v___jp_2122_;
}
v___jp_2122_:
{
uint64_t v___x_2124_; uint64_t v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint32_t v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; uint64_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2124_ = lean_uint64_of_nat(v_idx_2114_);
v___x_2125_ = l_Lean_Expr_Data_hash(v___x_2116_);
v___x_2126_ = lean_uint64_mix_hash(v___x_2124_, v___x_2125_);
v___x_2127_ = lean_uint64_mix_hash(v___y_2123_, v___x_2126_);
v___x_2128_ = lean_uint64_mix_hash(v___x_2121_, v___x_2127_);
v___x_2129_ = l_Lean_Expr_Data_looseBVarRange(v___x_2116_);
v___x_2130_ = lean_uint32_to_nat(v___x_2129_);
v___x_2131_ = l_Lean_Expr_Data_hasFVar(v___x_2116_);
v___x_2132_ = l_Lean_Expr_Data_hasExprMVar(v___x_2116_);
v___x_2133_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2116_);
v___x_2134_ = l_Lean_Expr_Data_hasLevelParam(v___x_2116_);
v___x_2135_ = lean_expr_mk_data(v___x_2128_, v___x_2130_, v___x_2120_, v___x_2131_, v___x_2132_, v___x_2133_, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2136_, 0, v_typeName_2113_);
lean_ctor_set(v___x_2136_, 1, v_idx_2114_);
lean_ctor_set(v___x_2136_, 2, v_struct_2115_);
lean_ctor_set_uint64(v___x_2136_, sizeof(void*)*3, v___x_2135_);
return v___x_2136_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2139_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = 0;
return v___x_2140_;
}
else
{
lean_object* v_head_2141_; lean_object* v_tail_2142_; uint8_t v___x_2143_; 
v_head_2141_ = lean_ctor_get(v_x_2139_, 0);
v_tail_2142_ = lean_ctor_get(v_x_2139_, 1);
v___x_2143_ = l_Lean_Level_hasMVar(v_head_2141_);
if (v___x_2143_ == 0)
{
v_x_2139_ = v_tail_2142_;
goto _start;
}
else
{
return v___x_2143_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2145_);
lean_dec(v_x_2145_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2148_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
uint8_t v___x_2149_; 
v___x_2149_ = 0;
return v___x_2149_;
}
else
{
lean_object* v_head_2150_; lean_object* v_tail_2151_; uint8_t v___x_2152_; 
v_head_2150_ = lean_ctor_get(v_x_2148_, 0);
v_tail_2151_ = lean_ctor_get(v_x_2148_, 1);
v___x_2152_ = l_Lean_Level_hasParam(v_head_2150_);
if (v___x_2152_ == 0)
{
v_x_2148_ = v_tail_2151_;
goto _start;
}
else
{
return v___x_2152_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2154_){
_start:
{
uint8_t v_res_2155_; lean_object* v_r_2156_; 
v_res_2155_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2154_);
lean_dec(v_x_2154_);
v_r_2156_ = lean_box(v_res_2155_);
return v_r_2156_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2157_, lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
return v_x_2157_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; uint64_t v___x_2161_; uint64_t v___x_2162_; 
v_head_2159_ = lean_ctor_get(v_x_2158_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2158_, 1);
v___x_2161_ = l_Lean_Level_hash(v_head_2159_);
v___x_2162_ = lean_uint64_mix_hash(v_x_2157_, v___x_2161_);
v_x_2157_ = v___x_2162_;
v_x_2158_ = v_tail_2160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
uint64_t v_x_1729__boxed_2166_; uint64_t v_res_2167_; lean_object* v_r_2168_; 
v_x_1729__boxed_2166_ = lean_unbox_uint64(v_x_2164_);
lean_dec_ref(v_x_2164_);
v_res_2167_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1729__boxed_2166_, v_x_2165_);
lean_dec(v_x_2165_);
v_r_2168_ = lean_box_uint64(v_res_2167_);
return v_r_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2169_, lean_object* v_us_2170_){
_start:
{
uint64_t v___x_2171_; uint64_t v___y_2173_; 
v___x_2171_ = 5ULL;
if (lean_obj_tag(v_declName_2169_) == 0)
{
uint64_t v___x_2185_; 
v___x_2185_ = 1723ULL;
v___y_2173_ = v___x_2185_;
goto v___jp_2172_;
}
else
{
uint64_t v_hash_2186_; 
v_hash_2186_ = lean_ctor_get_uint64(v_declName_2169_, sizeof(void*)*2);
v___y_2173_ = v_hash_2186_;
goto v___jp_2172_;
}
v___jp_2172_:
{
uint64_t v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; uint64_t v___x_2177_; lean_object* v___x_2178_; uint32_t v___x_2179_; uint8_t v___x_2180_; uint8_t v___x_2181_; uint8_t v___x_2182_; uint64_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2174_ = 7ULL;
v___x_2175_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2174_, v_us_2170_);
v___x_2176_ = lean_uint64_mix_hash(v___y_2173_, v___x_2175_);
v___x_2177_ = lean_uint64_mix_hash(v___x_2171_, v___x_2176_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = 0;
v___x_2180_ = 0;
v___x_2181_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2170_);
v___x_2182_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2170_);
v___x_2183_ = lean_expr_mk_data(v___x_2177_, v___x_2178_, v___x_2179_, v___x_2180_, v___x_2180_, v___x_2181_, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2184_, 0, v_declName_2169_);
lean_ctor_set(v___x_2184_, 1, v_us_2170_);
lean_ctor_set_uint64(v___x_2184_, sizeof(void*)*2, v___x_2183_);
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = l_Lean_instReprLevel_repr(v___y_2187_, v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_dec(v_x_2190_);
return v_x_2191_;
}
else
{
lean_object* v_head_2193_; lean_object* v_tail_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2205_; 
v_head_2193_ = lean_ctor_get(v_x_2192_, 0);
v_tail_2194_ = lean_ctor_get(v_x_2192_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2196_ = v_x_2192_;
v_isShared_2197_ = v_isSharedCheck_2205_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_tail_2194_);
lean_inc(v_head_2193_);
lean_dec(v_x_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2205_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
lean_inc(v_x_2190_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 5);
lean_ctor_set(v___x_2196_, 1, v_x_2190_);
lean_ctor_set(v___x_2196_, 0, v_x_2191_);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_x_2191_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_x_2190_);
v___x_2199_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_Lean_instReprLevel_repr(v_head_2193_, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2199_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v_x_2191_ = v___x_2202_;
v_x_2192_ = v_tail_2194_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
if (lean_obj_tag(v_x_2208_) == 0)
{
lean_dec(v_x_2206_);
return v_x_2207_;
}
else
{
lean_object* v_head_2209_; lean_object* v_tail_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2221_; 
v_head_2209_ = lean_ctor_get(v_x_2208_, 0);
v_tail_2210_ = lean_ctor_get(v_x_2208_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_x_2208_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2212_ = v_x_2208_;
v_isShared_2213_ = v_isSharedCheck_2221_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_tail_2210_);
lean_inc(v_head_2209_);
lean_dec(v_x_2208_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2221_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
lean_inc(v_x_2206_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 5);
lean_ctor_set(v___x_2212_, 1, v_x_2206_);
lean_ctor_set(v___x_2212_, 0, v_x_2207_);
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_x_2207_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_x_2206_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = l_Lean_instReprLevel_repr(v_head_2209_, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2215_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2206_, v___x_2218_, v_tail_2210_);
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2222_, lean_object* v_x_2223_){
_start:
{
if (lean_obj_tag(v_x_2222_) == 0)
{
lean_object* v___x_2224_; 
lean_dec(v_x_2223_);
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
else
{
lean_object* v_tail_2225_; 
v_tail_2225_ = lean_ctor_get(v_x_2222_, 1);
if (lean_obj_tag(v_tail_2225_) == 0)
{
lean_object* v_head_2226_; lean_object* v___x_2227_; 
lean_dec(v_x_2223_);
v_head_2226_ = lean_ctor_get(v_x_2222_, 0);
lean_inc(v_head_2226_);
lean_dec_ref_known(v_x_2222_, 2);
v___x_2227_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2226_);
return v___x_2227_;
}
else
{
lean_object* v_head_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_inc(v_tail_2225_);
v_head_2228_ = lean_ctor_get(v_x_2222_, 0);
lean_inc(v_head_2228_);
lean_dec_ref_known(v_x_2222_, 2);
v___x_2229_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2228_);
v___x_2230_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2223_, v___x_2229_, v_tail_2225_);
return v___x_2230_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2243_ = lean_string_length(v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2245_ = lean_nat_to_int(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2250_){
_start:
{
if (lean_obj_tag(v_a_2250_) == 0)
{
lean_object* v___x_2251_; 
v___x_2251_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2251_;
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; 
v___x_2252_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2253_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2250_, v___x_2252_);
v___x_2254_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2255_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2253_);
v___x_2257_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2254_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = 0;
v___x_2261_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*1, v___x_2260_);
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2334_, lean_object* v_prec_2335_){
_start:
{
switch(lean_obj_tag(v_x_2334_))
{
case 0:
{
lean_object* v_deBruijnIndex_2336_; lean_object* v___y_2338_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_deBruijnIndex_2336_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_deBruijnIndex_2336_);
lean_dec_ref_known(v_x_2334_, 1);
v___x_2347_ = lean_unsigned_to_nat(1024u);
v___x_2348_ = lean_nat_dec_le(v___x_2347_, v_prec_2335_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2338_ = v___x_2349_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2338_ = v___x_2350_;
goto v___jp_2337_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2339_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2340_ = l_Nat_reprFast(v_deBruijnIndex_2336_);
v___x_2341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2339_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
lean_inc(v___y_2338_);
v___x_2343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___y_2338_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = 0;
v___x_2345_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*1, v___x_2344_);
v___x_2346_ = l_Repr_addAppParen(v___x_2345_, v_prec_2335_);
return v___x_2346_;
}
}
case 1:
{
lean_object* v_fvarId_2351_; lean_object* v___y_2353_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_fvarId_2351_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_fvarId_2351_);
lean_dec_ref_known(v_x_2334_, 1);
v___x_2362_ = lean_unsigned_to_nat(1024u);
v___x_2363_ = lean_nat_dec_le(v___x_2362_, v_prec_2335_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2353_ = v___x_2364_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2353_ = v___x_2365_;
goto v___jp_2352_;
}
v___jp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2354_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2355_ = lean_unsigned_to_nat(1024u);
v___x_2356_ = l_Lean_Name_reprPrec(v_fvarId_2351_, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
lean_inc(v___y_2353_);
v___x_2358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2353_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = 0;
v___x_2360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set_uint8(v___x_2360_, sizeof(void*)*1, v___x_2359_);
v___x_2361_ = l_Repr_addAppParen(v___x_2360_, v_prec_2335_);
return v___x_2361_;
}
}
case 2:
{
lean_object* v_mvarId_2366_; lean_object* v___y_2368_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_mvarId_2366_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_mvarId_2366_);
lean_dec_ref_known(v_x_2334_, 1);
v___x_2377_ = lean_unsigned_to_nat(1024u);
v___x_2378_ = lean_nat_dec_le(v___x_2377_, v_prec_2335_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2368_ = v___x_2379_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2368_ = v___x_2380_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2369_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2370_ = lean_unsigned_to_nat(1024u);
v___x_2371_ = l_Lean_Name_reprPrec(v_mvarId_2366_, v___x_2370_);
v___x_2372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2369_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
lean_inc(v___y_2368_);
v___x_2373_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___y_2368_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = 0;
v___x_2375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*1, v___x_2374_);
v___x_2376_ = l_Repr_addAppParen(v___x_2375_, v_prec_2335_);
return v___x_2376_;
}
}
case 3:
{
lean_object* v_u_2381_; lean_object* v___y_2383_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v_u_2381_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_u_2381_);
lean_dec_ref_known(v_x_2334_, 1);
v___x_2392_ = lean_unsigned_to_nat(1024u);
v___x_2393_ = lean_nat_dec_le(v___x_2392_, v_prec_2335_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2383_ = v___x_2394_;
goto v___jp_2382_;
}
else
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2383_ = v___x_2395_;
goto v___jp_2382_;
}
v___jp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2384_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2385_ = lean_unsigned_to_nat(1024u);
v___x_2386_ = l_Lean_instReprLevel_repr(v_u_2381_, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2384_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
lean_inc(v___y_2383_);
v___x_2388_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___y_2383_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = 0;
v___x_2390_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set_uint8(v___x_2390_, sizeof(void*)*1, v___x_2389_);
v___x_2391_ = l_Repr_addAppParen(v___x_2390_, v_prec_2335_);
return v___x_2391_;
}
}
case 4:
{
lean_object* v_declName_2396_; lean_object* v_us_2397_; lean_object* v___y_2399_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_declName_2396_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_declName_2396_);
v_us_2397_ = lean_ctor_get(v_x_2334_, 1);
lean_inc(v_us_2397_);
lean_dec_ref_known(v_x_2334_, 2);
v___x_2412_ = lean_unsigned_to_nat(1024u);
v___x_2413_ = lean_nat_dec_le(v___x_2412_, v_prec_2335_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2399_ = v___x_2414_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2399_ = v___x_2415_;
goto v___jp_2398_;
}
v___jp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2400_ = lean_box(1);
v___x_2401_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2402_ = lean_unsigned_to_nat(1024u);
v___x_2403_ = l_Lean_Name_reprPrec(v_declName_2396_, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2401_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2400_);
v___x_2406_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2397_);
v___x_2407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
lean_inc(v___y_2399_);
v___x_2408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___y_2399_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = 0;
v___x_2410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*1, v___x_2409_);
v___x_2411_ = l_Repr_addAppParen(v___x_2410_, v_prec_2335_);
return v___x_2411_;
}
}
case 5:
{
lean_object* v_fn_2416_; lean_object* v_arg_2417_; lean_object* v___x_2418_; lean_object* v___y_2420_; uint8_t v___x_2432_; 
v_fn_2416_ = lean_ctor_get(v_x_2334_, 0);
lean_inc_ref(v_fn_2416_);
v_arg_2417_ = lean_ctor_get(v_x_2334_, 1);
lean_inc_ref(v_arg_2417_);
lean_dec_ref_known(v_x_2334_, 2);
v___x_2418_ = lean_unsigned_to_nat(1024u);
v___x_2432_ = lean_nat_dec_le(v___x_2418_, v_prec_2335_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2420_ = v___x_2433_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2420_ = v___x_2434_;
goto v___jp_2419_;
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2421_ = lean_box(1);
v___x_2422_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2423_ = l_Lean_instReprExpr_repr(v_fn_2416_, v___x_2418_);
v___x_2424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v___x_2421_);
v___x_2426_ = l_Lean_instReprExpr_repr(v_arg_2417_, v___x_2418_);
v___x_2427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
lean_inc(v___y_2420_);
v___x_2428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2420_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = 0;
v___x_2430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set_uint8(v___x_2430_, sizeof(void*)*1, v___x_2429_);
v___x_2431_ = l_Repr_addAppParen(v___x_2430_, v_prec_2335_);
return v___x_2431_;
}
}
case 6:
{
lean_object* v_binderName_2435_; lean_object* v_binderType_2436_; lean_object* v_body_2437_; uint8_t v_binderInfo_2438_; lean_object* v___x_2439_; lean_object* v___y_2441_; uint8_t v___x_2459_; 
v_binderName_2435_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_binderName_2435_);
v_binderType_2436_ = lean_ctor_get(v_x_2334_, 1);
lean_inc_ref(v_binderType_2436_);
v_body_2437_ = lean_ctor_get(v_x_2334_, 2);
lean_inc_ref(v_body_2437_);
v_binderInfo_2438_ = lean_ctor_get_uint8(v_x_2334_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2334_, 3);
v___x_2439_ = lean_unsigned_to_nat(1024u);
v___x_2459_ = lean_nat_dec_le(v___x_2439_, v_prec_2335_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2441_ = v___x_2460_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2441_ = v___x_2461_;
goto v___jp_2440_;
}
v___jp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2442_ = lean_box(1);
v___x_2443_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2444_ = l_Lean_Name_reprPrec(v_binderName_2435_, v___x_2439_);
v___x_2445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v___x_2442_);
v___x_2447_ = l_Lean_instReprExpr_repr(v_binderType_2436_, v___x_2439_);
v___x_2448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_2442_);
v___x_2450_ = l_Lean_instReprExpr_repr(v_body_2437_, v___x_2439_);
v___x_2451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___x_2442_);
v___x_2453_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2438_, v___x_2439_);
v___x_2454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
lean_inc(v___y_2441_);
v___x_2455_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___y_2441_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = 0;
v___x_2457_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*1, v___x_2456_);
v___x_2458_ = l_Repr_addAppParen(v___x_2457_, v_prec_2335_);
return v___x_2458_;
}
}
case 7:
{
lean_object* v_binderName_2462_; lean_object* v_binderType_2463_; lean_object* v_body_2464_; uint8_t v_binderInfo_2465_; lean_object* v___x_2466_; lean_object* v___y_2468_; uint8_t v___x_2486_; 
v_binderName_2462_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_binderName_2462_);
v_binderType_2463_ = lean_ctor_get(v_x_2334_, 1);
lean_inc_ref(v_binderType_2463_);
v_body_2464_ = lean_ctor_get(v_x_2334_, 2);
lean_inc_ref(v_body_2464_);
v_binderInfo_2465_ = lean_ctor_get_uint8(v_x_2334_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2334_, 3);
v___x_2466_ = lean_unsigned_to_nat(1024u);
v___x_2486_ = lean_nat_dec_le(v___x_2466_, v_prec_2335_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2468_ = v___x_2487_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2468_ = v___x_2488_;
goto v___jp_2467_;
}
v___jp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2469_ = lean_box(1);
v___x_2470_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2471_ = l_Lean_Name_reprPrec(v_binderName_2462_, v___x_2466_);
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2469_);
v___x_2474_ = l_Lean_instReprExpr_repr(v_binderType_2463_, v___x_2466_);
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2469_);
v___x_2477_ = l_Lean_instReprExpr_repr(v_body_2464_, v___x_2466_);
v___x_2478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2469_);
v___x_2480_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2465_, v___x_2466_);
v___x_2481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
lean_inc(v___y_2468_);
v___x_2482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___y_2468_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = 0;
v___x_2484_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*1, v___x_2483_);
v___x_2485_ = l_Repr_addAppParen(v___x_2484_, v_prec_2335_);
return v___x_2485_;
}
}
case 8:
{
lean_object* v_declName_2489_; lean_object* v_type_2490_; lean_object* v_value_2491_; lean_object* v_body_2492_; uint8_t v_nondep_2493_; lean_object* v___x_2494_; lean_object* v___y_2496_; uint8_t v___x_2517_; 
v_declName_2489_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_declName_2489_);
v_type_2490_ = lean_ctor_get(v_x_2334_, 1);
lean_inc_ref(v_type_2490_);
v_value_2491_ = lean_ctor_get(v_x_2334_, 2);
lean_inc_ref(v_value_2491_);
v_body_2492_ = lean_ctor_get(v_x_2334_, 3);
lean_inc_ref(v_body_2492_);
v_nondep_2493_ = lean_ctor_get_uint8(v_x_2334_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2334_, 4);
v___x_2494_ = lean_unsigned_to_nat(1024u);
v___x_2517_ = lean_nat_dec_le(v___x_2494_, v_prec_2335_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2496_ = v___x_2518_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2496_ = v___x_2519_;
goto v___jp_2495_;
}
v___jp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2497_ = lean_box(1);
v___x_2498_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2499_ = l_Lean_Name_reprPrec(v_declName_2489_, v___x_2494_);
v___x_2500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2497_);
v___x_2502_ = l_Lean_instReprExpr_repr(v_type_2490_, v___x_2494_);
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2497_);
v___x_2505_ = l_Lean_instReprExpr_repr(v_value_2491_, v___x_2494_);
v___x_2506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2497_);
v___x_2508_ = l_Lean_instReprExpr_repr(v_body_2492_, v___x_2494_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2497_);
v___x_2511_ = l_Bool_repr___redArg(v_nondep_2493_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_inc(v___y_2496_);
v___x_2513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2496_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2514_);
v___x_2516_ = l_Repr_addAppParen(v___x_2515_, v_prec_2335_);
return v___x_2516_;
}
}
case 9:
{
lean_object* v_a_2520_; lean_object* v___y_2522_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_a_2520_ = lean_ctor_get(v_x_2334_, 0);
lean_inc_ref(v_a_2520_);
lean_dec_ref_known(v_x_2334_, 1);
v___x_2531_ = lean_unsigned_to_nat(1024u);
v___x_2532_ = lean_nat_dec_le(v___x_2531_, v_prec_2335_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2522_ = v___x_2533_;
goto v___jp_2521_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2522_ = v___x_2534_;
goto v___jp_2521_;
}
v___jp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2523_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2524_ = lean_unsigned_to_nat(1024u);
v___x_2525_ = l_Lean_instReprLiteral_repr(v_a_2520_, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2523_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
lean_inc(v___y_2522_);
v___x_2527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___y_2522_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = 0;
v___x_2529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set_uint8(v___x_2529_, sizeof(void*)*1, v___x_2528_);
v___x_2530_ = l_Repr_addAppParen(v___x_2529_, v_prec_2335_);
return v___x_2530_;
}
}
case 10:
{
lean_object* v_data_2535_; lean_object* v_expr_2536_; lean_object* v___x_2537_; lean_object* v___y_2539_; uint8_t v___x_2551_; 
v_data_2535_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_data_2535_);
v_expr_2536_ = lean_ctor_get(v_x_2334_, 1);
lean_inc_ref(v_expr_2536_);
lean_dec_ref_known(v_x_2334_, 2);
v___x_2537_ = lean_unsigned_to_nat(1024u);
v___x_2551_ = lean_nat_dec_le(v___x_2537_, v_prec_2335_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2539_ = v___x_2552_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2539_ = v___x_2553_;
goto v___jp_2538_;
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2540_ = lean_box(1);
v___x_2541_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2542_ = l_Lean_instReprKVMap_repr___redArg(v_data_2535_);
v___x_2543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2540_);
v___x_2545_ = l_Lean_instReprExpr_repr(v_expr_2536_, v___x_2537_);
v___x_2546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
lean_inc(v___y_2539_);
v___x_2547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___y_2539_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = 0;
v___x_2549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set_uint8(v___x_2549_, sizeof(void*)*1, v___x_2548_);
v___x_2550_ = l_Repr_addAppParen(v___x_2549_, v_prec_2335_);
return v___x_2550_;
}
}
default: 
{
lean_object* v_typeName_2554_; lean_object* v_idx_2555_; lean_object* v_struct_2556_; lean_object* v___x_2557_; lean_object* v___y_2559_; uint8_t v___x_2575_; 
v_typeName_2554_ = lean_ctor_get(v_x_2334_, 0);
lean_inc(v_typeName_2554_);
v_idx_2555_ = lean_ctor_get(v_x_2334_, 1);
lean_inc(v_idx_2555_);
v_struct_2556_ = lean_ctor_get(v_x_2334_, 2);
lean_inc_ref(v_struct_2556_);
lean_dec_ref_known(v_x_2334_, 3);
v___x_2557_ = lean_unsigned_to_nat(1024u);
v___x_2575_ = lean_nat_dec_le(v___x_2557_, v_prec_2335_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2559_ = v___x_2576_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2559_ = v___x_2577_;
goto v___jp_2558_;
}
v___jp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2560_ = lean_box(1);
v___x_2561_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2562_ = l_Lean_Name_reprPrec(v_typeName_2554_, v___x_2557_);
v___x_2563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v___x_2560_);
v___x_2565_ = l_Nat_reprFast(v_idx_2555_);
v___x_2566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2564_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2560_);
v___x_2569_ = l_Lean_instReprExpr_repr(v_struct_2556_, v___x_2557_);
v___x_2570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
lean_inc(v___y_2559_);
v___x_2571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2559_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = 0;
v___x_2573_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*1, v___x_2572_);
v___x_2574_ = l_Repr_addAppParen(v___x_2573_, v_prec_2335_);
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2578_, lean_object* v_prec_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_instReprExpr_repr(v_x_2578_, v_prec_2579_);
lean_dec(v_prec_2579_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_nat_to_int(v_a_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2583_, lean_object* v_n_2584_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2586_, lean_object* v_n_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2586_, v_n_2587_);
lean_dec(v_n_2587_);
return v_res_2588_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2596_ = l_Lean_Expr_const___override(v___x_2595_, v___x_2594_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2610_){
_start:
{
switch(lean_obj_tag(v_x_2610_))
{
case 0:
{
lean_object* v___x_2611_; 
v___x_2611_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2611_;
}
case 1:
{
lean_object* v___x_2612_; 
v___x_2612_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2612_;
}
case 2:
{
lean_object* v___x_2613_; 
v___x_2613_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2613_;
}
case 3:
{
lean_object* v___x_2614_; 
v___x_2614_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2614_;
}
case 4:
{
lean_object* v___x_2615_; 
v___x_2615_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2615_;
}
case 5:
{
lean_object* v___x_2616_; 
v___x_2616_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2616_;
}
case 6:
{
lean_object* v___x_2617_; 
v___x_2617_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2617_;
}
case 7:
{
lean_object* v___x_2618_; 
v___x_2618_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2618_;
}
case 8:
{
lean_object* v___x_2619_; 
v___x_2619_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2619_;
}
case 9:
{
lean_object* v___x_2620_; 
v___x_2620_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2620_;
}
case 10:
{
lean_object* v___x_2621_; 
v___x_2621_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2621_;
}
default: 
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Expr_ctorName(v_x_2623_);
lean_dec_ref(v_x_2623_);
return v_res_2624_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2625_){
_start:
{
uint64_t v___x_2626_; uint64_t v___x_2627_; 
v___x_2626_ = lean_expr_data(v_e_2625_);
v___x_2627_ = l_Lean_Expr_Data_hash(v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2628_){
_start:
{
uint64_t v_res_2629_; lean_object* v_r_2630_; 
v_res_2629_ = l_Lean_Expr_hash(v_e_2628_);
lean_dec_ref(v_e_2628_);
v_r_2630_ = lean_box_uint64(v_res_2629_);
return v_r_2630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2633_){
_start:
{
uint64_t v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_expr_data(v_e_2633_);
v___x_2635_ = l_Lean_Expr_Data_hasFVar(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2636_){
_start:
{
uint8_t v_res_2637_; lean_object* v_r_2638_; 
v_res_2637_ = l_Lean_Expr_hasFVar(v_e_2636_);
lean_dec_ref(v_e_2636_);
v_r_2638_ = lean_box(v_res_2637_);
return v_r_2638_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2639_){
_start:
{
uint64_t v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = lean_expr_data(v_e_2639_);
v___x_2641_ = l_Lean_Expr_Data_hasExprMVar(v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Lean_Expr_hasExprMVar(v_e_2642_);
lean_dec_ref(v_e_2642_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2645_){
_start:
{
uint64_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = lean_expr_data(v_e_2645_);
v___x_2647_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2648_){
_start:
{
uint8_t v_res_2649_; lean_object* v_r_2650_; 
v_res_2649_ = l_Lean_Expr_hasLevelMVar(v_e_2648_);
lean_dec_ref(v_e_2648_);
v_r_2650_ = lean_box(v_res_2649_);
return v_r_2650_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2651_){
_start:
{
uint64_t v_d_2652_; uint8_t v___x_2653_; 
v_d_2652_ = lean_expr_data(v_e_2651_);
v___x_2653_ = l_Lean_Expr_Data_hasExprMVar(v_d_2652_);
if (v___x_2653_ == 0)
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2652_);
return v___x_2654_;
}
else
{
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Lean_Expr_hasMVar(v_e_2655_);
lean_dec_ref(v_e_2655_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2658_){
_start:
{
uint64_t v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = lean_expr_data(v_e_2658_);
v___x_2660_ = l_Lean_Expr_Data_hasLevelParam(v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2661_){
_start:
{
uint8_t v_res_2662_; lean_object* v_r_2663_; 
v_res_2662_ = l_Lean_Expr_hasLevelParam(v_e_2661_);
lean_dec_ref(v_e_2661_);
v_r_2663_ = lean_box(v_res_2662_);
return v_r_2663_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2664_){
_start:
{
uint64_t v___x_2665_; uint8_t v___x_2666_; uint32_t v___x_2667_; 
v___x_2665_ = lean_expr_data(v_e_2664_);
v___x_2666_ = l_Lean_Expr_Data_approxDepth(v___x_2665_);
v___x_2667_ = lean_uint8_to_uint32(v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2668_){
_start:
{
uint32_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Lean_Expr_approxDepth(v_e_2668_);
lean_dec_ref(v_e_2668_);
v_r_2670_ = lean_box_uint32(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2671_){
_start:
{
uint64_t v___x_2672_; uint32_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_expr_data(v_e_2671_);
v___x_2673_ = l_Lean_Expr_Data_looseBVarRange(v___x_2672_);
v___x_2674_ = lean_uint32_to_nat(v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Expr_looseBVarRange(v_e_2675_);
lean_dec_ref(v_e_2675_);
return v_res_2676_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2677_){
_start:
{
switch(lean_obj_tag(v_e_2677_))
{
case 7:
{
uint8_t v_binderInfo_2678_; 
v_binderInfo_2678_ = lean_ctor_get_uint8(v_e_2677_, sizeof(void*)*3 + 8);
return v_binderInfo_2678_;
}
case 6:
{
uint8_t v_binderInfo_2679_; 
v_binderInfo_2679_ = lean_ctor_get_uint8(v_e_2677_, sizeof(void*)*3 + 8);
return v_binderInfo_2679_;
}
default: 
{
uint8_t v___x_2680_; 
v___x_2680_ = 0;
return v___x_2680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2681_){
_start:
{
uint8_t v_res_2682_; lean_object* v_r_2683_; 
v_res_2682_ = l_Lean_Expr_binderInfo(v_e_2681_);
lean_dec_ref(v_e_2681_);
v_r_2683_ = lean_box(v_res_2682_);
return v_r_2683_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2684_){
_start:
{
uint64_t v___x_2685_; 
v___x_2685_ = l_Lean_Expr_hash(v_a_2684_);
lean_dec_ref(v_a_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2686_){
_start:
{
uint64_t v_res_2687_; lean_object* v_r_2688_; 
v_res_2687_ = lean_expr_hash(v_a_2686_);
v_r_2688_ = lean_box_uint64(v_res_2687_);
return v_r_2688_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2689_){
_start:
{
uint8_t v___x_2690_; 
v___x_2690_ = l_Lean_Expr_hasFVar(v_e_2689_);
lean_dec_ref(v_e_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2691_){
_start:
{
uint8_t v_res_2692_; lean_object* v_r_2693_; 
v_res_2692_ = lean_expr_has_fvar(v_e_2691_);
v_r_2693_ = lean_box(v_res_2692_);
return v_r_2693_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2694_){
_start:
{
uint8_t v___x_2695_; 
v___x_2695_ = l_Lean_Expr_hasExprMVar(v_e_2694_);
lean_dec_ref(v_e_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2696_){
_start:
{
uint8_t v_res_2697_; lean_object* v_r_2698_; 
v_res_2697_ = lean_expr_has_expr_mvar(v_e_2696_);
v_r_2698_ = lean_box(v_res_2697_);
return v_r_2698_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2699_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = l_Lean_Expr_hasLevelMVar(v_e_2699_);
lean_dec_ref(v_e_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2701_){
_start:
{
uint8_t v_res_2702_; lean_object* v_r_2703_; 
v_res_2702_ = lean_expr_has_level_mvar(v_e_2701_);
v_r_2703_ = lean_box(v_res_2702_);
return v_r_2703_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2704_){
_start:
{
uint8_t v___x_2705_; 
v___x_2705_ = l_Lean_Expr_hasLevelParam(v_e_2704_);
lean_dec_ref(v_e_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2706_){
_start:
{
uint8_t v_res_2707_; lean_object* v_r_2708_; 
v_res_2707_ = lean_expr_has_level_param(v_e_2706_);
v_r_2708_ = lean_box(v_res_2707_);
return v_r_2708_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2709_){
_start:
{
uint64_t v___x_2710_; uint32_t v___x_2711_; 
v___x_2710_ = lean_expr_data(v_e_2709_);
lean_dec_ref(v_e_2709_);
v___x_2711_ = l_Lean_Expr_Data_looseBVarRange(v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2712_){
_start:
{
uint32_t v_res_2713_; lean_object* v_r_2714_; 
v_res_2713_ = lean_expr_loose_bvar_range(v_e_2712_);
v_r_2714_ = lean_box_uint32(v_res_2713_);
return v_r_2714_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_Expr_binderInfo(v_e_2715_);
lean_dec_ref(v_e_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2717_){
_start:
{
uint8_t v_res_2718_; lean_object* v_r_2719_; 
v_res_2718_ = lean_expr_binder_info(v_e_2717_);
v_r_2719_ = lean_box(v_res_2718_);
return v_r_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2720_, lean_object* v_us_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Expr_const___override(v_declName_2720_, v_us_2721_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_box(0);
v___x_2727_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2728_ = l_Lean_Expr_const___override(v___x_2727_, v___x_2726_);
return v___x_2728_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = lean_box(0);
v___x_2733_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2734_ = l_Lean_Expr_const___override(v___x_2733_, v___x_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2735_){
_start:
{
if (lean_obj_tag(v_x_2735_) == 0)
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2736_;
}
else
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Literal_type(v_x_2738_);
lean_dec_ref(v_x_2738_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Literal_type(v_a_2740_);
lean_dec_ref(v_a_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_Expr_bvar___override(v_idx_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Expr_sort___override(v_u_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Expr_fvar___override(v_fvarId_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Expr_mvar___override(v_mvarId_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2750_, lean_object* v_e_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Expr_mdata___override(v_m_2750_, v_e_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2753_, lean_object* v_idx_2754_, lean_object* v_struct_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_Expr_proj___override(v_structName_2753_, v_idx_2754_, v_struct_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Expr_app___override(v_f_2757_, v_a_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2760_, uint8_t v_bi_2761_, lean_object* v_t_2762_, lean_object* v_b_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Expr_lam___override(v_x_2760_, v_t_2762_, v_b_2763_, v_bi_2761_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2765_, lean_object* v_bi_2766_, lean_object* v_t_2767_, lean_object* v_b_2768_){
_start:
{
uint8_t v_bi_boxed_2769_; lean_object* v_res_2770_; 
v_bi_boxed_2769_ = lean_unbox(v_bi_2766_);
v_res_2770_ = l_Lean_mkLambda(v_x_2765_, v_bi_boxed_2769_, v_t_2767_, v_b_2768_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2771_, uint8_t v_bi_2772_, lean_object* v_t_2773_, lean_object* v_b_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Expr_forallE___override(v_x_2771_, v_t_2773_, v_b_2774_, v_bi_2772_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2776_, lean_object* v_bi_2777_, lean_object* v_t_2778_, lean_object* v_b_2779_){
_start:
{
uint8_t v_bi_boxed_2780_; lean_object* v_res_2781_; 
v_bi_boxed_2780_ = lean_unbox(v_bi_2777_);
v_res_2781_ = l_Lean_mkForall(v_x_2776_, v_bi_boxed_2780_, v_t_2778_, v_b_2779_);
return v_res_2781_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_box(0);
v___x_2789_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2790_ = l_Lean_Expr_const___override(v___x_2789_, v___x_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2791_){
_start:
{
lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2793_ = 0;
v___x_2794_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2795_ = l_Lean_Expr_forallE___override(v___x_2792_, v___x_2794_, v_type_2791_, v___x_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2796_){
_start:
{
lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2797_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2798_ = 0;
v___x_2799_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2800_ = l_Lean_Expr_lam___override(v___x_2797_, v___x_2799_, v_type_2796_, v___x_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2801_, lean_object* v_t_2802_, lean_object* v_v_2803_, lean_object* v_b_2804_, uint8_t v_nondep_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Lean_Expr_letE___override(v_x_2801_, v_t_2802_, v_v_2803_, v_b_2804_, v_nondep_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2807_, lean_object* v_t_2808_, lean_object* v_v_2809_, lean_object* v_b_2810_, lean_object* v_nondep_2811_){
_start:
{
uint8_t v_nondep_boxed_2812_; lean_object* v_res_2813_; 
v_nondep_boxed_2812_ = lean_unbox(v_nondep_2811_);
v_res_2813_ = l_Lean_mkLet(v_x_2807_, v_t_2808_, v_v_2809_, v_b_2810_, v_nondep_boxed_2812_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2814_, lean_object* v_t_2815_, lean_object* v_v_2816_, lean_object* v_b_2817_){
_start:
{
uint8_t v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = 1;
v___x_2819_ = l_Lean_Expr_letE___override(v_x_2814_, v_t_2815_, v_v_2816_, v_b_2817_, v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2820_, lean_object* v_a_2821_, lean_object* v_b_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = l_Lean_Expr_app___override(v_f_2820_, v_a_2821_);
v___x_2824_ = l_Lean_Expr_app___override(v___x_2823_, v_b_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_mkAppB(v_f_2825_, v_a_2826_, v_b_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_, lean_object* v_c_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = l_Lean_mkAppB(v_f_2829_, v_a_2830_, v_b_2831_);
v___x_2834_ = l_Lean_Expr_app___override(v___x_2833_, v_c_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2835_, lean_object* v_a_2836_, lean_object* v_b_2837_, lean_object* v_c_2838_, lean_object* v_d_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = l_Lean_mkAppB(v_f_2835_, v_a_2836_, v_b_2837_);
v___x_2841_ = l_Lean_mkAppB(v___x_2840_, v_c_2838_, v_d_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2842_, lean_object* v_a_2843_, lean_object* v_b_2844_, lean_object* v_c_2845_, lean_object* v_d_2846_, lean_object* v_e_2847_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = l_Lean_mkApp4(v_f_2842_, v_a_2843_, v_b_2844_, v_c_2845_, v_d_2846_);
v___x_2849_ = l_Lean_Expr_app___override(v___x_2848_, v_e_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2850_, lean_object* v_a_2851_, lean_object* v_b_2852_, lean_object* v_c_2853_, lean_object* v_d_2854_, lean_object* v_e_u2081_2855_, lean_object* v_e_u2082_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = l_Lean_mkApp4(v_f_2850_, v_a_2851_, v_b_2852_, v_c_2853_, v_d_2854_);
v___x_2858_ = l_Lean_mkAppB(v___x_2857_, v_e_u2081_2855_, v_e_u2082_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_, lean_object* v_c_2862_, lean_object* v_d_2863_, lean_object* v_e_u2081_2864_, lean_object* v_e_u2082_2865_, lean_object* v_e_u2083_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = l_Lean_mkApp4(v_f_2859_, v_a_2860_, v_b_2861_, v_c_2862_, v_d_2863_);
v___x_2868_ = l_Lean_mkApp3(v___x_2867_, v_e_u2081_2864_, v_e_u2082_2865_, v_e_u2083_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2869_, lean_object* v_a_2870_, lean_object* v_b_2871_, lean_object* v_c_2872_, lean_object* v_d_2873_, lean_object* v_e_u2081_2874_, lean_object* v_e_u2082_2875_, lean_object* v_e_u2083_2876_, lean_object* v_e_u2084_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = l_Lean_mkApp4(v_f_2869_, v_a_2870_, v_b_2871_, v_c_2872_, v_d_2873_);
v___x_2879_ = l_Lean_mkApp4(v___x_2878_, v_e_u2081_2874_, v_e_u2082_2875_, v_e_u2083_2876_, v_e_u2084_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_, lean_object* v_c_2883_, lean_object* v_d_2884_, lean_object* v_e_u2081_2885_, lean_object* v_e_u2082_2886_, lean_object* v_e_u2083_2887_, lean_object* v_e_u2084_2888_, lean_object* v_e_u2085_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = l_Lean_mkApp4(v_f_2880_, v_a_2881_, v_b_2882_, v_c_2883_, v_d_2884_);
v___x_2891_ = l_Lean_mkApp5(v___x_2890_, v_e_u2081_2885_, v_e_u2082_2886_, v_e_u2083_2887_, v_e_u2084_2888_, v_e_u2085_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2892_, lean_object* v_a_2893_, lean_object* v_b_2894_, lean_object* v_c_2895_, lean_object* v_d_2896_, lean_object* v_e_u2081_2897_, lean_object* v_e_u2082_2898_, lean_object* v_e_u2083_2899_, lean_object* v_e_u2084_2900_, lean_object* v_e_u2085_2901_, lean_object* v_e_u2086_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = l_Lean_mkApp4(v_f_2892_, v_a_2893_, v_b_2894_, v_c_2895_, v_d_2896_);
v___x_2904_ = l_Lean_mkApp6(v___x_2903_, v_e_u2081_2897_, v_e_u2082_2898_, v_e_u2083_2899_, v_e_u2084_2900_, v_e_u2085_2901_, v_e_u2086_2902_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Expr_lit___override(v_l_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2907_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_n_2907_);
v___x_2909_ = l_Lean_Expr_lit___override(v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = lean_box(0);
v___x_2914_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2915_ = l_Lean_Expr_const___override(v___x_2914_, v___x_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2918_ = l_Lean_Expr_app___override(v___x_2917_, v_n_2916_);
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2928_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2929_ = l_Lean_Expr_const___override(v___x_2928_, v___x_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2930_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2931_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2932_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2930_);
v___x_2933_ = l_Lean_mkInstOfNatNat(v_n_2930_);
v___x_2934_ = l_Lean_mkApp3(v___x_2931_, v___x_2932_, v_n_2930_, v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = l_Lean_mkRawNatLit(v_n_2935_);
v___x_2937_ = l_Lean_mkNatLitCore(v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_s_2938_);
v___x_2940_ = l_Lean_Expr_lit___override(v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Expr_bvar___override(v_idx_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Expr_fvar___override(v_fvarId_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* v_mvarId_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Expr_mvar___override(v_mvarId_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Expr_sort___override(v_u_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2949_, lean_object* v_lvls_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_Expr_const___override(v_c_2949_, v_lvls_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Expr_app___override(v_f_2952_, v_a_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2955_, lean_object* v_d_2956_, lean_object* v_b_2957_, uint8_t v_bi_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Expr_lam___override(v_n_2955_, v_d_2956_, v_b_2957_, v_bi_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2960_, lean_object* v_d_2961_, lean_object* v_b_2962_, lean_object* v_bi_2963_){
_start:
{
uint8_t v_bi_boxed_2964_; lean_object* v_res_2965_; 
v_bi_boxed_2964_ = lean_unbox(v_bi_2963_);
v_res_2965_ = lean_expr_mk_lambda(v_n_2960_, v_d_2961_, v_b_2962_, v_bi_boxed_2964_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2966_, lean_object* v_d_2967_, lean_object* v_b_2968_, uint8_t v_bi_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Expr_forallE___override(v_n_2966_, v_d_2967_, v_b_2968_, v_bi_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2971_, lean_object* v_d_2972_, lean_object* v_b_2973_, lean_object* v_bi_2974_){
_start:
{
uint8_t v_bi_boxed_2975_; lean_object* v_res_2976_; 
v_bi_boxed_2975_ = lean_unbox(v_bi_2974_);
v_res_2976_ = lean_expr_mk_forall(v_n_2971_, v_d_2972_, v_b_2973_, v_bi_boxed_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2977_, lean_object* v_t_2978_, lean_object* v_v_2979_, lean_object* v_b_2980_, uint8_t v_nondep_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Expr_letE___override(v_n_2977_, v_t_2978_, v_v_2979_, v_b_2980_, v_nondep_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2983_, lean_object* v_t_2984_, lean_object* v_v_2985_, lean_object* v_b_2986_, lean_object* v_nondep_2987_){
_start:
{
uint8_t v_nondep_boxed_2988_; lean_object* v_res_2989_; 
v_nondep_boxed_2988_ = lean_unbox(v_nondep_2987_);
v_res_2989_ = lean_expr_mk_let(v_n_2983_, v_t_2984_, v_v_2985_, v_b_2986_, v_nondep_boxed_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_Expr_lit___override(v_l_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2992_, lean_object* v_e_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_Expr_mdata___override(v_m_2992_, v_e_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2995_, lean_object* v_idx_2996_, lean_object* v_struct_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Expr_proj___override(v_structName_2995_, v_idx_2996_, v_struct_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_2999_, size_t v_i_3000_, size_t v_stop_3001_, lean_object* v_b_3002_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_usize_dec_eq(v_i_3000_, v_stop_3001_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; size_t v___x_3006_; size_t v___x_3007_; 
v___x_3004_ = lean_array_uget_borrowed(v_as_2999_, v_i_3000_);
lean_inc(v___x_3004_);
v___x_3005_ = l_Lean_Expr_app___override(v_b_3002_, v___x_3004_);
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = lean_usize_add(v_i_3000_, v___x_3006_);
v_i_3000_ = v___x_3007_;
v_b_3002_ = v___x_3005_;
goto _start;
}
else
{
return v_b_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_3009_, lean_object* v_i_3010_, lean_object* v_stop_3011_, lean_object* v_b_3012_){
_start:
{
size_t v_i_boxed_3013_; size_t v_stop_boxed_3014_; lean_object* v_res_3015_; 
v_i_boxed_3013_ = lean_unbox_usize(v_i_3010_);
lean_dec(v_i_3010_);
v_stop_boxed_3014_ = lean_unbox_usize(v_stop_3011_);
lean_dec(v_stop_3011_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_3009_, v_i_boxed_3013_, v_stop_boxed_3014_, v_b_3012_);
lean_dec_ref(v_as_3009_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_3016_, lean_object* v_args_3017_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_array_get_size(v_args_3017_);
v___x_3020_ = lean_nat_dec_lt(v___x_3018_, v___x_3019_);
if (v___x_3020_ == 0)
{
return v_f_3016_;
}
else
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_nat_dec_le(v___x_3019_, v___x_3019_);
if (v___x_3021_ == 0)
{
if (v___x_3020_ == 0)
{
return v_f_3016_;
}
else
{
size_t v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = ((size_t)0ULL);
v___x_3023_ = lean_usize_of_nat(v___x_3019_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3017_, v___x_3022_, v___x_3023_, v_f_3016_);
return v___x_3024_;
}
}
else
{
size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((size_t)0ULL);
v___x_3026_ = lean_usize_of_nat(v___x_3019_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_3017_, v___x_3025_, v___x_3026_, v_f_3016_);
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_3028_, lean_object* v_args_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_mkAppN(v_f_3028_, v_args_3029_);
lean_dec_ref(v_args_3029_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_3031_, lean_object* v_args_3032_, lean_object* v_i_3033_, lean_object* v_e_3034_){
_start:
{
uint8_t v___x_3035_; 
v___x_3035_ = lean_nat_dec_lt(v_i_3033_, v_n_3031_);
if (v___x_3035_ == 0)
{
lean_dec(v_i_3033_);
return v_e_3034_;
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_add(v_i_3033_, v___x_3036_);
v___x_3038_ = l_Lean_instInhabitedExpr;
v___x_3039_ = lean_array_get_borrowed(v___x_3038_, v_args_3032_, v_i_3033_);
lean_dec(v_i_3033_);
lean_inc(v___x_3039_);
v___x_3040_ = l_Lean_Expr_app___override(v_e_3034_, v___x_3039_);
v_i_3033_ = v___x_3037_;
v_e_3034_ = v___x_3040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3042_, lean_object* v_args_3043_, lean_object* v_i_3044_, lean_object* v_e_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3042_, v_args_3043_, v_i_3044_, v_e_3045_);
lean_dec_ref(v_args_3043_);
lean_dec(v_n_3042_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3047_, lean_object* v_i_3048_, lean_object* v_j_3049_, lean_object* v_args_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3049_, v_args_3050_, v_i_3048_, v_f_3047_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3052_, lean_object* v_i_3053_, lean_object* v_j_3054_, lean_object* v_args_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_mkAppRange(v_f_3052_, v_i_3053_, v_j_3054_, v_args_3055_);
lean_dec_ref(v_args_3055_);
lean_dec(v_j_3054_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3057_, size_t v_i_3058_, size_t v_stop_3059_, lean_object* v_b_3060_){
_start:
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_usize_dec_eq(v_i_3058_, v_stop_3059_);
if (v___x_3061_ == 0)
{
size_t v___x_3062_; size_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_sub(v_i_3058_, v___x_3062_);
v___x_3064_ = lean_array_uget_borrowed(v_as_3057_, v___x_3063_);
lean_inc(v___x_3064_);
v___x_3065_ = l_Lean_Expr_app___override(v_b_3060_, v___x_3064_);
v_i_3058_ = v___x_3063_;
v_b_3060_ = v___x_3065_;
goto _start;
}
else
{
return v_b_3060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3067_, lean_object* v_i_3068_, lean_object* v_stop_3069_, lean_object* v_b_3070_){
_start:
{
size_t v_i_boxed_3071_; size_t v_stop_boxed_3072_; lean_object* v_res_3073_; 
v_i_boxed_3071_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_stop_boxed_3072_ = lean_unbox_usize(v_stop_3069_);
lean_dec(v_stop_3069_);
v_res_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3067_, v_i_boxed_3071_, v_stop_boxed_3072_, v_b_3070_);
lean_dec_ref(v_as_3067_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3074_, lean_object* v_revArgs_3075_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3076_ = lean_array_get_size(v_revArgs_3075_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = lean_nat_dec_lt(v___x_3077_, v___x_3076_);
if (v___x_3078_ == 0)
{
return v_fn_3074_;
}
else
{
size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_usize_of_nat(v___x_3076_);
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3075_, v___x_3079_, v___x_3080_, v_fn_3074_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3082_, lean_object* v_revArgs_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_mkAppRev(v_fn_3082_, v_revArgs_3083_);
lean_dec_ref(v_revArgs_3083_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = lean_expr_dbg_to_string(v_e_3086_);
lean_dec_ref(v_e_3086_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3090_, lean_object* v_b_3091_){
_start:
{
uint8_t v_res_3092_; lean_object* v_r_3093_; 
v_res_3092_ = lean_expr_quick_lt(v_a_3090_, v_b_3091_);
lean_dec_ref(v_b_3091_);
lean_dec_ref(v_a_3090_);
v_r_3093_ = lean_box(v_res_3092_);
return v_r_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3096_, lean_object* v_b_3097_){
_start:
{
uint8_t v_res_3098_; lean_object* v_r_3099_; 
v_res_3098_ = lean_expr_lt(v_a_3096_, v_b_3097_);
lean_dec_ref(v_b_3097_);
lean_dec_ref(v_a_3096_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3100_, lean_object* v_b_3101_){
_start:
{
uint8_t v___x_3102_; 
v___x_3102_ = lean_expr_quick_lt(v_a_3100_, v_b_3101_);
if (v___x_3102_ == 0)
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_expr_quick_lt(v_b_3101_, v_a_3100_);
if (v___x_3103_ == 0)
{
uint8_t v___x_3104_; 
v___x_3104_ = 1;
return v___x_3104_;
}
else
{
uint8_t v___x_3105_; 
v___x_3105_ = 2;
return v___x_3105_;
}
}
else
{
uint8_t v___x_3106_; 
v___x_3106_ = 0;
return v___x_3106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3107_, lean_object* v_b_3108_){
_start:
{
uint8_t v_res_3109_; lean_object* v_r_3110_; 
v_res_3109_ = l_Lean_Expr_quickComp(v_a_3107_, v_b_3108_);
lean_dec_ref(v_b_3108_);
lean_dec_ref(v_a_3107_);
v_r_3110_ = lean_box(v_res_3109_);
return v_r_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3113_, lean_object* v_b_3114_){
_start:
{
uint8_t v_res_3115_; lean_object* v_r_3116_; 
v_res_3115_ = lean_expr_eqv(v_a_3113_, v_b_3114_);
lean_dec_ref(v_b_3114_);
lean_dec_ref(v_a_3113_);
v_r_3116_ = lean_box(v_res_3115_);
return v_r_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3121_, lean_object* v_b_3122_){
_start:
{
uint8_t v_res_3123_; lean_object* v_r_3124_; 
v_res_3123_ = lean_expr_equal(v_a_3121_, v_b_3122_);
lean_dec_ref(v_b_3122_);
lean_dec_ref(v_a_3121_);
v_r_3124_ = lean_box(v_res_3123_);
return v_r_3124_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3125_){
_start:
{
if (lean_obj_tag(v_x_3125_) == 3)
{
uint8_t v___x_3126_; 
v___x_3126_ = 1;
return v___x_3126_;
}
else
{
uint8_t v___x_3127_; 
v___x_3127_ = 0;
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3128_){
_start:
{
uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_res_3129_ = l_Lean_Expr_isSort(v_x_3128_);
lean_dec_ref(v_x_3128_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3131_){
_start:
{
if (lean_obj_tag(v_x_3131_) == 3)
{
lean_object* v_u_3132_; 
v_u_3132_ = lean_ctor_get(v_x_3131_, 0);
if (lean_obj_tag(v_u_3132_) == 1)
{
uint8_t v___x_3133_; 
v___x_3133_ = 1;
return v___x_3133_;
}
else
{
uint8_t v___x_3134_; 
v___x_3134_ = 0;
return v___x_3134_;
}
}
else
{
uint8_t v___x_3135_; 
v___x_3135_ = 0;
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3136_){
_start:
{
uint8_t v_res_3137_; lean_object* v_r_3138_; 
v_res_3137_ = l_Lean_Expr_isType(v_x_3136_);
lean_dec_ref(v_x_3136_);
v_r_3138_ = lean_box(v_res_3137_);
return v_r_3138_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 3)
{
lean_object* v_u_3140_; 
v_u_3140_ = lean_ctor_get(v_x_3139_, 0);
if (lean_obj_tag(v_u_3140_) == 1)
{
lean_object* v_a_3141_; 
v_a_3141_ = lean_ctor_get(v_u_3140_, 0);
if (lean_obj_tag(v_a_3141_) == 0)
{
uint8_t v___x_3142_; 
v___x_3142_ = 1;
return v___x_3142_;
}
else
{
uint8_t v___x_3143_; 
v___x_3143_ = 0;
return v___x_3143_;
}
}
else
{
uint8_t v___x_3144_; 
v___x_3144_ = 0;
return v___x_3144_;
}
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = 0;
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3146_){
_start:
{
uint8_t v_res_3147_; lean_object* v_r_3148_; 
v_res_3147_ = l_Lean_Expr_isType0(v_x_3146_);
lean_dec_ref(v_x_3146_);
v_r_3148_ = lean_box(v_res_3147_);
return v_r_3148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3149_){
_start:
{
if (lean_obj_tag(v_x_3149_) == 3)
{
lean_object* v_u_3150_; 
v_u_3150_ = lean_ctor_get(v_x_3149_, 0);
if (lean_obj_tag(v_u_3150_) == 0)
{
uint8_t v___x_3151_; 
v___x_3151_ = 1;
return v___x_3151_;
}
else
{
uint8_t v___x_3152_; 
v___x_3152_ = 0;
return v___x_3152_;
}
}
else
{
uint8_t v___x_3153_; 
v___x_3153_ = 0;
return v___x_3153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3154_){
_start:
{
uint8_t v_res_3155_; lean_object* v_r_3156_; 
v_res_3155_ = l_Lean_Expr_isProp(v_x_3154_);
lean_dec_ref(v_x_3154_);
v_r_3156_ = lean_box(v_res_3155_);
return v_r_3156_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3157_){
_start:
{
if (lean_obj_tag(v_x_3157_) == 0)
{
uint8_t v___x_3158_; 
v___x_3158_ = 1;
return v___x_3158_;
}
else
{
uint8_t v___x_3159_; 
v___x_3159_ = 0;
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3160_){
_start:
{
uint8_t v_res_3161_; lean_object* v_r_3162_; 
v_res_3161_ = l_Lean_Expr_isBVar(v_x_3160_);
lean_dec_ref(v_x_3160_);
v_r_3162_ = lean_box(v_res_3161_);
return v_r_3162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3163_){
_start:
{
if (lean_obj_tag(v_x_3163_) == 2)
{
uint8_t v___x_3164_; 
v___x_3164_ = 1;
return v___x_3164_;
}
else
{
uint8_t v___x_3165_; 
v___x_3165_ = 0;
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3166_){
_start:
{
uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_res_3167_ = l_Lean_Expr_isMVar(v_x_3166_);
lean_dec_ref(v_x_3166_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3169_){
_start:
{
if (lean_obj_tag(v_x_3169_) == 1)
{
uint8_t v___x_3170_; 
v___x_3170_ = 1;
return v___x_3170_;
}
else
{
uint8_t v___x_3171_; 
v___x_3171_ = 0;
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3172_){
_start:
{
uint8_t v_res_3173_; lean_object* v_r_3174_; 
v_res_3173_ = l_Lean_Expr_isFVar(v_x_3172_);
lean_dec_ref(v_x_3172_);
v_r_3174_ = lean_box(v_res_3173_);
return v_r_3174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3175_){
_start:
{
if (lean_obj_tag(v_x_3175_) == 5)
{
uint8_t v___x_3176_; 
v___x_3176_ = 1;
return v___x_3176_;
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = 0;
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3178_){
_start:
{
uint8_t v_res_3179_; lean_object* v_r_3180_; 
v_res_3179_ = l_Lean_Expr_isApp(v_x_3178_);
lean_dec_ref(v_x_3178_);
v_r_3180_ = lean_box(v_res_3179_);
return v_r_3180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3181_){
_start:
{
if (lean_obj_tag(v_x_3181_) == 11)
{
uint8_t v___x_3182_; 
v___x_3182_ = 1;
return v___x_3182_;
}
else
{
uint8_t v___x_3183_; 
v___x_3183_ = 0;
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3184_){
_start:
{
uint8_t v_res_3185_; lean_object* v_r_3186_; 
v_res_3185_ = l_Lean_Expr_isProj(v_x_3184_);
lean_dec_ref(v_x_3184_);
v_r_3186_ = lean_box(v_res_3185_);
return v_r_3186_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3187_){
_start:
{
if (lean_obj_tag(v_x_3187_) == 4)
{
uint8_t v___x_3188_; 
v___x_3188_ = 1;
return v___x_3188_;
}
else
{
uint8_t v___x_3189_; 
v___x_3189_ = 0;
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3190_){
_start:
{
uint8_t v_res_3191_; lean_object* v_r_3192_; 
v_res_3191_ = l_Lean_Expr_isConst(v_x_3190_);
lean_dec_ref(v_x_3190_);
v_r_3192_ = lean_box(v_res_3191_);
return v_r_3192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3193_, lean_object* v_x_3194_){
_start:
{
if (lean_obj_tag(v_x_3193_) == 4)
{
lean_object* v_declName_3195_; uint8_t v___x_3196_; 
v_declName_3195_ = lean_ctor_get(v_x_3193_, 0);
v___x_3196_ = lean_name_eq(v_declName_3195_, v_x_3194_);
return v___x_3196_;
}
else
{
uint8_t v___x_3197_; 
v___x_3197_ = 0;
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
uint8_t v_res_3200_; lean_object* v_r_3201_; 
v_res_3200_ = l_Lean_Expr_isConstOf(v_x_3198_, v_x_3199_);
lean_dec(v_x_3199_);
lean_dec_ref(v_x_3198_);
v_r_3201_ = lean_box(v_res_3200_);
return v_r_3201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 1)
{
lean_object* v_fvarId_3204_; uint8_t v___x_3205_; 
v_fvarId_3204_ = lean_ctor_get(v_x_3202_, 0);
v___x_3205_ = lean_name_eq(v_fvarId_3204_, v_x_3203_);
return v___x_3205_;
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = 0;
return v___x_3206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
uint8_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_Lean_Expr_isFVarOf(v_x_3207_, v_x_3208_);
lean_dec(v_x_3208_);
lean_dec_ref(v_x_3207_);
v_r_3210_ = lean_box(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3211_) == 7)
{
uint8_t v___x_3212_; 
v___x_3212_ = 1;
return v___x_3212_;
}
else
{
uint8_t v___x_3213_; 
v___x_3213_ = 0;
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3214_){
_start:
{
uint8_t v_res_3215_; lean_object* v_r_3216_; 
v_res_3215_ = l_Lean_Expr_isForall(v_x_3214_);
lean_dec_ref(v_x_3214_);
v_r_3216_ = lean_box(v_res_3215_);
return v_r_3216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3217_){
_start:
{
if (lean_obj_tag(v_x_3217_) == 6)
{
uint8_t v___x_3218_; 
v___x_3218_ = 1;
return v___x_3218_;
}
else
{
uint8_t v___x_3219_; 
v___x_3219_ = 0;
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3220_){
_start:
{
uint8_t v_res_3221_; lean_object* v_r_3222_; 
v_res_3221_ = l_Lean_Expr_isLambda(v_x_3220_);
lean_dec_ref(v_x_3220_);
v_r_3222_ = lean_box(v_res_3221_);
return v_r_3222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3223_){
_start:
{
switch(lean_obj_tag(v_x_3223_))
{
case 6:
{
uint8_t v___x_3224_; 
v___x_3224_ = 1;
return v___x_3224_;
}
case 7:
{
uint8_t v___x_3225_; 
v___x_3225_ = 1;
return v___x_3225_;
}
default: 
{
uint8_t v___x_3226_; 
v___x_3226_ = 0;
return v___x_3226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3227_){
_start:
{
uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_res_3228_ = l_Lean_Expr_isBinding(v_x_3227_);
lean_dec_ref(v_x_3227_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_x_3230_) == 8)
{
uint8_t v___x_3231_; 
v___x_3231_ = 1;
return v___x_3231_;
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = 0;
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3233_){
_start:
{
uint8_t v_res_3234_; lean_object* v_r_3235_; 
v_res_3234_ = l_Lean_Expr_isLet(v_x_3233_);
lean_dec_ref(v_x_3233_);
v_r_3235_ = lean_box(v_res_3234_);
return v_r_3235_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3236_){
_start:
{
if (lean_obj_tag(v_x_3236_) == 8)
{
uint8_t v_nondep_3237_; 
v_nondep_3237_ = lean_ctor_get_uint8(v_x_3236_, sizeof(void*)*4 + 8);
return v_nondep_3237_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = 0;
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3239_){
_start:
{
uint8_t v_res_3240_; lean_object* v_r_3241_; 
v_res_3240_ = l_Lean_Expr_isHave(v_x_3239_);
lean_dec_ref(v_x_3239_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = l_Lean_Expr_isHave(v_a_3242_);
lean_dec_ref(v_a_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = lean_expr_is_have(v_a_3244_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3247_){
_start:
{
if (lean_obj_tag(v_x_3247_) == 10)
{
uint8_t v___x_3248_; 
v___x_3248_ = 1;
return v___x_3248_;
}
else
{
uint8_t v___x_3249_; 
v___x_3249_ = 0;
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3250_){
_start:
{
uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_res_3251_ = l_Lean_Expr_isMData(v_x_3250_);
lean_dec_ref(v_x_3250_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3253_) == 9)
{
uint8_t v___x_3254_; 
v___x_3254_ = 1;
return v___x_3254_;
}
else
{
uint8_t v___x_3255_; 
v___x_3255_ = 0;
return v___x_3255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3256_){
_start:
{
uint8_t v_res_3257_; lean_object* v_r_3258_; 
v_res_3257_ = l_Lean_Expr_isLit(v_x_3256_);
lean_dec_ref(v_x_3256_);
v_r_3258_ = lean_box(v_res_3257_);
return v_r_3258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3259_){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = l_Lean_instInhabitedExpr;
v___x_3261_ = lean_panic_fn_borrowed(v___x_3260_, v_msg_3259_);
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3265_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3266_ = lean_unsigned_to_nat(15u);
v___x_3267_ = lean_unsigned_to_nat(932u);
v___x_3268_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3269_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3270_ = l_mkPanicMessageWithDecl(v___x_3269_, v___x_3268_, v___x_3267_, v___x_3266_, v___x_3265_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 5)
{
lean_object* v_fn_3272_; 
v_fn_3272_ = lean_ctor_get(v_x_3271_, 0);
lean_inc_ref(v_fn_3272_);
return v_fn_3272_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3274_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3273_);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_Expr_appFn_x21(v_x_3275_);
lean_dec_ref(v_x_3275_);
return v_res_3276_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3278_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3279_ = lean_unsigned_to_nat(15u);
v___x_3280_ = lean_unsigned_to_nat(936u);
v___x_3281_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3282_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3283_ = l_mkPanicMessageWithDecl(v___x_3282_, v___x_3281_, v___x_3280_, v___x_3279_, v___x_3278_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3284_){
_start:
{
if (lean_obj_tag(v_x_3284_) == 5)
{
lean_object* v_arg_3285_; 
v_arg_3285_ = lean_ctor_get(v_x_3284_, 1);
lean_inc_ref(v_arg_3285_);
return v_arg_3285_;
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3287_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3286_);
return v___x_3287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Expr_appArg_x21(v_x_3288_);
lean_dec_ref(v_x_3288_);
return v_res_3289_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3291_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3292_ = lean_unsigned_to_nat(17u);
v___x_3293_ = lean_unsigned_to_nat(941u);
v___x_3294_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3295_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3296_ = l_mkPanicMessageWithDecl(v___x_3295_, v___x_3294_, v___x_3293_, v___x_3292_, v___x_3291_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3297_){
_start:
{
switch(lean_obj_tag(v_x_3297_))
{
case 10:
{
lean_object* v_expr_3298_; 
v_expr_3298_ = lean_ctor_get(v_x_3297_, 1);
v_x_3297_ = v_expr_3298_;
goto _start;
}
case 5:
{
lean_object* v_fn_3300_; 
v_fn_3300_ = lean_ctor_get(v_x_3297_, 0);
lean_inc_ref(v_fn_3300_);
return v_fn_3300_;
}
default: 
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3302_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3301_);
return v___x_3302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Expr_appFn_x21_x27(v_x_3303_);
lean_dec_ref(v_x_3303_);
return v_res_3304_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3306_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3307_ = lean_unsigned_to_nat(17u);
v___x_3308_ = lean_unsigned_to_nat(946u);
v___x_3309_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3310_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3311_ = l_mkPanicMessageWithDecl(v___x_3310_, v___x_3309_, v___x_3308_, v___x_3307_, v___x_3306_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3312_){
_start:
{
switch(lean_obj_tag(v_x_3312_))
{
case 10:
{
lean_object* v_expr_3313_; 
v_expr_3313_ = lean_ctor_get(v_x_3312_, 1);
v_x_3312_ = v_expr_3313_;
goto _start;
}
case 5:
{
lean_object* v_arg_3315_; 
v_arg_3315_ = lean_ctor_get(v_x_3312_, 1);
lean_inc_ref(v_arg_3315_);
return v_arg_3315_;
}
default: 
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3317_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3316_);
return v___x_3317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Expr_appArg_x21_x27(v_x_3318_);
lean_dec_ref(v_x_3318_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3320_){
_start:
{
lean_object* v_arg_3321_; 
v_arg_3321_ = lean_ctor_get(v_e_3320_, 1);
lean_inc_ref(v_arg_3321_);
return v_arg_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Expr_appArg___redArg(v_e_3322_);
lean_dec_ref(v_e_3322_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3324_, lean_object* v_h_3325_){
_start:
{
lean_object* v_arg_3326_; 
v_arg_3326_ = lean_ctor_get(v_e_3324_, 1);
lean_inc_ref(v_arg_3326_);
return v_arg_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3327_, lean_object* v_h_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_Expr_appArg(v_e_3327_, v_h_3328_);
lean_dec_ref(v_e_3327_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3330_){
_start:
{
lean_object* v_fn_3331_; 
v_fn_3331_ = lean_ctor_get(v_e_3330_, 0);
lean_inc_ref(v_fn_3331_);
return v_fn_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Expr_appFn___redArg(v_e_3332_);
lean_dec_ref(v_e_3332_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3334_, lean_object* v_h_3335_){
_start:
{
lean_object* v_fn_3336_; 
v_fn_3336_ = lean_ctor_get(v_e_3334_, 0);
lean_inc_ref(v_fn_3336_);
return v_fn_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3337_, lean_object* v_h_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_Expr_appFn(v_e_3337_, v_h_3338_);
lean_dec_ref(v_e_3337_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_panic_fn_borrowed(v___x_3341_, v_msg_3340_);
return v___x_3342_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3345_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3346_ = lean_unsigned_to_nat(14u);
v___x_3347_ = lean_unsigned_to_nat(958u);
v___x_3348_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3349_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3350_ = l_mkPanicMessageWithDecl(v___x_3349_, v___x_3348_, v___x_3347_, v___x_3346_, v___x_3345_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3351_){
_start:
{
if (lean_obj_tag(v_x_3351_) == 3)
{
lean_object* v_u_3352_; 
v_u_3352_ = lean_ctor_get(v_x_3351_, 0);
lean_inc(v_u_3352_);
return v_u_3352_;
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3354_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3353_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Expr_sortLevel_x21(v_x_3355_);
lean_dec_ref(v_x_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3357_){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3359_ = lean_panic_fn_borrowed(v___x_3358_, v_msg_3357_);
return v___x_3359_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3362_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3363_ = lean_unsigned_to_nat(13u);
v___x_3364_ = lean_unsigned_to_nat(962u);
v___x_3365_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3366_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3367_ = l_mkPanicMessageWithDecl(v___x_3366_, v___x_3365_, v___x_3364_, v___x_3363_, v___x_3362_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3368_){
_start:
{
if (lean_obj_tag(v_x_3368_) == 9)
{
lean_object* v_a_3369_; 
v_a_3369_ = lean_ctor_get(v_x_3368_, 0);
lean_inc_ref(v_a_3369_);
return v_a_3369_;
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3371_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3370_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Expr_litValue_x21(v_x_3372_);
lean_dec_ref(v_x_3372_);
return v_res_3373_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3374_){
_start:
{
if (lean_obj_tag(v_x_3374_) == 9)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v_x_3374_, 0);
if (lean_obj_tag(v_a_3375_) == 0)
{
uint8_t v___x_3376_; 
v___x_3376_ = 1;
return v___x_3376_;
}
else
{
uint8_t v___x_3377_; 
v___x_3377_ = 0;
return v___x_3377_;
}
}
else
{
uint8_t v___x_3378_; 
v___x_3378_ = 0;
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3379_){
_start:
{
uint8_t v_res_3380_; lean_object* v_r_3381_; 
v_res_3380_ = l_Lean_Expr_isRawNatLit(v_x_3379_);
lean_dec_ref(v_x_3379_);
v_r_3381_ = lean_box(v_res_3380_);
return v_r_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3382_){
_start:
{
if (lean_obj_tag(v_x_3382_) == 9)
{
lean_object* v_a_3383_; 
v_a_3383_ = lean_ctor_get(v_x_3382_, 0);
lean_inc_ref(v_a_3383_);
lean_dec_ref_known(v_x_3382_, 1);
if (lean_obj_tag(v_a_3383_) == 0)
{
lean_object* v_val_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
v_val_3384_ = lean_ctor_get(v_a_3383_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v_a_3383_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_val_3384_);
lean_dec(v_a_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 1);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_val_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
else
{
lean_object* v___x_3392_; 
lean_dec_ref(v_a_3383_);
v___x_3392_ = lean_box(0);
return v___x_3392_;
}
}
else
{
lean_object* v___x_3393_; 
lean_dec_ref(v_x_3382_);
v___x_3393_ = lean_box(0);
return v___x_3393_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3394_){
_start:
{
if (lean_obj_tag(v_x_3394_) == 9)
{
lean_object* v_a_3395_; 
v_a_3395_ = lean_ctor_get(v_x_3394_, 0);
if (lean_obj_tag(v_a_3395_) == 1)
{
uint8_t v___x_3396_; 
v___x_3396_ = 1;
return v___x_3396_;
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = 0;
return v___x_3397_;
}
}
else
{
uint8_t v___x_3398_; 
v___x_3398_ = 0;
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3399_){
_start:
{
uint8_t v_res_3400_; lean_object* v_r_3401_; 
v_res_3400_ = l_Lean_Expr_isStringLit(v_x_3399_);
lean_dec_ref(v_x_3399_);
v_r_3401_ = lean_box(v_res_3400_);
return v_r_3401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3406_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 5)
{
lean_object* v_fn_3407_; 
v_fn_3407_ = lean_ctor_get(v_x_3406_, 0);
if (lean_obj_tag(v_fn_3407_) == 4)
{
lean_object* v_arg_3408_; lean_object* v_declName_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v_arg_3408_ = lean_ctor_get(v_x_3406_, 1);
v_declName_3409_ = lean_ctor_get(v_fn_3407_, 0);
v___x_3410_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3411_ = lean_name_eq(v_declName_3409_, v___x_3410_);
if (v___x_3411_ == 0)
{
return v___x_3411_;
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = l_Lean_Expr_isRawNatLit(v_arg_3408_);
return v___x_3412_;
}
}
else
{
uint8_t v___x_3413_; 
v___x_3413_ = 0;
return v___x_3413_;
}
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = 0;
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3415_){
_start:
{
uint8_t v_res_3416_; lean_object* v_r_3417_; 
v_res_3416_ = l_Lean_Expr_isCharLit(v_x_3415_);
lean_dec_ref(v_x_3415_);
v_r_3417_ = lean_box(v_res_3416_);
return v_r_3417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3418_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_panic_fn_borrowed(v___x_3419_, v_msg_3418_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3423_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3424_ = lean_unsigned_to_nat(17u);
v___x_3425_ = lean_unsigned_to_nat(986u);
v___x_3426_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3427_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3428_ = l_mkPanicMessageWithDecl(v___x_3427_, v___x_3426_, v___x_3425_, v___x_3424_, v___x_3423_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3429_){
_start:
{
if (lean_obj_tag(v_x_3429_) == 4)
{
lean_object* v_declName_3430_; 
v_declName_3430_ = lean_ctor_get(v_x_3429_, 0);
lean_inc(v_declName_3430_);
return v_declName_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3432_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3431_);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Expr_constName_x21(v_x_3433_);
lean_dec_ref(v_x_3433_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 4)
{
lean_object* v_declName_3436_; lean_object* v___x_3437_; 
v_declName_3436_ = lean_ctor_get(v_x_3435_, 0);
lean_inc(v_declName_3436_);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_declName_3436_);
return v___x_3437_;
}
else
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_box(0);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Expr_constName_x3f(v_x_3439_);
lean_dec_ref(v_x_3439_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Expr_constName_x3f(v_e_3441_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_box(0);
return v___x_3443_;
}
else
{
lean_object* v_val_3444_; 
v_val_3444_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_val_3444_);
lean_dec_ref_known(v___x_3442_, 1);
return v_val_3444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Expr_constName(v_e_3445_);
lean_dec_ref(v_e_3445_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3447_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_box(0);
v___x_3449_ = lean_panic_fn_borrowed(v___x_3448_, v_msg_3447_);
return v___x_3449_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3451_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3452_ = lean_unsigned_to_nat(18u);
v___x_3453_ = lean_unsigned_to_nat(1006u);
v___x_3454_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3455_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3456_ = l_mkPanicMessageWithDecl(v___x_3455_, v___x_3454_, v___x_3453_, v___x_3452_, v___x_3451_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3457_){
_start:
{
if (lean_obj_tag(v_x_3457_) == 4)
{
lean_object* v_us_3458_; 
v_us_3458_ = lean_ctor_get(v_x_3457_, 1);
lean_inc(v_us_3458_);
return v_us_3458_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3460_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3459_);
return v___x_3460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Expr_constLevels_x21(v_x_3461_);
lean_dec_ref(v_x_3461_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3463_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_panic_fn_borrowed(v___x_3464_, v_msg_3463_);
return v___x_3465_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3468_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3469_ = lean_unsigned_to_nat(16u);
v___x_3470_ = lean_unsigned_to_nat(1010u);
v___x_3471_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3472_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3473_ = l_mkPanicMessageWithDecl(v___x_3472_, v___x_3471_, v___x_3470_, v___x_3469_, v___x_3468_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3474_){
_start:
{
if (lean_obj_tag(v_x_3474_) == 0)
{
lean_object* v_deBruijnIndex_3475_; 
v_deBruijnIndex_3475_ = lean_ctor_get(v_x_3474_, 0);
lean_inc(v_deBruijnIndex_3475_);
return v_deBruijnIndex_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3477_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3476_);
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Expr_bvarIdx_x21(v_x_3478_);
lean_dec_ref(v_x_3478_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3480_){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_panic_fn_borrowed(v___x_3481_, v_msg_3480_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3485_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3486_ = lean_unsigned_to_nat(14u);
v___x_3487_ = lean_unsigned_to_nat(1014u);
v___x_3488_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3489_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3490_ = l_mkPanicMessageWithDecl(v___x_3489_, v___x_3488_, v___x_3487_, v___x_3486_, v___x_3485_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3491_){
_start:
{
if (lean_obj_tag(v_x_3491_) == 1)
{
lean_object* v_fvarId_3492_; 
v_fvarId_3492_ = lean_ctor_get(v_x_3491_, 0);
lean_inc(v_fvarId_3492_);
return v_fvarId_3492_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3494_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3493_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_Expr_fvarId_x21(v_x_3495_);
lean_dec_ref(v_x_3495_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3497_){
_start:
{
if (lean_obj_tag(v_x_3497_) == 1)
{
lean_object* v_fvarId_3498_; lean_object* v___x_3499_; 
v_fvarId_3498_ = lean_ctor_get(v_x_3497_, 0);
lean_inc(v_fvarId_3498_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_fvarId_3498_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_box(0);
return v___x_3500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_Expr_fvarId_x3f(v_x_3501_);
lean_dec_ref(v_x_3501_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3503_){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_box(0);
v___x_3505_ = lean_panic_fn_borrowed(v___x_3504_, v_msg_3503_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3508_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3509_ = lean_unsigned_to_nat(14u);
v___x_3510_ = lean_unsigned_to_nat(1022u);
v___x_3511_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3512_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3513_ = l_mkPanicMessageWithDecl(v___x_3512_, v___x_3511_, v___x_3510_, v___x_3509_, v___x_3508_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 2)
{
lean_object* v_mvarId_3515_; 
v_mvarId_3515_ = lean_ctor_get(v_x_3514_, 0);
lean_inc(v_mvarId_3515_);
return v_mvarId_3515_;
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3517_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3516_);
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_Expr_mvarId_x21(v_x_3518_);
lean_dec_ref(v_x_3518_);
return v_res_3519_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3522_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3523_ = lean_unsigned_to_nat(23u);
v___x_3524_ = lean_unsigned_to_nat(1027u);
v___x_3525_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3526_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3527_ = l_mkPanicMessageWithDecl(v___x_3526_, v___x_3525_, v___x_3524_, v___x_3523_, v___x_3522_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3528_){
_start:
{
switch(lean_obj_tag(v_x_3528_))
{
case 7:
{
lean_object* v_binderName_3529_; 
v_binderName_3529_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_binderName_3529_);
return v_binderName_3529_;
}
case 6:
{
lean_object* v_binderName_3530_; 
v_binderName_3530_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_binderName_3530_);
return v_binderName_3530_;
}
default: 
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3532_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3531_);
return v___x_3532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Expr_bindingName_x21(v_x_3533_);
lean_dec_ref(v_x_3533_);
return v_res_3534_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3536_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3537_ = lean_unsigned_to_nat(23u);
v___x_3538_ = lean_unsigned_to_nat(1032u);
v___x_3539_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3540_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3541_ = l_mkPanicMessageWithDecl(v___x_3540_, v___x_3539_, v___x_3538_, v___x_3537_, v___x_3536_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3542_){
_start:
{
switch(lean_obj_tag(v_x_3542_))
{
case 7:
{
lean_object* v_binderType_3543_; 
v_binderType_3543_ = lean_ctor_get(v_x_3542_, 1);
lean_inc_ref(v_binderType_3543_);
return v_binderType_3543_;
}
case 6:
{
lean_object* v_binderType_3544_; 
v_binderType_3544_ = lean_ctor_get(v_x_3542_, 1);
lean_inc_ref(v_binderType_3544_);
return v_binderType_3544_;
}
default: 
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3546_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3545_);
return v___x_3546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_Expr_bindingDomain_x21(v_x_3547_);
lean_dec_ref(v_x_3547_);
return v_res_3548_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3550_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3551_ = lean_unsigned_to_nat(23u);
v___x_3552_ = lean_unsigned_to_nat(1037u);
v___x_3553_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3554_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3555_ = l_mkPanicMessageWithDecl(v___x_3554_, v___x_3553_, v___x_3552_, v___x_3551_, v___x_3550_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3556_){
_start:
{
switch(lean_obj_tag(v_x_3556_))
{
case 7:
{
lean_object* v_body_3557_; 
v_body_3557_ = lean_ctor_get(v_x_3556_, 2);
lean_inc_ref(v_body_3557_);
return v_body_3557_;
}
case 6:
{
lean_object* v_body_3558_; 
v_body_3558_ = lean_ctor_get(v_x_3556_, 2);
lean_inc_ref(v_body_3558_);
return v_body_3558_;
}
default: 
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3560_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3559_);
return v___x_3560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Expr_bindingBody_x21(v_x_3561_);
lean_dec_ref(v_x_3561_);
return v_res_3562_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3563_){
_start:
{
uint8_t v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3564_ = 0;
v___x_3565_ = lean_box(v___x_3564_);
v___x_3566_ = lean_panic_fn_borrowed(v___x_3565_, v_msg_3563_);
lean_dec(v___x_3565_);
v___x_3567_ = lean_unbox(v___x_3566_);
lean_dec(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3568_){
_start:
{
uint8_t v_res_3569_; lean_object* v_r_3570_; 
v_res_3569_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3568_);
v_r_3570_ = lean_box(v_res_3569_);
return v_r_3570_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3572_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3573_ = lean_unsigned_to_nat(24u);
v___x_3574_ = lean_unsigned_to_nat(1042u);
v___x_3575_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3576_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3577_ = l_mkPanicMessageWithDecl(v___x_3576_, v___x_3575_, v___x_3574_, v___x_3573_, v___x_3572_);
return v___x_3577_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3578_){
_start:
{
switch(lean_obj_tag(v_x_3578_))
{
case 7:
{
uint8_t v_binderInfo_3579_; 
v_binderInfo_3579_ = lean_ctor_get_uint8(v_x_3578_, sizeof(void*)*3 + 8);
return v_binderInfo_3579_;
}
case 6:
{
uint8_t v_binderInfo_3580_; 
v_binderInfo_3580_ = lean_ctor_get_uint8(v_x_3578_, sizeof(void*)*3 + 8);
return v_binderInfo_3580_;
}
default: 
{
lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3582_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3581_);
return v___x_3582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3583_){
_start:
{
uint8_t v_res_3584_; lean_object* v_r_3585_; 
v_res_3584_ = l_Lean_Expr_bindingInfo_x21(v_x_3583_);
lean_dec_ref(v_x_3583_);
v_r_3585_ = lean_box(v_res_3584_);
return v_r_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3586_){
_start:
{
lean_object* v_binderName_3587_; 
v_binderName_3587_ = lean_ctor_get(v_x_3586_, 0);
lean_inc(v_binderName_3587_);
return v_binderName_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Expr_forallName___redArg(v_x_3588_);
lean_dec_ref(v_x_3588_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v_binderName_3592_; 
v_binderName_3592_ = lean_ctor_get(v_x_3590_, 0);
lean_inc(v_binderName_3592_);
return v_binderName_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3593_, lean_object* v_x_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Expr_forallName(v_x_3593_, v_x_3594_);
lean_dec_ref(v_x_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3596_){
_start:
{
lean_object* v_binderType_3597_; 
v_binderType_3597_ = lean_ctor_get(v_x_3596_, 1);
lean_inc_ref(v_binderType_3597_);
return v_binderType_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Expr_forallDomain___redArg(v_x_3598_);
lean_dec_ref(v_x_3598_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v_binderType_3602_; 
v_binderType_3602_ = lean_ctor_get(v_x_3600_, 1);
lean_inc_ref(v_binderType_3602_);
return v_binderType_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Expr_forallDomain(v_x_3603_, v_x_3604_);
lean_dec_ref(v_x_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3606_){
_start:
{
lean_object* v_body_3607_; 
v_body_3607_ = lean_ctor_get(v_x_3606_, 2);
lean_inc_ref(v_body_3607_);
return v_body_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Expr_forallBody___redArg(v_x_3608_);
lean_dec_ref(v_x_3608_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
lean_object* v_body_3612_; 
v_body_3612_ = lean_ctor_get(v_x_3610_, 2);
lean_inc_ref(v_body_3612_);
return v_body_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Expr_forallBody(v_x_3613_, v_x_3614_);
lean_dec_ref(v_x_3613_);
return v_res_3615_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3616_){
_start:
{
uint8_t v_binderInfo_3617_; 
v_binderInfo_3617_ = lean_ctor_get_uint8(v_x_3616_, sizeof(void*)*3 + 8);
return v_binderInfo_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3618_){
_start:
{
uint8_t v_res_3619_; lean_object* v_r_3620_; 
v_res_3619_ = l_Lean_Expr_forallInfo___redArg(v_x_3618_);
lean_dec_ref(v_x_3618_);
v_r_3620_ = lean_box(v_res_3619_);
return v_r_3620_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
uint8_t v_binderInfo_3623_; 
v_binderInfo_3623_ = lean_ctor_get_uint8(v_x_3621_, sizeof(void*)*3 + 8);
return v_binderInfo_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
uint8_t v_res_3626_; lean_object* v_r_3627_; 
v_res_3626_ = l_Lean_Expr_forallInfo(v_x_3624_, v_x_3625_);
lean_dec_ref(v_x_3624_);
v_r_3627_ = lean_box(v_res_3626_);
return v_r_3627_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3630_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3631_ = lean_unsigned_to_nat(17u);
v___x_3632_ = lean_unsigned_to_nat(1058u);
v___x_3633_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3634_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3635_ = l_mkPanicMessageWithDecl(v___x_3634_, v___x_3633_, v___x_3632_, v___x_3631_, v___x_3630_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3636_){
_start:
{
if (lean_obj_tag(v_x_3636_) == 8)
{
lean_object* v_declName_3637_; 
v_declName_3637_ = lean_ctor_get(v_x_3636_, 0);
lean_inc(v_declName_3637_);
return v_declName_3637_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3639_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3638_);
return v___x_3639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_Expr_letName_x21(v_x_3640_);
lean_dec_ref(v_x_3640_);
return v_res_3641_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3643_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3644_ = lean_unsigned_to_nat(19u);
v___x_3645_ = lean_unsigned_to_nat(1062u);
v___x_3646_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3647_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3648_ = l_mkPanicMessageWithDecl(v___x_3647_, v___x_3646_, v___x_3645_, v___x_3644_, v___x_3643_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3649_){
_start:
{
if (lean_obj_tag(v_x_3649_) == 8)
{
lean_object* v_type_3650_; 
v_type_3650_ = lean_ctor_get(v_x_3649_, 1);
lean_inc_ref(v_type_3650_);
return v_type_3650_;
}
else
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3652_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3651_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Expr_letType_x21(v_x_3653_);
lean_dec_ref(v_x_3653_);
return v_res_3654_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3656_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3657_ = lean_unsigned_to_nat(21u);
v___x_3658_ = lean_unsigned_to_nat(1066u);
v___x_3659_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3660_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3661_ = l_mkPanicMessageWithDecl(v___x_3660_, v___x_3659_, v___x_3658_, v___x_3657_, v___x_3656_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3662_){
_start:
{
if (lean_obj_tag(v_x_3662_) == 8)
{
lean_object* v_value_3663_; 
v_value_3663_ = lean_ctor_get(v_x_3662_, 2);
lean_inc_ref(v_value_3663_);
return v_value_3663_;
}
else
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3665_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3664_);
return v___x_3665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Expr_letValue_x21(v_x_3666_);
lean_dec_ref(v_x_3666_);
return v_res_3667_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3669_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3670_ = lean_unsigned_to_nat(23u);
v___x_3671_ = lean_unsigned_to_nat(1070u);
v___x_3672_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3673_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3674_ = l_mkPanicMessageWithDecl(v___x_3673_, v___x_3672_, v___x_3671_, v___x_3670_, v___x_3669_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3675_){
_start:
{
if (lean_obj_tag(v_x_3675_) == 8)
{
lean_object* v_body_3676_; 
v_body_3676_ = lean_ctor_get(v_x_3675_, 3);
lean_inc_ref(v_body_3676_);
return v_body_3676_;
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3678_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3677_);
return v___x_3678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Expr_letBody_x21(v_x_3679_);
lean_dec_ref(v_x_3679_);
return v_res_3680_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3681_){
_start:
{
uint8_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v___x_3682_ = 0;
v___x_3683_ = lean_box(v___x_3682_);
v___x_3684_ = lean_panic_fn_borrowed(v___x_3683_, v_msg_3681_);
lean_dec(v___x_3683_);
v___x_3685_ = lean_unbox(v___x_3684_);
lean_dec(v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3686_){
_start:
{
uint8_t v_res_3687_; lean_object* v_r_3688_; 
v_res_3687_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3686_);
v_r_3688_ = lean_box(v_res_3687_);
return v_r_3688_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3690_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3691_ = lean_unsigned_to_nat(27u);
v___x_3692_ = lean_unsigned_to_nat(1074u);
v___x_3693_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3694_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3695_ = l_mkPanicMessageWithDecl(v___x_3694_, v___x_3693_, v___x_3692_, v___x_3691_, v___x_3690_);
return v___x_3695_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3696_){
_start:
{
if (lean_obj_tag(v_x_3696_) == 8)
{
uint8_t v_nondep_3697_; 
v_nondep_3697_ = lean_ctor_get_uint8(v_x_3696_, sizeof(void*)*4 + 8);
return v_nondep_3697_;
}
else
{
lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3699_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3698_);
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3700_){
_start:
{
uint8_t v_res_3701_; lean_object* v_r_3702_; 
v_res_3701_ = l_Lean_Expr_letNondep_x21(v_x_3700_);
lean_dec_ref(v_x_3700_);
v_r_3702_ = lean_box(v_res_3701_);
return v_r_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3703_){
_start:
{
if (lean_obj_tag(v_x_3703_) == 10)
{
lean_object* v_expr_3704_; 
v_expr_3704_ = lean_ctor_get(v_x_3703_, 1);
v_x_3703_ = v_expr_3704_;
goto _start;
}
else
{
lean_inc_ref(v_x_3703_);
return v_x_3703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_Expr_consumeMData(v_x_3706_);
lean_dec_ref(v_x_3706_);
return v_res_3707_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3710_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3711_ = lean_unsigned_to_nat(17u);
v___x_3712_ = lean_unsigned_to_nat(1082u);
v___x_3713_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3714_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3715_ = l_mkPanicMessageWithDecl(v___x_3714_, v___x_3713_, v___x_3712_, v___x_3711_, v___x_3710_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 10)
{
lean_object* v_expr_3717_; 
v_expr_3717_ = lean_ctor_get(v_x_3716_, 1);
lean_inc_ref(v_expr_3717_);
return v_expr_3717_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3719_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3718_);
return v___x_3719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Expr_mdataExpr_x21(v_x_3720_);
lean_dec_ref(v_x_3720_);
return v_res_3721_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3724_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3725_ = lean_unsigned_to_nat(18u);
v___x_3726_ = lean_unsigned_to_nat(1086u);
v___x_3727_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3728_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3729_ = l_mkPanicMessageWithDecl(v___x_3728_, v___x_3727_, v___x_3726_, v___x_3725_, v___x_3724_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3730_){
_start:
{
if (lean_obj_tag(v_x_3730_) == 11)
{
lean_object* v_struct_3731_; 
v_struct_3731_ = lean_ctor_get(v_x_3730_, 2);
lean_inc_ref(v_struct_3731_);
return v_struct_3731_;
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3733_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3732_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Expr_projExpr_x21(v_x_3734_);
lean_dec_ref(v_x_3734_);
return v_res_3735_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3737_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3738_ = lean_unsigned_to_nat(18u);
v___x_3739_ = lean_unsigned_to_nat(1090u);
v___x_3740_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3741_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3742_ = l_mkPanicMessageWithDecl(v___x_3741_, v___x_3740_, v___x_3739_, v___x_3738_, v___x_3737_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3743_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 11)
{
lean_object* v_idx_3744_; 
v_idx_3744_ = lean_ctor_get(v_x_3743_, 1);
lean_inc(v_idx_3744_);
return v_idx_3744_;
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3746_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3745_);
return v___x_3746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_Expr_projIdx_x21(v_x_3747_);
lean_dec_ref(v_x_3747_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3749_){
_start:
{
if (lean_obj_tag(v_x_3749_) == 7)
{
lean_object* v_body_3750_; 
v_body_3750_ = lean_ctor_get(v_x_3749_, 2);
v_x_3749_ = v_body_3750_;
goto _start;
}
else
{
lean_inc_ref(v_x_3749_);
return v_x_3749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_Expr_getForallBody(v_x_3752_);
lean_dec_ref(v_x_3752_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3754_, lean_object* v_x_3755_){
_start:
{
lean_object* v_zero_3756_; uint8_t v_isZero_3757_; 
v_zero_3756_ = lean_unsigned_to_nat(0u);
v_isZero_3757_ = lean_nat_dec_eq(v_x_3754_, v_zero_3756_);
if (v_isZero_3757_ == 1)
{
lean_dec(v_x_3754_);
lean_inc_ref(v_x_3755_);
return v_x_3755_;
}
else
{
if (lean_obj_tag(v_x_3755_) == 7)
{
lean_object* v_body_3758_; lean_object* v_one_3759_; lean_object* v_n_3760_; 
v_body_3758_ = lean_ctor_get(v_x_3755_, 2);
v_one_3759_ = lean_unsigned_to_nat(1u);
v_n_3760_ = lean_nat_sub(v_x_3754_, v_one_3759_);
lean_dec(v_x_3754_);
v_x_3754_ = v_n_3760_;
v_x_3755_ = v_body_3758_;
goto _start;
}
else
{
lean_dec(v_x_3754_);
lean_inc_ref(v_x_3755_);
return v_x_3755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3762_, lean_object* v_x_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3762_, v_x_3763_);
lean_dec_ref(v_x_3763_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3765_){
_start:
{
if (lean_obj_tag(v_x_3765_) == 7)
{
lean_object* v_binderName_3766_; lean_object* v_body_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v_binderName_3766_ = lean_ctor_get(v_x_3765_, 0);
v_body_3767_ = lean_ctor_get(v_x_3765_, 2);
v___x_3768_ = l_Lean_Expr_getForallBinderNames(v_body_3767_);
lean_inc(v_binderName_3766_);
v___x_3769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3769_, 0, v_binderName_3766_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
return v___x_3769_;
}
else
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_box(0);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Expr_getForallBinderNames(v_x_3771_);
lean_dec_ref(v_x_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3773_){
_start:
{
switch(lean_obj_tag(v_x_3773_))
{
case 10:
{
lean_object* v_expr_3774_; 
v_expr_3774_ = lean_ctor_get(v_x_3773_, 1);
v_x_3773_ = v_expr_3774_;
goto _start;
}
case 7:
{
lean_object* v_body_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_body_3776_ = lean_ctor_get(v_x_3773_, 2);
v___x_3777_ = l_Lean_Expr_getNumHeadForalls(v_body_3776_);
v___x_3778_ = lean_unsigned_to_nat(1u);
v___x_3779_ = lean_nat_add(v___x_3777_, v___x_3778_);
lean_dec(v___x_3777_);
return v___x_3779_;
}
default: 
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_unsigned_to_nat(0u);
return v___x_3780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Expr_getNumHeadForalls(v_x_3781_);
lean_dec_ref(v_x_3781_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3783_){
_start:
{
if (lean_obj_tag(v_x_3783_) == 5)
{
lean_object* v_fn_3784_; 
v_fn_3784_ = lean_ctor_get(v_x_3783_, 0);
v_x_3783_ = v_fn_3784_;
goto _start;
}
else
{
lean_inc_ref(v_x_3783_);
return v_x_3783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Expr_getAppFn(v_x_3786_);
lean_dec_ref(v_x_3786_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3788_){
_start:
{
switch(lean_obj_tag(v_x_3788_))
{
case 5:
{
lean_object* v_fn_3789_; 
v_fn_3789_ = lean_ctor_get(v_x_3788_, 0);
v_x_3788_ = v_fn_3789_;
goto _start;
}
case 10:
{
lean_object* v_expr_3791_; 
v_expr_3791_ = lean_ctor_get(v_x_3788_, 1);
v_x_3788_ = v_expr_3791_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3788_);
return v_x_3788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Expr_getAppFn_x27(v_x_3793_);
lean_dec_ref(v_x_3793_);
return v_res_3794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3795_, lean_object* v_n_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Expr_getAppFn(v_e_3795_);
if (lean_obj_tag(v___x_3797_) == 4)
{
lean_object* v_declName_3798_; uint8_t v___x_3799_; 
v_declName_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_declName_3798_);
lean_dec_ref_known(v___x_3797_, 2);
v___x_3799_ = lean_name_eq(v_declName_3798_, v_n_3796_);
lean_dec(v_declName_3798_);
return v___x_3799_;
}
else
{
uint8_t v___x_3800_; 
lean_dec_ref(v___x_3797_);
v___x_3800_ = 0;
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3801_, lean_object* v_n_3802_){
_start:
{
uint8_t v_res_3803_; lean_object* v_r_3804_; 
v_res_3803_ = l_Lean_Expr_isAppOf(v_e_3801_, v_n_3802_);
lean_dec(v_n_3802_);
lean_dec_ref(v_e_3801_);
v_r_3804_ = lean_box(v_res_3803_);
return v_r_3804_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3805_, lean_object* v_x_3806_, lean_object* v_x_3807_){
_start:
{
switch(lean_obj_tag(v_x_3805_))
{
case 4:
{
lean_object* v_declName_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v_declName_3808_ = lean_ctor_get(v_x_3805_, 0);
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = lean_nat_dec_eq(v_x_3807_, v___x_3809_);
lean_dec(v_x_3807_);
if (v___x_3810_ == 0)
{
return v___x_3810_;
}
else
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_name_eq(v_declName_3808_, v_x_3806_);
return v___x_3811_;
}
}
case 5:
{
lean_object* v_fn_3812_; lean_object* v_zero_3813_; uint8_t v_isZero_3814_; 
v_fn_3812_ = lean_ctor_get(v_x_3805_, 0);
v_zero_3813_ = lean_unsigned_to_nat(0u);
v_isZero_3814_ = lean_nat_dec_eq(v_x_3807_, v_zero_3813_);
if (v_isZero_3814_ == 0)
{
lean_object* v_one_3815_; lean_object* v_n_3816_; 
v_one_3815_ = lean_unsigned_to_nat(1u);
v_n_3816_ = lean_nat_sub(v_x_3807_, v_one_3815_);
lean_dec(v_x_3807_);
v_x_3805_ = v_fn_3812_;
v_x_3807_ = v_n_3816_;
goto _start;
}
else
{
uint8_t v___x_3818_; 
lean_dec(v_x_3807_);
v___x_3818_ = 0;
return v___x_3818_;
}
}
default: 
{
uint8_t v___x_3819_; 
lean_dec(v_x_3807_);
v___x_3819_ = 0;
return v___x_3819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3820_, lean_object* v_x_3821_, lean_object* v_x_3822_){
_start:
{
uint8_t v_res_3823_; lean_object* v_r_3824_; 
v_res_3823_ = l_Lean_Expr_isAppOfArity(v_x_3820_, v_x_3821_, v_x_3822_);
lean_dec(v_x_3821_);
lean_dec_ref(v_x_3820_);
v_r_3824_ = lean_box(v_res_3823_);
return v_r_3824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3825_, lean_object* v_x_3826_, lean_object* v_x_3827_){
_start:
{
switch(lean_obj_tag(v_x_3825_))
{
case 10:
{
lean_object* v_expr_3828_; 
v_expr_3828_ = lean_ctor_get(v_x_3825_, 1);
v_x_3825_ = v_expr_3828_;
goto _start;
}
case 4:
{
lean_object* v_declName_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v_declName_3830_ = lean_ctor_get(v_x_3825_, 0);
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = lean_nat_dec_eq(v_x_3827_, v___x_3831_);
lean_dec(v_x_3827_);
if (v___x_3832_ == 0)
{
return v___x_3832_;
}
else
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_name_eq(v_declName_3830_, v_x_3826_);
return v___x_3833_;
}
}
case 5:
{
lean_object* v_fn_3834_; lean_object* v_zero_3835_; uint8_t v_isZero_3836_; 
v_fn_3834_ = lean_ctor_get(v_x_3825_, 0);
v_zero_3835_ = lean_unsigned_to_nat(0u);
v_isZero_3836_ = lean_nat_dec_eq(v_x_3827_, v_zero_3835_);
if (v_isZero_3836_ == 0)
{
lean_object* v_one_3837_; lean_object* v_n_3838_; 
v_one_3837_ = lean_unsigned_to_nat(1u);
v_n_3838_ = lean_nat_sub(v_x_3827_, v_one_3837_);
lean_dec(v_x_3827_);
v_x_3825_ = v_fn_3834_;
v_x_3827_ = v_n_3838_;
goto _start;
}
else
{
uint8_t v___x_3840_; 
lean_dec(v_x_3827_);
v___x_3840_ = 0;
return v___x_3840_;
}
}
default: 
{
uint8_t v___x_3841_; 
lean_dec(v_x_3827_);
v___x_3841_ = 0;
return v___x_3841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3842_, lean_object* v_x_3843_, lean_object* v_x_3844_){
_start:
{
uint8_t v_res_3845_; lean_object* v_r_3846_; 
v_res_3845_ = l_Lean_Expr_isAppOfArity_x27(v_x_3842_, v_x_3843_, v_x_3844_);
lean_dec(v_x_3843_);
lean_dec_ref(v_x_3842_);
v_r_3846_ = lean_box(v_res_3845_);
return v_r_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
if (lean_obj_tag(v_x_3847_) == 5)
{
lean_object* v_fn_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_fn_3849_ = lean_ctor_get(v_x_3847_, 0);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_add(v_x_3848_, v___x_3850_);
lean_dec(v_x_3848_);
v_x_3847_ = v_fn_3849_;
v_x_3848_ = v___x_3851_;
goto _start;
}
else
{
return v_x_3848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3853_, lean_object* v_x_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3853_, v_x_3854_);
lean_dec_ref(v_x_3853_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3856_){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_unsigned_to_nat(0u);
v___x_3858_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3856_, v___x_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Expr_getAppNumArgs(v_e_3859_);
lean_dec_ref(v_e_3859_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
switch(lean_obj_tag(v_a_3861_))
{
case 10:
{
lean_object* v_expr_3863_; 
v_expr_3863_ = lean_ctor_get(v_a_3861_, 1);
v_a_3861_ = v_expr_3863_;
goto _start;
}
case 5:
{
lean_object* v_fn_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_fn_3865_ = lean_ctor_get(v_a_3861_, 0);
v___x_3866_ = lean_unsigned_to_nat(1u);
v___x_3867_ = lean_nat_add(v_a_3862_, v___x_3866_);
lean_dec(v_a_3862_);
v_a_3861_ = v_fn_3865_;
v_a_3862_ = v___x_3867_;
goto _start;
}
default: 
{
return v_a_3862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3869_, v_a_3870_);
lean_dec_ref(v_a_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3872_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v___x_3874_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3872_, v___x_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3875_);
lean_dec_ref(v_e_3875_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_zero_3879_; uint8_t v_isZero_3880_; 
v_zero_3879_ = lean_unsigned_to_nat(0u);
v_isZero_3880_ = lean_nat_dec_eq(v_x_3877_, v_zero_3879_);
if (v_isZero_3880_ == 0)
{
if (lean_obj_tag(v_x_3878_) == 5)
{
lean_object* v_fn_3881_; lean_object* v_one_3882_; lean_object* v_n_3883_; 
v_fn_3881_ = lean_ctor_get(v_x_3878_, 0);
v_one_3882_ = lean_unsigned_to_nat(1u);
v_n_3883_ = lean_nat_sub(v_x_3877_, v_one_3882_);
lean_dec(v_x_3877_);
v_x_3877_ = v_n_3883_;
v_x_3878_ = v_fn_3881_;
goto _start;
}
else
{
lean_dec(v_x_3877_);
lean_inc_ref(v_x_3878_);
return v_x_3878_;
}
}
else
{
lean_dec(v_x_3877_);
lean_inc_ref(v_x_3878_);
return v_x_3878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3885_, lean_object* v_x_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Expr_getBoundedAppFn(v_x_3885_, v_x_3886_);
lean_dec_ref(v_x_3886_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3888_) == 5)
{
lean_object* v_fn_3891_; lean_object* v_arg_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_fn_3891_ = lean_ctor_get(v_x_3888_, 0);
lean_inc_ref(v_fn_3891_);
v_arg_3892_ = lean_ctor_get(v_x_3888_, 1);
lean_inc_ref(v_arg_3892_);
lean_dec_ref_known(v_x_3888_, 2);
v___x_3893_ = lean_array_set(v_x_3889_, v_x_3890_, v_arg_3892_);
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_nat_sub(v_x_3890_, v___x_3894_);
lean_dec(v_x_3890_);
v_x_3888_ = v_fn_3891_;
v_x_3889_ = v___x_3893_;
v_x_3890_ = v___x_3895_;
goto _start;
}
else
{
lean_dec(v_x_3890_);
lean_dec_ref(v_x_3888_);
return v_x_3889_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3897_; lean_object* v_dummy_3898_; 
v___x_3897_ = lean_box(0);
v_dummy_3898_ = l_Lean_Expr_sort___override(v___x_3897_);
return v_dummy_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3899_){
_start:
{
lean_object* v_dummy_3900_; lean_object* v_nargs_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_dummy_3900_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3901_ = l_Lean_Expr_getAppNumArgs(v_e_3899_);
lean_inc(v_nargs_3901_);
v___x_3902_ = lean_mk_array(v_nargs_3901_, v_dummy_3900_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_nat_sub(v_nargs_3901_, v___x_3903_);
lean_dec(v_nargs_3901_);
v___x_3905_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3899_, v___x_3902_, v___x_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_){
_start:
{
if (lean_obj_tag(v_x_3906_) == 5)
{
lean_object* v_fn_3909_; lean_object* v_arg_3910_; lean_object* v_zero_3911_; uint8_t v_isZero_3912_; 
v_fn_3909_ = lean_ctor_get(v_x_3906_, 0);
lean_inc_ref(v_fn_3909_);
v_arg_3910_ = lean_ctor_get(v_x_3906_, 1);
lean_inc_ref(v_arg_3910_);
lean_dec_ref_known(v_x_3906_, 2);
v_zero_3911_ = lean_unsigned_to_nat(0u);
v_isZero_3912_ = lean_nat_dec_eq(v_x_3908_, v_zero_3911_);
if (v_isZero_3912_ == 0)
{
lean_object* v_one_3913_; lean_object* v_n_3914_; lean_object* v___x_3915_; 
v_one_3913_ = lean_unsigned_to_nat(1u);
v_n_3914_ = lean_nat_sub(v_x_3908_, v_one_3913_);
lean_dec(v_x_3908_);
v___x_3915_ = lean_array_set(v_x_3907_, v_n_3914_, v_arg_3910_);
v_x_3906_ = v_fn_3909_;
v_x_3907_ = v___x_3915_;
v_x_3908_ = v_n_3914_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3910_);
lean_dec_ref(v_fn_3909_);
lean_dec(v_x_3908_);
return v_x_3907_;
}
}
else
{
lean_dec(v_x_3908_);
lean_dec_ref(v_x_3906_);
return v_x_3907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3917_, lean_object* v_e_3918_){
_start:
{
lean_object* v_dummy_3919_; lean_object* v___y_3921_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_dummy_3919_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3924_ = l_Lean_Expr_getAppNumArgs(v_e_3918_);
v___x_3925_ = lean_nat_dec_le(v_maxArgs_3917_, v___x_3924_);
if (v___x_3925_ == 0)
{
lean_dec(v_maxArgs_3917_);
v___y_3921_ = v___x_3924_;
goto v___jp_3920_;
}
else
{
lean_dec(v___x_3924_);
v___y_3921_ = v_maxArgs_3917_;
goto v___jp_3920_;
}
v___jp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_inc(v___y_3921_);
v___x_3922_ = lean_mk_array(v___y_3921_, v_dummy_3919_);
v___x_3923_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3918_, v___x_3922_, v___y_3921_);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3926_, lean_object* v_x_3927_){
_start:
{
if (lean_obj_tag(v_x_3926_) == 5)
{
lean_object* v_fn_3928_; lean_object* v_arg_3929_; lean_object* v___x_3930_; 
v_fn_3928_ = lean_ctor_get(v_x_3926_, 0);
lean_inc_ref(v_fn_3928_);
v_arg_3929_ = lean_ctor_get(v_x_3926_, 1);
lean_inc_ref(v_arg_3929_);
lean_dec_ref_known(v_x_3926_, 2);
v___x_3930_ = lean_array_push(v_x_3927_, v_arg_3929_);
v_x_3926_ = v_fn_3928_;
v_x_3927_ = v___x_3930_;
goto _start;
}
else
{
lean_dec_ref(v_x_3926_);
return v_x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3932_){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3933_ = l_Lean_Expr_getAppNumArgs(v_e_3932_);
v___x_3934_ = lean_mk_empty_array_with_capacity(v___x_3933_);
lean_dec(v___x_3933_);
v___x_3935_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3932_, v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3936_, lean_object* v_x_3937_, lean_object* v_x_3938_, lean_object* v_x_3939_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 5)
{
lean_object* v_fn_3940_; lean_object* v_arg_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_fn_3940_ = lean_ctor_get(v_x_3937_, 0);
lean_inc_ref(v_fn_3940_);
v_arg_3941_ = lean_ctor_get(v_x_3937_, 1);
lean_inc_ref(v_arg_3941_);
lean_dec_ref_known(v_x_3937_, 2);
v___x_3942_ = lean_array_set(v_x_3938_, v_x_3939_, v_arg_3941_);
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_nat_sub(v_x_3939_, v___x_3943_);
lean_dec(v_x_3939_);
v_x_3937_ = v_fn_3940_;
v_x_3938_ = v___x_3942_;
v_x_3939_ = v___x_3944_;
goto _start;
}
else
{
lean_object* v___x_3946_; 
lean_dec(v_x_3939_);
v___x_3946_ = lean_apply_2(v_k_3936_, v_x_3937_, v_x_3938_);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3947_, lean_object* v_k_3948_, lean_object* v_x_3949_, lean_object* v_x_3950_, lean_object* v_x_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_Expr_withAppAux___redArg(v_k_3948_, v_x_3949_, v_x_3950_, v_x_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3953_, lean_object* v_k_3954_){
_start:
{
lean_object* v_dummy_3955_; lean_object* v_nargs_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_dummy_3955_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3956_ = l_Lean_Expr_getAppNumArgs(v_e_3953_);
lean_inc(v_nargs_3956_);
v___x_3957_ = lean_mk_array(v_nargs_3956_, v_dummy_3955_);
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_sub(v_nargs_3956_, v___x_3958_);
lean_dec(v_nargs_3956_);
v___x_3960_ = l_Lean_Expr_withAppAux___redArg(v_k_3954_, v_e_3953_, v___x_3957_, v___x_3959_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3961_, lean_object* v_e_3962_, lean_object* v_k_3963_){
_start:
{
lean_object* v_dummy_3964_; lean_object* v_nargs_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_dummy_3964_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3965_ = l_Lean_Expr_getAppNumArgs(v_e_3962_);
lean_inc(v_nargs_3965_);
v___x_3966_ = lean_mk_array(v_nargs_3965_, v_dummy_3964_);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_sub(v_nargs_3965_, v___x_3967_);
lean_dec(v_nargs_3965_);
v___x_3969_ = l_Lean_Expr_withAppAux___redArg(v_k_3963_, v_e_3962_, v___x_3966_, v___x_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3970_, lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
if (lean_obj_tag(v_x_3970_) == 5)
{
lean_object* v_fn_3973_; lean_object* v_arg_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_fn_3973_ = lean_ctor_get(v_x_3970_, 0);
lean_inc_ref(v_fn_3973_);
v_arg_3974_ = lean_ctor_get(v_x_3970_, 1);
lean_inc_ref(v_arg_3974_);
lean_dec_ref_known(v_x_3970_, 2);
v___x_3975_ = lean_array_set(v_x_3971_, v_x_3972_, v_arg_3974_);
v___x_3976_ = lean_unsigned_to_nat(1u);
v___x_3977_ = lean_nat_sub(v_x_3972_, v___x_3976_);
lean_dec(v_x_3972_);
v_x_3970_ = v_fn_3973_;
v_x_3971_ = v___x_3975_;
v_x_3972_ = v___x_3977_;
goto _start;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v_x_3972_);
v___x_3979_ = l_Lean_Expr_constName(v_x_3970_);
lean_dec_ref(v_x_3970_);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
lean_ctor_set(v___x_3980_, 1, v_x_3971_);
return v___x_3980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3981_){
_start:
{
lean_object* v_dummy_3982_; lean_object* v_nargs_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_dummy_3982_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3983_ = l_Lean_Expr_getAppNumArgs(v_e_3981_);
lean_inc(v_nargs_3983_);
v___x_3984_ = lean_mk_array(v_nargs_3983_, v_dummy_3982_);
v___x_3985_ = lean_unsigned_to_nat(1u);
v___x_3986_ = lean_nat_sub(v_nargs_3983_, v___x_3985_);
lean_dec(v_nargs_3983_);
v___x_3987_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3981_, v___x_3984_, v___x_3986_);
return v___x_3987_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Array_instInhabited(lean_box(0));
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3989_){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3991_ = lean_panic_fn_borrowed(v___x_3990_, v_msg_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3994_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3995_ = lean_unsigned_to_nat(27u);
v___x_3996_ = lean_unsigned_to_nat(1247u);
v___x_3997_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_3998_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3999_ = l_mkPanicMessageWithDecl(v___x_3998_, v___x_3997_, v___x_3996_, v___x_3995_, v___x_3994_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_zero_4003_; uint8_t v_isZero_4004_; 
v_zero_4003_ = lean_unsigned_to_nat(0u);
v_isZero_4004_ = lean_nat_dec_eq(v_a_4000_, v_zero_4003_);
if (v_isZero_4004_ == 1)
{
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
return v_a_4002_;
}
else
{
if (lean_obj_tag(v_a_4001_) == 5)
{
lean_object* v_fn_4005_; lean_object* v_arg_4006_; lean_object* v_one_4007_; lean_object* v_n_4008_; lean_object* v___x_4009_; 
v_fn_4005_ = lean_ctor_get(v_a_4001_, 0);
lean_inc_ref(v_fn_4005_);
v_arg_4006_ = lean_ctor_get(v_a_4001_, 1);
lean_inc_ref(v_arg_4006_);
lean_dec_ref_known(v_a_4001_, 2);
v_one_4007_ = lean_unsigned_to_nat(1u);
v_n_4008_ = lean_nat_sub(v_a_4000_, v_one_4007_);
lean_dec(v_a_4000_);
v___x_4009_ = lean_array_set(v_a_4002_, v_n_4008_, v_arg_4006_);
v_a_4000_ = v_n_4008_;
v_a_4001_ = v_fn_4005_;
v_a_4002_ = v___x_4009_;
goto _start;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec_ref(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
v___x_4011_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_4012_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_4011_);
return v___x_4012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_4013_, lean_object* v_n_4014_){
_start:
{
lean_object* v_dummy_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v_dummy_4015_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_4014_);
v___x_4016_ = lean_mk_array(v_n_4014_, v_dummy_4015_);
v___x_4017_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_4014_, v_e_4013_, v___x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4018_, lean_object* v_n_4019_){
_start:
{
lean_object* v_zero_4020_; uint8_t v_isZero_4021_; 
v_zero_4020_ = lean_unsigned_to_nat(0u);
v_isZero_4021_ = lean_nat_dec_eq(v_n_4019_, v_zero_4020_);
if (v_isZero_4021_ == 1)
{
lean_dec(v_n_4019_);
lean_inc_ref(v_e_4018_);
return v_e_4018_;
}
else
{
if (lean_obj_tag(v_e_4018_) == 5)
{
lean_object* v_fn_4022_; lean_object* v_one_4023_; lean_object* v_n_4024_; 
v_fn_4022_ = lean_ctor_get(v_e_4018_, 0);
v_one_4023_ = lean_unsigned_to_nat(1u);
v_n_4024_ = lean_nat_sub(v_n_4019_, v_one_4023_);
lean_dec(v_n_4019_);
v_e_4018_ = v_fn_4022_;
v_n_4019_ = v_n_4024_;
goto _start;
}
else
{
lean_dec(v_n_4019_);
lean_inc_ref(v_e_4018_);
return v_e_4018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4026_, lean_object* v_n_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_Expr_stripArgsN(v_e_4026_, v_n_4027_);
lean_dec_ref(v_e_4026_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4029_, lean_object* v_n_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = l_Lean_Expr_getAppNumArgs(v_e_4029_);
v___x_4032_ = lean_nat_sub(v___x_4031_, v_n_4030_);
lean_dec(v___x_4031_);
v___x_4033_ = l_Lean_Expr_stripArgsN(v_e_4029_, v___x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4034_, lean_object* v_n_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Expr_getAppPrefix(v_e_4034_, v_n_4035_);
lean_dec(v_n_4035_);
lean_dec_ref(v_e_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4037_, lean_object* v_inst_4038_, lean_object* v_f_4039_, lean_object* v_x_4040_){
_start:
{
size_t v_sz_4041_; size_t v___x_4042_; lean_object* v___x_4043_; 
v_sz_4041_ = lean_array_size(v_args_4037_);
v___x_4042_ = ((size_t)0ULL);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4038_, v_f_4039_, v_sz_4041_, v___x_4042_, v_args_4037_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4045_, lean_object* v_inst_4046_, lean_object* v_f_4047_, lean_object* v_toSeq_4048_, lean_object* v_fn_4049_, lean_object* v_args_4050_){
_start:
{
lean_object* v_map_4051_; lean_object* v___f_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_map_4051_ = lean_ctor_get(v_toFunctor_4045_, 0);
lean_inc(v_map_4051_);
lean_dec_ref(v_toFunctor_4045_);
lean_inc(v_f_4047_);
v___f_4052_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4052_, 0, v_args_4050_);
lean_closure_set(v___f_4052_, 1, v_inst_4046_);
lean_closure_set(v___f_4052_, 2, v_f_4047_);
v___x_4053_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4054_ = lean_apply_1(v_f_4047_, v_fn_4049_);
v___x_4055_ = lean_apply_4(v_map_4051_, lean_box(0), lean_box(0), v___x_4053_, v___x_4054_);
v___x_4056_ = lean_apply_4(v_toSeq_4048_, lean_box(0), lean_box(0), v___x_4055_, v___f_4052_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4057_, lean_object* v_f_4058_, lean_object* v_e_4059_){
_start:
{
lean_object* v_toApplicative_4060_; lean_object* v_toFunctor_4061_; lean_object* v_toSeq_4062_; lean_object* v___f_4063_; lean_object* v_dummy_4064_; lean_object* v_nargs_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_toApplicative_4060_ = lean_ctor_get(v_inst_4057_, 0);
v_toFunctor_4061_ = lean_ctor_get(v_toApplicative_4060_, 0);
lean_inc_ref(v_toFunctor_4061_);
v_toSeq_4062_ = lean_ctor_get(v_toApplicative_4060_, 2);
lean_inc(v_toSeq_4062_);
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4063_, 0, v_toFunctor_4061_);
lean_closure_set(v___f_4063_, 1, v_inst_4057_);
lean_closure_set(v___f_4063_, 2, v_f_4058_);
lean_closure_set(v___f_4063_, 3, v_toSeq_4062_);
v_dummy_4064_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4065_ = l_Lean_Expr_getAppNumArgs(v_e_4059_);
lean_inc(v_nargs_4065_);
v___x_4066_ = lean_mk_array(v_nargs_4065_, v_dummy_4064_);
v___x_4067_ = lean_unsigned_to_nat(1u);
v___x_4068_ = lean_nat_sub(v_nargs_4065_, v___x_4067_);
lean_dec(v_nargs_4065_);
v___x_4069_ = l_Lean_Expr_withAppAux___redArg(v___f_4063_, v_e_4059_, v___x_4066_, v___x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4070_, lean_object* v_inst_4071_, lean_object* v_f_4072_, lean_object* v_e_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_Expr_traverseApp___redArg(v_inst_4071_, v_f_4072_, v_e_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4075_, lean_object* v_x_4076_, lean_object* v_x_4077_){
_start:
{
if (lean_obj_tag(v_x_4076_) == 5)
{
lean_object* v_fn_4078_; lean_object* v_arg_4079_; lean_object* v___x_4080_; 
v_fn_4078_ = lean_ctor_get(v_x_4076_, 0);
lean_inc_ref(v_fn_4078_);
v_arg_4079_ = lean_ctor_get(v_x_4076_, 1);
lean_inc_ref(v_arg_4079_);
lean_dec_ref_known(v_x_4076_, 2);
v___x_4080_ = lean_array_push(v_x_4077_, v_arg_4079_);
v_x_4076_ = v_fn_4078_;
v_x_4077_ = v___x_4080_;
goto _start;
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_apply_2(v_k_4075_, v_x_4076_, v_x_4077_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4083_, lean_object* v_k_4084_, lean_object* v_x_4085_, lean_object* v_x_4086_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4084_, v_x_4085_, v_x_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4088_, lean_object* v_k_4089_){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4090_ = l_Lean_Expr_getAppNumArgs(v_e_4088_);
v___x_4091_ = lean_mk_empty_array_with_capacity(v___x_4090_);
lean_dec(v___x_4090_);
v___x_4092_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4089_, v_e_4088_, v___x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4093_, lean_object* v_e_4094_, lean_object* v_k_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = l_Lean_Expr_getAppNumArgs(v_e_4094_);
v___x_4097_ = lean_mk_empty_array_with_capacity(v___x_4096_);
lean_dec(v___x_4096_);
v___x_4098_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4095_, v_e_4094_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4099_, lean_object* v_x_4100_, lean_object* v_x_4101_){
_start:
{
if (lean_obj_tag(v_x_4099_) == 5)
{
lean_object* v_fn_4102_; lean_object* v_arg_4103_; lean_object* v_zero_4104_; uint8_t v_isZero_4105_; 
v_fn_4102_ = lean_ctor_get(v_x_4099_, 0);
v_arg_4103_ = lean_ctor_get(v_x_4099_, 1);
v_zero_4104_ = lean_unsigned_to_nat(0u);
v_isZero_4105_ = lean_nat_dec_eq(v_x_4100_, v_zero_4104_);
if (v_isZero_4105_ == 1)
{
lean_dec(v_x_4100_);
lean_inc_ref(v_arg_4103_);
return v_arg_4103_;
}
else
{
lean_object* v_one_4106_; lean_object* v_n_4107_; 
v_one_4106_ = lean_unsigned_to_nat(1u);
v_n_4107_ = lean_nat_sub(v_x_4100_, v_one_4106_);
lean_dec(v_x_4100_);
v_x_4099_ = v_fn_4102_;
v_x_4100_ = v_n_4107_;
goto _start;
}
}
else
{
lean_dec(v_x_4100_);
lean_inc_ref(v_x_4101_);
return v_x_4101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4109_, lean_object* v_x_4110_, lean_object* v_x_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_Expr_getRevArgD(v_x_4109_, v_x_4110_, v_x_4111_);
lean_dec_ref(v_x_4111_);
lean_dec_ref(v_x_4109_);
return v_res_4112_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4115_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4116_ = lean_unsigned_to_nat(20u);
v___x_4117_ = lean_unsigned_to_nat(1288u);
v___x_4118_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4119_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4120_ = l_mkPanicMessageWithDecl(v___x_4119_, v___x_4118_, v___x_4117_, v___x_4116_, v___x_4115_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4121_, lean_object* v_x_4122_){
_start:
{
if (lean_obj_tag(v_x_4121_) == 5)
{
lean_object* v_fn_4123_; lean_object* v_arg_4124_; lean_object* v_zero_4125_; uint8_t v_isZero_4126_; 
v_fn_4123_ = lean_ctor_get(v_x_4121_, 0);
v_arg_4124_ = lean_ctor_get(v_x_4121_, 1);
v_zero_4125_ = lean_unsigned_to_nat(0u);
v_isZero_4126_ = lean_nat_dec_eq(v_x_4122_, v_zero_4125_);
if (v_isZero_4126_ == 1)
{
lean_dec(v_x_4122_);
lean_inc_ref(v_arg_4124_);
return v_arg_4124_;
}
else
{
lean_object* v_one_4127_; lean_object* v_n_4128_; 
v_one_4127_ = lean_unsigned_to_nat(1u);
v_n_4128_ = lean_nat_sub(v_x_4122_, v_one_4127_);
lean_dec(v_x_4122_);
v_x_4121_ = v_fn_4123_;
v_x_4122_ = v_n_4128_;
goto _start;
}
}
else
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_dec(v_x_4122_);
v___x_4130_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4131_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4130_);
return v___x_4131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4132_, lean_object* v_x_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Lean_Expr_getRevArg_x21(v_x_4132_, v_x_4133_);
lean_dec_ref(v_x_4132_);
return v_res_4134_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4136_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4137_ = lean_unsigned_to_nat(20u);
v___x_4138_ = lean_unsigned_to_nat(1295u);
v___x_4139_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4140_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4141_ = l_mkPanicMessageWithDecl(v___x_4140_, v___x_4139_, v___x_4138_, v___x_4137_, v___x_4136_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4142_, lean_object* v_x_4143_){
_start:
{
switch(lean_obj_tag(v_x_4142_))
{
case 10:
{
lean_object* v_expr_4144_; 
v_expr_4144_ = lean_ctor_get(v_x_4142_, 1);
v_x_4142_ = v_expr_4144_;
goto _start;
}
case 5:
{
lean_object* v_fn_4146_; lean_object* v_arg_4147_; lean_object* v_zero_4148_; uint8_t v_isZero_4149_; 
v_fn_4146_ = lean_ctor_get(v_x_4142_, 0);
v_arg_4147_ = lean_ctor_get(v_x_4142_, 1);
v_zero_4148_ = lean_unsigned_to_nat(0u);
v_isZero_4149_ = lean_nat_dec_eq(v_x_4143_, v_zero_4148_);
if (v_isZero_4149_ == 1)
{
lean_dec(v_x_4143_);
lean_inc_ref(v_arg_4147_);
return v_arg_4147_;
}
else
{
lean_object* v_one_4150_; lean_object* v_n_4151_; 
v_one_4150_ = lean_unsigned_to_nat(1u);
v_n_4151_ = lean_nat_sub(v_x_4143_, v_one_4150_);
lean_dec(v_x_4143_);
v_x_4142_ = v_fn_4146_;
v_x_4143_ = v_n_4151_;
goto _start;
}
}
default: 
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec(v_x_4143_);
v___x_4153_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4154_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4153_);
return v___x_4154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4155_, lean_object* v_x_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4155_, v_x_4156_);
lean_dec_ref(v_x_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4158_, lean_object* v_i_4159_, lean_object* v_n_4160_){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4161_ = lean_nat_sub(v_n_4160_, v_i_4159_);
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4163_ = lean_nat_sub(v___x_4161_, v___x_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = l_Lean_Expr_getRevArg_x21(v_e_4158_, v___x_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4165_, lean_object* v_i_4166_, lean_object* v_n_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Expr_getArg_x21(v_e_4165_, v_i_4166_, v_n_4167_);
lean_dec(v_n_4167_);
lean_dec(v_i_4166_);
lean_dec_ref(v_e_4165_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4169_, lean_object* v_i_4170_, lean_object* v_n_4171_){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4172_ = lean_nat_sub(v_n_4171_, v_i_4170_);
v___x_4173_ = lean_unsigned_to_nat(1u);
v___x_4174_ = lean_nat_sub(v___x_4172_, v___x_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4169_, v___x_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4176_, lean_object* v_i_4177_, lean_object* v_n_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Expr_getArg_x21_x27(v_e_4176_, v_i_4177_, v_n_4178_);
lean_dec(v_n_4178_);
lean_dec(v_i_4177_);
lean_dec_ref(v_e_4176_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4180_, lean_object* v_i_4181_, lean_object* v_v_u2080_4182_, lean_object* v_n_4183_){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4184_ = lean_nat_sub(v_n_4183_, v_i_4181_);
v___x_4185_ = lean_unsigned_to_nat(1u);
v___x_4186_ = lean_nat_sub(v___x_4184_, v___x_4185_);
lean_dec(v___x_4184_);
v___x_4187_ = l_Lean_Expr_getRevArgD(v_e_4180_, v___x_4186_, v_v_u2080_4182_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4188_, lean_object* v_i_4189_, lean_object* v_v_u2080_4190_, lean_object* v_n_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Expr_getArgD(v_e_4188_, v_i_4189_, v_v_u2080_4190_, v_n_4191_);
lean_dec(v_n_4191_);
lean_dec_ref(v_v_u2080_4190_);
lean_dec(v_i_4189_);
lean_dec_ref(v_e_4188_);
return v_res_4192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4193_){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4194_ = lean_unsigned_to_nat(0u);
v___x_4195_ = l_Lean_Expr_looseBVarRange(v_e_4193_);
v___x_4196_ = lean_nat_dec_lt(v___x_4194_, v___x_4195_);
lean_dec(v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4197_){
_start:
{
uint8_t v_res_4198_; lean_object* v_r_4199_; 
v_res_4198_ = l_Lean_Expr_hasLooseBVars(v_e_4197_);
lean_dec_ref(v_e_4197_);
v_r_4199_ = lean_box(v_res_4198_);
return v_r_4199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4200_){
_start:
{
if (lean_obj_tag(v_e_4200_) == 7)
{
lean_object* v_body_4201_; uint8_t v___x_4202_; 
v_body_4201_ = lean_ctor_get(v_e_4200_, 2);
v___x_4202_ = l_Lean_Expr_hasLooseBVars(v_body_4201_);
if (v___x_4202_ == 0)
{
uint8_t v___x_4203_; 
v___x_4203_ = 1;
return v___x_4203_;
}
else
{
uint8_t v___x_4204_; 
v___x_4204_ = 0;
return v___x_4204_;
}
}
else
{
uint8_t v___x_4205_; 
v___x_4205_ = 0;
return v___x_4205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4206_){
_start:
{
uint8_t v_res_4207_; lean_object* v_r_4208_; 
v_res_4207_ = l_Lean_Expr_isArrow(v_e_4206_);
lean_dec_ref(v_e_4206_);
v_r_4208_ = lean_box(v_res_4207_);
return v_r_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4211_, lean_object* v_bvarIdx_4212_){
_start:
{
uint8_t v_res_4213_; lean_object* v_r_4214_; 
v_res_4213_ = lean_expr_has_loose_bvar(v_e_4211_, v_bvarIdx_4212_);
lean_dec(v_bvarIdx_4212_);
lean_dec_ref(v_e_4211_);
v_r_4214_ = lean_box(v_res_4213_);
return v_r_4214_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4215_, lean_object* v_bvarIdx_4216_, uint8_t v_considerRange_4217_){
_start:
{
if (lean_obj_tag(v_e_4215_) == 7)
{
lean_object* v_binderType_4218_; lean_object* v_body_4219_; uint8_t v_binderInfo_4220_; uint8_t v___y_4222_; uint8_t v___x_4226_; 
v_binderType_4218_ = lean_ctor_get(v_e_4215_, 1);
v_body_4219_ = lean_ctor_get(v_e_4215_, 2);
v_binderInfo_4220_ = lean_ctor_get_uint8(v_e_4215_, sizeof(void*)*3 + 8);
v___x_4226_ = lean_expr_has_loose_bvar(v_binderType_4218_, v_bvarIdx_4216_);
if (v___x_4226_ == 0)
{
v___y_4222_ = v___x_4226_;
goto v___jp_4221_;
}
else
{
uint8_t v___x_4227_; 
v___x_4227_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4220_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4219_, v___x_4228_, v_considerRange_4217_);
v___y_4222_ = v___x_4229_;
goto v___jp_4221_;
}
else
{
v___y_4222_ = v___x_4227_;
goto v___jp_4221_;
}
}
v___jp_4221_:
{
if (v___y_4222_ == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_unsigned_to_nat(1u);
v___x_4224_ = lean_nat_add(v_bvarIdx_4216_, v___x_4223_);
lean_dec(v_bvarIdx_4216_);
v_e_4215_ = v_body_4219_;
v_bvarIdx_4216_ = v___x_4224_;
goto _start;
}
else
{
lean_dec(v_bvarIdx_4216_);
return v___y_4222_;
}
}
}
else
{
if (v_considerRange_4217_ == 0)
{
lean_dec(v_bvarIdx_4216_);
return v_considerRange_4217_;
}
else
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_expr_has_loose_bvar(v_e_4215_, v_bvarIdx_4216_);
lean_dec(v_bvarIdx_4216_);
return v___x_4230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4231_, lean_object* v_bvarIdx_4232_, lean_object* v_considerRange_4233_){
_start:
{
uint8_t v_considerRange_boxed_4234_; uint8_t v_res_4235_; lean_object* v_r_4236_; 
v_considerRange_boxed_4234_ = lean_unbox(v_considerRange_4233_);
v_res_4235_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4231_, v_bvarIdx_4232_, v_considerRange_boxed_4234_);
lean_dec_ref(v_e_4231_);
v_r_4236_ = lean_box(v_res_4235_);
return v_r_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4240_, lean_object* v_s_4241_, lean_object* v_d_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = lean_expr_lower_loose_bvars(v_e_4240_, v_s_4241_, v_d_4242_);
lean_dec(v_d_4242_);
lean_dec(v_s_4241_);
lean_dec_ref(v_e_4240_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4247_, lean_object* v_s_4248_, lean_object* v_d_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = lean_expr_lift_loose_bvars(v_e_4247_, v_s_4248_, v_d_4249_);
lean_dec(v_d_4249_);
lean_dec(v_s_4248_);
lean_dec_ref(v_e_4247_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4251_, lean_object* v_numParams_4252_, uint8_t v_considerRange_4253_){
_start:
{
if (lean_obj_tag(v_e_4251_) == 7)
{
lean_object* v_binderName_4254_; lean_object* v_binderType_4255_; lean_object* v_body_4256_; uint8_t v_binderInfo_4257_; lean_object* v_zero_4258_; uint8_t v_isZero_4259_; 
v_binderName_4254_ = lean_ctor_get(v_e_4251_, 0);
v_binderType_4255_ = lean_ctor_get(v_e_4251_, 1);
v_body_4256_ = lean_ctor_get(v_e_4251_, 2);
v_binderInfo_4257_ = lean_ctor_get_uint8(v_e_4251_, sizeof(void*)*3 + 8);
v_zero_4258_ = lean_unsigned_to_nat(0u);
v_isZero_4259_ = lean_nat_dec_eq(v_numParams_4252_, v_zero_4258_);
if (v_isZero_4259_ == 0)
{
lean_object* v_one_4260_; lean_object* v_n_4261_; lean_object* v_b_4262_; uint8_t v___y_4264_; uint8_t v___x_4268_; 
lean_inc_ref(v_body_4256_);
lean_inc_ref(v_binderType_4255_);
lean_inc(v_binderName_4254_);
lean_dec_ref_known(v_e_4251_, 3);
v_one_4260_ = lean_unsigned_to_nat(1u);
v_n_4261_ = lean_nat_sub(v_numParams_4252_, v_one_4260_);
v_b_4262_ = l_Lean_Expr_inferImplicit(v_body_4256_, v_n_4261_, v_considerRange_4253_);
lean_dec(v_n_4261_);
v___x_4268_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4257_);
if (v___x_4268_ == 0)
{
v___y_4264_ = v___x_4268_;
goto v___jp_4263_;
}
else
{
uint8_t v___x_4269_; 
v___x_4269_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4262_, v_zero_4258_, v_considerRange_4253_);
v___y_4264_ = v___x_4269_;
goto v___jp_4263_;
}
v___jp_4263_:
{
if (v___y_4264_ == 0)
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Lean_Expr_forallE___override(v_binderName_4254_, v_binderType_4255_, v_b_4262_, v_binderInfo_4257_);
return v___x_4265_;
}
else
{
uint8_t v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = 1;
v___x_4267_ = l_Lean_Expr_forallE___override(v_binderName_4254_, v_binderType_4255_, v_b_4262_, v___x_4266_);
return v___x_4267_;
}
}
}
else
{
return v_e_4251_;
}
}
else
{
return v_e_4251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4270_, lean_object* v_numParams_4271_, lean_object* v_considerRange_4272_){
_start:
{
uint8_t v_considerRange_boxed_4273_; lean_object* v_res_4274_; 
v_considerRange_boxed_4273_ = lean_unbox(v_considerRange_4272_);
v_res_4274_ = l_Lean_Expr_inferImplicit(v_e_4270_, v_numParams_4271_, v_considerRange_boxed_4273_);
lean_dec(v_numParams_4271_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4275_, lean_object* v_binderInfos_x3f_4276_){
_start:
{
if (lean_obj_tag(v_e_4275_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4276_) == 1)
{
lean_object* v_binderName_4277_; lean_object* v_binderType_4278_; lean_object* v_body_4279_; uint8_t v_binderInfo_4280_; lean_object* v_head_4281_; lean_object* v_tail_4282_; lean_object* v_b_4283_; 
v_binderName_4277_ = lean_ctor_get(v_e_4275_, 0);
lean_inc(v_binderName_4277_);
v_binderType_4278_ = lean_ctor_get(v_e_4275_, 1);
lean_inc_ref(v_binderType_4278_);
v_body_4279_ = lean_ctor_get(v_e_4275_, 2);
lean_inc_ref(v_body_4279_);
v_binderInfo_4280_ = lean_ctor_get_uint8(v_e_4275_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4275_, 3);
v_head_4281_ = lean_ctor_get(v_binderInfos_x3f_4276_, 0);
v_tail_4282_ = lean_ctor_get(v_binderInfos_x3f_4276_, 1);
v_b_4283_ = l_Lean_Expr_updateForallBinderInfos(v_body_4279_, v_tail_4282_);
if (lean_obj_tag(v_head_4281_) == 0)
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Expr_forallE___override(v_binderName_4277_, v_binderType_4278_, v_b_4283_, v_binderInfo_4280_);
return v___x_4284_;
}
else
{
lean_object* v_val_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; 
v_val_4285_ = lean_ctor_get(v_head_4281_, 0);
v___x_4286_ = lean_unbox(v_val_4285_);
v___x_4287_ = l_Lean_Expr_forallE___override(v_binderName_4277_, v_binderType_4278_, v_b_4283_, v___x_4286_);
return v___x_4287_;
}
}
else
{
return v_e_4275_;
}
}
else
{
return v_e_4275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4288_, lean_object* v_binderInfos_x3f_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Expr_updateForallBinderInfos(v_e_4288_, v_binderInfos_x3f_4289_);
lean_dec(v_binderInfos_x3f_4289_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4291_, lean_object* v_binderNames_x3f_4292_){
_start:
{
switch(lean_obj_tag(v_e_4291_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4292_) == 1)
{
lean_object* v_binderName_4293_; lean_object* v_binderType_4294_; lean_object* v_body_4295_; uint8_t v_binderInfo_4296_; lean_object* v_head_4297_; lean_object* v_tail_4298_; lean_object* v_b_4299_; 
v_binderName_4293_ = lean_ctor_get(v_e_4291_, 0);
lean_inc(v_binderName_4293_);
v_binderType_4294_ = lean_ctor_get(v_e_4291_, 1);
lean_inc_ref(v_binderType_4294_);
v_body_4295_ = lean_ctor_get(v_e_4291_, 2);
lean_inc_ref(v_body_4295_);
v_binderInfo_4296_ = lean_ctor_get_uint8(v_e_4291_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4291_, 3);
v_head_4297_ = lean_ctor_get(v_binderNames_x3f_4292_, 0);
lean_inc(v_head_4297_);
v_tail_4298_ = lean_ctor_get(v_binderNames_x3f_4292_, 1);
lean_inc(v_tail_4298_);
lean_dec_ref_known(v_binderNames_x3f_4292_, 2);
v_b_4299_ = l_Lean_Expr_updateBinderNames(v_body_4295_, v_tail_4298_);
if (lean_obj_tag(v_head_4297_) == 0)
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_Expr_forallE___override(v_binderName_4293_, v_binderType_4294_, v_b_4299_, v_binderInfo_4296_);
return v___x_4300_;
}
else
{
lean_object* v_val_4301_; lean_object* v___x_4302_; 
lean_dec(v_binderName_4293_);
v_val_4301_ = lean_ctor_get(v_head_4297_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v_head_4297_, 1);
v___x_4302_ = l_Lean_Expr_forallE___override(v_val_4301_, v_binderType_4294_, v_b_4299_, v_binderInfo_4296_);
return v___x_4302_;
}
}
else
{
lean_dec(v_binderNames_x3f_4292_);
return v_e_4291_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4292_) == 1)
{
lean_object* v_binderName_4303_; lean_object* v_binderType_4304_; lean_object* v_body_4305_; uint8_t v_binderInfo_4306_; lean_object* v_head_4307_; lean_object* v_tail_4308_; lean_object* v_b_4309_; 
v_binderName_4303_ = lean_ctor_get(v_e_4291_, 0);
lean_inc(v_binderName_4303_);
v_binderType_4304_ = lean_ctor_get(v_e_4291_, 1);
lean_inc_ref(v_binderType_4304_);
v_body_4305_ = lean_ctor_get(v_e_4291_, 2);
lean_inc_ref(v_body_4305_);
v_binderInfo_4306_ = lean_ctor_get_uint8(v_e_4291_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4291_, 3);
v_head_4307_ = lean_ctor_get(v_binderNames_x3f_4292_, 0);
lean_inc(v_head_4307_);
v_tail_4308_ = lean_ctor_get(v_binderNames_x3f_4292_, 1);
lean_inc(v_tail_4308_);
lean_dec_ref_known(v_binderNames_x3f_4292_, 2);
v_b_4309_ = l_Lean_Expr_updateBinderNames(v_body_4305_, v_tail_4308_);
if (lean_obj_tag(v_head_4307_) == 0)
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_Expr_lam___override(v_binderName_4303_, v_binderType_4304_, v_b_4309_, v_binderInfo_4306_);
return v___x_4310_;
}
else
{
lean_object* v_val_4311_; lean_object* v___x_4312_; 
lean_dec(v_binderName_4303_);
v_val_4311_ = lean_ctor_get(v_head_4307_, 0);
lean_inc(v_val_4311_);
lean_dec_ref_known(v_head_4307_, 1);
v___x_4312_ = l_Lean_Expr_lam___override(v_val_4311_, v_binderType_4304_, v_b_4309_, v_binderInfo_4306_);
return v___x_4312_;
}
}
else
{
lean_dec(v_binderNames_x3f_4292_);
return v_e_4291_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4292_);
return v_e_4291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4315_, lean_object* v_subst_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = lean_expr_instantiate(v_e_4315_, v_subst_4316_);
lean_dec_ref(v_subst_4316_);
lean_dec_ref(v_e_4315_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4320_, lean_object* v_subst_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = lean_expr_instantiate1(v_e_4320_, v_subst_4321_);
lean_dec_ref(v_subst_4321_);
lean_dec_ref(v_e_4320_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4325_, lean_object* v_subst_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = lean_expr_instantiate_rev(v_e_4325_, v_subst_4326_);
lean_dec_ref(v_subst_4326_);
lean_dec_ref(v_e_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4332_, lean_object* v_beginIdx_4333_, lean_object* v_endIdx_4334_, lean_object* v_subst_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = lean_expr_instantiate_range(v_e_4332_, v_beginIdx_4333_, v_endIdx_4334_, v_subst_4335_);
lean_dec_ref(v_subst_4335_);
lean_dec(v_endIdx_4334_);
lean_dec(v_beginIdx_4333_);
lean_dec_ref(v_e_4332_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4341_, lean_object* v_beginIdx_4342_, lean_object* v_endIdx_4343_, lean_object* v_subst_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = lean_expr_instantiate_rev_range(v_e_4341_, v_beginIdx_4342_, v_endIdx_4343_, v_subst_4344_);
lean_dec_ref(v_subst_4344_);
lean_dec(v_endIdx_4343_);
lean_dec(v_beginIdx_4342_);
lean_dec_ref(v_e_4341_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4348_, lean_object* v_xs_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = lean_expr_abstract(v_e_4348_, v_xs_4349_);
lean_dec_ref(v_xs_4349_);
lean_dec_ref(v_e_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4354_, lean_object* v_n_4355_, lean_object* v_xs_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = lean_expr_abstract_range(v_e_4354_, v_n_4355_, v_xs_4356_);
lean_dec_ref(v_xs_4356_);
lean_dec(v_n_4355_);
lean_dec_ref(v_e_4354_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4358_, lean_object* v_fvar_4359_, lean_object* v_v_4360_){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = lean_mk_empty_array_with_capacity(v___x_4361_);
v___x_4363_ = lean_array_push(v___x_4362_, v_fvar_4359_);
v___x_4364_ = lean_expr_abstract(v_e_4358_, v___x_4363_);
lean_dec_ref(v___x_4363_);
v___x_4365_ = lean_expr_instantiate1(v___x_4364_, v_v_4360_);
lean_dec_ref(v___x_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4366_, lean_object* v_fvar_4367_, lean_object* v_v_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_Expr_replaceFVar(v_e_4366_, v_fvar_4367_, v_v_4368_);
lean_dec_ref(v_v_4368_);
lean_dec_ref(v_e_4366_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4370_, lean_object* v_fvarId_4371_, lean_object* v_v_4372_){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = l_Lean_Expr_fvar___override(v_fvarId_4371_);
v___x_4374_ = l_Lean_Expr_replaceFVar(v_e_4370_, v___x_4373_, v_v_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4375_, lean_object* v_fvarId_4376_, lean_object* v_v_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Expr_replaceFVarId(v_e_4375_, v_fvarId_4376_, v_v_4377_);
lean_dec_ref(v_v_4377_);
lean_dec_ref(v_e_4375_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4379_, lean_object* v_fvars_4380_, lean_object* v_vs_4381_){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = lean_expr_abstract(v_e_4379_, v_fvars_4380_);
v___x_4383_ = lean_expr_instantiate_rev(v___x_4382_, v_vs_4381_);
lean_dec_ref(v___x_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4384_, lean_object* v_fvars_4385_, lean_object* v_vs_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Expr_replaceFVars(v_e_4384_, v_fvars_4385_, v_vs_4386_);
lean_dec_ref(v_vs_4386_);
lean_dec_ref(v_fvars_4385_);
lean_dec_ref(v_e_4384_);
return v_res_4387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4390_){
_start:
{
switch(lean_obj_tag(v_x_4390_))
{
case 4:
{
uint8_t v___x_4391_; 
v___x_4391_ = 1;
return v___x_4391_;
}
case 3:
{
uint8_t v___x_4392_; 
v___x_4392_ = 1;
return v___x_4392_;
}
case 0:
{
uint8_t v___x_4393_; 
v___x_4393_ = 1;
return v___x_4393_;
}
case 9:
{
uint8_t v___x_4394_; 
v___x_4394_ = 1;
return v___x_4394_;
}
case 2:
{
uint8_t v___x_4395_; 
v___x_4395_ = 1;
return v___x_4395_;
}
case 1:
{
uint8_t v___x_4396_; 
v___x_4396_ = 1;
return v___x_4396_;
}
default: 
{
uint8_t v___x_4397_; 
v___x_4397_ = 0;
return v___x_4397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4398_){
_start:
{
uint8_t v_res_4399_; lean_object* v_r_4400_; 
v_res_4399_ = l_Lean_Expr_isAtomic(v_x_4398_);
lean_dec_ref(v_x_4398_);
v_r_4400_ = lean_box(v_res_4399_);
return v_r_4400_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = lean_box(0);
v___x_4407_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4408_ = l_Lean_Expr_const___override(v___x_4407_, v___x_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4409_, lean_object* v_proof_4410_){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4412_ = l_Lean_mkAppB(v___x_4411_, v_pred_4409_, v_proof_4410_);
return v___x_4412_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = lean_box(0);
v___x_4418_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4419_ = l_Lean_Expr_const___override(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4420_, lean_object* v_proof_4421_){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4423_ = l_Lean_mkAppB(v___x_4422_, v_pred_4420_, v_proof_4421_);
return v___x_4423_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4425_; 
v___x_4425_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4426_){
_start:
{
lean_inc_ref(v_val_4426_);
return v_val_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4427_);
lean_dec_ref(v_val_4427_);
return v_res_4428_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4431_, lean_object* v_x_4432_){
_start:
{
uint8_t v___x_4433_; 
v___x_4433_ = lean_expr_equal(v_x_4431_, v_x_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4434_, lean_object* v_x_4435_){
_start:
{
uint8_t v_res_4436_; lean_object* v_r_4437_; 
v_res_4436_ = l_Lean_ExprStructEq_beq(v_x_4434_, v_x_4435_);
lean_dec_ref(v_x_4435_);
lean_dec_ref(v_x_4434_);
v_r_4437_ = lean_box(v_res_4436_);
return v_r_4437_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4438_){
_start:
{
uint64_t v___x_4439_; 
v___x_4439_ = l_Lean_Expr_hash(v_x_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4440_){
_start:
{
uint64_t v_res_4441_; lean_object* v_r_4442_; 
v_res_4441_ = l_Lean_ExprStructEq_hash(v_x_4440_);
lean_dec_ref(v_x_4440_);
v_r_4442_ = lean_box_uint64(v_res_4441_);
return v_r_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4449_, lean_object* v_start_4450_, lean_object* v_b_4451_, lean_object* v_i_4452_){
_start:
{
uint8_t v___x_4453_; 
v___x_4453_ = lean_nat_dec_le(v_i_4452_, v_start_4450_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; lean_object* v_i_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4454_ = lean_unsigned_to_nat(1u);
v_i_4455_ = lean_nat_sub(v_i_4452_, v___x_4454_);
lean_dec(v_i_4452_);
v___x_4456_ = l_Lean_instInhabitedExpr;
v___x_4457_ = lean_array_get_borrowed(v___x_4456_, v_revArgs_4449_, v_i_4455_);
lean_inc(v___x_4457_);
v___x_4458_ = l_Lean_Expr_app___override(v_b_4451_, v___x_4457_);
v_b_4451_ = v___x_4458_;
v_i_4452_ = v_i_4455_;
goto _start;
}
else
{
lean_dec(v_i_4452_);
return v_b_4451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4460_, lean_object* v_start_4461_, lean_object* v_b_4462_, lean_object* v_i_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4460_, v_start_4461_, v_b_4462_, v_i_4463_);
lean_dec(v_start_4461_);
lean_dec_ref(v_revArgs_4460_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4465_, lean_object* v_beginIdx_4466_, lean_object* v_endIdx_4467_, lean_object* v_revArgs_4468_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4468_, v_beginIdx_4466_, v_f_4465_, v_endIdx_4467_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4470_, lean_object* v_beginIdx_4471_, lean_object* v_endIdx_4472_, lean_object* v_revArgs_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Lean_Expr_mkAppRevRange(v_f_4470_, v_beginIdx_4471_, v_endIdx_4472_, v_revArgs_4473_);
lean_dec_ref(v_revArgs_4473_);
lean_dec(v_beginIdx_4471_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4475_, uint8_t v_useZeta_4476_, uint8_t v_preserveMData_4477_, lean_object* v_sz_4478_, lean_object* v_e_4479_, lean_object* v_i_4480_){
_start:
{
switch(lean_obj_tag(v_e_4479_))
{
case 6:
{
lean_object* v_body_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v_body_4486_ = lean_ctor_get(v_e_4479_, 2);
lean_inc_ref(v_body_4486_);
lean_dec_ref_known(v_e_4479_, 3);
v___x_4487_ = lean_unsigned_to_nat(1u);
v___x_4488_ = lean_nat_add(v_i_4480_, v___x_4487_);
lean_dec(v_i_4480_);
v___x_4489_ = lean_nat_dec_lt(v___x_4488_, v_sz_4478_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; 
lean_dec(v___x_4488_);
v___x_4490_ = lean_expr_instantiate(v_body_4486_, v_revArgs_4475_);
lean_dec_ref(v_body_4486_);
return v___x_4490_;
}
else
{
v_e_4479_ = v_body_4486_;
v_i_4480_ = v___x_4488_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4476_ == 0)
{
goto v___jp_4481_;
}
else
{
lean_object* v_value_4492_; lean_object* v_body_4493_; uint8_t v___x_4494_; 
v_value_4492_ = lean_ctor_get(v_e_4479_, 2);
v_body_4493_ = lean_ctor_get(v_e_4479_, 3);
v___x_4494_ = lean_nat_dec_lt(v_i_4480_, v_sz_4478_);
if (v___x_4494_ == 0)
{
goto v___jp_4481_;
}
else
{
lean_object* v___x_4495_; 
lean_inc_ref(v_body_4493_);
lean_inc_ref(v_value_4492_);
lean_dec_ref_known(v_e_4479_, 4);
v___x_4495_ = lean_expr_instantiate1(v_body_4493_, v_value_4492_);
lean_dec_ref(v_value_4492_);
lean_dec_ref(v_body_4493_);
v_e_4479_ = v___x_4495_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4477_ == 0)
{
lean_object* v_expr_4497_; 
v_expr_4497_ = lean_ctor_get(v_e_4479_, 1);
lean_inc_ref(v_expr_4497_);
lean_dec_ref_known(v_e_4479_, 2);
v_e_4479_ = v_expr_4497_;
goto _start;
}
else
{
goto v___jp_4481_;
}
}
default: 
{
goto v___jp_4481_;
}
}
v___jp_4481_:
{
lean_object* v_n_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v_n_4482_ = lean_nat_sub(v_sz_4478_, v_i_4480_);
lean_dec(v_i_4480_);
v___x_4483_ = lean_expr_instantiate_range(v_e_4479_, v_n_4482_, v_sz_4478_, v_revArgs_4475_);
lean_dec_ref(v_e_4479_);
v___x_4484_ = lean_unsigned_to_nat(0u);
v___x_4485_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4475_, v___x_4484_, v___x_4483_, v_n_4482_);
return v___x_4485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4499_, lean_object* v_useZeta_4500_, lean_object* v_preserveMData_4501_, lean_object* v_sz_4502_, lean_object* v_e_4503_, lean_object* v_i_4504_){
_start:
{
uint8_t v_useZeta_boxed_4505_; uint8_t v_preserveMData_boxed_4506_; lean_object* v_res_4507_; 
v_useZeta_boxed_4505_ = lean_unbox(v_useZeta_4500_);
v_preserveMData_boxed_4506_ = lean_unbox(v_preserveMData_4501_);
v_res_4507_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4499_, v_useZeta_boxed_4505_, v_preserveMData_boxed_4506_, v_sz_4502_, v_e_4503_, v_i_4504_);
lean_dec(v_sz_4502_);
lean_dec_ref(v_revArgs_4499_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4508_, lean_object* v_revArgs_4509_, uint8_t v_useZeta_4510_, uint8_t v_preserveMData_4511_){
_start:
{
lean_object* v_sz_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v_sz_4512_ = lean_array_get_size(v_revArgs_4509_);
v___x_4513_ = lean_unsigned_to_nat(0u);
v___x_4514_ = lean_nat_dec_eq(v_sz_4512_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; 
v___x_4515_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4509_, v_useZeta_4510_, v_preserveMData_4511_, v_sz_4512_, v_f_4508_, v___x_4513_);
return v___x_4515_;
}
else
{
return v_f_4508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4516_, lean_object* v_revArgs_4517_, lean_object* v_useZeta_4518_, lean_object* v_preserveMData_4519_){
_start:
{
uint8_t v_useZeta_boxed_4520_; uint8_t v_preserveMData_boxed_4521_; lean_object* v_res_4522_; 
v_useZeta_boxed_4520_ = lean_unbox(v_useZeta_4518_);
v_preserveMData_boxed_4521_ = lean_unbox(v_preserveMData_4519_);
v_res_4522_ = l_Lean_Expr_betaRev(v_f_4516_, v_revArgs_4517_, v_useZeta_boxed_4520_, v_preserveMData_boxed_4521_);
lean_dec_ref(v_revArgs_4517_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4523_, lean_object* v_args_4524_){
_start:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = l_Array_reverse___redArg(v_args_4524_);
v___x_4526_ = 0;
v___x_4527_ = l_Lean_Expr_betaRev(v_f_4523_, v___x_4525_, v___x_4526_, v___x_4526_);
lean_dec_ref(v___x_4525_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4528_){
_start:
{
switch(lean_obj_tag(v_x_4528_))
{
case 6:
{
lean_object* v_body_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v_body_4529_ = lean_ctor_get(v_x_4528_, 2);
v___x_4530_ = l_Lean_Expr_getNumHeadLambdas(v_body_4529_);
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_nat_add(v___x_4530_, v___x_4531_);
lean_dec(v___x_4530_);
return v___x_4532_;
}
case 10:
{
lean_object* v_expr_4533_; 
v_expr_4533_ = lean_ctor_get(v_x_4528_, 1);
v_x_4528_ = v_expr_4533_;
goto _start;
}
default: 
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_unsigned_to_nat(0u);
return v___x_4535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_Expr_getNumHeadLambdas(v_x_4536_);
lean_dec_ref(v_x_4536_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4538_){
_start:
{
switch(lean_obj_tag(v_x_4538_))
{
case 6:
{
lean_object* v_body_4539_; 
v_body_4539_ = lean_ctor_get(v_x_4538_, 2);
v_x_4538_ = v_body_4539_;
goto _start;
}
case 10:
{
lean_object* v_expr_4541_; 
v_expr_4541_ = lean_ctor_get(v_x_4538_, 1);
v_x_4538_ = v_expr_4541_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4538_);
return v_x_4538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Expr_getLambdaBody(v_x_4543_);
lean_dec_ref(v_x_4543_);
return v_res_4544_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4545_, lean_object* v_x_4546_){
_start:
{
switch(lean_obj_tag(v_x_4546_))
{
case 6:
{
uint8_t v___x_4547_; 
v___x_4547_ = 1;
return v___x_4547_;
}
case 8:
{
if (v_useZeta_4545_ == 0)
{
return v_useZeta_4545_;
}
else
{
lean_object* v_body_4548_; 
v_body_4548_ = lean_ctor_get(v_x_4546_, 3);
v_x_4546_ = v_body_4548_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4550_; 
v_expr_4550_ = lean_ctor_get(v_x_4546_, 1);
v_x_4546_ = v_expr_4550_;
goto _start;
}
default: 
{
uint8_t v___x_4552_; 
v___x_4552_ = 0;
return v___x_4552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4553_, lean_object* v_x_4554_){
_start:
{
uint8_t v_useZeta_boxed_4555_; uint8_t v_res_4556_; lean_object* v_r_4557_; 
v_useZeta_boxed_4555_ = lean_unbox(v_useZeta_4553_);
v_res_4556_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4555_, v_x_4554_);
lean_dec_ref(v_x_4554_);
v_r_4557_ = lean_box(v_res_4556_);
return v_r_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4558_){
_start:
{
lean_object* v_f_4559_; uint8_t v___x_4560_; uint8_t v___x_4561_; 
v_f_4559_ = l_Lean_Expr_getAppFn(v_e_4558_);
v___x_4560_ = 0;
v___x_4561_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4560_, v_f_4559_);
if (v___x_4561_ == 0)
{
lean_dec_ref(v_f_4559_);
return v_e_4558_;
}
else
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4562_ = l_Lean_Expr_getAppNumArgs(v_e_4558_);
v___x_4563_ = lean_mk_empty_array_with_capacity(v___x_4562_);
lean_dec(v___x_4562_);
v___x_4564_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4558_, v___x_4563_);
v___x_4565_ = l_Lean_Expr_betaRev(v_f_4559_, v___x_4564_, v___x_4560_, v___x_4560_);
lean_dec_ref(v___x_4564_);
return v___x_4565_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4566_, uint8_t v_useZeta_4567_){
_start:
{
uint8_t v___x_4568_; 
v___x_4568_ = l_Lean_Expr_isApp(v_e_4566_);
if (v___x_4568_ == 0)
{
return v___x_4568_;
}
else
{
lean_object* v___x_4569_; uint8_t v___x_4570_; 
v___x_4569_ = l_Lean_Expr_getAppFn(v_e_4566_);
v___x_4570_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4567_, v___x_4569_);
lean_dec_ref(v___x_4569_);
return v___x_4570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4571_, lean_object* v_useZeta_4572_){
_start:
{
uint8_t v_useZeta_boxed_4573_; uint8_t v_res_4574_; lean_object* v_r_4575_; 
v_useZeta_boxed_4573_ = lean_unbox(v_useZeta_4572_);
v_res_4574_ = l_Lean_Expr_isHeadBetaTarget(v_e_4571_, v_useZeta_boxed_4573_);
lean_dec_ref(v_e_4571_);
v_r_4575_ = lean_box(v_res_4574_);
return v_r_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4576_, lean_object* v_x_4577_, lean_object* v_x_4578_){
_start:
{
lean_object* v_f_4580_; 
if (lean_obj_tag(v_x_4576_) == 5)
{
lean_object* v_arg_4584_; 
v_arg_4584_ = lean_ctor_get(v_x_4576_, 1);
if (lean_obj_tag(v_arg_4584_) == 0)
{
lean_object* v_fn_4585_; lean_object* v_deBruijnIndex_4586_; lean_object* v_zero_4587_; uint8_t v_isZero_4588_; 
v_fn_4585_ = lean_ctor_get(v_x_4576_, 0);
v_deBruijnIndex_4586_ = lean_ctor_get(v_arg_4584_, 0);
v_zero_4587_ = lean_unsigned_to_nat(0u);
v_isZero_4588_ = lean_nat_dec_eq(v_x_4577_, v_zero_4587_);
if (v_isZero_4588_ == 1)
{
lean_dec(v_x_4578_);
lean_dec(v_x_4577_);
v_f_4580_ = v_x_4576_;
goto v___jp_4579_;
}
else
{
uint8_t v___x_4589_; 
lean_inc(v_deBruijnIndex_4586_);
lean_inc_ref(v_fn_4585_);
lean_dec_ref_known(v_x_4576_, 2);
v___x_4589_ = lean_nat_dec_eq(v_deBruijnIndex_4586_, v_x_4578_);
lean_dec(v_deBruijnIndex_4586_);
if (v___x_4589_ == 0)
{
lean_object* v___x_4590_; 
lean_dec_ref(v_fn_4585_);
lean_dec(v_x_4578_);
lean_dec(v_x_4577_);
v___x_4590_ = lean_box(0);
return v___x_4590_;
}
else
{
lean_object* v_one_4591_; lean_object* v_n_4592_; lean_object* v___x_4593_; 
v_one_4591_ = lean_unsigned_to_nat(1u);
v_n_4592_ = lean_nat_sub(v_x_4577_, v_one_4591_);
lean_dec(v_x_4577_);
v___x_4593_ = lean_nat_add(v_x_4578_, v_one_4591_);
lean_dec(v_x_4578_);
v_x_4576_ = v_fn_4585_;
v_x_4577_ = v_n_4592_;
v_x_4578_ = v___x_4593_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4595_; uint8_t v_isZero_4596_; 
lean_dec(v_x_4578_);
v_zero_4595_ = lean_unsigned_to_nat(0u);
v_isZero_4596_ = lean_nat_dec_eq(v_x_4577_, v_zero_4595_);
lean_dec(v_x_4577_);
if (v_isZero_4596_ == 1)
{
v_f_4580_ = v_x_4576_;
goto v___jp_4579_;
}
else
{
lean_object* v___x_4597_; 
lean_dec_ref_known(v_x_4576_, 2);
v___x_4597_ = lean_box(0);
return v___x_4597_;
}
}
}
else
{
lean_object* v_zero_4598_; uint8_t v_isZero_4599_; 
lean_dec(v_x_4578_);
v_zero_4598_ = lean_unsigned_to_nat(0u);
v_isZero_4599_ = lean_nat_dec_eq(v_x_4577_, v_zero_4598_);
lean_dec(v_x_4577_);
if (v_isZero_4599_ == 1)
{
v_f_4580_ = v_x_4576_;
goto v___jp_4579_;
}
else
{
lean_object* v___x_4600_; 
lean_dec_ref(v_x_4576_);
v___x_4600_ = lean_box(0);
return v___x_4600_;
}
}
v___jp_4579_:
{
uint8_t v___x_4581_; 
v___x_4581_ = l_Lean_Expr_hasLooseBVars(v_f_4580_);
if (v___x_4581_ == 0)
{
lean_object* v___x_4582_; 
v___x_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4582_, 0, v_f_4580_);
return v___x_4582_;
}
else
{
lean_object* v___x_4583_; 
lean_dec_ref(v_f_4580_);
v___x_4583_ = lean_box(0);
return v___x_4583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4601_, lean_object* v_x_4602_){
_start:
{
if (lean_obj_tag(v_x_4601_) == 6)
{
lean_object* v_body_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v_body_4603_ = lean_ctor_get(v_x_4601_, 2);
lean_inc_ref(v_body_4603_);
lean_dec_ref_known(v_x_4601_, 3);
v___x_4604_ = lean_unsigned_to_nat(1u);
v___x_4605_ = lean_nat_add(v_x_4602_, v___x_4604_);
lean_dec(v_x_4602_);
v_x_4601_ = v_body_4603_;
v_x_4602_ = v___x_4605_;
goto _start;
}
else
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4601_, v_x_4602_, v___x_4607_);
return v___x_4608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4609_){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = lean_unsigned_to_nat(0u);
v___x_4611_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4609_, v___x_4610_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4612_){
_start:
{
if (lean_obj_tag(v_x_4612_) == 6)
{
lean_object* v_body_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v_body_4613_ = lean_ctor_get(v_x_4612_, 2);
lean_inc_ref(v_body_4613_);
lean_dec_ref_known(v_x_4612_, 3);
v___x_4614_ = lean_unsigned_to_nat(1u);
v___x_4615_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4613_, v___x_4614_);
return v___x_4615_;
}
else
{
lean_object* v___x_4616_; 
lean_dec_ref(v_x_4612_);
v___x_4616_ = lean_box(0);
return v___x_4616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4620_){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; 
v___x_4621_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4622_ = lean_unsigned_to_nat(2u);
v___x_4623_ = l_Lean_Expr_isAppOfArity(v_e_4620_, v___x_4621_, v___x_4622_);
if (v___x_4623_ == 0)
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_box(0);
return v___x_4624_;
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = l_Lean_Expr_appArg_x21(v_e_4620_);
v___x_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
return v___x_4626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4627_);
lean_dec_ref(v_e_4627_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4632_){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; uint8_t v___x_4635_; 
v___x_4633_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4634_ = lean_unsigned_to_nat(2u);
v___x_4635_ = l_Lean_Expr_isAppOfArity(v_e_4632_, v___x_4633_, v___x_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; 
v___x_4636_ = lean_box(0);
return v___x_4636_;
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = l_Lean_Expr_appArg_x21(v_e_4632_);
v___x_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4639_);
lean_dec_ref(v_e_4639_);
return v_res_4640_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4644_){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4645_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4646_ = lean_unsigned_to_nat(1u);
v___x_4647_ = l_Lean_Expr_isAppOfArity(v_e_4644_, v___x_4645_, v___x_4646_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4648_){
_start:
{
uint8_t v_res_4649_; lean_object* v_r_4650_; 
v_res_4649_ = l_Lean_Expr_isOutParam(v_e_4648_);
lean_dec_ref(v_e_4648_);
v_r_4650_ = lean_box(v_res_4649_);
return v_r_4650_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4654_){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4655_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4656_ = lean_unsigned_to_nat(1u);
v___x_4657_ = l_Lean_Expr_isAppOfArity(v_e_4654_, v___x_4655_, v___x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4658_){
_start:
{
uint8_t v_res_4659_; lean_object* v_r_4660_; 
v_res_4659_ = l_Lean_Expr_isSemiOutParam(v_e_4658_);
lean_dec_ref(v_e_4658_);
v_r_4660_ = lean_box(v_res_4659_);
return v_r_4660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4661_){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4662_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4663_ = lean_unsigned_to_nat(2u);
v___x_4664_ = l_Lean_Expr_isAppOfArity(v_e_4661_, v___x_4662_, v___x_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4665_){
_start:
{
uint8_t v_res_4666_; lean_object* v_r_4667_; 
v_res_4666_ = l_Lean_Expr_isOptParam(v_e_4665_);
lean_dec_ref(v_e_4665_);
v_r_4667_ = lean_box(v_res_4666_);
return v_r_4667_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4668_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4669_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4670_ = lean_unsigned_to_nat(2u);
v___x_4671_ = l_Lean_Expr_isAppOfArity(v_e_4668_, v___x_4669_, v___x_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4672_){
_start:
{
uint8_t v_res_4673_; lean_object* v_r_4674_; 
v_res_4673_ = l_Lean_Expr_isAutoParam(v_e_4672_);
lean_dec_ref(v_e_4672_);
v_r_4674_ = lean_box(v_res_4673_);
return v_r_4674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4675_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_Expr_getAppFn(v_e_4675_);
if (lean_obj_tag(v___x_4676_) == 4)
{
lean_object* v_declName_4677_; uint8_t v___y_4679_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v_declName_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_declName_4677_);
lean_dec_ref_known(v___x_4676_, 2);
v___x_4684_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4685_ = lean_name_eq(v_declName_4677_, v___x_4684_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; uint8_t v___x_4687_; 
v___x_4686_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4687_ = lean_name_eq(v_declName_4677_, v___x_4686_);
v___y_4679_ = v___x_4687_;
goto v___jp_4678_;
}
else
{
v___y_4679_ = v___x_4685_;
goto v___jp_4678_;
}
v___jp_4678_:
{
if (v___y_4679_ == 0)
{
lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___x_4680_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4681_ = lean_name_eq(v_declName_4677_, v___x_4680_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4682_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4683_ = lean_name_eq(v_declName_4677_, v___x_4682_);
lean_dec(v_declName_4677_);
return v___x_4683_;
}
else
{
lean_dec(v_declName_4677_);
return v___x_4681_;
}
}
else
{
lean_dec(v_declName_4677_);
return v___y_4679_;
}
}
}
else
{
uint8_t v___x_4688_; 
lean_dec_ref(v___x_4676_);
v___x_4688_ = 0;
return v___x_4688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4689_){
_start:
{
uint8_t v_res_4690_; lean_object* v_r_4691_; 
v_res_4690_ = l_Lean_Expr_isTypeAnnotation(v_e_4689_);
lean_dec_ref(v_e_4689_);
v_r_4691_ = lean_box(v_res_4690_);
return v_r_4691_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4692_){
_start:
{
uint8_t v___y_4694_; uint8_t v___y_4698_; uint8_t v___x_4704_; 
v___x_4704_ = l_Lean_Expr_isOptParam(v_e_4692_);
if (v___x_4704_ == 0)
{
uint8_t v___x_4705_; 
v___x_4705_ = l_Lean_Expr_isAutoParam(v_e_4692_);
v___y_4698_ = v___x_4705_;
goto v___jp_4697_;
}
else
{
v___y_4698_ = v___x_4704_;
goto v___jp_4697_;
}
v___jp_4693_:
{
if (v___y_4694_ == 0)
{
return v_e_4692_;
}
else
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_Expr_appArg_x21(v_e_4692_);
lean_dec_ref(v_e_4692_);
v_e_4692_ = v___x_4695_;
goto _start;
}
}
v___jp_4697_:
{
if (v___y_4698_ == 0)
{
uint8_t v___x_4699_; 
v___x_4699_ = l_Lean_Expr_isOutParam(v_e_4692_);
if (v___x_4699_ == 0)
{
uint8_t v___x_4700_; 
v___x_4700_ = l_Lean_Expr_isSemiOutParam(v_e_4692_);
v___y_4694_ = v___x_4700_;
goto v___jp_4693_;
}
else
{
v___y_4694_ = v___x_4699_;
goto v___jp_4693_;
}
}
else
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = l_Lean_Expr_appFn_x21(v_e_4692_);
lean_dec_ref(v_e_4692_);
v___x_4702_ = l_Lean_Expr_appArg_x21(v___x_4701_);
lean_dec_ref(v___x_4701_);
v_e_4692_ = v___x_4702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4706_){
_start:
{
lean_object* v___x_4707_; lean_object* v_e_x27_4708_; uint8_t v___x_4709_; 
v___x_4707_ = l_Lean_Expr_consumeMData(v_e_4706_);
v_e_x27_4708_ = lean_expr_consume_type_annotations(v___x_4707_);
v___x_4709_ = lean_expr_eqv(v_e_x27_4708_, v_e_4706_);
if (v___x_4709_ == 0)
{
lean_dec_ref(v_e_4706_);
v_e_4706_ = v_e_x27_4708_;
goto _start;
}
else
{
lean_dec_ref(v_e_x27_4708_);
return v_e_4706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4711_){
_start:
{
lean_object* v_fn_4712_; lean_object* v___x_4713_; 
v_fn_4712_ = lean_ctor_get(v_e_4711_, 0);
lean_inc_ref(v_fn_4712_);
lean_dec_ref(v_e_4711_);
v___x_4713_ = l_Lean_Expr_cleanupAnnotations(v_fn_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4714_, lean_object* v_h_4715_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4714_);
return v___x_4716_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4720_){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4721_ = l_Lean_Expr_cleanupAnnotations(v_e_4720_);
v___x_4722_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4723_ = l_Lean_Expr_isConstOf(v___x_4721_, v___x_4722_);
lean_dec_ref(v___x_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4724_){
_start:
{
uint8_t v_res_4725_; lean_object* v_r_4726_; 
v_res_4725_ = l_Lean_Expr_isFalse(v_e_4724_);
v_r_4726_ = lean_box(v_res_4725_);
return v_r_4726_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4730_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4731_ = l_Lean_Expr_cleanupAnnotations(v_e_4730_);
v___x_4732_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4733_ = l_Lean_Expr_isConstOf(v___x_4731_, v___x_4732_);
lean_dec_ref(v___x_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4734_){
_start:
{
uint8_t v_res_4735_; lean_object* v_r_4736_; 
v_res_4735_ = l_Lean_Expr_isTrue(v_e_4734_);
v_r_4736_ = lean_box(v_res_4735_);
return v_r_4736_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4741_){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; uint8_t v___x_4744_; 
v___x_4742_ = l_Lean_Expr_cleanupAnnotations(v_e_4741_);
v___x_4743_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_4744_ = l_Lean_Expr_isConstOf(v___x_4742_, v___x_4743_);
lean_dec_ref(v___x_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4745_){
_start:
{
uint8_t v_res_4746_; lean_object* v_r_4747_; 
v_res_4746_ = l_Lean_Expr_isBoolFalse(v_e_4745_);
v_r_4747_ = lean_box(v_res_4746_);
return v_r_4747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4751_){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v___x_4752_ = l_Lean_Expr_cleanupAnnotations(v_e_4751_);
v___x_4753_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4754_ = l_Lean_Expr_isConstOf(v___x_4752_, v___x_4753_);
lean_dec_ref(v___x_4752_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4755_){
_start:
{
uint8_t v_res_4756_; lean_object* v_r_4757_; 
v_res_4756_ = l_Lean_Expr_isBoolTrue(v_e_4755_);
v_r_4757_ = lean_box(v_res_4756_);
return v_r_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4758_){
_start:
{
switch(lean_obj_tag(v_x_4758_))
{
case 10:
{
lean_object* v_expr_4759_; 
v_expr_4759_ = lean_ctor_get(v_x_4758_, 1);
lean_inc_ref(v_expr_4759_);
lean_dec_ref_known(v_x_4758_, 2);
v_x_4758_ = v_expr_4759_;
goto _start;
}
case 7:
{
lean_object* v_body_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_body_4761_ = lean_ctor_get(v_x_4758_, 2);
lean_inc_ref(v_body_4761_);
lean_dec_ref_known(v_x_4758_, 3);
v___x_4762_ = l_Lean_Expr_getForallArity(v_body_4761_);
v___x_4763_ = lean_unsigned_to_nat(1u);
v___x_4764_ = lean_nat_add(v___x_4762_, v___x_4763_);
lean_dec(v___x_4762_);
return v___x_4764_;
}
default: 
{
uint8_t v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = 0;
v___x_4766_ = l_Lean_Expr_isHeadBetaTarget(v_x_4758_, v___x_4765_);
if (v___x_4766_ == 0)
{
lean_object* v_e_x27_4767_; uint8_t v___x_4768_; 
lean_inc_ref(v_x_4758_);
v_e_x27_4767_ = l_Lean_Expr_cleanupAnnotations(v_x_4758_);
v___x_4768_ = lean_expr_eqv(v_x_4758_, v_e_x27_4767_);
lean_dec_ref(v_x_4758_);
if (v___x_4768_ == 0)
{
v_x_4758_ = v_e_x27_4767_;
goto _start;
}
else
{
lean_object* v___x_4770_; 
lean_dec_ref(v_e_x27_4767_);
v___x_4770_ = lean_unsigned_to_nat(0u);
return v___x_4770_;
}
}
else
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Lean_Expr_headBeta(v_x_4758_);
v_x_4758_ = v___x_4771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4773_){
_start:
{
lean_object* v___x_4774_; uint8_t v___x_4775_; 
v___x_4774_ = l_Lean_Expr_cleanupAnnotations(v_e_4773_);
v___x_4775_ = l_Lean_Expr_isApp(v___x_4774_);
if (v___x_4775_ == 0)
{
lean_object* v___x_4776_; 
lean_dec_ref(v___x_4774_);
v___x_4776_ = lean_box(0);
return v___x_4776_;
}
else
{
lean_object* v___x_4777_; uint8_t v___x_4778_; 
v___x_4777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4774_);
v___x_4778_ = l_Lean_Expr_isApp(v___x_4777_);
if (v___x_4778_ == 0)
{
lean_object* v___x_4779_; 
lean_dec_ref(v___x_4777_);
v___x_4779_ = lean_box(0);
return v___x_4779_;
}
else
{
lean_object* v_arg_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v_arg_4780_ = lean_ctor_get(v___x_4777_, 1);
lean_inc_ref(v_arg_4780_);
v___x_4781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4777_);
v___x_4782_ = l_Lean_Expr_isApp(v___x_4781_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
lean_dec_ref(v___x_4781_);
lean_dec_ref(v_arg_4780_);
v___x_4783_ = lean_box(0);
return v___x_4783_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4784_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4781_);
v___x_4785_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4786_ = l_Lean_Expr_isConstOf(v___x_4784_, v___x_4785_);
lean_dec_ref(v___x_4784_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; 
lean_dec_ref(v_arg_4780_);
v___x_4787_ = lean_box(0);
return v___x_4787_;
}
else
{
if (lean_obj_tag(v_arg_4780_) == 9)
{
lean_object* v_a_4788_; 
v_a_4788_ = lean_ctor_get(v_arg_4780_, 0);
lean_inc_ref(v_a_4788_);
lean_dec_ref_known(v_arg_4780_, 1);
if (lean_obj_tag(v_a_4788_) == 0)
{
lean_object* v_val_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
v_val_4789_ = lean_ctor_get(v_a_4788_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v_a_4788_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v_a_4788_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_val_4789_);
lean_dec(v_a_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
lean_ctor_set_tag(v___x_4791_, 1);
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_val_4789_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
else
{
lean_object* v___x_4797_; 
lean_dec_ref(v_a_4788_);
v___x_4797_ = lean_box(0);
return v___x_4797_;
}
}
else
{
lean_object* v___x_4798_; 
lean_dec_ref(v_arg_4780_);
v___x_4798_ = lean_box(0);
return v___x_4798_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4804_){
_start:
{
lean_object* v___x_4817_; uint8_t v___x_4818_; 
lean_inc_ref(v_e_4804_);
v___x_4817_ = l_Lean_Expr_cleanupAnnotations(v_e_4804_);
v___x_4818_ = l_Lean_Expr_isApp(v___x_4817_);
if (v___x_4818_ == 0)
{
lean_dec_ref(v___x_4817_);
goto v___jp_4805_;
}
else
{
lean_object* v_arg_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; 
v_arg_4819_ = lean_ctor_get(v___x_4817_, 1);
lean_inc_ref(v_arg_4819_);
v___x_4820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4817_);
v___x_4821_ = l_Lean_Expr_isApp(v___x_4820_);
if (v___x_4821_ == 0)
{
lean_dec_ref(v___x_4820_);
lean_dec_ref(v_arg_4819_);
goto v___jp_4805_;
}
else
{
lean_object* v___x_4822_; uint8_t v___x_4823_; 
v___x_4822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4820_);
v___x_4823_ = l_Lean_Expr_isApp(v___x_4822_);
if (v___x_4823_ == 0)
{
lean_dec_ref(v___x_4822_);
lean_dec_ref(v_arg_4819_);
goto v___jp_4805_;
}
else
{
lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
v___x_4824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4822_);
v___x_4825_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4826_ = l_Lean_Expr_isConstOf(v___x_4824_, v___x_4825_);
lean_dec_ref(v___x_4824_);
if (v___x_4826_ == 0)
{
lean_dec_ref(v_arg_4819_);
goto v___jp_4805_;
}
else
{
lean_object* v___x_4827_; 
lean_dec_ref(v_e_4804_);
v___x_4827_ = l_Lean_Expr_nat_x3f(v_arg_4819_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_box(0);
return v___x_4828_;
}
else
{
lean_object* v_val_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4841_; 
v_val_4829_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4831_ = v___x_4827_;
v_isShared_4832_ = v_isSharedCheck_4841_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_val_4829_);
lean_dec(v___x_4827_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4841_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4833_ = lean_unsigned_to_nat(0u);
v___x_4834_ = lean_nat_dec_eq(v_val_4829_, v___x_4833_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4835_ = lean_nat_to_int(v_val_4829_);
v___x_4836_ = lean_int_neg(v___x_4835_);
lean_dec(v___x_4835_);
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 0, v___x_4836_);
v___x_4838_ = v___x_4831_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
else
{
lean_object* v___x_4840_; 
lean_del_object(v___x_4831_);
lean_dec(v_val_4829_);
v___x_4840_ = lean_box(0);
return v___x_4840_;
}
}
}
}
}
}
}
v___jp_4805_:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_Expr_nat_x3f(v_e_4804_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v___x_4807_; 
v___x_4807_ = lean_box(0);
return v___x_4807_;
}
else
{
lean_object* v_val_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4816_; 
v_val_4808_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4810_ = v___x_4806_;
v_isShared_4811_ = v_isSharedCheck_4816_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_val_4808_);
lean_dec(v___x_4806_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4816_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4812_ = lean_nat_to_int(v_val_4808_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4812_);
v___x_4814_ = v___x_4810_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4842_, lean_object* v_e_4843_){
_start:
{
uint8_t v___x_4844_; lean_object* v_d_4846_; lean_object* v_b_4847_; 
v___x_4844_ = l_Lean_Expr_hasFVar(v_e_4843_);
if (v___x_4844_ == 0)
{
lean_dec_ref(v_e_4843_);
lean_dec_ref(v_p_4842_);
return v___x_4844_;
}
else
{
switch(lean_obj_tag(v_e_4843_))
{
case 7:
{
lean_object* v_binderType_4850_; lean_object* v_body_4851_; 
v_binderType_4850_ = lean_ctor_get(v_e_4843_, 1);
lean_inc_ref(v_binderType_4850_);
v_body_4851_ = lean_ctor_get(v_e_4843_, 2);
lean_inc_ref(v_body_4851_);
lean_dec_ref_known(v_e_4843_, 3);
v_d_4846_ = v_binderType_4850_;
v_b_4847_ = v_body_4851_;
goto v___jp_4845_;
}
case 6:
{
lean_object* v_binderType_4852_; lean_object* v_body_4853_; 
v_binderType_4852_ = lean_ctor_get(v_e_4843_, 1);
lean_inc_ref(v_binderType_4852_);
v_body_4853_ = lean_ctor_get(v_e_4843_, 2);
lean_inc_ref(v_body_4853_);
lean_dec_ref_known(v_e_4843_, 3);
v_d_4846_ = v_binderType_4852_;
v_b_4847_ = v_body_4853_;
goto v___jp_4845_;
}
case 10:
{
lean_object* v_expr_4854_; 
v_expr_4854_ = lean_ctor_get(v_e_4843_, 1);
lean_inc_ref(v_expr_4854_);
lean_dec_ref_known(v_e_4843_, 2);
v_e_4843_ = v_expr_4854_;
goto _start;
}
case 8:
{
lean_object* v_type_4856_; lean_object* v_value_4857_; lean_object* v_body_4858_; uint8_t v___x_4859_; 
v_type_4856_ = lean_ctor_get(v_e_4843_, 1);
lean_inc_ref(v_type_4856_);
v_value_4857_ = lean_ctor_get(v_e_4843_, 2);
lean_inc_ref(v_value_4857_);
v_body_4858_ = lean_ctor_get(v_e_4843_, 3);
lean_inc_ref(v_body_4858_);
lean_dec_ref_known(v_e_4843_, 4);
lean_inc_ref(v_p_4842_);
v___x_4859_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4842_, v_type_4856_);
if (v___x_4859_ == 0)
{
uint8_t v___x_4860_; 
lean_inc_ref(v_p_4842_);
v___x_4860_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4842_, v_value_4857_);
if (v___x_4860_ == 0)
{
v_e_4843_ = v_body_4858_;
goto _start;
}
else
{
lean_dec_ref(v_body_4858_);
lean_dec_ref(v_p_4842_);
return v___x_4844_;
}
}
else
{
lean_dec_ref(v_body_4858_);
lean_dec_ref(v_value_4857_);
lean_dec_ref(v_p_4842_);
return v___x_4844_;
}
}
case 5:
{
lean_object* v_fn_4862_; lean_object* v_arg_4863_; uint8_t v___x_4864_; 
v_fn_4862_ = lean_ctor_get(v_e_4843_, 0);
lean_inc_ref(v_fn_4862_);
v_arg_4863_ = lean_ctor_get(v_e_4843_, 1);
lean_inc_ref(v_arg_4863_);
lean_dec_ref_known(v_e_4843_, 2);
lean_inc_ref(v_p_4842_);
v___x_4864_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4842_, v_fn_4862_);
if (v___x_4864_ == 0)
{
v_e_4843_ = v_arg_4863_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4863_);
lean_dec_ref(v_p_4842_);
return v___x_4844_;
}
}
case 11:
{
lean_object* v_struct_4866_; 
v_struct_4866_ = lean_ctor_get(v_e_4843_, 2);
lean_inc_ref(v_struct_4866_);
lean_dec_ref_known(v_e_4843_, 3);
v_e_4843_ = v_struct_4866_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4868_; lean_object* v___x_4869_; uint8_t v___x_4870_; 
v_fvarId_4868_ = lean_ctor_get(v_e_4843_, 0);
lean_inc(v_fvarId_4868_);
lean_dec_ref_known(v_e_4843_, 1);
v___x_4869_ = lean_apply_1(v_p_4842_, v_fvarId_4868_);
v___x_4870_ = lean_unbox(v___x_4869_);
return v___x_4870_;
}
default: 
{
uint8_t v___x_4871_; 
lean_dec_ref(v_e_4843_);
lean_dec_ref(v_p_4842_);
v___x_4871_ = 0;
return v___x_4871_;
}
}
}
v___jp_4845_:
{
uint8_t v___x_4848_; 
lean_inc_ref(v_p_4842_);
v___x_4848_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4842_, v_d_4846_);
if (v___x_4848_ == 0)
{
v_e_4843_ = v_b_4847_;
goto _start;
}
else
{
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_p_4842_);
return v___x_4844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4872_, lean_object* v_e_4873_){
_start:
{
uint8_t v_res_4874_; lean_object* v_r_4875_; 
v_res_4874_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4872_, v_e_4873_);
v_r_4875_ = lean_box(v_res_4874_);
return v_r_4875_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4876_, lean_object* v_p_4877_){
_start:
{
uint8_t v___x_4878_; 
v___x_4878_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4877_, v_e_4876_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4879_, lean_object* v_p_4880_){
_start:
{
uint8_t v_res_4881_; lean_object* v_r_4882_; 
v_res_4881_ = l_Lean_Expr_hasAnyFVar(v_e_4879_, v_p_4880_);
v_r_4882_ = lean_box(v_res_4881_);
return v_r_4882_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4883_, lean_object* v_e_4884_){
_start:
{
uint8_t v___x_4885_; lean_object* v_d_4887_; lean_object* v_b_4888_; 
v___x_4885_ = l_Lean_Expr_hasFVar(v_e_4884_);
if (v___x_4885_ == 0)
{
return v___x_4885_;
}
else
{
switch(lean_obj_tag(v_e_4884_))
{
case 7:
{
lean_object* v_binderType_4891_; lean_object* v_body_4892_; 
v_binderType_4891_ = lean_ctor_get(v_e_4884_, 1);
v_body_4892_ = lean_ctor_get(v_e_4884_, 2);
v_d_4887_ = v_binderType_4891_;
v_b_4888_ = v_body_4892_;
goto v___jp_4886_;
}
case 6:
{
lean_object* v_binderType_4893_; lean_object* v_body_4894_; 
v_binderType_4893_ = lean_ctor_get(v_e_4884_, 1);
v_body_4894_ = lean_ctor_get(v_e_4884_, 2);
v_d_4887_ = v_binderType_4893_;
v_b_4888_ = v_body_4894_;
goto v___jp_4886_;
}
case 10:
{
lean_object* v_expr_4895_; 
v_expr_4895_ = lean_ctor_get(v_e_4884_, 1);
v_e_4884_ = v_expr_4895_;
goto _start;
}
case 8:
{
lean_object* v_type_4897_; lean_object* v_value_4898_; lean_object* v_body_4899_; uint8_t v___x_4900_; 
v_type_4897_ = lean_ctor_get(v_e_4884_, 1);
v_value_4898_ = lean_ctor_get(v_e_4884_, 2);
v_body_4899_ = lean_ctor_get(v_e_4884_, 3);
v___x_4900_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4883_, v_type_4897_);
if (v___x_4900_ == 0)
{
uint8_t v___x_4901_; 
v___x_4901_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4883_, v_value_4898_);
if (v___x_4901_ == 0)
{
v_e_4884_ = v_body_4899_;
goto _start;
}
else
{
return v___x_4885_;
}
}
else
{
return v___x_4885_;
}
}
case 5:
{
lean_object* v_fn_4903_; lean_object* v_arg_4904_; uint8_t v___x_4905_; 
v_fn_4903_ = lean_ctor_get(v_e_4884_, 0);
v_arg_4904_ = lean_ctor_get(v_e_4884_, 1);
v___x_4905_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4883_, v_fn_4903_);
if (v___x_4905_ == 0)
{
v_e_4884_ = v_arg_4904_;
goto _start;
}
else
{
return v___x_4885_;
}
}
case 11:
{
lean_object* v_struct_4907_; 
v_struct_4907_ = lean_ctor_get(v_e_4884_, 2);
v_e_4884_ = v_struct_4907_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4909_; uint8_t v___x_4910_; 
v_fvarId_4909_ = lean_ctor_get(v_e_4884_, 0);
v___x_4910_ = lean_name_eq(v_fvarId_4909_, v_fvarId_4883_);
return v___x_4910_;
}
default: 
{
uint8_t v___x_4911_; 
v___x_4911_ = 0;
return v___x_4911_;
}
}
}
v___jp_4886_:
{
uint8_t v___x_4889_; 
v___x_4889_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4883_, v_d_4887_);
if (v___x_4889_ == 0)
{
v_e_4884_ = v_b_4888_;
goto _start;
}
else
{
return v___x_4885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4912_, lean_object* v_e_4913_){
_start:
{
uint8_t v_res_4914_; lean_object* v_r_4915_; 
v_res_4914_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4912_, v_e_4913_);
lean_dec_ref(v_e_4913_);
lean_dec(v_fvarId_4912_);
v_r_4915_ = lean_box(v_res_4914_);
return v_r_4915_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4916_, lean_object* v_fvarId_4917_){
_start:
{
uint8_t v___x_4918_; 
v___x_4918_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4917_, v_e_4916_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4919_, lean_object* v_fvarId_4920_){
_start:
{
uint8_t v_res_4921_; lean_object* v_r_4922_; 
v_res_4921_ = l_Lean_Expr_containsFVar(v_e_4919_, v_fvarId_4920_);
lean_dec(v_fvarId_4920_);
lean_dec_ref(v_e_4919_);
v_r_4922_ = lean_box(v_res_4921_);
return v_r_4922_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4924_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_4925_ = lean_unsigned_to_nat(18u);
v___x_4926_ = lean_unsigned_to_nat(1847u);
v___x_4927_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_4928_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4929_ = l_mkPanicMessageWithDecl(v___x_4928_, v___x_4927_, v___x_4926_, v___x_4925_, v___x_4924_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_4930_, lean_object* v_newFn_4931_, lean_object* v_newArg_4932_){
_start:
{
uint8_t v___y_4934_; 
if (lean_obj_tag(v_e_4930_) == 5)
{
lean_object* v_fn_4936_; lean_object* v_arg_4937_; size_t v___x_4938_; size_t v___x_4939_; uint8_t v___x_4940_; 
v_fn_4936_ = lean_ctor_get(v_e_4930_, 0);
v_arg_4937_ = lean_ctor_get(v_e_4930_, 1);
v___x_4938_ = lean_ptr_addr(v_fn_4936_);
v___x_4939_ = lean_ptr_addr(v_newFn_4931_);
v___x_4940_ = lean_usize_dec_eq(v___x_4938_, v___x_4939_);
if (v___x_4940_ == 0)
{
v___y_4934_ = v___x_4940_;
goto v___jp_4933_;
}
else
{
size_t v___x_4941_; size_t v___x_4942_; uint8_t v___x_4943_; 
v___x_4941_ = lean_ptr_addr(v_arg_4937_);
v___x_4942_ = lean_ptr_addr(v_newArg_4932_);
v___x_4943_ = lean_usize_dec_eq(v___x_4941_, v___x_4942_);
v___y_4934_ = v___x_4943_;
goto v___jp_4933_;
}
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
lean_dec_ref(v_newArg_4932_);
lean_dec_ref(v_newFn_4931_);
v___x_4944_ = l_Lean_instInhabitedExpr;
v___x_4945_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_4946_ = l_panic___redArg(v___x_4944_, v___x_4945_);
return v___x_4946_;
}
v___jp_4933_:
{
if (v___y_4934_ == 0)
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_Expr_app___override(v_newFn_4931_, v_newArg_4932_);
return v___x_4935_;
}
else
{
lean_dec_ref(v_newArg_4932_);
lean_dec_ref(v_newFn_4931_);
lean_inc_ref(v_e_4930_);
return v_e_4930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_4947_, lean_object* v_newFn_4948_, lean_object* v_newArg_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_4947_, v_newFn_4948_, v_newArg_4949_);
lean_dec_ref(v_e_4947_);
return v_res_4950_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4952_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_4953_ = lean_unsigned_to_nat(20u);
v___x_4954_ = lean_unsigned_to_nat(1858u);
v___x_4955_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_4956_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4957_ = l_mkPanicMessageWithDecl(v___x_4956_, v___x_4955_, v___x_4954_, v___x_4953_, v___x_4952_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_4958_, lean_object* v_fvarIdNew_4959_){
_start:
{
if (lean_obj_tag(v_e_4958_) == 1)
{
lean_object* v_fvarId_4960_; uint8_t v___x_4961_; 
v_fvarId_4960_ = lean_ctor_get(v_e_4958_, 0);
v___x_4961_ = lean_name_eq(v_fvarId_4960_, v_fvarIdNew_4959_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Lean_Expr_fvar___override(v_fvarIdNew_4959_);
return v___x_4962_;
}
else
{
lean_dec(v_fvarIdNew_4959_);
lean_inc_ref(v_e_4958_);
return v_e_4958_;
}
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
lean_dec(v_fvarIdNew_4959_);
v___x_4963_ = l_Lean_instInhabitedExpr;
v___x_4964_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_4965_ = l_panic___redArg(v___x_4963_, v___x_4964_);
return v___x_4965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_4966_, lean_object* v_fvarIdNew_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_Expr_updateFVar_x21(v_e_4966_, v_fvarIdNew_4967_);
lean_dec_ref(v_e_4966_);
return v_res_4968_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4970_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_4971_ = lean_unsigned_to_nat(18u);
v___x_4972_ = lean_unsigned_to_nat(1863u);
v___x_4973_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_4974_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4975_ = l_mkPanicMessageWithDecl(v___x_4974_, v___x_4973_, v___x_4972_, v___x_4971_, v___x_4970_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_4976_, lean_object* v_newLevels_4977_){
_start:
{
if (lean_obj_tag(v_e_4976_) == 4)
{
lean_object* v_declName_4978_; lean_object* v_us_4979_; uint8_t v___x_4980_; 
v_declName_4978_ = lean_ctor_get(v_e_4976_, 0);
v_us_4979_ = lean_ctor_get(v_e_4976_, 1);
v___x_4980_ = l_ptrEqList___redArg(v_us_4979_, v_newLevels_4977_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
lean_inc(v_declName_4978_);
lean_dec_ref_known(v_e_4976_, 2);
v___x_4981_ = l_Lean_Expr_const___override(v_declName_4978_, v_newLevels_4977_);
return v___x_4981_;
}
else
{
lean_dec(v_newLevels_4977_);
return v_e_4976_;
}
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec(v_newLevels_4977_);
lean_dec_ref(v_e_4976_);
v___x_4982_ = l_Lean_instInhabitedExpr;
v___x_4983_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_4984_ = l_panic___redArg(v___x_4982_, v___x_4983_);
return v___x_4984_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4987_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_4988_ = lean_unsigned_to_nat(14u);
v___x_4989_ = lean_unsigned_to_nat(1874u);
v___x_4990_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_4991_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4992_ = l_mkPanicMessageWithDecl(v___x_4991_, v___x_4990_, v___x_4989_, v___x_4988_, v___x_4987_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_4993_, lean_object* v_u_x27_4994_){
_start:
{
if (lean_obj_tag(v_e_4993_) == 3)
{
lean_object* v_u_4995_; size_t v___x_4996_; size_t v___x_4997_; uint8_t v___x_4998_; 
v_u_4995_ = lean_ctor_get(v_e_4993_, 0);
v___x_4996_ = lean_ptr_addr(v_u_4995_);
v___x_4997_ = lean_ptr_addr(v_u_x27_4994_);
v___x_4998_ = lean_usize_dec_eq(v___x_4996_, v___x_4997_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lean_Expr_sort___override(v_u_x27_4994_);
return v___x_4999_;
}
else
{
lean_dec(v_u_x27_4994_);
lean_inc_ref(v_e_4993_);
return v_e_4993_;
}
}
else
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
lean_dec(v_u_x27_4994_);
v___x_5000_ = l_Lean_instInhabitedExpr;
v___x_5001_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5002_ = l_panic___redArg(v___x_5000_, v___x_5001_);
return v___x_5002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5003_, lean_object* v_u_x27_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5003_, v_u_x27_5004_);
lean_dec_ref(v_e_5003_);
return v_res_5005_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5008_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5009_ = lean_unsigned_to_nat(17u);
v___x_5010_ = lean_unsigned_to_nat(1885u);
v___x_5011_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5012_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5013_ = l_mkPanicMessageWithDecl(v___x_5012_, v___x_5011_, v___x_5010_, v___x_5009_, v___x_5008_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5014_, lean_object* v_newExpr_5015_){
_start:
{
if (lean_obj_tag(v_e_5014_) == 10)
{
lean_object* v_data_5016_; lean_object* v_expr_5017_; size_t v___x_5018_; size_t v___x_5019_; uint8_t v___x_5020_; 
v_data_5016_ = lean_ctor_get(v_e_5014_, 0);
v_expr_5017_ = lean_ctor_get(v_e_5014_, 1);
v___x_5018_ = lean_ptr_addr(v_expr_5017_);
v___x_5019_ = lean_ptr_addr(v_newExpr_5015_);
v___x_5020_ = lean_usize_dec_eq(v___x_5018_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_inc(v_data_5016_);
lean_dec_ref_known(v_e_5014_, 2);
v___x_5021_ = l_Lean_Expr_mdata___override(v_data_5016_, v_newExpr_5015_);
return v___x_5021_;
}
else
{
lean_dec_ref(v_newExpr_5015_);
return v_e_5014_;
}
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
lean_dec_ref(v_newExpr_5015_);
lean_dec_ref(v_e_5014_);
v___x_5022_ = l_Lean_instInhabitedExpr;
v___x_5023_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5024_ = l_panic___redArg(v___x_5022_, v___x_5023_);
return v___x_5024_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5027_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5028_ = lean_unsigned_to_nat(18u);
v___x_5029_ = lean_unsigned_to_nat(1896u);
v___x_5030_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5031_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5032_ = l_mkPanicMessageWithDecl(v___x_5031_, v___x_5030_, v___x_5029_, v___x_5028_, v___x_5027_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5033_, lean_object* v_newExpr_5034_){
_start:
{
if (lean_obj_tag(v_e_5033_) == 11)
{
lean_object* v_typeName_5035_; lean_object* v_idx_5036_; lean_object* v_struct_5037_; size_t v___x_5038_; size_t v___x_5039_; uint8_t v___x_5040_; 
v_typeName_5035_ = lean_ctor_get(v_e_5033_, 0);
v_idx_5036_ = lean_ctor_get(v_e_5033_, 1);
v_struct_5037_ = lean_ctor_get(v_e_5033_, 2);
v___x_5038_ = lean_ptr_addr(v_struct_5037_);
v___x_5039_ = lean_ptr_addr(v_newExpr_5034_);
v___x_5040_ = lean_usize_dec_eq(v___x_5038_, v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; 
lean_inc(v_idx_5036_);
lean_inc(v_typeName_5035_);
lean_dec_ref_known(v_e_5033_, 3);
v___x_5041_ = l_Lean_Expr_proj___override(v_typeName_5035_, v_idx_5036_, v_newExpr_5034_);
return v___x_5041_;
}
else
{
lean_dec_ref(v_newExpr_5034_);
return v_e_5033_;
}
}
else
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec_ref(v_newExpr_5034_);
lean_dec_ref(v_e_5033_);
v___x_5042_ = l_Lean_instInhabitedExpr;
v___x_5043_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5044_ = l_panic___redArg(v___x_5042_, v___x_5043_);
return v___x_5044_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5047_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5048_ = lean_unsigned_to_nat(23u);
v___x_5049_ = lean_unsigned_to_nat(1911u);
v___x_5050_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5051_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5052_ = l_mkPanicMessageWithDecl(v___x_5051_, v___x_5050_, v___x_5049_, v___x_5048_, v___x_5047_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5053_, uint8_t v_newBinfo_5054_, lean_object* v_newDomain_5055_, lean_object* v_newBody_5056_){
_start:
{
if (lean_obj_tag(v_e_5053_) == 7)
{
lean_object* v_binderName_5057_; lean_object* v_binderType_5058_; lean_object* v_body_5059_; uint8_t v_binderInfo_5060_; uint8_t v___y_5062_; size_t v___x_5066_; size_t v___x_5067_; uint8_t v___x_5068_; 
v_binderName_5057_ = lean_ctor_get(v_e_5053_, 0);
v_binderType_5058_ = lean_ctor_get(v_e_5053_, 1);
v_body_5059_ = lean_ctor_get(v_e_5053_, 2);
v_binderInfo_5060_ = lean_ctor_get_uint8(v_e_5053_, sizeof(void*)*3 + 8);
v___x_5066_ = lean_ptr_addr(v_binderType_5058_);
v___x_5067_ = lean_ptr_addr(v_newDomain_5055_);
v___x_5068_ = lean_usize_dec_eq(v___x_5066_, v___x_5067_);
if (v___x_5068_ == 0)
{
v___y_5062_ = v___x_5068_;
goto v___jp_5061_;
}
else
{
size_t v___x_5069_; size_t v___x_5070_; uint8_t v___x_5071_; 
v___x_5069_ = lean_ptr_addr(v_body_5059_);
v___x_5070_ = lean_ptr_addr(v_newBody_5056_);
v___x_5071_ = lean_usize_dec_eq(v___x_5069_, v___x_5070_);
v___y_5062_ = v___x_5071_;
goto v___jp_5061_;
}
v___jp_5061_:
{
if (v___y_5062_ == 0)
{
lean_object* v___x_5063_; 
lean_inc(v_binderName_5057_);
lean_dec_ref_known(v_e_5053_, 3);
v___x_5063_ = l_Lean_Expr_forallE___override(v_binderName_5057_, v_newDomain_5055_, v_newBody_5056_, v_newBinfo_5054_);
return v___x_5063_;
}
else
{
uint8_t v___x_5064_; 
v___x_5064_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5060_, v_newBinfo_5054_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; 
lean_inc(v_binderName_5057_);
lean_dec_ref_known(v_e_5053_, 3);
v___x_5065_ = l_Lean_Expr_forallE___override(v_binderName_5057_, v_newDomain_5055_, v_newBody_5056_, v_newBinfo_5054_);
return v___x_5065_;
}
else
{
lean_dec_ref(v_newBody_5056_);
lean_dec_ref(v_newDomain_5055_);
return v_e_5053_;
}
}
}
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
lean_dec_ref(v_newBody_5056_);
lean_dec_ref(v_newDomain_5055_);
lean_dec_ref(v_e_5053_);
v___x_5072_ = l_Lean_instInhabitedExpr;
v___x_5073_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5074_ = l_panic___redArg(v___x_5072_, v___x_5073_);
return v___x_5074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5075_, lean_object* v_newBinfo_5076_, lean_object* v_newDomain_5077_, lean_object* v_newBody_5078_){
_start:
{
uint8_t v_newBinfo_boxed_5079_; lean_object* v_res_5080_; 
v_newBinfo_boxed_5079_ = lean_unbox(v_newBinfo_5076_);
v_res_5080_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5075_, v_newBinfo_boxed_5079_, v_newDomain_5077_, v_newBody_5078_);
return v_res_5080_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5082_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5083_ = lean_unsigned_to_nat(24u);
v___x_5084_ = lean_unsigned_to_nat(1922u);
v___x_5085_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5086_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5087_ = l_mkPanicMessageWithDecl(v___x_5086_, v___x_5085_, v___x_5084_, v___x_5083_, v___x_5082_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5088_, lean_object* v_newDomain_5089_, lean_object* v_newBody_5090_){
_start:
{
if (lean_obj_tag(v_e_5088_) == 7)
{
lean_object* v_binderName_5091_; lean_object* v_binderType_5092_; lean_object* v_body_5093_; uint8_t v_binderInfo_5094_; uint8_t v___y_5096_; size_t v___x_5100_; size_t v___x_5101_; uint8_t v___x_5102_; 
v_binderName_5091_ = lean_ctor_get(v_e_5088_, 0);
v_binderType_5092_ = lean_ctor_get(v_e_5088_, 1);
v_body_5093_ = lean_ctor_get(v_e_5088_, 2);
v_binderInfo_5094_ = lean_ctor_get_uint8(v_e_5088_, sizeof(void*)*3 + 8);
v___x_5100_ = lean_ptr_addr(v_binderType_5092_);
v___x_5101_ = lean_ptr_addr(v_newDomain_5089_);
v___x_5102_ = lean_usize_dec_eq(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
v___y_5096_ = v___x_5102_;
goto v___jp_5095_;
}
else
{
size_t v___x_5103_; size_t v___x_5104_; uint8_t v___x_5105_; 
v___x_5103_ = lean_ptr_addr(v_body_5093_);
v___x_5104_ = lean_ptr_addr(v_newBody_5090_);
v___x_5105_ = lean_usize_dec_eq(v___x_5103_, v___x_5104_);
v___y_5096_ = v___x_5105_;
goto v___jp_5095_;
}
v___jp_5095_:
{
if (v___y_5096_ == 0)
{
lean_object* v___x_5097_; 
lean_inc(v_binderName_5091_);
lean_dec_ref_known(v_e_5088_, 3);
v___x_5097_ = l_Lean_Expr_forallE___override(v_binderName_5091_, v_newDomain_5089_, v_newBody_5090_, v_binderInfo_5094_);
return v___x_5097_;
}
else
{
uint8_t v___x_5098_; 
v___x_5098_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5094_, v_binderInfo_5094_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; 
lean_inc(v_binderName_5091_);
lean_dec_ref_known(v_e_5088_, 3);
v___x_5099_ = l_Lean_Expr_forallE___override(v_binderName_5091_, v_newDomain_5089_, v_newBody_5090_, v_binderInfo_5094_);
return v___x_5099_;
}
else
{
lean_dec_ref(v_newBody_5090_);
lean_dec_ref(v_newDomain_5089_);
return v_e_5088_;
}
}
}
}
else
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
lean_dec_ref(v_newBody_5090_);
lean_dec_ref(v_newDomain_5089_);
lean_dec_ref(v_e_5088_);
v___x_5106_ = l_Lean_instInhabitedExpr;
v___x_5107_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5108_ = l_panic___redArg(v___x_5106_, v___x_5107_);
return v___x_5108_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5111_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5112_ = lean_unsigned_to_nat(19u);
v___x_5113_ = lean_unsigned_to_nat(1931u);
v___x_5114_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5115_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5116_ = l_mkPanicMessageWithDecl(v___x_5115_, v___x_5114_, v___x_5113_, v___x_5112_, v___x_5111_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5117_, uint8_t v_newBinfo_5118_, lean_object* v_newDomain_5119_, lean_object* v_newBody_5120_){
_start:
{
if (lean_obj_tag(v_e_5117_) == 6)
{
lean_object* v_binderName_5121_; lean_object* v_binderType_5122_; lean_object* v_body_5123_; uint8_t v_binderInfo_5124_; uint8_t v___y_5126_; size_t v___x_5130_; size_t v___x_5131_; uint8_t v___x_5132_; 
v_binderName_5121_ = lean_ctor_get(v_e_5117_, 0);
v_binderType_5122_ = lean_ctor_get(v_e_5117_, 1);
v_body_5123_ = lean_ctor_get(v_e_5117_, 2);
v_binderInfo_5124_ = lean_ctor_get_uint8(v_e_5117_, sizeof(void*)*3 + 8);
v___x_5130_ = lean_ptr_addr(v_binderType_5122_);
v___x_5131_ = lean_ptr_addr(v_newDomain_5119_);
v___x_5132_ = lean_usize_dec_eq(v___x_5130_, v___x_5131_);
if (v___x_5132_ == 0)
{
v___y_5126_ = v___x_5132_;
goto v___jp_5125_;
}
else
{
size_t v___x_5133_; size_t v___x_5134_; uint8_t v___x_5135_; 
v___x_5133_ = lean_ptr_addr(v_body_5123_);
v___x_5134_ = lean_ptr_addr(v_newBody_5120_);
v___x_5135_ = lean_usize_dec_eq(v___x_5133_, v___x_5134_);
v___y_5126_ = v___x_5135_;
goto v___jp_5125_;
}
v___jp_5125_:
{
if (v___y_5126_ == 0)
{
lean_object* v___x_5127_; 
lean_inc(v_binderName_5121_);
lean_dec_ref_known(v_e_5117_, 3);
v___x_5127_ = l_Lean_Expr_lam___override(v_binderName_5121_, v_newDomain_5119_, v_newBody_5120_, v_newBinfo_5118_);
return v___x_5127_;
}
else
{
uint8_t v___x_5128_; 
v___x_5128_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5124_, v_newBinfo_5118_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
lean_inc(v_binderName_5121_);
lean_dec_ref_known(v_e_5117_, 3);
v___x_5129_ = l_Lean_Expr_lam___override(v_binderName_5121_, v_newDomain_5119_, v_newBody_5120_, v_newBinfo_5118_);
return v___x_5129_;
}
else
{
lean_dec_ref(v_newBody_5120_);
lean_dec_ref(v_newDomain_5119_);
return v_e_5117_;
}
}
}
}
else
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
lean_dec_ref(v_newBody_5120_);
lean_dec_ref(v_newDomain_5119_);
lean_dec_ref(v_e_5117_);
v___x_5136_ = l_Lean_instInhabitedExpr;
v___x_5137_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5138_ = l_panic___redArg(v___x_5136_, v___x_5137_);
return v___x_5138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5139_, lean_object* v_newBinfo_5140_, lean_object* v_newDomain_5141_, lean_object* v_newBody_5142_){
_start:
{
uint8_t v_newBinfo_boxed_5143_; lean_object* v_res_5144_; 
v_newBinfo_boxed_5143_ = lean_unbox(v_newBinfo_5140_);
v_res_5144_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5139_, v_newBinfo_boxed_5143_, v_newDomain_5141_, v_newBody_5142_);
return v_res_5144_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5146_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5147_ = lean_unsigned_to_nat(20u);
v___x_5148_ = lean_unsigned_to_nat(1942u);
v___x_5149_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5150_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5151_ = l_mkPanicMessageWithDecl(v___x_5150_, v___x_5149_, v___x_5148_, v___x_5147_, v___x_5146_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5152_, lean_object* v_newDomain_5153_, lean_object* v_newBody_5154_){
_start:
{
if (lean_obj_tag(v_e_5152_) == 6)
{
lean_object* v_binderName_5155_; lean_object* v_binderType_5156_; lean_object* v_body_5157_; uint8_t v_binderInfo_5158_; uint8_t v___y_5160_; size_t v___x_5164_; size_t v___x_5165_; uint8_t v___x_5166_; 
v_binderName_5155_ = lean_ctor_get(v_e_5152_, 0);
v_binderType_5156_ = lean_ctor_get(v_e_5152_, 1);
v_body_5157_ = lean_ctor_get(v_e_5152_, 2);
v_binderInfo_5158_ = lean_ctor_get_uint8(v_e_5152_, sizeof(void*)*3 + 8);
v___x_5164_ = lean_ptr_addr(v_binderType_5156_);
v___x_5165_ = lean_ptr_addr(v_newDomain_5153_);
v___x_5166_ = lean_usize_dec_eq(v___x_5164_, v___x_5165_);
if (v___x_5166_ == 0)
{
v___y_5160_ = v___x_5166_;
goto v___jp_5159_;
}
else
{
size_t v___x_5167_; size_t v___x_5168_; uint8_t v___x_5169_; 
v___x_5167_ = lean_ptr_addr(v_body_5157_);
v___x_5168_ = lean_ptr_addr(v_newBody_5154_);
v___x_5169_ = lean_usize_dec_eq(v___x_5167_, v___x_5168_);
v___y_5160_ = v___x_5169_;
goto v___jp_5159_;
}
v___jp_5159_:
{
if (v___y_5160_ == 0)
{
lean_object* v___x_5161_; 
lean_inc(v_binderName_5155_);
lean_dec_ref_known(v_e_5152_, 3);
v___x_5161_ = l_Lean_Expr_lam___override(v_binderName_5155_, v_newDomain_5153_, v_newBody_5154_, v_binderInfo_5158_);
return v___x_5161_;
}
else
{
uint8_t v___x_5162_; 
v___x_5162_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5158_, v_binderInfo_5158_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; 
lean_inc(v_binderName_5155_);
lean_dec_ref_known(v_e_5152_, 3);
v___x_5163_ = l_Lean_Expr_lam___override(v_binderName_5155_, v_newDomain_5153_, v_newBody_5154_, v_binderInfo_5158_);
return v___x_5163_;
}
else
{
lean_dec_ref(v_newBody_5154_);
lean_dec_ref(v_newDomain_5153_);
return v_e_5152_;
}
}
}
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
lean_dec_ref(v_newBody_5154_);
lean_dec_ref(v_newDomain_5153_);
lean_dec_ref(v_e_5152_);
v___x_5170_ = l_Lean_instInhabitedExpr;
v___x_5171_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5172_ = l_panic___redArg(v___x_5170_, v___x_5171_);
return v___x_5172_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5174_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5175_ = lean_unsigned_to_nat(22u);
v___x_5176_ = lean_unsigned_to_nat(1951u);
v___x_5177_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5178_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5179_ = l_mkPanicMessageWithDecl(v___x_5178_, v___x_5177_, v___x_5176_, v___x_5175_, v___x_5174_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5180_, lean_object* v_newType_5181_, lean_object* v_newVal_5182_, lean_object* v_newBody_5183_, uint8_t v_newNondep_5184_){
_start:
{
if (lean_obj_tag(v_e_5180_) == 8)
{
lean_object* v_declName_5185_; lean_object* v_type_5186_; lean_object* v_value_5187_; lean_object* v_body_5188_; uint8_t v_nondep_5189_; uint8_t v___y_5191_; size_t v___x_5199_; size_t v___x_5200_; uint8_t v___x_5201_; 
v_declName_5185_ = lean_ctor_get(v_e_5180_, 0);
v_type_5186_ = lean_ctor_get(v_e_5180_, 1);
v_value_5187_ = lean_ctor_get(v_e_5180_, 2);
v_body_5188_ = lean_ctor_get(v_e_5180_, 3);
v_nondep_5189_ = lean_ctor_get_uint8(v_e_5180_, sizeof(void*)*4 + 8);
v___x_5199_ = lean_ptr_addr(v_type_5186_);
v___x_5200_ = lean_ptr_addr(v_newType_5181_);
v___x_5201_ = lean_usize_dec_eq(v___x_5199_, v___x_5200_);
if (v___x_5201_ == 0)
{
v___y_5191_ = v___x_5201_;
goto v___jp_5190_;
}
else
{
size_t v___x_5202_; size_t v___x_5203_; uint8_t v___x_5204_; 
v___x_5202_ = lean_ptr_addr(v_value_5187_);
v___x_5203_ = lean_ptr_addr(v_newVal_5182_);
v___x_5204_ = lean_usize_dec_eq(v___x_5202_, v___x_5203_);
v___y_5191_ = v___x_5204_;
goto v___jp_5190_;
}
v___jp_5190_:
{
if (v___y_5191_ == 0)
{
lean_object* v___x_5192_; 
lean_inc(v_declName_5185_);
lean_dec_ref_known(v_e_5180_, 4);
v___x_5192_ = l_Lean_Expr_letE___override(v_declName_5185_, v_newType_5181_, v_newVal_5182_, v_newBody_5183_, v_newNondep_5184_);
return v___x_5192_;
}
else
{
size_t v___x_5193_; size_t v___x_5194_; uint8_t v___x_5195_; 
v___x_5193_ = lean_ptr_addr(v_body_5188_);
v___x_5194_ = lean_ptr_addr(v_newBody_5183_);
v___x_5195_ = lean_usize_dec_eq(v___x_5193_, v___x_5194_);
if (v___x_5195_ == 0)
{
lean_object* v___x_5196_; 
lean_inc(v_declName_5185_);
lean_dec_ref_known(v_e_5180_, 4);
v___x_5196_ = l_Lean_Expr_letE___override(v_declName_5185_, v_newType_5181_, v_newVal_5182_, v_newBody_5183_, v_newNondep_5184_);
return v___x_5196_;
}
else
{
if (v_nondep_5189_ == 0)
{
if (v_newNondep_5184_ == 0)
{
lean_dec_ref(v_newBody_5183_);
lean_dec_ref(v_newVal_5182_);
lean_dec_ref(v_newType_5181_);
return v_e_5180_;
}
else
{
lean_object* v___x_5197_; 
lean_inc(v_declName_5185_);
lean_dec_ref_known(v_e_5180_, 4);
v___x_5197_ = l_Lean_Expr_letE___override(v_declName_5185_, v_newType_5181_, v_newVal_5182_, v_newBody_5183_, v_newNondep_5184_);
return v___x_5197_;
}
}
else
{
if (v_newNondep_5184_ == 0)
{
lean_object* v___x_5198_; 
lean_inc(v_declName_5185_);
lean_dec_ref_known(v_e_5180_, 4);
v___x_5198_ = l_Lean_Expr_letE___override(v_declName_5185_, v_newType_5181_, v_newVal_5182_, v_newBody_5183_, v_newNondep_5184_);
return v___x_5198_;
}
else
{
lean_dec_ref(v_newBody_5183_);
lean_dec_ref(v_newVal_5182_);
lean_dec_ref(v_newType_5181_);
return v_e_5180_;
}
}
}
}
}
}
else
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
lean_dec_ref(v_newBody_5183_);
lean_dec_ref(v_newVal_5182_);
lean_dec_ref(v_newType_5181_);
lean_dec_ref(v_e_5180_);
v___x_5205_ = l_Lean_instInhabitedExpr;
v___x_5206_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5207_ = l_panic___redArg(v___x_5205_, v___x_5206_);
return v___x_5207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5208_, lean_object* v_newType_5209_, lean_object* v_newVal_5210_, lean_object* v_newBody_5211_, lean_object* v_newNondep_5212_){
_start:
{
uint8_t v_newNondep_boxed_5213_; lean_object* v_res_5214_; 
v_newNondep_boxed_5213_ = lean_unbox(v_newNondep_5212_);
v_res_5214_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5208_, v_newType_5209_, v_newVal_5210_, v_newBody_5211_, v_newNondep_boxed_5213_);
return v_res_5214_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5216_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5217_ = lean_unsigned_to_nat(27u);
v___x_5218_ = lean_unsigned_to_nat(1964u);
v___x_5219_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5220_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5221_ = l_mkPanicMessageWithDecl(v___x_5220_, v___x_5219_, v___x_5218_, v___x_5217_, v___x_5216_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5222_, lean_object* v_newType_5223_, lean_object* v_newVal_5224_, lean_object* v_newBody_5225_){
_start:
{
if (lean_obj_tag(v_e_5222_) == 8)
{
lean_object* v_declName_5226_; lean_object* v_type_5227_; lean_object* v_value_5228_; lean_object* v_body_5229_; uint8_t v_nondep_5230_; uint8_t v___y_5232_; size_t v___x_5238_; size_t v___x_5239_; uint8_t v___x_5240_; 
v_declName_5226_ = lean_ctor_get(v_e_5222_, 0);
v_type_5227_ = lean_ctor_get(v_e_5222_, 1);
v_value_5228_ = lean_ctor_get(v_e_5222_, 2);
v_body_5229_ = lean_ctor_get(v_e_5222_, 3);
v_nondep_5230_ = lean_ctor_get_uint8(v_e_5222_, sizeof(void*)*4 + 8);
v___x_5238_ = lean_ptr_addr(v_type_5227_);
v___x_5239_ = lean_ptr_addr(v_newType_5223_);
v___x_5240_ = lean_usize_dec_eq(v___x_5238_, v___x_5239_);
if (v___x_5240_ == 0)
{
v___y_5232_ = v___x_5240_;
goto v___jp_5231_;
}
else
{
size_t v___x_5241_; size_t v___x_5242_; uint8_t v___x_5243_; 
v___x_5241_ = lean_ptr_addr(v_value_5228_);
v___x_5242_ = lean_ptr_addr(v_newVal_5224_);
v___x_5243_ = lean_usize_dec_eq(v___x_5241_, v___x_5242_);
v___y_5232_ = v___x_5243_;
goto v___jp_5231_;
}
v___jp_5231_:
{
if (v___y_5232_ == 0)
{
lean_object* v___x_5233_; 
lean_inc(v_declName_5226_);
lean_dec_ref_known(v_e_5222_, 4);
v___x_5233_ = l_Lean_Expr_letE___override(v_declName_5226_, v_newType_5223_, v_newVal_5224_, v_newBody_5225_, v_nondep_5230_);
return v___x_5233_;
}
else
{
size_t v___x_5234_; size_t v___x_5235_; uint8_t v___x_5236_; 
v___x_5234_ = lean_ptr_addr(v_body_5229_);
v___x_5235_ = lean_ptr_addr(v_newBody_5225_);
v___x_5236_ = lean_usize_dec_eq(v___x_5234_, v___x_5235_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; 
lean_inc(v_declName_5226_);
lean_dec_ref_known(v_e_5222_, 4);
v___x_5237_ = l_Lean_Expr_letE___override(v_declName_5226_, v_newType_5223_, v_newVal_5224_, v_newBody_5225_, v_nondep_5230_);
return v___x_5237_;
}
else
{
lean_dec_ref(v_newBody_5225_);
lean_dec_ref(v_newVal_5224_);
lean_dec_ref(v_newType_5223_);
return v_e_5222_;
}
}
}
}
else
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
lean_dec_ref(v_newBody_5225_);
lean_dec_ref(v_newVal_5224_);
lean_dec_ref(v_newType_5223_);
lean_dec_ref(v_e_5222_);
v___x_5244_ = l_Lean_instInhabitedExpr;
v___x_5245_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5246_ = l_panic___redArg(v___x_5244_, v___x_5245_);
return v___x_5246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5247_, lean_object* v_x_5248_){
_start:
{
if (lean_obj_tag(v_x_5247_) == 5)
{
lean_object* v_fn_5249_; lean_object* v_arg_5250_; lean_object* v___x_5251_; uint8_t v___y_5253_; size_t v___x_5255_; size_t v___x_5256_; uint8_t v___x_5257_; 
v_fn_5249_ = lean_ctor_get(v_x_5247_, 0);
v_arg_5250_ = lean_ctor_get(v_x_5247_, 1);
lean_inc_ref(v_fn_5249_);
v___x_5251_ = l_Lean_Expr_updateFn(v_fn_5249_, v_x_5248_);
v___x_5255_ = lean_ptr_addr(v_fn_5249_);
v___x_5256_ = lean_ptr_addr(v___x_5251_);
v___x_5257_ = lean_usize_dec_eq(v___x_5255_, v___x_5256_);
if (v___x_5257_ == 0)
{
v___y_5253_ = v___x_5257_;
goto v___jp_5252_;
}
else
{
size_t v___x_5258_; uint8_t v___x_5259_; 
v___x_5258_ = lean_ptr_addr(v_arg_5250_);
v___x_5259_ = lean_usize_dec_eq(v___x_5258_, v___x_5258_);
v___y_5253_ = v___x_5259_;
goto v___jp_5252_;
}
v___jp_5252_:
{
if (v___y_5253_ == 0)
{
lean_object* v___x_5254_; 
lean_inc_ref(v_arg_5250_);
lean_dec_ref_known(v_x_5247_, 2);
v___x_5254_ = l_Lean_Expr_app___override(v___x_5251_, v_arg_5250_);
return v___x_5254_;
}
else
{
lean_dec_ref(v___x_5251_);
return v_x_5247_;
}
}
}
else
{
lean_dec_ref(v_x_5247_);
lean_inc_ref(v_x_5248_);
return v_x_5248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5260_, lean_object* v_x_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_Expr_updateFn(v_x_5260_, v_x_5261_);
lean_dec_ref(v_x_5261_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5263_){
_start:
{
if (lean_obj_tag(v_e_5263_) == 6)
{
lean_object* v_binderName_5264_; lean_object* v_binderType_5265_; lean_object* v_body_5266_; uint8_t v_binderInfo_5267_; lean_object* v_b_x27_5268_; uint8_t v___y_5270_; uint8_t v___y_5275_; 
v_binderName_5264_ = lean_ctor_get(v_e_5263_, 0);
v_binderType_5265_ = lean_ctor_get(v_e_5263_, 1);
v_body_5266_ = lean_ctor_get(v_e_5263_, 2);
v_binderInfo_5267_ = lean_ctor_get_uint8(v_e_5263_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5266_);
v_b_x27_5268_ = l_Lean_Expr_eta(v_body_5266_);
if (lean_obj_tag(v_b_x27_5268_) == 5)
{
lean_object* v_arg_5285_; 
v_arg_5285_ = lean_ctor_get(v_b_x27_5268_, 1);
lean_inc_ref(v_arg_5285_);
if (lean_obj_tag(v_arg_5285_) == 0)
{
lean_object* v_fn_5286_; lean_object* v_deBruijnIndex_5287_; lean_object* v___x_5288_; uint8_t v___x_5289_; 
v_fn_5286_ = lean_ctor_get(v_b_x27_5268_, 0);
lean_inc_ref(v_fn_5286_);
v_deBruijnIndex_5287_ = lean_ctor_get(v_arg_5285_, 0);
lean_inc(v_deBruijnIndex_5287_);
lean_dec_ref_known(v_arg_5285_, 1);
v___x_5288_ = lean_unsigned_to_nat(0u);
v___x_5289_ = lean_nat_dec_eq(v_deBruijnIndex_5287_, v___x_5288_);
lean_dec(v_deBruijnIndex_5287_);
if (v___x_5289_ == 0)
{
lean_dec_ref(v_fn_5286_);
goto v___jp_5279_;
}
else
{
uint8_t v___x_5290_; 
v___x_5290_ = lean_expr_has_loose_bvar(v_fn_5286_, v___x_5288_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
lean_dec_ref_known(v_b_x27_5268_, 2);
lean_dec_ref_known(v_e_5263_, 3);
v___x_5291_ = lean_unsigned_to_nat(1u);
v___x_5292_ = lean_expr_lower_loose_bvars(v_fn_5286_, v___x_5291_, v___x_5291_);
lean_dec_ref(v_fn_5286_);
return v___x_5292_;
}
else
{
size_t v___x_5293_; uint8_t v___x_5294_; 
lean_dec_ref(v_fn_5286_);
v___x_5293_ = lean_ptr_addr(v_binderType_5265_);
v___x_5294_ = lean_usize_dec_eq(v___x_5293_, v___x_5293_);
if (v___x_5294_ == 0)
{
v___y_5270_ = v___x_5294_;
goto v___jp_5269_;
}
else
{
size_t v___x_5295_; size_t v___x_5296_; uint8_t v___x_5297_; 
v___x_5295_ = lean_ptr_addr(v_body_5266_);
v___x_5296_ = lean_ptr_addr(v_b_x27_5268_);
v___x_5297_ = lean_usize_dec_eq(v___x_5295_, v___x_5296_);
v___y_5270_ = v___x_5297_;
goto v___jp_5269_;
}
}
}
}
else
{
lean_dec_ref(v_arg_5285_);
goto v___jp_5279_;
}
}
else
{
goto v___jp_5279_;
}
v___jp_5269_:
{
if (v___y_5270_ == 0)
{
lean_object* v___x_5271_; 
lean_inc_ref(v_binderType_5265_);
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5263_, 3);
v___x_5271_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_binderType_5265_, v_b_x27_5268_, v_binderInfo_5267_);
return v___x_5271_;
}
else
{
uint8_t v___x_5272_; 
v___x_5272_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5267_, v_binderInfo_5267_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; 
lean_inc_ref(v_binderType_5265_);
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5263_, 3);
v___x_5273_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_binderType_5265_, v_b_x27_5268_, v_binderInfo_5267_);
return v___x_5273_;
}
else
{
lean_dec_ref(v_b_x27_5268_);
return v_e_5263_;
}
}
}
v___jp_5274_:
{
if (v___y_5275_ == 0)
{
lean_object* v___x_5276_; 
lean_inc_ref(v_binderType_5265_);
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5263_, 3);
v___x_5276_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_binderType_5265_, v_b_x27_5268_, v_binderInfo_5267_);
return v___x_5276_;
}
else
{
uint8_t v___x_5277_; 
v___x_5277_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5267_, v_binderInfo_5267_);
if (v___x_5277_ == 0)
{
lean_object* v___x_5278_; 
lean_inc_ref(v_binderType_5265_);
lean_inc(v_binderName_5264_);
lean_dec_ref_known(v_e_5263_, 3);
v___x_5278_ = l_Lean_Expr_lam___override(v_binderName_5264_, v_binderType_5265_, v_b_x27_5268_, v_binderInfo_5267_);
return v___x_5278_;
}
else
{
lean_dec_ref(v_b_x27_5268_);
return v_e_5263_;
}
}
}
v___jp_5279_:
{
size_t v___x_5280_; uint8_t v___x_5281_; 
v___x_5280_ = lean_ptr_addr(v_binderType_5265_);
v___x_5281_ = lean_usize_dec_eq(v___x_5280_, v___x_5280_);
if (v___x_5281_ == 0)
{
v___y_5275_ = v___x_5281_;
goto v___jp_5274_;
}
else
{
size_t v___x_5282_; size_t v___x_5283_; uint8_t v___x_5284_; 
v___x_5282_ = lean_ptr_addr(v_body_5266_);
v___x_5283_ = lean_ptr_addr(v_b_x27_5268_);
v___x_5284_ = lean_usize_dec_eq(v___x_5282_, v___x_5283_);
v___y_5275_ = v___x_5284_;
goto v___jp_5274_;
}
}
}
else
{
return v_e_5263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5298_, lean_object* v_optionName_5299_, lean_object* v_inst_5300_, lean_object* v_val_5301_){
_start:
{
lean_object* v_toDataValue_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
v_toDataValue_5302_ = lean_ctor_get(v_inst_5300_, 0);
lean_inc_ref(v_toDataValue_5302_);
lean_dec_ref(v_inst_5300_);
v___x_5303_ = lean_box(0);
v___x_5304_ = lean_apply_1(v_toDataValue_5302_, v_val_5301_);
v___x_5305_ = l_Lean_KVMap_insert(v___x_5303_, v_optionName_5299_, v___x_5304_);
v___x_5306_ = l_Lean_Expr_mdata___override(v___x_5305_, v_e_5298_);
return v___x_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5307_, lean_object* v_e_5308_, lean_object* v_optionName_5309_, lean_object* v_inst_5310_, lean_object* v_val_5311_){
_start:
{
lean_object* v___x_5312_; 
v___x_5312_ = l_Lean_Expr_setOption___redArg(v_e_5308_, v_optionName_5309_, v_inst_5310_, v_val_5311_);
return v___x_5312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5313_, lean_object* v_optionName_5314_, uint8_t v_val_5315_){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; 
v___x_5316_ = lean_box(0);
v___x_5317_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5317_, 0, v_val_5315_);
v___x_5318_ = l_Lean_KVMap_insert(v___x_5316_, v_optionName_5314_, v___x_5317_);
v___x_5319_ = l_Lean_Expr_mdata___override(v___x_5318_, v_e_5313_);
return v___x_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5320_, lean_object* v_optionName_5321_, lean_object* v_val_5322_){
_start:
{
uint8_t v_val_boxed_5323_; lean_object* v_res_5324_; 
v_val_boxed_5323_ = lean_unbox(v_val_5322_);
v_res_5324_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5320_, v_optionName_5321_, v_val_boxed_5323_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5330_, uint8_t v_flag_5331_){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5332_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5333_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5330_, v___x_5332_, v_flag_5331_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5334_, lean_object* v_flag_5335_){
_start:
{
uint8_t v_flag_boxed_5336_; lean_object* v_res_5337_; 
v_flag_boxed_5336_ = lean_unbox(v_flag_5335_);
v_res_5337_ = l_Lean_Expr_setPPExplicit(v_e_5334_, v_flag_boxed_5336_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5342_, uint8_t v_flag_5343_){
_start:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5344_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5345_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5342_, v___x_5344_, v_flag_5343_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5346_, lean_object* v_flag_5347_){
_start:
{
uint8_t v_flag_boxed_5348_; lean_object* v_res_5349_; 
v_flag_boxed_5348_ = lean_unbox(v_flag_5347_);
v_res_5349_ = l_Lean_Expr_setPPUniverses(v_e_5346_, v_flag_boxed_5348_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5354_, uint8_t v_flag_5355_){
_start:
{
lean_object* v___x_5356_; lean_object* v___x_5357_; 
v___x_5356_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5357_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5354_, v___x_5356_, v_flag_5355_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5358_, lean_object* v_flag_5359_){
_start:
{
uint8_t v_flag_boxed_5360_; lean_object* v_res_5361_; 
v_flag_boxed_5360_ = lean_unbox(v_flag_5359_);
v_res_5361_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5358_, v_flag_boxed_5360_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5366_, uint8_t v_flag_5367_){
_start:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5369_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5366_, v___x_5368_, v_flag_5367_);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5370_, lean_object* v_flag_5371_){
_start:
{
uint8_t v_flag_boxed_5372_; lean_object* v_res_5373_; 
v_flag_boxed_5372_ = lean_unbox(v_flag_5371_);
v_res_5373_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5370_, v_flag_boxed_5372_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5378_, uint8_t v_flag_5379_){
_start:
{
lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5380_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5381_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5378_, v___x_5380_, v_flag_5379_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5382_, lean_object* v_flag_5383_){
_start:
{
uint8_t v_flag_boxed_5384_; lean_object* v_res_5385_; 
v_flag_boxed_5384_ = lean_unbox(v_flag_5383_);
v_res_5385_ = l_Lean_Expr_setPPNumericTypes(v_e_5382_, v_flag_boxed_5384_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5386_, size_t v_i_5387_, lean_object* v_bs_5388_){
_start:
{
uint8_t v___x_5389_; 
v___x_5389_ = lean_usize_dec_lt(v_i_5387_, v_sz_5386_);
if (v___x_5389_ == 0)
{
return v_bs_5388_;
}
else
{
uint8_t v___x_5390_; lean_object* v_v_5391_; lean_object* v___x_5392_; lean_object* v_bs_x27_5393_; lean_object* v___x_5394_; size_t v___x_5395_; size_t v___x_5396_; lean_object* v___x_5397_; 
v___x_5390_ = 0;
v_v_5391_ = lean_array_uget(v_bs_5388_, v_i_5387_);
v___x_5392_ = lean_unsigned_to_nat(0u);
v_bs_x27_5393_ = lean_array_uset(v_bs_5388_, v_i_5387_, v___x_5392_);
v___x_5394_ = l_Lean_Expr_setPPExplicit(v_v_5391_, v___x_5390_);
v___x_5395_ = ((size_t)1ULL);
v___x_5396_ = lean_usize_add(v_i_5387_, v___x_5395_);
v___x_5397_ = lean_array_uset(v_bs_x27_5393_, v_i_5387_, v___x_5394_);
v_i_5387_ = v___x_5396_;
v_bs_5388_ = v___x_5397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5399_, lean_object* v_i_5400_, lean_object* v_bs_5401_){
_start:
{
size_t v_sz_boxed_5402_; size_t v_i_boxed_5403_; lean_object* v_res_5404_; 
v_sz_boxed_5402_ = lean_unbox_usize(v_sz_5399_);
lean_dec(v_sz_5399_);
v_i_boxed_5403_ = lean_unbox_usize(v_i_5400_);
lean_dec(v_i_5400_);
v_res_5404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5402_, v_i_boxed_5403_, v_bs_5401_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5405_){
_start:
{
if (lean_obj_tag(v_e_5405_) == 5)
{
lean_object* v___x_5406_; uint8_t v___x_5407_; lean_object* v_f_5408_; lean_object* v_dummy_5409_; lean_object* v_nargs_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; size_t v_sz_5415_; size_t v___x_5416_; lean_object* v_args_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; lean_object* v___x_5420_; 
v___x_5406_ = l_Lean_Expr_getAppFn(v_e_5405_);
v___x_5407_ = 0;
v_f_5408_ = l_Lean_Expr_setPPExplicit(v___x_5406_, v___x_5407_);
v_dummy_5409_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5410_ = l_Lean_Expr_getAppNumArgs(v_e_5405_);
lean_inc(v_nargs_5410_);
v___x_5411_ = lean_mk_array(v_nargs_5410_, v_dummy_5409_);
v___x_5412_ = lean_unsigned_to_nat(1u);
v___x_5413_ = lean_nat_sub(v_nargs_5410_, v___x_5412_);
lean_dec(v_nargs_5410_);
v___x_5414_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5405_, v___x_5411_, v___x_5413_);
v_sz_5415_ = lean_array_size(v___x_5414_);
v___x_5416_ = ((size_t)0ULL);
v_args_5417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5415_, v___x_5416_, v___x_5414_);
v___x_5418_ = l_Lean_mkAppN(v_f_5408_, v_args_5417_);
lean_dec_ref(v_args_5417_);
v___x_5419_ = 1;
v___x_5420_ = l_Lean_Expr_setPPExplicit(v___x_5418_, v___x_5419_);
return v___x_5420_;
}
else
{
return v_e_5405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5421_, size_t v_i_5422_, lean_object* v_bs_5423_){
_start:
{
uint8_t v___x_5424_; 
v___x_5424_ = lean_usize_dec_lt(v_i_5422_, v_sz_5421_);
if (v___x_5424_ == 0)
{
return v_bs_5423_;
}
else
{
lean_object* v_v_5425_; lean_object* v___x_5426_; lean_object* v_bs_x27_5427_; lean_object* v___y_5429_; uint8_t v___x_5434_; 
v_v_5425_ = lean_array_uget(v_bs_5423_, v_i_5422_);
v___x_5426_ = lean_unsigned_to_nat(0u);
v_bs_x27_5427_ = lean_array_uset(v_bs_5423_, v_i_5422_, v___x_5426_);
v___x_5434_ = l_Lean_Expr_hasMVar(v_v_5425_);
if (v___x_5434_ == 0)
{
lean_object* v___x_5435_; 
v___x_5435_ = l_Lean_Expr_setPPExplicit(v_v_5425_, v___x_5434_);
v___y_5429_ = v___x_5435_;
goto v___jp_5428_;
}
else
{
v___y_5429_ = v_v_5425_;
goto v___jp_5428_;
}
v___jp_5428_:
{
size_t v___x_5430_; size_t v___x_5431_; lean_object* v___x_5432_; 
v___x_5430_ = ((size_t)1ULL);
v___x_5431_ = lean_usize_add(v_i_5422_, v___x_5430_);
v___x_5432_ = lean_array_uset(v_bs_x27_5427_, v_i_5422_, v___y_5429_);
v_i_5422_ = v___x_5431_;
v_bs_5423_ = v___x_5432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5436_, lean_object* v_i_5437_, lean_object* v_bs_5438_){
_start:
{
size_t v_sz_boxed_5439_; size_t v_i_boxed_5440_; lean_object* v_res_5441_; 
v_sz_boxed_5439_ = lean_unbox_usize(v_sz_5436_);
lean_dec(v_sz_5436_);
v_i_boxed_5440_ = lean_unbox_usize(v_i_5437_);
lean_dec(v_i_5437_);
v_res_5441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5439_, v_i_boxed_5440_, v_bs_5438_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5442_){
_start:
{
if (lean_obj_tag(v_e_5442_) == 5)
{
lean_object* v___x_5443_; uint8_t v___x_5444_; lean_object* v_f_5445_; lean_object* v_dummy_5446_; lean_object* v_nargs_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; size_t v_sz_5452_; size_t v___x_5453_; lean_object* v_args_5454_; lean_object* v___x_5455_; uint8_t v___x_5456_; lean_object* v___x_5457_; 
v___x_5443_ = l_Lean_Expr_getAppFn(v_e_5442_);
v___x_5444_ = 0;
v_f_5445_ = l_Lean_Expr_setPPExplicit(v___x_5443_, v___x_5444_);
v_dummy_5446_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5447_ = l_Lean_Expr_getAppNumArgs(v_e_5442_);
lean_inc(v_nargs_5447_);
v___x_5448_ = lean_mk_array(v_nargs_5447_, v_dummy_5446_);
v___x_5449_ = lean_unsigned_to_nat(1u);
v___x_5450_ = lean_nat_sub(v_nargs_5447_, v___x_5449_);
lean_dec(v_nargs_5447_);
v___x_5451_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5442_, v___x_5448_, v___x_5450_);
v_sz_5452_ = lean_array_size(v___x_5451_);
v___x_5453_ = ((size_t)0ULL);
v_args_5454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5452_, v___x_5453_, v___x_5451_);
v___x_5455_ = l_Lean_mkAppN(v_f_5445_, v_args_5454_);
lean_dec_ref(v_args_5454_);
v___x_5456_ = 1;
v___x_5457_ = l_Lean_Expr_setPPExplicit(v___x_5455_, v___x_5456_);
return v___x_5457_;
}
else
{
return v_e_5442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5458_, lean_object* v_body_5459_, lean_object* v_x_5460_){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = lean_apply_1(v_f_5458_, v_body_5459_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5462_, lean_object* v_binderType_5463_, lean_object* v_x_5464_){
_start:
{
lean_object* v___x_5465_; 
v___x_5465_ = lean_apply_1(v_f_5462_, v_binderType_5463_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5466_, lean_object* v_value_5467_, lean_object* v_x_5468_){
_start:
{
lean_object* v___x_5469_; 
v___x_5469_ = lean_apply_1(v_f_5466_, v_value_5467_);
return v___x_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5470_, lean_object* v_type_5471_, lean_object* v_x_5472_){
_start:
{
lean_object* v___x_5473_; 
v___x_5473_ = lean_apply_1(v_f_5470_, v_type_5471_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5474_, lean_object* v_arg_5475_, lean_object* v_x_5476_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = lean_apply_1(v_f_5474_, v_arg_5475_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5478_, lean_object* v_fn_5479_, lean_object* v_x_5480_){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = lean_apply_1(v_f_5478_, v_fn_5479_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5482_, lean_object* v_f_5483_, lean_object* v_x_5484_){
_start:
{
switch(lean_obj_tag(v_x_5484_))
{
case 7:
{
lean_object* v_toPure_5485_; lean_object* v_toSeq_5486_; lean_object* v_binderType_5487_; lean_object* v_body_5488_; lean_object* v___f_5489_; lean_object* v___f_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v_toPure_5485_ = lean_ctor_get(v_inst_5482_, 1);
lean_inc(v_toPure_5485_);
v_toSeq_5486_ = lean_ctor_get(v_inst_5482_, 2);
lean_inc_n(v_toSeq_5486_, 2);
lean_dec_ref(v_inst_5482_);
v_binderType_5487_ = lean_ctor_get(v_x_5484_, 1);
v_body_5488_ = lean_ctor_get(v_x_5484_, 2);
lean_inc_ref(v_body_5488_);
lean_inc(v_f_5483_);
v___f_5489_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5489_, 0, v_f_5483_);
lean_closure_set(v___f_5489_, 1, v_body_5488_);
lean_inc_ref(v_binderType_5487_);
v___f_5490_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5490_, 0, v_f_5483_);
lean_closure_set(v___f_5490_, 1, v_binderType_5487_);
v___x_5491_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5491_, 0, v_x_5484_);
v___x_5492_ = lean_apply_2(v_toPure_5485_, lean_box(0), v___x_5491_);
v___x_5493_ = lean_apply_4(v_toSeq_5486_, lean_box(0), lean_box(0), v___x_5492_, v___f_5490_);
v___x_5494_ = lean_apply_4(v_toSeq_5486_, lean_box(0), lean_box(0), v___x_5493_, v___f_5489_);
return v___x_5494_;
}
case 6:
{
lean_object* v_toPure_5495_; lean_object* v_toSeq_5496_; lean_object* v_binderType_5497_; lean_object* v_body_5498_; lean_object* v___f_5499_; lean_object* v___f_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; 
v_toPure_5495_ = lean_ctor_get(v_inst_5482_, 1);
lean_inc(v_toPure_5495_);
v_toSeq_5496_ = lean_ctor_get(v_inst_5482_, 2);
lean_inc_n(v_toSeq_5496_, 2);
lean_dec_ref(v_inst_5482_);
v_binderType_5497_ = lean_ctor_get(v_x_5484_, 1);
v_body_5498_ = lean_ctor_get(v_x_5484_, 2);
lean_inc_ref(v_body_5498_);
lean_inc(v_f_5483_);
v___f_5499_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5499_, 0, v_f_5483_);
lean_closure_set(v___f_5499_, 1, v_body_5498_);
lean_inc_ref(v_binderType_5497_);
v___f_5500_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5500_, 0, v_f_5483_);
lean_closure_set(v___f_5500_, 1, v_binderType_5497_);
v___x_5501_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5501_, 0, v_x_5484_);
v___x_5502_ = lean_apply_2(v_toPure_5495_, lean_box(0), v___x_5501_);
v___x_5503_ = lean_apply_4(v_toSeq_5496_, lean_box(0), lean_box(0), v___x_5502_, v___f_5500_);
v___x_5504_ = lean_apply_4(v_toSeq_5496_, lean_box(0), lean_box(0), v___x_5503_, v___f_5499_);
return v___x_5504_;
}
case 10:
{
lean_object* v_toFunctor_5505_; lean_object* v_expr_5506_; lean_object* v_map_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
v_toFunctor_5505_ = lean_ctor_get(v_inst_5482_, 0);
lean_inc_ref(v_toFunctor_5505_);
lean_dec_ref(v_inst_5482_);
v_expr_5506_ = lean_ctor_get(v_x_5484_, 1);
lean_inc_ref(v_expr_5506_);
v_map_5507_ = lean_ctor_get(v_toFunctor_5505_, 0);
lean_inc(v_map_5507_);
lean_dec_ref(v_toFunctor_5505_);
v___x_5508_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5508_, 0, v_x_5484_);
v___x_5509_ = lean_apply_1(v_f_5483_, v_expr_5506_);
v___x_5510_ = lean_apply_4(v_map_5507_, lean_box(0), lean_box(0), v___x_5508_, v___x_5509_);
return v___x_5510_;
}
case 8:
{
lean_object* v_toPure_5511_; lean_object* v_toSeq_5512_; lean_object* v_type_5513_; lean_object* v_value_5514_; lean_object* v_body_5515_; lean_object* v___f_5516_; lean_object* v___f_5517_; lean_object* v___f_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v_toPure_5511_ = lean_ctor_get(v_inst_5482_, 1);
lean_inc(v_toPure_5511_);
v_toSeq_5512_ = lean_ctor_get(v_inst_5482_, 2);
lean_inc_n(v_toSeq_5512_, 3);
lean_dec_ref(v_inst_5482_);
v_type_5513_ = lean_ctor_get(v_x_5484_, 1);
v_value_5514_ = lean_ctor_get(v_x_5484_, 2);
v_body_5515_ = lean_ctor_get(v_x_5484_, 3);
lean_inc_ref(v_body_5515_);
lean_inc_n(v_f_5483_, 2);
v___f_5516_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5516_, 0, v_f_5483_);
lean_closure_set(v___f_5516_, 1, v_body_5515_);
lean_inc_ref(v_value_5514_);
v___f_5517_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5517_, 0, v_f_5483_);
lean_closure_set(v___f_5517_, 1, v_value_5514_);
lean_inc_ref(v_type_5513_);
v___f_5518_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5518_, 0, v_f_5483_);
lean_closure_set(v___f_5518_, 1, v_type_5513_);
v___x_5519_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5519_, 0, v_x_5484_);
v___x_5520_ = lean_apply_2(v_toPure_5511_, lean_box(0), v___x_5519_);
v___x_5521_ = lean_apply_4(v_toSeq_5512_, lean_box(0), lean_box(0), v___x_5520_, v___f_5518_);
v___x_5522_ = lean_apply_4(v_toSeq_5512_, lean_box(0), lean_box(0), v___x_5521_, v___f_5517_);
v___x_5523_ = lean_apply_4(v_toSeq_5512_, lean_box(0), lean_box(0), v___x_5522_, v___f_5516_);
return v___x_5523_;
}
case 5:
{
lean_object* v_toPure_5524_; lean_object* v_toSeq_5525_; lean_object* v_fn_5526_; lean_object* v_arg_5527_; lean_object* v___f_5528_; lean_object* v___f_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v_toPure_5524_ = lean_ctor_get(v_inst_5482_, 1);
lean_inc(v_toPure_5524_);
v_toSeq_5525_ = lean_ctor_get(v_inst_5482_, 2);
lean_inc_n(v_toSeq_5525_, 2);
lean_dec_ref(v_inst_5482_);
v_fn_5526_ = lean_ctor_get(v_x_5484_, 0);
v_arg_5527_ = lean_ctor_get(v_x_5484_, 1);
lean_inc_ref(v_arg_5527_);
lean_inc(v_f_5483_);
v___f_5528_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5528_, 0, v_f_5483_);
lean_closure_set(v___f_5528_, 1, v_arg_5527_);
lean_inc_ref(v_fn_5526_);
v___f_5529_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5529_, 0, v_f_5483_);
lean_closure_set(v___f_5529_, 1, v_fn_5526_);
v___x_5530_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5530_, 0, v_x_5484_);
v___x_5531_ = lean_apply_2(v_toPure_5524_, lean_box(0), v___x_5530_);
v___x_5532_ = lean_apply_4(v_toSeq_5525_, lean_box(0), lean_box(0), v___x_5531_, v___f_5529_);
v___x_5533_ = lean_apply_4(v_toSeq_5525_, lean_box(0), lean_box(0), v___x_5532_, v___f_5528_);
return v___x_5533_;
}
case 11:
{
lean_object* v_toFunctor_5534_; lean_object* v_struct_5535_; lean_object* v_map_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; 
v_toFunctor_5534_ = lean_ctor_get(v_inst_5482_, 0);
lean_inc_ref(v_toFunctor_5534_);
lean_dec_ref(v_inst_5482_);
v_struct_5535_ = lean_ctor_get(v_x_5484_, 2);
lean_inc_ref(v_struct_5535_);
v_map_5536_ = lean_ctor_get(v_toFunctor_5534_, 0);
lean_inc(v_map_5536_);
lean_dec_ref(v_toFunctor_5534_);
v___x_5537_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5537_, 0, v_x_5484_);
v___x_5538_ = lean_apply_1(v_f_5483_, v_struct_5535_);
v___x_5539_ = lean_apply_4(v_map_5536_, lean_box(0), lean_box(0), v___x_5537_, v___x_5538_);
return v___x_5539_;
}
default: 
{
lean_object* v_toPure_5540_; lean_object* v___x_5541_; 
lean_dec(v_f_5483_);
v_toPure_5540_ = lean_ctor_get(v_inst_5482_, 1);
lean_inc(v_toPure_5540_);
lean_dec_ref(v_inst_5482_);
v___x_5541_ = lean_apply_2(v_toPure_5540_, lean_box(0), v_x_5484_);
return v___x_5541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5542_, lean_object* v_inst_5543_, lean_object* v_f_5544_, lean_object* v_x_5545_){
_start:
{
lean_object* v___x_5546_; 
v___x_5546_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5543_, v_f_5544_, v_x_5545_);
return v___x_5546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5547_){
_start:
{
lean_object* v_snd_5548_; 
v_snd_5548_ = lean_ctor_get(v_self_5547_, 1);
lean_inc(v_snd_5548_);
return v_snd_5548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5549_);
lean_dec_ref(v_self_5549_);
return v_res_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5551_, lean_object* v_snd_5552_){
_start:
{
lean_object* v___x_5553_; 
v___x_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5553_, 0, v_e_x27_5551_);
lean_ctor_set(v___x_5553_, 1, v_snd_5552_);
return v___x_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5554_, lean_object* v_map_5555_, lean_object* v_e_x27_5556_, lean_object* v_a_5557_){
_start:
{
lean_object* v___f_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; 
lean_inc_ref(v_e_x27_5556_);
v___f_5558_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5558_, 0, v_e_x27_5556_);
v___x_5559_ = lean_apply_2(v_f_5554_, v_a_5557_, v_e_x27_5556_);
v___x_5560_ = lean_apply_4(v_map_5555_, lean_box(0), lean_box(0), v___f_5558_, v___x_5559_);
return v___x_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5562_, lean_object* v_f_5563_, lean_object* v_init_5564_, lean_object* v_e_5565_){
_start:
{
lean_object* v_toApplicative_5566_; lean_object* v_toFunctor_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5594_; 
v_toApplicative_5566_ = lean_ctor_get(v_inst_5562_, 0);
lean_inc_ref(v_toApplicative_5566_);
v_toFunctor_5567_ = lean_ctor_get(v_toApplicative_5566_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_toApplicative_5566_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; lean_object* v_unused_5596_; lean_object* v_unused_5597_; lean_object* v_unused_5598_; 
v_unused_5595_ = lean_ctor_get(v_toApplicative_5566_, 4);
lean_dec(v_unused_5595_);
v_unused_5596_ = lean_ctor_get(v_toApplicative_5566_, 3);
lean_dec(v_unused_5596_);
v_unused_5597_ = lean_ctor_get(v_toApplicative_5566_, 2);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_toApplicative_5566_, 1);
lean_dec(v_unused_5598_);
v___x_5569_ = v_toApplicative_5566_;
v_isShared_5570_ = v_isSharedCheck_5594_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_toFunctor_5567_);
lean_dec(v_toApplicative_5566_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5594_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v_map_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5592_; 
v_map_5571_ = lean_ctor_get(v_toFunctor_5567_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v_toFunctor_5567_);
if (v_isSharedCheck_5592_ == 0)
{
lean_object* v_unused_5593_; 
v_unused_5593_ = lean_ctor_get(v_toFunctor_5567_, 1);
lean_dec(v_unused_5593_);
v___x_5573_ = v_toFunctor_5567_;
v_isShared_5574_ = v_isSharedCheck_5592_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_map_5571_);
lean_dec(v_toFunctor_5567_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5592_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___f_5575_; lean_object* v___f_5576_; lean_object* v___f_5577_; lean_object* v___f_5578_; lean_object* v___f_5579_; lean_object* v___f_5580_; lean_object* v___x_5581_; lean_object* v___x_5583_; 
v___f_5575_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5571_);
v___f_5576_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5576_, 0, v_f_5563_);
lean_closure_set(v___f_5576_, 1, v_map_5571_);
lean_inc_ref_n(v_inst_5562_, 5);
v___f_5577_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5577_, 0, v_inst_5562_);
v___f_5578_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5578_, 0, v_inst_5562_);
v___f_5579_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5579_, 0, v_inst_5562_);
v___f_5580_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5580_, 0, v_inst_5562_);
v___x_5581_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5581_, 0, lean_box(0));
lean_closure_set(v___x_5581_, 1, lean_box(0));
lean_closure_set(v___x_5581_, 2, v_inst_5562_);
if (v_isShared_5574_ == 0)
{
lean_ctor_set(v___x_5573_, 1, v___f_5577_);
lean_ctor_set(v___x_5573_, 0, v___x_5581_);
v___x_5583_ = v___x_5573_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v___f_5577_);
v___x_5583_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5584_; lean_object* v___x_5586_; 
v___x_5584_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5584_, 0, lean_box(0));
lean_closure_set(v___x_5584_, 1, lean_box(0));
lean_closure_set(v___x_5584_, 2, v_inst_5562_);
if (v_isShared_5570_ == 0)
{
lean_ctor_set(v___x_5569_, 4, v___f_5580_);
lean_ctor_set(v___x_5569_, 3, v___f_5579_);
lean_ctor_set(v___x_5569_, 2, v___f_5578_);
lean_ctor_set(v___x_5569_, 1, v___x_5584_);
lean_ctor_set(v___x_5569_, 0, v___x_5583_);
v___x_5586_ = v___x_5569_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5583_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5584_);
lean_ctor_set(v_reuseFailAlloc_5590_, 2, v___f_5578_);
lean_ctor_set(v_reuseFailAlloc_5590_, 3, v___f_5579_);
lean_ctor_set(v_reuseFailAlloc_5590_, 4, v___f_5580_);
v___x_5586_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_18__overap_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_18__overap_5587_ = l_Lean_Expr_traverseChildren___redArg(v___x_5586_, v___f_5576_, v_e_5565_);
v___x_5588_ = lean_apply_1(v___x_18__overap_5587_, v_init_5564_);
v___x_5589_ = lean_apply_4(v_map_5571_, lean_box(0), lean_box(0), v___f_5575_, v___x_5588_);
return v___x_5589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5599_, lean_object* v_m_5600_, lean_object* v_inst_5601_, lean_object* v_f_5602_, lean_object* v_init_5603_, lean_object* v_e_5604_){
_start:
{
lean_object* v___x_5605_; 
v___x_5605_ = l_Lean_Expr_foldlM___redArg(v_inst_5601_, v_f_5602_, v_init_5603_, v_e_5604_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5606_){
_start:
{
lean_object* v_d_5608_; lean_object* v_b_5609_; 
switch(lean_obj_tag(v_x_5606_))
{
case 5:
{
lean_object* v_fn_5615_; lean_object* v_arg_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; 
v_fn_5615_ = lean_ctor_get(v_x_5606_, 0);
v_arg_5616_ = lean_ctor_get(v_x_5606_, 1);
v___x_5617_ = lean_unsigned_to_nat(1u);
v___x_5618_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5615_);
v___x_5619_ = lean_nat_add(v___x_5617_, v___x_5618_);
lean_dec(v___x_5618_);
v___x_5620_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5616_);
v___x_5621_ = lean_nat_add(v___x_5619_, v___x_5620_);
lean_dec(v___x_5620_);
lean_dec(v___x_5619_);
return v___x_5621_;
}
case 6:
{
lean_object* v_binderType_5622_; lean_object* v_body_5623_; 
v_binderType_5622_ = lean_ctor_get(v_x_5606_, 1);
v_body_5623_ = lean_ctor_get(v_x_5606_, 2);
v_d_5608_ = v_binderType_5622_;
v_b_5609_ = v_body_5623_;
goto v___jp_5607_;
}
case 7:
{
lean_object* v_binderType_5624_; lean_object* v_body_5625_; 
v_binderType_5624_ = lean_ctor_get(v_x_5606_, 1);
v_body_5625_ = lean_ctor_get(v_x_5606_, 2);
v_d_5608_ = v_binderType_5624_;
v_b_5609_ = v_body_5625_;
goto v___jp_5607_;
}
case 8:
{
lean_object* v_type_5626_; lean_object* v_value_5627_; lean_object* v_body_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; 
v_type_5626_ = lean_ctor_get(v_x_5606_, 1);
v_value_5627_ = lean_ctor_get(v_x_5606_, 2);
v_body_5628_ = lean_ctor_get(v_x_5606_, 3);
v___x_5629_ = lean_unsigned_to_nat(1u);
v___x_5630_ = l_Lean_Expr_sizeWithoutSharing(v_type_5626_);
v___x_5631_ = lean_nat_add(v___x_5629_, v___x_5630_);
lean_dec(v___x_5630_);
v___x_5632_ = l_Lean_Expr_sizeWithoutSharing(v_value_5627_);
v___x_5633_ = lean_nat_add(v___x_5631_, v___x_5632_);
lean_dec(v___x_5632_);
lean_dec(v___x_5631_);
v___x_5634_ = l_Lean_Expr_sizeWithoutSharing(v_body_5628_);
v___x_5635_ = lean_nat_add(v___x_5633_, v___x_5634_);
lean_dec(v___x_5634_);
lean_dec(v___x_5633_);
return v___x_5635_;
}
case 10:
{
lean_object* v_expr_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; 
v_expr_5636_ = lean_ctor_get(v_x_5606_, 1);
v___x_5637_ = lean_unsigned_to_nat(1u);
v___x_5638_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5636_);
v___x_5639_ = lean_nat_add(v___x_5637_, v___x_5638_);
lean_dec(v___x_5638_);
return v___x_5639_;
}
case 11:
{
lean_object* v_struct_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; 
v_struct_5640_ = lean_ctor_get(v_x_5606_, 2);
v___x_5641_ = lean_unsigned_to_nat(1u);
v___x_5642_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5640_);
v___x_5643_ = lean_nat_add(v___x_5641_, v___x_5642_);
lean_dec(v___x_5642_);
return v___x_5643_;
}
default: 
{
lean_object* v___x_5644_; 
v___x_5644_ = lean_unsigned_to_nat(1u);
return v___x_5644_;
}
}
v___jp_5607_:
{
lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
v___x_5610_ = lean_unsigned_to_nat(1u);
v___x_5611_ = l_Lean_Expr_sizeWithoutSharing(v_d_5608_);
v___x_5612_ = lean_nat_add(v___x_5610_, v___x_5611_);
lean_dec(v___x_5611_);
v___x_5613_ = l_Lean_Expr_sizeWithoutSharing(v_b_5609_);
v___x_5614_ = lean_nat_add(v___x_5612_, v___x_5613_);
lean_dec(v___x_5613_);
lean_dec(v___x_5612_);
return v___x_5614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l_Lean_Expr_sizeWithoutSharing(v_x_5645_);
lean_dec_ref(v_x_5645_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5649_, lean_object* v_e_5650_){
_start:
{
lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5651_ = l_Lean_KVMap_empty;
v___x_5652_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5653_ = l_Lean_KVMap_insert(v___x_5651_, v_kind_5649_, v___x_5652_);
v___x_5654_ = l_Lean_Expr_mdata___override(v___x_5653_, v_e_5650_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5655_, lean_object* v_e_5656_){
_start:
{
if (lean_obj_tag(v_e_5656_) == 10)
{
lean_object* v_data_5657_; lean_object* v_expr_5658_; uint8_t v___y_5660_; lean_object* v___x_5663_; lean_object* v___x_5664_; uint8_t v___x_5665_; 
v_data_5657_ = lean_ctor_get(v_e_5656_, 0);
v_expr_5658_ = lean_ctor_get(v_e_5656_, 1);
v___x_5663_ = l_Lean_KVMap_size(v_data_5657_);
v___x_5664_ = lean_unsigned_to_nat(1u);
v___x_5665_ = lean_nat_dec_eq(v___x_5663_, v___x_5664_);
lean_dec(v___x_5663_);
if (v___x_5665_ == 0)
{
v___y_5660_ = v___x_5665_;
goto v___jp_5659_;
}
else
{
uint8_t v___x_5666_; uint8_t v___x_5667_; 
v___x_5666_ = 0;
v___x_5667_ = l_Lean_KVMap_getBool(v_data_5657_, v_kind_5655_, v___x_5666_);
v___y_5660_ = v___x_5667_;
goto v___jp_5659_;
}
v___jp_5659_:
{
if (v___y_5660_ == 0)
{
lean_object* v___x_5661_; 
v___x_5661_ = lean_box(0);
return v___x_5661_;
}
else
{
lean_object* v___x_5662_; 
lean_inc_ref(v_expr_5658_);
v___x_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5662_, 0, v_expr_5658_);
return v___x_5662_;
}
}
}
else
{
lean_object* v___x_5668_; 
v___x_5668_ = lean_box(0);
return v___x_5668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5669_, lean_object* v_e_5670_){
_start:
{
lean_object* v_res_5671_; 
v_res_5671_ = l_Lean_annotation_x3f(v_kind_5669_, v_e_5670_);
lean_dec_ref(v_e_5670_);
lean_dec(v_kind_5669_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5675_){
_start:
{
lean_object* v___x_5676_; lean_object* v___x_5677_; 
v___x_5676_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5677_ = l_Lean_mkAnnotation(v___x_5676_, v_e_5675_);
return v___x_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5678_){
_start:
{
lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5679_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5680_ = l_Lean_annotation_x3f(v___x_5679_, v_e_5678_);
return v___x_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5681_){
_start:
{
lean_object* v_res_5682_; 
v_res_5682_ = l_Lean_inaccessible_x3f(v_e_5681_);
lean_dec_ref(v_e_5681_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5687_){
_start:
{
if (lean_obj_tag(v_p_5687_) == 10)
{
lean_object* v_data_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v_data_5688_ = lean_ctor_get(v_p_5687_, 0);
v___x_5689_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5690_ = l_Lean_KVMap_find(v_data_5688_, v___x_5689_);
if (lean_obj_tag(v___x_5690_) == 1)
{
lean_object* v_val_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5702_; 
v_val_5691_ = lean_ctor_get(v___x_5690_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5690_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5693_ = v___x_5690_;
v_isShared_5694_ = v_isSharedCheck_5702_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_val_5691_);
lean_dec(v___x_5690_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5702_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
if (lean_obj_tag(v_val_5691_) == 5)
{
lean_object* v_v_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5699_; 
v_v_5695_ = lean_ctor_get(v_val_5691_, 0);
lean_inc(v_v_5695_);
lean_dec_ref_known(v_val_5691_, 1);
v___x_5696_ = l_Lean_Expr_mdataExpr_x21(v_p_5687_);
v___x_5697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5697_, 0, v_v_5695_);
lean_ctor_set(v___x_5697_, 1, v___x_5696_);
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 0, v___x_5697_);
v___x_5699_ = v___x_5693_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5697_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
else
{
lean_object* v___x_5701_; 
lean_del_object(v___x_5693_);
lean_dec(v_val_5691_);
v___x_5701_ = lean_box(0);
return v___x_5701_;
}
}
}
else
{
lean_object* v___x_5703_; 
lean_dec(v___x_5690_);
v___x_5703_ = lean_box(0);
return v___x_5703_;
}
}
else
{
lean_object* v___x_5704_; 
v___x_5704_ = lean_box(0);
return v___x_5704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5705_){
_start:
{
lean_object* v_res_5706_; 
v_res_5706_ = l_Lean_patternWithRef_x3f(v_p_5705_);
lean_dec_ref(v_p_5705_);
return v_res_5706_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5707_){
_start:
{
lean_object* v___x_5708_; 
v___x_5708_ = l_Lean_patternWithRef_x3f(v_p_5707_);
if (lean_obj_tag(v___x_5708_) == 0)
{
uint8_t v___x_5709_; 
v___x_5709_ = 0;
return v___x_5709_;
}
else
{
uint8_t v___x_5710_; 
lean_dec_ref_known(v___x_5708_, 1);
v___x_5710_ = 1;
return v___x_5710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5711_){
_start:
{
uint8_t v_res_5712_; lean_object* v_r_5713_; 
v_res_5712_ = l_Lean_isPatternWithRef(v_p_5711_);
lean_dec_ref(v_p_5711_);
v_r_5713_ = lean_box(v_res_5712_);
return v_r_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5714_, lean_object* v_stx_5715_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_Lean_patternWithRef_x3f(v_p_5714_);
if (lean_obj_tag(v___x_5716_) == 0)
{
lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v___x_5717_ = l_Lean_KVMap_empty;
v___x_5718_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5719_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5719_, 0, v_stx_5715_);
v___x_5720_ = l_Lean_KVMap_insert(v___x_5717_, v___x_5718_, v___x_5719_);
v___x_5721_ = l_Lean_Expr_mdata___override(v___x_5720_, v_p_5714_);
return v___x_5721_;
}
else
{
lean_dec_ref_known(v___x_5716_, 1);
lean_dec(v_stx_5715_);
return v_p_5714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5722_){
_start:
{
lean_object* v___x_5723_; 
v___x_5723_ = l_Lean_inaccessible_x3f(v_e_5722_);
if (lean_obj_tag(v___x_5723_) == 1)
{
return v___x_5723_;
}
else
{
lean_object* v___x_5724_; 
lean_dec(v___x_5723_);
v___x_5724_ = l_Lean_patternWithRef_x3f(v_e_5722_);
if (lean_obj_tag(v___x_5724_) == 1)
{
lean_object* v_val_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5733_; 
v_val_5725_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5733_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5733_ == 0)
{
v___x_5727_ = v___x_5724_;
v_isShared_5728_ = v_isSharedCheck_5733_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_val_5725_);
lean_dec(v___x_5724_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5733_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v_snd_5729_; lean_object* v___x_5731_; 
v_snd_5729_ = lean_ctor_get(v_val_5725_, 1);
lean_inc(v_snd_5729_);
lean_dec(v_val_5725_);
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 0, v_snd_5729_);
v___x_5731_ = v___x_5727_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_snd_5729_);
v___x_5731_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
return v___x_5731_;
}
}
}
else
{
lean_object* v___x_5734_; 
lean_dec(v___x_5724_);
v___x_5734_ = lean_box(0);
return v___x_5734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5735_){
_start:
{
lean_object* v_res_5736_; 
v_res_5736_ = l_Lean_patternAnnotation_x3f(v_e_5735_);
lean_dec_ref(v_e_5735_);
return v_res_5736_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5740_){
_start:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; 
v___x_5741_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5742_ = l_Lean_mkAnnotation(v___x_5741_, v_e_5740_);
return v___x_5742_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5746_){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; 
v___x_5747_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5748_ = l_Lean_annotation_x3f(v___x_5747_, v_e_5746_);
if (lean_obj_tag(v___x_5748_) == 0)
{
return v___x_5748_;
}
else
{
lean_object* v_val_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5762_; 
v_val_5749_ = lean_ctor_get(v___x_5748_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5751_ = v___x_5748_;
v_isShared_5752_ = v_isSharedCheck_5762_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_val_5749_);
lean_dec(v___x_5748_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5762_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; uint8_t v___x_5755_; 
v___x_5753_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5754_ = lean_unsigned_to_nat(3u);
v___x_5755_ = l_Lean_Expr_isAppOfArity(v_val_5749_, v___x_5753_, v___x_5754_);
if (v___x_5755_ == 0)
{
lean_object* v___x_5756_; 
lean_del_object(v___x_5751_);
lean_dec(v_val_5749_);
v___x_5756_ = lean_box(0);
return v___x_5756_;
}
else
{
lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5760_; 
v___x_5757_ = l_Lean_Expr_appFn_x21(v_val_5749_);
lean_dec(v_val_5749_);
v___x_5758_ = l_Lean_Expr_appArg_x21(v___x_5757_);
lean_dec_ref(v___x_5757_);
if (v_isShared_5752_ == 0)
{
lean_ctor_set(v___x_5751_, 0, v___x_5758_);
v___x_5760_ = v___x_5751_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v___x_5758_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l_Lean_isLHSGoal_x3f(v_e_5763_);
lean_dec_ref(v_e_5763_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5765_, lean_object* v_____do__lift_5766_){
_start:
{
lean_object* v___x_5767_; 
v___x_5767_ = lean_apply_2(v_toPure_5765_, lean_box(0), v_____do__lift_5766_);
return v___x_5767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5768_, lean_object* v_inst_5769_){
_start:
{
lean_object* v_toApplicative_5770_; lean_object* v_toBind_5771_; lean_object* v_toPure_5772_; lean_object* v___x_5773_; lean_object* v___f_5774_; lean_object* v___x_5775_; 
v_toApplicative_5770_ = lean_ctor_get(v_inst_5768_, 0);
v_toBind_5771_ = lean_ctor_get(v_inst_5768_, 1);
lean_inc(v_toBind_5771_);
v_toPure_5772_ = lean_ctor_get(v_toApplicative_5770_, 1);
lean_inc(v_toPure_5772_);
v___x_5773_ = l_Lean_mkFreshId___redArg(v_inst_5768_, v_inst_5769_);
v___f_5774_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5774_, 0, v_toPure_5772_);
v___x_5775_ = lean_apply_4(v_toBind_5771_, lean_box(0), lean_box(0), v___x_5773_, v___f_5774_);
return v___x_5775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5776_, lean_object* v_inst_5777_, lean_object* v_inst_5778_){
_start:
{
lean_object* v___x_5779_; 
v___x_5779_ = l_Lean_mkFreshFVarId___redArg(v_inst_5777_, v_inst_5778_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5780_, lean_object* v_inst_5781_){
_start:
{
lean_object* v_toApplicative_5782_; lean_object* v_toBind_5783_; lean_object* v_toPure_5784_; lean_object* v___x_5785_; lean_object* v___f_5786_; lean_object* v___x_5787_; 
v_toApplicative_5782_ = lean_ctor_get(v_inst_5780_, 0);
v_toBind_5783_ = lean_ctor_get(v_inst_5780_, 1);
lean_inc(v_toBind_5783_);
v_toPure_5784_ = lean_ctor_get(v_toApplicative_5782_, 1);
lean_inc(v_toPure_5784_);
v___x_5785_ = l_Lean_mkFreshId___redArg(v_inst_5780_, v_inst_5781_);
v___f_5786_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5786_, 0, v_toPure_5784_);
v___x_5787_ = lean_apply_4(v_toBind_5783_, lean_box(0), lean_box(0), v___x_5785_, v___f_5786_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5788_, lean_object* v_inst_5789_, lean_object* v_inst_5790_){
_start:
{
lean_object* v___x_5791_; 
v___x_5791_ = l_Lean_mkFreshMVarId___redArg(v_inst_5789_, v_inst_5790_);
return v___x_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5792_, lean_object* v_inst_5793_){
_start:
{
lean_object* v_toApplicative_5794_; lean_object* v_toBind_5795_; lean_object* v_toPure_5796_; lean_object* v___x_5797_; lean_object* v___f_5798_; lean_object* v___x_5799_; 
v_toApplicative_5794_ = lean_ctor_get(v_inst_5792_, 0);
v_toBind_5795_ = lean_ctor_get(v_inst_5792_, 1);
lean_inc(v_toBind_5795_);
v_toPure_5796_ = lean_ctor_get(v_toApplicative_5794_, 1);
lean_inc(v_toPure_5796_);
v___x_5797_ = l_Lean_mkFreshId___redArg(v_inst_5792_, v_inst_5793_);
v___f_5798_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5798_, 0, v_toPure_5796_);
v___x_5799_ = lean_apply_4(v_toBind_5795_, lean_box(0), lean_box(0), v___x_5797_, v___f_5798_);
return v___x_5799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5800_, lean_object* v_inst_5801_, lean_object* v_inst_5802_){
_start:
{
lean_object* v___x_5803_; 
v___x_5803_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5801_, v_inst_5802_);
return v___x_5803_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5807_ = lean_box(0);
v___x_5808_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5809_ = l_Lean_Expr_const___override(v___x_5808_, v___x_5807_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5810_){
_start:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5811_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5812_ = l_Lean_Expr_app___override(v___x_5811_, v_p_5810_);
return v___x_5812_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5816_ = lean_box(0);
v___x_5817_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5818_ = l_Lean_Expr_const___override(v___x_5817_, v___x_5816_);
return v___x_5818_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5819_, lean_object* v_q_5820_){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5822_ = l_Lean_mkAppB(v___x_5821_, v_p_5819_, v_q_5820_);
return v___x_5822_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5826_ = lean_box(0);
v___x_5827_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5828_ = l_Lean_Expr_const___override(v___x_5827_, v___x_5826_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5829_, lean_object* v_q_5830_){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5831_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5832_ = l_Lean_mkAppB(v___x_5831_, v_p_5829_, v_q_5830_);
return v___x_5832_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5833_ = lean_box(0);
v___x_5834_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5835_ = l_Lean_Expr_const___override(v___x_5834_, v___x_5833_);
return v___x_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5836_){
_start:
{
if (lean_obj_tag(v_x_5836_) == 0)
{
lean_object* v___x_5837_; 
v___x_5837_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5837_;
}
else
{
lean_object* v_tail_5838_; 
v_tail_5838_ = lean_ctor_get(v_x_5836_, 1);
if (lean_obj_tag(v_tail_5838_) == 0)
{
lean_object* v_head_5839_; 
v_head_5839_ = lean_ctor_get(v_x_5836_, 0);
lean_inc(v_head_5839_);
lean_dec_ref_known(v_x_5836_, 2);
return v_head_5839_;
}
else
{
lean_object* v_head_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; 
lean_inc(v_tail_5838_);
v_head_5840_ = lean_ctor_get(v_x_5836_, 0);
lean_inc(v_head_5840_);
lean_dec_ref_known(v_x_5836_, 2);
v___x_5841_ = l_Lean_mkAndN(v_tail_5838_);
v___x_5842_ = l_Lean_mkAnd(v_head_5840_, v___x_5841_);
return v___x_5842_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5848_ = lean_box(0);
v___x_5849_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5850_ = l_Lean_Expr_const___override(v___x_5849_, v___x_5848_);
return v___x_5850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5851_){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5853_ = l_Lean_Expr_app___override(v___x_5852_, v_p_5851_);
return v___x_5853_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = lean_box(0);
v___x_5858_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5859_ = l_Lean_Expr_const___override(v___x_5858_, v___x_5857_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5860_, lean_object* v_q_5861_){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5862_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5863_ = l_Lean_mkAppB(v___x_5862_, v_p_5860_, v_q_5861_);
return v___x_5863_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5864_; 
v___x_5864_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5864_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5868_ = lean_box(0);
v___x_5869_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5870_ = l_Lean_Expr_const___override(v___x_5869_, v___x_5868_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5871_; 
v___x_5871_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5871_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___x_5875_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5876_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5877_ = l_Lean_Expr_const___override(v___x_5876_, v___x_5875_);
return v___x_5877_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5878_ = l_Lean_Nat_mkInstAdd;
v___x_5879_ = l_Lean_Nat_mkType;
v___x_5880_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5881_ = l_Lean_mkAppB(v___x_5880_, v___x_5879_, v___x_5878_);
return v___x_5881_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5882_; 
v___x_5882_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5882_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5886_ = lean_box(0);
v___x_5887_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5888_ = l_Lean_Expr_const___override(v___x_5887_, v___x_5886_);
return v___x_5888_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5889_; 
v___x_5889_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5889_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5893_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5894_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5895_ = l_Lean_Expr_const___override(v___x_5894_, v___x_5893_);
return v___x_5895_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5896_ = l_Lean_Nat_mkInstSub;
v___x_5897_ = l_Lean_Nat_mkType;
v___x_5898_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5899_ = l_Lean_mkAppB(v___x_5898_, v___x_5897_, v___x_5896_);
return v___x_5899_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5900_; 
v___x_5900_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5900_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5904_ = lean_box(0);
v___x_5905_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5906_ = l_Lean_Expr_const___override(v___x_5905_, v___x_5904_);
return v___x_5906_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5907_; 
v___x_5907_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5907_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5911_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5912_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5913_ = l_Lean_Expr_const___override(v___x_5912_, v___x_5911_);
return v___x_5913_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5914_ = l_Lean_Nat_mkInstMul;
v___x_5915_ = l_Lean_Nat_mkType;
v___x_5916_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_5917_ = l_Lean_mkAppB(v___x_5916_, v___x_5915_, v___x_5914_);
return v___x_5917_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_5918_; 
v___x_5918_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_5918_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; 
v___x_5923_ = lean_box(0);
v___x_5924_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_5925_ = l_Lean_Expr_const___override(v___x_5924_, v___x_5923_);
return v___x_5925_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_5926_; 
v___x_5926_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_5926_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5930_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5931_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_5932_ = l_Lean_Expr_const___override(v___x_5931_, v___x_5930_);
return v___x_5932_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5933_ = l_Lean_Nat_mkInstDiv;
v___x_5934_ = l_Lean_Nat_mkType;
v___x_5935_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_5936_ = l_Lean_mkAppB(v___x_5935_, v___x_5934_, v___x_5933_);
return v___x_5936_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_5937_; 
v___x_5937_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_5937_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; 
v___x_5942_ = lean_box(0);
v___x_5943_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_5944_ = l_Lean_Expr_const___override(v___x_5943_, v___x_5942_);
return v___x_5944_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_5945_; 
v___x_5945_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_5945_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; 
v___x_5949_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5950_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_5951_ = l_Lean_Expr_const___override(v___x_5950_, v___x_5949_);
return v___x_5951_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5952_ = l_Lean_Nat_mkInstMod;
v___x_5953_ = l_Lean_Nat_mkType;
v___x_5954_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_5955_ = l_Lean_mkAppB(v___x_5954_, v___x_5953_, v___x_5952_);
return v___x_5955_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_5956_; 
v___x_5956_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_5956_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; 
v___x_5960_ = lean_box(0);
v___x_5961_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_5962_ = l_Lean_Expr_const___override(v___x_5961_, v___x_5960_);
return v___x_5962_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_5963_; 
v___x_5963_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_5963_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5967_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5968_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_5969_ = l_Lean_Expr_const___override(v___x_5968_, v___x_5967_);
return v___x_5969_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
v___x_5970_ = l_Lean_Nat_mkInstNatPow;
v___x_5971_ = l_Lean_Nat_mkType;
v___x_5972_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_5973_ = l_Lean_mkAppB(v___x_5972_, v___x_5971_, v___x_5970_);
return v___x_5973_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_5974_; 
v___x_5974_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_5974_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5981_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_5982_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_5983_ = l_Lean_Expr_const___override(v___x_5982_, v___x_5981_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5984_ = l_Lean_Nat_mkInstPow;
v___x_5985_ = l_Lean_Nat_mkType;
v___x_5986_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_5987_ = l_Lean_mkApp3(v___x_5986_, v___x_5985_, v___x_5985_, v___x_5984_);
return v___x_5987_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_5988_; 
v___x_5988_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_5988_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; 
v___x_5992_ = lean_box(0);
v___x_5993_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_5994_ = l_Lean_Expr_const___override(v___x_5993_, v___x_5992_);
return v___x_5994_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_5995_; 
v___x_5995_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_5995_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v___x_5999_ = lean_box(0);
v___x_6000_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6001_ = l_Lean_Expr_const___override(v___x_6000_, v___x_5999_);
return v___x_6001_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6002_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; 
v___x_6008_ = lean_unsigned_to_nat(0u);
v___x_6009_ = l_Lean_Level_ofNat(v___x_6008_);
return v___x_6009_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; 
v___x_6010_ = lean_box(0);
v___x_6011_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6011_);
lean_ctor_set(v___x_6012_, 1, v___x_6010_);
return v___x_6012_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6013_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6014_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set(v___x_6015_, 1, v___x_6013_);
return v___x_6015_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6016_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6017_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6017_);
lean_ctor_set(v___x_6018_, 1, v___x_6016_);
return v___x_6018_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v___x_6019_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6020_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6021_ = l_Lean_Expr_const___override(v___x_6020_, v___x_6019_);
return v___x_6021_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6022_ = l_Lean_Nat_mkInstHAdd;
v___x_6023_ = l_Lean_Nat_mkType;
v___x_6024_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6025_ = l_Lean_mkApp4(v___x_6024_, v___x_6023_, v___x_6023_, v___x_6023_, v___x_6022_);
return v___x_6025_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6026_; 
v___x_6026_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6026_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6032_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6033_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6034_ = l_Lean_Expr_const___override(v___x_6033_, v___x_6032_);
return v___x_6034_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6035_ = l_Lean_Nat_mkInstHSub;
v___x_6036_ = l_Lean_Nat_mkType;
v___x_6037_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6038_ = l_Lean_mkApp4(v___x_6037_, v___x_6036_, v___x_6036_, v___x_6036_, v___x_6035_);
return v___x_6038_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6039_; 
v___x_6039_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6039_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6045_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6046_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6047_ = l_Lean_Expr_const___override(v___x_6046_, v___x_6045_);
return v___x_6047_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6048_ = l_Lean_Nat_mkInstHMul;
v___x_6049_ = l_Lean_Nat_mkType;
v___x_6050_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6051_ = l_Lean_mkApp4(v___x_6050_, v___x_6049_, v___x_6049_, v___x_6049_, v___x_6048_);
return v___x_6051_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6052_; 
v___x_6052_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6052_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6058_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6059_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6060_ = l_Lean_Expr_const___override(v___x_6059_, v___x_6058_);
return v___x_6060_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; 
v___x_6061_ = l_Lean_Nat_mkInstHPow;
v___x_6062_ = l_Lean_Nat_mkType;
v___x_6063_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6064_ = l_Lean_mkApp4(v___x_6063_, v___x_6062_, v___x_6062_, v___x_6062_, v___x_6061_);
return v___x_6064_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6065_; 
v___x_6065_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6065_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6070_ = lean_box(0);
v___x_6071_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6072_ = l_Lean_Expr_const___override(v___x_6071_, v___x_6070_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6073_){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; 
v___x_6074_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6075_ = l_Lean_Expr_app___override(v___x_6074_, v_a_6073_);
return v___x_6075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6076_, lean_object* v_b_6077_){
_start:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6078_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6079_ = l_Lean_mkAppB(v___x_6078_, v_a_6076_, v_b_6077_);
return v___x_6079_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6080_, lean_object* v_b_6081_){
_start:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6082_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6083_ = l_Lean_mkAppB(v___x_6082_, v_a_6080_, v_b_6081_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6084_, lean_object* v_b_6085_){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; 
v___x_6086_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6087_ = l_Lean_mkAppB(v___x_6086_, v_a_6084_, v_b_6085_);
return v___x_6087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6088_, lean_object* v_b_6089_){
_start:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6091_ = l_Lean_mkAppB(v___x_6090_, v_a_6088_, v_b_6089_);
return v___x_6091_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6097_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6098_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6099_ = l_Lean_Expr_const___override(v___x_6098_, v___x_6097_);
return v___x_6099_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6100_ = l_Lean_Nat_mkInstLE;
v___x_6101_ = l_Lean_Nat_mkType;
v___x_6102_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6103_ = l_Lean_mkAppB(v___x_6102_, v___x_6101_, v___x_6100_);
return v___x_6103_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6104_; 
v___x_6104_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6104_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6105_, lean_object* v_b_6106_){
_start:
{
lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6107_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6108_ = l_Lean_mkAppB(v___x_6107_, v_a_6105_, v_b_6106_);
return v___x_6108_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6109_ = lean_unsigned_to_nat(1u);
v___x_6110_ = l_Lean_Level_ofNat(v___x_6109_);
return v___x_6110_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6111_ = lean_box(0);
v___x_6112_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_6111_);
return v___x_6113_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6114_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6115_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6116_ = l_Lean_Expr_const___override(v___x_6115_, v___x_6114_);
return v___x_6116_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; 
v___x_6117_ = l_Lean_Nat_mkType;
v___x_6118_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6119_ = l_Lean_Expr_app___override(v___x_6118_, v___x_6117_);
return v___x_6119_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6120_; 
v___x_6120_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6121_, lean_object* v_b_6122_){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6123_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6124_ = l_Lean_mkAppB(v___x_6123_, v_a_6121_, v_b_6122_);
return v___x_6124_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6125_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6126_ = l_Lean_Expr_sort___override(v___x_6125_);
return v___x_6126_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6127_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6128_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6129_ = l_Lean_Expr_app___override(v___x_6128_, v___x_6127_);
return v___x_6129_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6130_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6131_, lean_object* v_b_6132_){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; 
v___x_6133_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6134_ = l_Lean_mkAppB(v___x_6133_, v_a_6131_, v_b_6132_);
return v___x_6134_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; 
v___x_6138_ = lean_box(0);
v___x_6139_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6140_ = l_Lean_Expr_const___override(v___x_6139_, v___x_6138_);
return v___x_6140_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6141_; 
v___x_6141_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6141_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6146_ = lean_box(0);
v___x_6147_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6148_ = l_Lean_Expr_const___override(v___x_6147_, v___x_6146_);
return v___x_6148_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6149_; 
v___x_6149_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6149_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6154_ = lean_box(0);
v___x_6155_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6156_ = l_Lean_Expr_const___override(v___x_6155_, v___x_6154_);
return v___x_6156_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6157_; 
v___x_6157_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6157_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; 
v___x_6158_ = l_Lean_Int_mkInstAdd;
v___x_6159_ = l_Lean_Int_mkType;
v___x_6160_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6161_ = l_Lean_mkAppB(v___x_6160_, v___x_6159_, v___x_6158_);
return v___x_6161_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6162_; 
v___x_6162_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6162_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6167_ = lean_box(0);
v___x_6168_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6169_ = l_Lean_Expr_const___override(v___x_6168_, v___x_6167_);
return v___x_6169_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6170_; 
v___x_6170_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6170_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v___x_6171_ = l_Lean_Int_mkInstSub;
v___x_6172_ = l_Lean_Int_mkType;
v___x_6173_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6174_ = l_Lean_mkAppB(v___x_6173_, v___x_6172_, v___x_6171_);
return v___x_6174_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6175_; 
v___x_6175_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6175_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6180_ = lean_box(0);
v___x_6181_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6182_ = l_Lean_Expr_const___override(v___x_6181_, v___x_6180_);
return v___x_6182_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6183_; 
v___x_6183_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6183_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; 
v___x_6184_ = l_Lean_Int_mkInstMul;
v___x_6185_ = l_Lean_Int_mkType;
v___x_6186_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6187_ = l_Lean_mkAppB(v___x_6186_, v___x_6185_, v___x_6184_);
return v___x_6187_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6188_; 
v___x_6188_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6188_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
v___x_6192_ = lean_box(0);
v___x_6193_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6194_ = l_Lean_Expr_const___override(v___x_6193_, v___x_6192_);
return v___x_6194_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6195_; 
v___x_6195_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6195_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6196_ = l_Lean_Int_mkInstDiv;
v___x_6197_ = l_Lean_Int_mkType;
v___x_6198_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6199_ = l_Lean_mkAppB(v___x_6198_, v___x_6197_, v___x_6196_);
return v___x_6199_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6200_; 
v___x_6200_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6200_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; 
v___x_6204_ = lean_box(0);
v___x_6205_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6206_ = l_Lean_Expr_const___override(v___x_6205_, v___x_6204_);
return v___x_6206_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6207_; 
v___x_6207_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6207_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; 
v___x_6208_ = l_Lean_Int_mkInstMod;
v___x_6209_ = l_Lean_Int_mkType;
v___x_6210_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6211_ = l_Lean_mkAppB(v___x_6210_, v___x_6209_, v___x_6208_);
return v___x_6211_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6212_; 
v___x_6212_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6212_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; 
v___x_6217_ = lean_box(0);
v___x_6218_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6219_ = l_Lean_Expr_const___override(v___x_6218_, v___x_6217_);
return v___x_6219_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6220_; 
v___x_6220_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6220_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v___x_6221_ = l_Lean_Int_mkInstPow;
v___x_6222_ = l_Lean_Int_mkType;
v___x_6223_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6224_ = l_Lean_mkAppB(v___x_6223_, v___x_6222_, v___x_6221_);
return v___x_6224_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6225_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; 
v___x_6226_ = l_Lean_Int_mkInstPowNat;
v___x_6227_ = l_Lean_Nat_mkType;
v___x_6228_ = l_Lean_Int_mkType;
v___x_6229_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6230_ = l_Lean_mkApp3(v___x_6229_, v___x_6228_, v___x_6227_, v___x_6226_);
return v___x_6230_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6231_; 
v___x_6231_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6231_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6236_ = lean_box(0);
v___x_6237_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6238_ = l_Lean_Expr_const___override(v___x_6237_, v___x_6236_);
return v___x_6238_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6239_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; 
v___x_6244_ = lean_box(0);
v___x_6245_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6246_ = l_Lean_Expr_const___override(v___x_6245_, v___x_6244_);
return v___x_6246_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6247_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; 
v___x_6251_ = lean_box(0);
v___x_6252_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6253_ = l_Lean_Expr_const___override(v___x_6252_, v___x_6251_);
return v___x_6253_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6254_; 
v___x_6254_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6254_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; 
v___x_6255_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6256_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6257_ = l_Lean_Expr_const___override(v___x_6256_, v___x_6255_);
return v___x_6257_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; 
v___x_6258_ = l_Lean_Int_mkInstNeg;
v___x_6259_ = l_Lean_Int_mkType;
v___x_6260_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6261_ = l_Lean_mkAppB(v___x_6260_, v___x_6259_, v___x_6258_);
return v___x_6261_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6262_; 
v___x_6262_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6262_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; 
v___x_6263_ = l_Lean_Int_mkInstHAdd;
v___x_6264_ = l_Lean_Int_mkType;
v___x_6265_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6266_ = l_Lean_mkApp4(v___x_6265_, v___x_6264_, v___x_6264_, v___x_6264_, v___x_6263_);
return v___x_6266_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6267_; 
v___x_6267_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6267_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; 
v___x_6268_ = l_Lean_Int_mkInstHSub;
v___x_6269_ = l_Lean_Int_mkType;
v___x_6270_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6271_ = l_Lean_mkApp4(v___x_6270_, v___x_6269_, v___x_6269_, v___x_6269_, v___x_6268_);
return v___x_6271_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6272_; 
v___x_6272_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6272_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; 
v___x_6273_ = l_Lean_Int_mkInstHMul;
v___x_6274_ = l_Lean_Int_mkType;
v___x_6275_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6276_ = l_Lean_mkApp4(v___x_6275_, v___x_6274_, v___x_6274_, v___x_6274_, v___x_6273_);
return v___x_6276_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6277_; 
v___x_6277_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6277_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3(void){
_start:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6283_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6284_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intDivFn___closed__2));
v___x_6285_ = l_Lean_Expr_const___override(v___x_6284_, v___x_6283_);
return v___x_6285_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4(void){
_start:
{
lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; 
v___x_6286_ = l_Lean_Int_mkInstHDiv;
v___x_6287_ = l_Lean_Int_mkType;
v___x_6288_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__3, &l___private_Lean_Expr_0__Lean_intDivFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__3);
v___x_6289_ = l_Lean_mkApp4(v___x_6288_, v___x_6287_, v___x_6287_, v___x_6287_, v___x_6286_);
return v___x_6289_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6290_; 
v___x_6290_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__4, &l___private_Lean_Expr_0__Lean_intDivFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__4);
return v___x_6290_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3(void){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6296_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6297_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intModFn___closed__2));
v___x_6298_ = l_Lean_Expr_const___override(v___x_6297_, v___x_6296_);
return v___x_6298_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4(void){
_start:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; 
v___x_6299_ = l_Lean_Int_mkInstHMod;
v___x_6300_ = l_Lean_Int_mkType;
v___x_6301_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__3, &l___private_Lean_Expr_0__Lean_intModFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__3);
v___x_6302_ = l_Lean_mkApp4(v___x_6301_, v___x_6300_, v___x_6300_, v___x_6300_, v___x_6299_);
return v___x_6302_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6303_; 
v___x_6303_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__4, &l___private_Lean_Expr_0__Lean_intModFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__4);
return v___x_6303_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; 
v___x_6304_ = l_Lean_Int_mkInstHPow;
v___x_6305_ = l_Lean_Nat_mkType;
v___x_6306_ = l_Lean_Int_mkType;
v___x_6307_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6308_ = l_Lean_mkApp4(v___x_6307_, v___x_6306_, v___x_6305_, v___x_6306_, v___x_6304_);
return v___x_6308_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6309_; 
v___x_6309_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6309_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6315_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6316_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6317_ = l_Lean_Expr_const___override(v___x_6316_, v___x_6315_);
return v___x_6317_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6318_ = l_Lean_Int_mkInstNatCast;
v___x_6319_ = l_Lean_Int_mkType;
v___x_6320_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6321_ = l_Lean_mkAppB(v___x_6320_, v___x_6319_, v___x_6318_);
return v___x_6321_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6322_; 
v___x_6322_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6323_){
_start:
{
lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6324_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6325_ = l_Lean_Expr_app___override(v___x_6324_, v_a_6323_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6326_, lean_object* v_b_6327_){
_start:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; 
v___x_6328_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6329_ = l_Lean_mkAppB(v___x_6328_, v_a_6326_, v_b_6327_);
return v___x_6329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6330_, lean_object* v_b_6331_){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; 
v___x_6332_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6333_ = l_Lean_mkAppB(v___x_6332_, v_a_6330_, v_b_6331_);
return v___x_6333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6334_, lean_object* v_b_6335_){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6336_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6337_ = l_Lean_mkAppB(v___x_6336_, v_a_6334_, v_b_6335_);
return v___x_6337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6338_, lean_object* v_b_6339_){
_start:
{
lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6340_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6341_ = l_Lean_mkAppB(v___x_6340_, v_a_6338_, v_b_6339_);
return v___x_6341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6342_, lean_object* v_b_6343_){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6344_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6345_ = l_Lean_mkAppB(v___x_6344_, v_a_6342_, v_b_6343_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6346_){
_start:
{
lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6347_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6348_ = l_Lean_Expr_app___override(v___x_6347_, v_a_6346_);
return v___x_6348_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6349_, lean_object* v_b_6350_){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; 
v___x_6351_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6352_ = l_Lean_mkAppB(v___x_6351_, v_a_6349_, v_b_6350_);
return v___x_6352_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; 
v___x_6353_ = l_Lean_Int_mkInstLE;
v___x_6354_ = l_Lean_Int_mkType;
v___x_6355_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6356_ = l_Lean_mkAppB(v___x_6355_, v___x_6354_, v___x_6353_);
return v___x_6356_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6357_; 
v___x_6357_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6358_, lean_object* v_b_6359_){
_start:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6360_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6361_ = l_Lean_mkAppB(v___x_6360_, v_a_6358_, v_b_6359_);
return v___x_6361_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; 
v___x_6367_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6368_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6369_ = l_Lean_Expr_const___override(v___x_6368_, v___x_6367_);
return v___x_6369_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6370_ = l_Lean_Int_mkInstLT;
v___x_6371_ = l_Lean_Int_mkType;
v___x_6372_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6373_ = l_Lean_mkAppB(v___x_6372_, v___x_6371_, v___x_6370_);
return v___x_6373_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6374_; 
v___x_6374_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6375_, lean_object* v_b_6376_){
_start:
{
lean_object* v___x_6377_; lean_object* v___x_6378_; 
v___x_6377_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6378_ = l_Lean_mkAppB(v___x_6377_, v_a_6375_, v_b_6376_);
return v___x_6378_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; 
v___x_6379_ = l_Lean_Int_mkType;
v___x_6380_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6381_ = l_Lean_Expr_app___override(v___x_6380_, v___x_6379_);
return v___x_6381_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6382_; 
v___x_6382_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6382_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6383_, lean_object* v_b_6384_){
_start:
{
lean_object* v___x_6385_; lean_object* v___x_6386_; 
v___x_6385_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6386_ = l_Lean_mkAppB(v___x_6385_, v_a_6383_, v_b_6384_);
return v___x_6386_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; 
v___x_6392_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6393_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6394_ = l_Lean_Expr_const___override(v___x_6393_, v___x_6392_);
return v___x_6394_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; 
v___x_6399_ = lean_box(0);
v___x_6400_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6401_ = l_Lean_Expr_const___override(v___x_6400_, v___x_6399_);
return v___x_6401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6402_, lean_object* v_b_6403_){
_start:
{
lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6404_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6405_ = l_Lean_Int_mkType;
v___x_6406_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6407_ = l_Lean_mkApp4(v___x_6404_, v___x_6405_, v___x_6406_, v_a_6402_, v_b_6403_);
return v___x_6407_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; 
v___x_6411_ = lean_box(0);
v___x_6412_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6413_ = l_Lean_Expr_const___override(v___x_6412_, v___x_6411_);
return v___x_6413_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6414_ = lean_unsigned_to_nat(0u);
v___x_6415_ = lean_nat_to_int(v___x_6414_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6416_){
_start:
{
lean_object* v___x_6417_; lean_object* v_r_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v_r_6423_; lean_object* v___x_6424_; uint8_t v___x_6425_; 
v___x_6417_ = lean_nat_abs(v_n_6416_);
v_r_6418_ = l_Lean_mkRawNatLit(v___x_6417_);
v___x_6419_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6420_ = l_Lean_Int_mkType;
v___x_6421_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6418_);
v___x_6422_ = l_Lean_Expr_app___override(v___x_6421_, v_r_6418_);
v_r_6423_ = l_Lean_mkApp3(v___x_6419_, v___x_6420_, v_r_6418_, v___x_6422_);
v___x_6424_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6425_ = lean_int_dec_lt(v_n_6416_, v___x_6424_);
if (v___x_6425_ == 0)
{
return v_r_6423_;
}
else
{
lean_object* v___x_6426_; 
v___x_6426_ = l_Lean_mkIntNeg(v_r_6423_);
return v___x_6426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6427_){
_start:
{
lean_object* v_res_6428_; 
v_res_6428_ = l_Lean_mkIntLit(v_n_6427_);
lean_dec(v_n_6427_);
return v_res_6428_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6433_ = lean_box(0);
v___x_6434_ = l_Lean_Level_succ___override(v___x_6433_);
return v___x_6434_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; 
v___x_6435_ = lean_box(0);
v___x_6436_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6437_, 0, v___x_6436_);
lean_ctor_set(v___x_6437_, 1, v___x_6435_);
return v___x_6437_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; 
v___x_6438_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6439_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6440_ = l_Lean_Expr_const___override(v___x_6439_, v___x_6438_);
return v___x_6440_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; 
v___x_6443_ = lean_box(0);
v___x_6444_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6445_ = l_Lean_Expr_const___override(v___x_6444_, v___x_6443_);
return v___x_6445_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; 
v___x_6446_ = lean_box(0);
v___x_6447_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6448_ = l_Lean_Expr_const___override(v___x_6447_, v___x_6446_);
return v___x_6448_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6449_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6450_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6451_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6452_ = l_Lean_mkAppB(v___x_6451_, v___x_6450_, v___x_6449_);
return v___x_6452_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6453_; 
v___x_6453_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6453_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6454_ = lean_box(0);
v___x_6455_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__1));
v___x_6456_ = l_Lean_Expr_const___override(v___x_6455_, v___x_6454_);
return v___x_6456_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; 
v___x_6457_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6458_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6459_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6460_ = l_Lean_mkAppB(v___x_6459_, v___x_6458_, v___x_6457_);
return v___x_6460_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6461_; 
v___x_6461_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6461_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; 
v___x_6465_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6466_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6467_ = l_Lean_Expr_const___override(v___x_6466_, v___x_6465_);
return v___x_6467_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; 
v___x_6468_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6469_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6470_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6471_ = l_Lean_mkApp3(v___x_6470_, v___x_6469_, v___x_6468_, v___x_6468_);
return v___x_6471_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; 
v___x_6472_ = l_Lean_reflBoolTrue;
v___x_6473_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6474_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6475_ = l_Lean_mkAppB(v___x_6474_, v___x_6473_, v___x_6472_);
return v___x_6475_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6476_; 
v___x_6476_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6476_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; 
v___x_6477_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6478_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6479_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6480_ = l_Lean_mkApp3(v___x_6479_, v___x_6478_, v___x_6477_, v___x_6477_);
return v___x_6480_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6481_ = l_Lean_reflBoolFalse;
v___x_6482_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6483_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6484_ = l_Lean_mkAppB(v___x_6483_, v___x_6482_, v___x_6481_);
return v___x_6484_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6485_; 
v___x_6485_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6485_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; 
v___x_6488_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6489_ = lean_unsigned_to_nat(9u);
v___x_6490_ = lean_unsigned_to_nat(2441u);
v___x_6491_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6492_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6493_ = l_mkPanicMessageWithDecl(v___x_6492_, v___x_6491_, v___x_6490_, v___x_6489_, v___x_6488_);
return v___x_6493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6494_, lean_object* v_declName_6495_){
_start:
{
switch(lean_obj_tag(v_e_6494_))
{
case 5:
{
lean_object* v_fn_6496_; lean_object* v_arg_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; 
v_fn_6496_ = lean_ctor_get(v_e_6494_, 0);
lean_inc_ref(v_fn_6496_);
v_arg_6497_ = lean_ctor_get(v_e_6494_, 1);
lean_inc_ref(v_arg_6497_);
lean_dec_ref_known(v_e_6494_, 2);
v___x_6498_ = l_Lean_Expr_replaceFn(v_fn_6496_, v_declName_6495_);
v___x_6499_ = l_Lean_Expr_app___override(v___x_6498_, v_arg_6497_);
return v___x_6499_;
}
case 4:
{
lean_object* v_us_6500_; lean_object* v___x_6501_; 
v_us_6500_ = lean_ctor_get(v_e_6494_, 1);
lean_inc(v_us_6500_);
lean_dec_ref_known(v_e_6494_, 2);
v___x_6501_ = l_Lean_Expr_const___override(v_declName_6495_, v_us_6500_);
return v___x_6501_;
}
default: 
{
lean_object* v___x_6502_; lean_object* v___x_6503_; 
lean_dec(v_declName_6495_);
lean_dec_ref(v_e_6494_);
v___x_6502_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6503_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6502_);
return v___x_6503_;
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
